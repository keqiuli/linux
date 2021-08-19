/*
 * Copyright (c) 2000-2019 Stephen Williams (steve@icarus.com)
 *
 *    This source code is free software; you can redistribute it
 *    and/or modify it in source code form under the terms of the GNU
 *    General Public License as published by the Free Software
 *    Foundation; either version 2 of the License, or (at your option)
 *    any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.
 */

# include "config.h"

# include  <iostream>
# include  <set>
# include  <cstdlib>
# include  <string.h>
#include <algorithm>

/*
 * This source file contains all the implementations of the Design
 * class declared in netlist.h.
 */

# include  "netlist.h"
# include  "util.h"
# include  "compiler.h"
# include  "netmisc.h"
# include  "PExpr.h"
# include  "PTask.h"
# include  <sstream>
# include  "ivl_assert.h"


Design:: Design()
    : errors(0), nodes_(0), procs_(0), aprocs_(0)
{
      branches_ = 0;
      procs_idx_ = 0;
      des_precision_ = 0;
      nodes_functor_cur_ = 0;
      nodes_functor_nxt_ = 0;
      des_delay_sel_ = Design::TYP;
}

Design::~Design()
{
}

void Design::set_precision(int val)
{
      if (val < des_precision_)
	    des_precision_ = val;
}

int Design::get_precision() const
{
      return des_precision_;
}

void Design::set_delay_sel(delay_sel_t sel)
{
      des_delay_sel_ = sel;
}

const char* Design::get_delay_sel() const
{
      switch (des_delay_sel_) {
	case Design::MIN:
	    return "MINIMUM";
	    break;
	case Design::TYP:
	    return "TYPICAL";
	    break;
	case Design::MAX:
	    return "MAXIMUM";
	    break;
	default:
	    assert(0);
	    return "TYPICAL";
      }
}


uint64_t Design::scale_to_precision(uint64_t val,
				    const NetScope*scope) const
{
      int units = scope->time_unit();
      assert( units >= des_precision_ );

      while (units > des_precision_) {
	    units -= 1;
	    val *= 10;
      }

      return val;
}

NetScope* Design::make_root_scope(perm_string root, NetScope*unit_scope,
				  bool program_block, bool is_interface)
{
      NetScope *root_scope_;
      root_scope_ = new NetScope(0, hname_t(root), NetScope::MODULE, unit_scope,
				 false, program_block, is_interface);
	/* This relies on the fact that the basename return value is
	   permallocated. */
      root_scope_->set_module_name(root_scope_->basename());
      root_scopes_.push_back(root_scope_);
      return root_scope_;
}

NetScope* Design::find_root_scope()
{
      assert(root_scopes_.front());
      return root_scopes_.front();
}

list<NetScope*> Design::find_root_scopes() const
{
      return root_scopes_;
}

NetScope* Design::make_package_scope(perm_string name, NetScope*unit_scope,
				     bool is_unit)
{
      NetScope*scope;

      scope = new NetScope(0, hname_t(name), NetScope::PACKAGE, unit_scope,
			   false, false, false, is_unit);
      scope->set_module_name(scope->basename());
      packages_[name] = scope;
      return scope;
}

NetScope* Design::find_package(perm_string name) const
{
      map<perm_string,NetScope*>::const_iterator cur = packages_.find(name);
      if (cur == packages_.end())
	    return 0;

      return cur->second;
}

list<NetScope*> Design::find_package_scopes() const
{
      list<NetScope*>res;
      for (map<perm_string,NetScope*>::const_iterator cur = packages_.begin()
		 ; cur != packages_.end() ; ++cur) {
	    res.push_back (cur->second);
      }

      return res;
}

/*
 * This method locates a scope in the design, given its rooted
 * hierarchical name. Each component of the key is used to scan one
 * more step down the tree until the name runs out or the search
 * fails.
 */
NetScope* Design::find_scope(const std::list<hname_t>&path) const
{
      if (path.empty())
	    return 0;

      for (list<NetScope*>::const_iterator scope = root_scopes_.begin()
		 ; scope != root_scopes_.end(); ++ scope ) {

	    NetScope*cur = *scope;
	    if (path.front() != cur->fullname())
		  continue;

	    std::list<hname_t> tmp = path;
	    tmp.pop_front();

	    while (cur) {
		  if (tmp.empty()) return cur;

		  cur = cur->child( tmp.front() );

		  tmp.pop_front();
	    }
      }

      return 0;
}

/*
 * This method locates a scope in the design, given its rooted
 * hierarchical name. Each component of the key is used to scan one
 * more step down the tree until the name runs out or the search
 * fails.
 */
NetScope* Design::find_scope(const hname_t&path) const
{
      for (list<NetScope*>::const_iterator scope = root_scopes_.begin()
		 ; scope != root_scopes_.end(); ++ scope ) {

	    NetScope*cur = *scope;
	    if (path.peek_name() == cur->basename())
		  return cur;

      }

      return 0;
}

static bool is_design_unit(NetScope*scope)
{
      return (scope->type() == NetScope::MODULE && !scope->nested_module())
	  || (scope->type() == NetScope::PACKAGE);
}

static bool is_subroutine(NetScope::TYPE type)
{
      return type == NetScope::TASK || type == NetScope::FUNC;
}

/*
 * This method locates a scope within another scope, given its relative
 * hierarchical name. Each component of the key is used to scan one
 * more step down the tree until the name runs out or the search
 * fails.
 */
NetScope* Design::find_scope_(NetScope*scope, const std::list<hname_t>&path,
                              NetScope::TYPE type) const
{
      std::list<hname_t> tmp = path;

      do {
	    hname_t key = tmp.front();
	      /* If we are looking for a module or we are not
	       * looking at the last path component check for
	       * a name match (second line). */
	    if (scope->type() == NetScope::MODULE
		&& (type == NetScope::MODULE || tmp.size() > 1)
		&& scope->module_name()==key.peek_name()) {

		    /* Up references may match module name */

	    } else {
		  NetScope*found_scope = scope->child(key);
		  if (found_scope == 0) {
			found_scope = scope->find_import(this, key.peek_name());
			if (found_scope)
			      found_scope = found_scope->child(key);
		  }
		  scope = found_scope;
		  if (scope == 0) break;
	    }
	    tmp.pop_front();
      } while (! tmp.empty());

      return scope;
}

/*
 * This is a relative lookup of a scope by name. The starting point is
 * the scope parameter within which I start looking for the scope. If
 * I do not find the scope within the passed scope, start looking in
 * parent scopes until I find it, or I run out of parent scopes.
 */
NetScope* Design::find_scope(NetScope*scope, const std::list<hname_t>&path,
                             NetScope::TYPE type) const
{
      assert(scope);
      if (path.empty())
	    return scope;

	// Record the compilation unit scope for use later.
      NetScope*unit_scope = scope->unit();

	// First search upwards through the hierarchy.
      while (scope) {
	    NetScope*found_scope = find_scope_(scope, path, type);
	    if (found_scope)
		  return found_scope;

	      // Avoid searching the unit scope twice.
	    if (scope == unit_scope)
		  unit_scope = 0;

	      // Special case - see IEEE 1800-2012 section 23.8.1.
	    if (unit_scope && is_design_unit(scope) && is_subroutine(type)) {
		  found_scope = find_scope_(unit_scope, path, type);
		  if (found_scope)
			  return found_scope;

		  unit_scope = 0;
	    }

	    scope = scope->parent();
      }

	// If we haven't already done so, search the compilation unit scope.
      if (unit_scope) {
	    NetScope*found_scope = find_scope_(unit_scope, path, type);
	    if (found_scope)
		  return found_scope;
      }

	// Last chance. Look for the name starting at the root.
      return find_scope(path);
}

/*
 * This method locates a scope within another scope, given its relative
 * hierarchical name. Each component of the key is used to scan one
 * more step down the tree until the name runs out or the search
 * fails.
 */
NetScope* Design::find_scope_(NetScope*scope, const hname_t&path,
                              NetScope::TYPE type) const
{
	/* If we are looking for a module or we are not
	 * looking at the last path component check for
	 * a name match (second line). */
      if ((scope->type() == NetScope::MODULE) && (type == NetScope::MODULE)
	  && (scope->module_name() == path.peek_name())) {
	      /* Up references may match module name */
	    return scope;
      }
      NetScope*found_scope = scope->child(path);
      if (found_scope == 0) {
	    found_scope = scope->find_import(this, path.peek_name());
	    if (found_scope)
		  found_scope = found_scope->child(path);
      }
      return found_scope;
}

/*
 * This is a relative lookup of a scope by name. The starting point is
 * the scope parameter within which I start looking for the scope. If
 * I do not find the scope within the passed scope, start looking in
 * parent scopes until I find it, or I run out of parent scopes.
 */
NetScope* Design::find_scope(NetScope*scope, const hname_t&path,
                             NetScope::TYPE type) const
{
      assert(scope);

	// Record the compilation unit scope for use later.
      NetScope*unit_scope = scope->unit();

	// First search upwards through the hierarchy.
      while (scope) {
	    NetScope*found_scope = find_scope_(scope, path, type);
	    if (found_scope)
		  return found_scope;

	      // Avoid searching the unit scope twice.
	    if (scope == unit_scope)
		  unit_scope = 0;

	      // Special case - see IEEE 1800-2012 section 23.8.1.
	    if (unit_scope && is_design_unit(scope) && is_subroutine(type)) {
		  found_scope = find_scope_(unit_scope, path, type);
		  if (found_scope)
			  return found_scope;

		  unit_scope = 0;
	    }

	    scope = scope->parent();
      }

	// If we haven't already done so, search the compilation unit scope.
      if (unit_scope) {
	    NetScope*found_scope = find_scope_(unit_scope, path, type);
	    if (found_scope)
		  return found_scope;
      }

	// Last chance. Look for the name starting at the root.
      list<hname_t>path_list;
      path_list.push_back(path);
      return find_scope(path_list);
}

/*
 * This method runs through the scope, noticing the defparam
 * statements that were collected during the elaborate_scope pass and
 * applying them to the target parameters. The implementation actually
 * works by using a specialized method from the NetScope class that
 * does all the work for me.
 */
void Design::run_defparams()
{
      for (list<NetScope*>::const_iterator scope = root_scopes_.begin();
	   scope != root_scopes_.end(); ++ scope )
	    (*scope)->run_defparams(this);
}

void NetScope::run_defparams(Design*des)
{
      for (map<hname_t,NetScope*>::const_iterator cur = children_.begin()
		 ; cur != children_.end() ; ++ cur )
	    cur->second->run_defparams(des);

      while (! defparams.empty()) {
	    pair<pform_name_t,PExpr*> pp = defparams.front();
	    defparams.pop_front();

	    pform_name_t path = pp.first;
	    PExpr*val = pp.second;

	    perm_string perm_name = peek_tail_name(path);
	    path.pop_back();

	    list<hname_t> eval_path = eval_scope_path(des, this, path);

	      /* If there is no path on the name, then the targ_scope
		 is the current scope. */
	    NetScope*targ_scope = des->find_scope(this, eval_path);
	    if (targ_scope == 0) {

		    // Push the defparam onto a list for retry
		    // later. It is possible for the scope lookup to
		    // fail if the scope being defparam'd into is
		    // generated by an index array for generate.
		  eval_path.push_back(hname_t(perm_name));
		  defparams_later.push_back(make_pair(eval_path,val));
		  continue;
	    }

	    bool flag = targ_scope->replace_parameter(perm_name, val, this);
	    if (! flag) {
		  cerr << val->get_fileline() << ": warning: parameter "
		       << perm_name << " not found in "
		       << scope_path(targ_scope) << "." << endl;
	    }

      }

	// If some of the defparams didn't find a scope in the name,
	// then try again later. It may be that the target scope is
	// created later by generate scheme or instance array.
      if (! defparams_later.empty())
	    des->defparams_later.insert(this);
}

void NetScope::run_defparams_later(Design*des)
{
      set<NetScope*> target_scopes;
      list<pair<list<hname_t>,PExpr*> > defparams_even_later;

      while (! defparams_later.empty()) {
	    pair<list<hname_t>,PExpr*> cur = defparams_later.front();
	    defparams_later.pop_front();

	    list<hname_t>eval_path = cur.first;
	    perm_string name = eval_path.back().peek_name();
	    eval_path.pop_back();

	    PExpr*val = cur.second;

	    NetScope*targ_scope = des->find_scope(this, eval_path);
	    if (targ_scope == 0) {
		    // If a scope in the target path is not found,
		    // then push this defparam for handling even
		    // later. Maybe a later generate scheme or
		    // instance array will create the scope.
		  defparams_even_later.push_back(cur);
		  continue;
	    }

	    bool flag = targ_scope->replace_parameter(name, val, this);
	    if (! flag) {
		  cerr << val->get_fileline() << ": warning: parameter "
		       << name << " not found in "
		       << scope_path(targ_scope) << "." << endl;
	    }

	      // We'll need to re-evaluate parameters in this scope
	    target_scopes.insert(targ_scope);
      }

	// The scopes that this defparam set touched will be
	// re-evaluated later it a top_defparams work item. So do not
	// do the evaluation now.

	// If there are some scopes that still have missing scopes,
	// then save them back into the defparams_later list for a
	// later pass.
      defparams_later = defparams_even_later;
      if (! defparams_later.empty())
	    des->defparams_later.insert(this);
}

void Design::evaluate_parameters()
{
      for (map<perm_string,NetScope*>::const_iterator cur = packages_.begin()
		 ; cur != packages_.end() ; ++ cur) {
	    cur->second->evaluate_parameters(this);
      }

      for (list<NetScope*>::const_iterator scope = root_scopes_.begin()
		 ; scope != root_scopes_.end() ; ++ scope ) {
	    (*scope)->evaluate_parameters(this);
      }
}

void NetScope::evaluate_parameter_logic_(Design*des, param_ref_t cur)
{
      long msb = 0;
      long lsb = 0;
      bool range_flag = false;

	/* Evaluate the msb expression, if it is present. */
      PExpr*msb_expr = (*cur).second.msb_expr;
      if (msb_expr) {
            (*cur).second.msb = elab_and_eval(des, this, msb_expr, -1, true);
	    if (! eval_as_long(msb, (*cur).second.msb)) {
		  cerr << (*cur).second.val->get_fileline()
		       << ": error: Unable to evaluate msb expression "
		       << "for parameter " << (*cur).first << ": "
		       << *(*cur).second.msb << endl;
		  des->errors += 1;
		  return;
	    }

	    range_flag = true;
      }

	/* Evaluate the lsb expression, if it is present. */
      PExpr*lsb_expr = (*cur).second.lsb_expr;
      if (lsb_expr) {
            (*cur).second.lsb = elab_and_eval(des, this, lsb_expr, -1, true);
	    if (! eval_as_long(lsb, (*cur).second.lsb)) {
		  cerr << (*cur).second.val->get_fileline()
		       << ": error: Unable to evaluate lsb expression "
		       << "for parameter " << (*cur).first << ": "
		       << *(*cur).second.lsb << endl;
		  des->errors += 1;
		  return;
	    }

	    range_flag = true;
      }

	/* Evaluate the parameter expression. */
      PExpr*val_expr = (*cur).second.val_expr;
      NetScope*val_scope = (*cur).second.val_scope;

      int lv_width = -2;
      if (range_flag)
	    lv_width = (msb >= lsb) ? 1 + msb - lsb : 1 + lsb - msb;

      NetExpr*expr = elab_and_eval(des, val_scope, val_expr, lv_width, true,
                                   (*cur).second.is_annotatable,
                                   (*cur).second.type);
      if (! expr)
            return;

      switch (expr->expr_type()) {
	  case IVL_VT_REAL:
	    if (! dynamic_cast<const NetECReal*>(expr)) {
		  cerr << expr->get_fileline()
		       << ": error: Unable to evaluate real parameter "
		       << (*cur).first << " value: " << *expr << endl;
		  des->errors += 1;
		  return;
	    }
	    break;

	  case IVL_VT_LOGIC:
	  case IVL_VT_BOOL:
	    if (! dynamic_cast<const NetEConst*>(expr)) {
		  cerr << expr->get_fileline()
		       << ": error: Unable to evaluate parameter "
		       << (*cur).first << " value: " << *expr << endl;
		  des->errors += 1;
		  return;
	    }

	      // If the parameter has type or range information, then
	      // make sure the type is set right. Note that if the
	      // parameter doesn't have an explicit type or range,
	      // then it will get the signedness from the expression itself.
	    if (cur->second.type != IVL_VT_NO_TYPE) {
		  expr->cast_signed(cur->second.signed_flag);
	    } else if (cur->second.signed_flag) {
		  expr->cast_signed(true);
	    }

	    if (!range_flag && !expr->has_width()) {
		  expr = pad_to_width(expr, integer_width, *expr);
	    }
	    break;

	  default:
	    cerr << expr->get_fileline()
		 << ": internal error: "
		 << "Unhandled expression type?" << endl;
	    des->errors += 1;
	    return;
      }

      cur->second.val = expr;

	// If there are no value ranges to test the value against,
	// then we are done.
      if ((*cur).second.range == 0) {
	    return;
      }

      NetEConst*val = dynamic_cast<NetEConst*>((*cur).second.val);
      ivl_assert(*(*cur).second.val, (*cur).second.val);
      ivl_assert(*(*cur).second.val, val);

      verinum value = val->value();

      bool from_flag = (*cur).second.range == 0? true : false;
      for (range_t*value_range = (*cur).second.range
		 ; value_range ; value_range = value_range->next) {

	      // If we already know that the value is
	      // within a "from" range, then do not test
	      // any more of the from ranges.
	    if (from_flag && value_range->exclude_flag==false)
		  continue;

	    if (value_range->low_expr) {
		  NetEConst*tmp = dynamic_cast<NetEConst*>(value_range->low_expr);
		  ivl_assert(*value_range->low_expr, tmp);
		  if (value_range->low_open_flag && value <= tmp->value())
			continue;
		  else if (value < tmp->value())
			continue;
	    }

	    if (value_range->high_expr) {
		  NetEConst*tmp = dynamic_cast<NetEConst*>(value_range->high_expr);
		  ivl_assert(*value_range->high_expr, tmp);
		  if (value_range->high_open_flag && value >= tmp->value())
			continue;
		  else if (value > tmp->value())
			continue;
	    }

	      // Within the range. If this is a "from"
	      // range, then set the from_flag and continue.
	    if (value_range->exclude_flag == false) {
		  from_flag = true;
		  continue;
	    }

	      // OH NO! In an excluded range. signal an error.
	    from_flag = false;
	    break;
      }

	// If we found no from range that contains the
	// value, then report an error.
      if (! from_flag) {
	    cerr << val->get_fileline() << ": error: "
		 << "Parameter value " << value
		 << " is out of range for parameter " << (*cur).first
		 << "." << endl;
	    des->errors += 1;
      }
}

void NetScope::evaluate_parameter_real_(Design*des, param_ref_t cur)
{
      PExpr*val_expr = (*cur).second.val_expr;
      NetScope*val_scope = (*cur).second.val_scope;

      NetExpr*expr = elab_and_eval(des, val_scope, val_expr, -1, true,
                                   (*cur).second.is_annotatable,
                                   (*cur).second.type);
      if (! expr)
            return;

      NetECReal*res = 0;

      switch (expr->expr_type()) {
	  case IVL_VT_REAL:
	    if (NetECReal*tmp = dynamic_cast<NetECReal*>(expr)) {
		  res = tmp;
	    } else {
		  cerr << expr->get_fileline()
		       << ": error: "
		       << "Unable to evaluate real parameter "
		       << (*cur).first << " value: " << *expr << endl;
		  des->errors += 1;
		  return;
	    }
	    break;

	  default:
	    cerr << expr->get_fileline()
		 << ": internal error: "
		 << "Failed to cast expression?" << endl;
	    des->errors += 1;
	    return;
	    break;
      }

      (*cur).second.val = res;
      double value = res->value().as_double();

      bool from_flag = (*cur).second.range == 0? true : false;
      for (range_t*value_range = (*cur).second.range
		 ; value_range ; value_range = value_range->next) {

	    if (from_flag && value_range->exclude_flag==false)
		  continue;

	    if (value_range->low_expr) {
		  double tmp;
		  bool flag = eval_as_double(tmp, value_range->low_expr);
		  ivl_assert(*value_range->low_expr, flag);
		  if (value_range->low_open_flag && value <= tmp)
			continue;
		  else if (value < tmp)
			continue;
	    }

	    if (value_range->high_expr) {
		  double tmp;
		  bool flag = eval_as_double(tmp, value_range->high_expr);
		  ivl_assert(*value_range->high_expr, flag);
		  if (value_range->high_open_flag && value >= tmp)
			continue;
		  else if (value > tmp)
			continue;
	    }

	    if (value_range->exclude_flag == false) {
		  from_flag = true;
		  continue;
	    }

	      // All the above tests failed, so we must have tripped
	      // an exclude rule.
	    from_flag = false;
	    break;
      }

      if (! from_flag) {
	    cerr << res->get_fileline() << ": error: "
		 << "Parameter value " << value
		 << " is out of range for real parameter " << (*cur).first
		 << "." << endl;
	    des->errors += 1;
      }
}

void NetScope::evaluate_parameter_(Design*des, param_ref_t cur)
{
	// If the parameter has already been evaluated, quietly return.
      if (cur->second.val_expr == 0)
            return;

      if (cur->second.solving) {
            cerr << cur->second.get_fileline() << ": error: "
	         << "Recursive parameter reference found involving "
                 << cur->first << "." << endl;
	    des->errors += 1;
      } else {
            cur->second.solving = true;
            switch (cur->second.type) {
                case IVL_VT_NO_TYPE:
                case IVL_VT_BOOL:
                case IVL_VT_LOGIC:
                  evaluate_parameter_logic_(des, cur);
                  break;

                case IVL_VT_REAL:
                  evaluate_parameter_real_(des, cur);
                  break;

                default:
                  cerr << cur->second.get_fileline() << ": internal error: "
                       << "Unexpected expression type " << cur->second.type
                       << "." << endl;
                  cerr << cur->second.get_fileline() << ":               : "
                       << "Parameter name: " << cur->first << endl;
                  cerr << cur->second.get_fileline() << ":               : "
                       << "Expression is: " << *cur->second.val_expr << endl;
                  ivl_assert(cur->second, 0);
                  break;
            }
            cur->second.solving = false;
      }

        // If we have failed to evaluate the expression, create a dummy
        // value. This prevents spurious error messages being output.
      if (cur->second.val == 0) {
            verinum val(verinum::Vx);
            cur->second.val = new NetEConst(val);
      }

        // Flag that the expression has been evaluated.
      cur->second.val_expr = 0;
}

void NetScope::evaluate_parameters(Design*des)
{
      for (map<hname_t,NetScope*>::const_iterator cur = children_.begin()
		 ; cur != children_.end() ; ++ cur )
	    cur->second->evaluate_parameters(des);

      if (debug_scopes)
	    cerr << "debug: "
		 << "Evaluating parameters in " << scope_path(this) << endl;

      for (param_ref_t cur = parameters.begin()
		 ; cur != parameters.end() ;  ++ cur) {

            evaluate_parameter_(des, cur);
      }
}

void Design::residual_defparams()
{
      for (list<NetScope*>::const_iterator scope = root_scopes_.begin();
	   scope != root_scopes_.end(); ++ scope )
	    (*scope)->residual_defparams(this);
}

void NetScope::residual_defparams(Design*des)
{
	// Clean out the list of defparams that never managed to match
	// a scope. Print a warning for each.
      while (! defparams_later.empty()) {
	    pair<list<hname_t>,PExpr*> cur = defparams_later.front();
	    defparams_later.pop_front();

	    cerr << cur.second->get_fileline() << ": warning: "
		 << "Scope of " << cur.first << " not found." << endl;
      }

      for (map<hname_t,NetScope*>::const_iterator cur = children_.begin()
		 ; cur != children_.end() ; ++ cur )
	    cur->second->residual_defparams(des);
}

const char* Design::get_flag(const string&key) const
{
      map<string,const char*>::const_iterator tmp = flags_.find(key);
      if (tmp == flags_.end())
	    return "";
      else
	    return (*tmp).second;
}

/*
 * This method looks for a signal (reg, wire, whatever) starting at
 * the specified scope. If the name is hierarchical, it is split into
 * scope and name and the scope used to find the proper starting point
 * for the real search.
 *
 * It is the job of this function to properly implement Verilog scope
 * rules as signals are concerned.
 */
NetNet* Design::find_signal(NetScope*scope, pform_name_t path)
{
      assert(scope);

      perm_string key = peek_tail_name(path);
      path.pop_back();
      if (! path.empty()) {
	    list<hname_t> eval_path = eval_scope_path(this, scope, path);
	    scope = find_scope(scope, eval_path);
      }

      while (scope) {
	    if (NetNet*net = scope->find_signal(key))
		  return net;

	    if (NetScope*import_scope = scope->find_import(this, key)) {
		  scope = import_scope;
		  continue;
	    }

	    if (scope->type() == NetScope::MODULE)
		  break;

	    scope = scope->parent();
      }

      return 0;
}

NetFuncDef* Design::find_function(NetScope*scope, const pform_name_t&name)
{
      assert(scope);

      std::list<hname_t> eval_path = eval_scope_path(this, scope, name);
      NetScope*func = find_scope(scope, eval_path, NetScope::FUNC);
      if (func && (func->type() == NetScope::FUNC)) {
              // If a function is used in a parameter definition or in
              // a signal declaration, it is possible to get here before
              // the function's signals have been elaborated. If this is
              // the case, elaborate them now.
            if (func->elab_stage() < 2) {
		  func->need_const_func(true);
                  const PFunction*pfunc = func->func_pform();
                  assert(pfunc);
                  pfunc->elaborate_sig(this, func);
            }
	    return func->func_def();
      }
      return 0;
}

NetScope* Design::find_task(NetScope*scope, const pform_name_t&name)
{
      std::list<hname_t> eval_path = eval_scope_path(this, scope, name);
      NetScope*task = find_scope(scope, eval_path, NetScope::TASK);
      if (task && (task->type() == NetScope::TASK))
	    return task;

      return 0;
}

void Design::add_node(NetNode*net)
{
      assert(net->design_ == 0);
      if (nodes_ == 0) {
	    net->node_next_ = net;
	    net->node_prev_ = net;
      } else {
	    net->node_next_ = nodes_->node_next_;
	    net->node_prev_ = nodes_;
	    net->node_next_->node_prev_ = net;
	    net->node_prev_->node_next_ = net;
      }
      nodes_ = net;
      net->design_ = this;
}

void Design::del_node(NetNode*net)
{
      assert(net != 0);
      assert(net->design_ == this);

	/* Interact with the Design::functor method by manipulating the
	   cur and nxt pointers that it is using. */
      if (net == nodes_functor_nxt_)
	    nodes_functor_nxt_ = nodes_functor_nxt_->node_next_;
      if (net == nodes_functor_nxt_)
	    nodes_functor_nxt_ = 0;

      if (net == nodes_functor_cur_)
	    nodes_functor_cur_ = 0;

	/* Now perform the actual delete. */
      if (nodes_ == net)
	    nodes_ = net->node_prev_;

      if (nodes_ == net) {
	    nodes_ = 0;
      } else {
	    net->node_next_->node_prev_ = net->node_prev_;
	    net->node_prev_->node_next_ = net->node_next_;
      }

      net->design_ = 0;
}

void Design::add_branch(NetBranch*bra)
{
      bra->next_ = branches_;
      branches_ = bra;
}

void Design::add_process(NetProcTop*pro)
{
      pro->next_ = procs_;
      procs_ = pro;
}

void Design::add_process(NetAnalogTop*pro)
{
      pro->next_ = aprocs_;
      aprocs_ = pro;
}
void Design::delete_process(NetProcTop*top)
{
      assert(top);
      if (procs_ == top) {
	    procs_ = top->next_;

      } else {
	    NetProcTop*cur = procs_;
	    while (cur->next_ != top) {
		  assert(cur->next_);
		  cur = cur->next_;
	    }

	    cur->next_ = top->next_;
      }

      if (procs_idx_ == top)
	    procs_idx_ = top->next_;

      delete top;
}

void Design::join_islands(void)
{
      if (nodes_ == 0)
	    return;

      NetNode*cur = nodes_->node_next_;
      do {
	    join_island(cur);
	    cur = cur->node_next_;
      } while (cur != nodes_->node_next_);
}


void Design::check_driver_conflict(const NetProc* pro, reg_search_ele ele, list<regelement> *regmem, regelement memele){
	
	//单赋值语句
	if(typeid(*pro) == typeid(NetAssignNB)||typeid(*pro) == typeid(NetAssign)){

		NetAssign* asgn       = (NetAssign*)pro;
                NetAssign_* lva         = asgn->l_val(0);
                unsigned  width         = lva->lwidth();//unsigned 变量的位宽
                const NetExpr* base     = lva->get_base();//NetExpr*变量位的起始
		double base_num		= -1;
		if((base!=NULL) && (typeid(*base)==typeid(NetEConst))){
			NetEConst*netnum     = (NetEConst*)base;
			base_num            = netnum->value().as_double();

		}else if(base == NULL){
			base_num	= 0;
		}
		
                NetExpr*word            = lva->word();
                NetNet::Type typ        = lva->sig()->type();//NetNet::Type reg
                perm_string name        = lva->sig()->name();//perm_string 变量名
                if(name == ele.name){
                	regelement  lele	;			
			lele.name 		= name;
			lele.base		= base_num == -1 ? lele.base :base_num;
			lele.width		= width;
			lele.forstart		= memele.forstart;
			lele.forwidth		= memele.forwidth;
			lele.sstack.asgn	= pro;
			lele.sstack.cf 		= memele.sstack.cf;
			lele.sstack.alw  	= memele.sstack.alw;
			lele.lino		= asgn->get_lineno();
			if((lele.sstack.cf!=NULL)&&(typeid(*lele.sstack.cf)==typeid(NetForLoop))){
				lele.base  = lele.forstart;
				lele.width = lele.forwidth;
			}
			regmem->push_back(lele);
			//asgn->dump(std::cout,4);
			//std::cout<< name <<":"<<typ<<":"<<base<<"<"<<base_num<<">"<<":"<<width<<std::endl;

		}
		return;		
	}
	
	//block语句块
	if(typeid(*pro) == typeid(NetBlock)){
		NetBlock* blk =(NetBlock*)pro;
		for(const NetProc*st = blk->proc_first();st != NULL ;st = blk->proc_next(st)){
			check_driver_conflict(st, ele, regmem, memele);
		}	
	}

	//cond语句块
	if(typeid(*pro)==typeid(NetCondit)){
		NetCondit* cond 	= (NetCondit*)pro;
		memele.sstack.cf 	= cond;//类型入栈
		check_driver_conflict(cond->if_clause()  , ele, regmem, memele);
		check_driver_conflict(cond->else_clause(), ele, regmem, memele);
		
	}
	//for语句
	if(typeid(*pro)==typeid(NetForLoop)){
		NetForLoop* forloop = (NetForLoop*)pro;

		//初始值
		const NetExpr* init = forloop->init_expr_;
		//init->dump(std::cout);
		//std::cout<<"初始数值结束"<<std::endl;
		NetEConst*num = (NetEConst*)init;
                double ini =num->value().as_double();


		//条件值
		NetEBinary* con =(NetEBinary*)(forloop->condition_);
		const NetExpr* lim = con->right();
		//lim->dump(std::cout);
		//std::cout<<"条件语句结束"<<std::endl;
		num = (NetEConst*)lim;
                double li =num->value().as_double();
		

		//循环语句块
		NetProc* statement = (NetProc*)forloop->statement_;
		//statement->dump(std::cout,4);
		//std::cout<<"循环语句结束"<<std::endl;

		//步长语句
		NetProc* step = (NetProc*)forloop->step_statement_;
		//step->dump(std::cout,4);
		//std::cout<<"步长语句结束"<<std::endl;


		//std::cout<<"init wid:"<<(init->expr_width())<<"---"<< ini <<std::endl;
		//std::cout<<"lim	 wid:"<<(lim->expr_width())<<"---"<< li <<std::endl;
		//forloop->dump(std::cout,4);
		//
		memele.sstack.cf = forloop;//for类型以及参数入栈
		memele.forstart  = ini;
		memele.forwidth  = li - ini;
		check_driver_conflict(statement, ele, regmem, memele);

	}

}
/*
 * NetProc*pro 		: always以下的语句块，可能包括begin/end,也可能是单语句
 * perm_string reg_name : 需要寻找的reg变量
 * regmem		: 存放寻找到reg变量的容器
 * */
void Design::check_confict(){
	//需要检验的变量
	list<reg_search_ele> regs_search;
	//搜索记录
	list<regelement> regmem ;
	regelement memele;

	regs_search.clear();
	memset(&memele,'\0',sizeof(memele));

	//搜索所有需要检验的变量
	for(list<NetScope*>::const_iterator scope = root_scopes_.begin();
	   scope != root_scopes_.end(); ++ scope){
		//
		for (map<perm_string,NetNet*>::iterator cur = (*scope)->signals_map_.begin(); 
				cur != (*scope)->signals_map_.end() ; ++ cur) {

			NetNet::Type type = cur->second->type();//NetNet表
			if(type == NetNet::REG){
				std::cout<<cur->second->name()<<"  "<<cur->second->vector_width()<<std::endl;
				reg_search_ele ele;
				ele.name  = cur->second->name();
				ele.width = cur->second->vector_width();
				regs_search.push_back(ele);
			}
      		}
	
	}
	

	while(!regs_search.empty()){
		//遍历所有always，查找要检验的变量的赋值语句
		for(NetProcTop* tmp = procs_;tmp!=NULL;tmp = tmp->next_){
			if(tmp->type()==IVL_PR_ALWAYS){
			
				NetEvWait* alw   = (NetEvWait*)tmp->statement();
				NetProc* prost = alw->statement();//always里面语句块
				memele.sstack.alw = alw;
				check_driver_conflict(prost,regs_search.front(),&regmem, memele);		
			}	
		}


		for(list<regelement>::const_iterator cur = regmem.begin(); cur != regmem.end(); ++ cur){
			//std::cout<<""<<(*cur).name<<":"<<(*cur).base<<":"<<(*cur).width<<":"<<(*cur).forstart<<":"<<(*cur).forwidth<<":"<<(*cur).lino<<std::endl;
			bool conflict = false;
			for(list<regelement>::const_iterator ncur = regmem.begin(); ncur != regmem.end(); ++ ncur){
				//std::cout<<""<<ncur->name<<":"<<ncur->base<<":"<<ncur->width<<":"<<ncur->forstart<<":"<<ncur->forwidth<<":"<<ncur->lino<<std::endl;
				int regwidth = regs_search.front().width;
				int left1  = cur->base;
				int right1 = cur->base + cur->width -1;
				int left2  = ncur->base;
				int right2 = ncur->base + ncur->width -1;
				bool widthconflict = (right1>=left2)&&(left1<=right2);//赋值位宽冲突
				//bool samecon	   = (cur->sstack.cf == ncur->sstack.cf);//在同一个if_else /for分支下
				bool samealw 	   = cur->sstack.alw == ncur->sstack.alw;//在同一个alway下
				bool case1 = widthconflict && (!samealw);
				bool case2 = widthconflict && samealw &&((cur->sstack.cf!=NULL && ncur->sstack.cf==NULL)||(cur->sstack.cf==NULL && ncur->sstack.cf!=NULL));
				if(case1||case2){
					//std::cout<<"conflict:"<<std::endl;
					//std::cout<<"          "<<cur->lino <<":"<<cur->name <<std::endl;
					std::cout<<"         line number: "<<ncur->lino<<": "<<ncur->name<<std::endl;
					conflict = true;

				}/*else{
					std::cout<<"serive    ncur     line number: "<<ncur->lino<<";nwidth="<<ncur->width<<";nbase="<<ncur->base<<std::endl;
					std::cout<<"serive    cur      line number: "<<cur->lino<<";width="<<cur->width<<";base="<<cur->base<<std::endl;
					const char* curtype  = cur->sstack.cf != NULL ? typeid(*(cur->sstack.cf)).name():"0";
					const char* ncurtype = ncur->sstack.cf!= NULL ? typeid(*(ncur->sstack.cf)).name():"0";
					std::cout<<"samealw = "<<samealw<<";cur->sstack.cf="<<curtype<<std::endl;
					std::cout<<"ncur->sstack.cf="<<ncurtype<<std::endl;
				}*/
			}

			if(conflict){
        	        	std::cout<<"above valiable is driver conflict with "<<cur->name <<"  :lino"<<cur->lino<<std::endl;
			}

			//std::cout<<"end loop"<<std::endl;
		}//记录打印

		//清空记录regmem memele,寻找过的变量出栈
		regmem.clear();
		memset(&memele,'\0',sizeof(memele));
		regs_search.pop_front();





	}//end while
	//dump(std::cout);
}
