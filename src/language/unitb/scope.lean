
import meta.declaration

import util.control.applicative
import util.meta.expr

open tactic lean lean.parser interactive.types
open applicative (mmapp) list (map)

meta def add_symbols : list (name × expr) → environment → exceptional environment
 | list.nil d := return d
 | ((n , t) :: xs) d := d.add (declaration.cnst n [ ] t ff) >>= add_symbols xs

meta def mk_subst_list : list (name × expr) → tactic (list (name × expr)) :=
mmapp $ λ n t, prod.mk n <$> mk_local_def n t

meta def subst_consts (s : name_map expr) : pexpr → tactic pexpr
| (expr.const n ls) := to_pexpr <$> s.find n <|> return (expr.const n ls)
| e := expr.traverse subst_consts e

meta structure scope :=
  (mch_nm : name)
  (vars : name_map expr)
  (primed_v : name_map expr)
  (names : list name)
  (env : environment)

meta def scope.local_consts (s : scope) : list expr :=
s.vars.values

meta def scope.primed_consts (s : scope) : list expr :=
s.primed_v.values

meta def scope.texpr (s : scope) : parser pexpr :=
do env₀ ← (tactic.get_env : parser _),
   set_env s.env,
   e ← texpr,
   set_env env₀,
   subst_consts s.vars e

meta def scope.state (s : scope) : tactic record_param :=
do t ← mk_const (s.mch_nm <.> "state"),
   v ← mk_local_def `s t,
   return $ record_param.record
     v
     (s.mch_nm <.> "state")
     (s.mch_nm <.> "state" <.> "cases_on")
     [ ]
     s.local_consts

meta def scope.primed_state (s : scope) : tactic record_param :=
do t ← mk_const (s.mch_nm <.> "state"),
   v ← mk_local_def `s t,
   return $ record_param.record
     v
     (s.mch_nm <.> "state")
     (s.mch_nm <.> "state" <.> "cases_on")
     [ ]
     s.primed_consts

meta def scope.s_var (s : scope) (pre_state : bool) : parser expr :=
do v ← ident,
   (if pre_state
      then s.primed_v.find v
      else s.vars.find v)
       <|> fail format!"Invalid state variable: {v}\nExpecting: {s.names}"

meta def scope.mk_state_pred (s : scope) (n : name) (pred : list (name × pexpr)) : tactic pexpr :=
do p ← s.state,
   mk_pred n [p] pred

meta def mk_scope (n : name) (vs : list (name × expr)) : parser scope :=
do env ← tactic.get_env,
   vars ← (rb_map.of_list <$> mk_subst_list vs : tactic _),
   ps ← (mmapp (λ (v : name) p,
         do let v' := v.primed,
            prod.mk v <$> mk_local_def v' p) vs : tactic _),
   env' ← add_symbols vs env,
   return { mch_nm := n
          , vars := vars
          , primed_v := rb_map.of_list ps
          , env := env'
          , names := map prod.fst vs }
