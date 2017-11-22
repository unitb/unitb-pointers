
import util.control.applicative
import util.control.monad

import language.unitb.semantics
import language.unitb.scope

import unitb.models.pointers.basic

import theories.set_theory

namespace unitb.parser

open tactic tactic.interactive interactive.types
open lean lean.parser
open list monad (mmap₂) applicative (mmapp)

meta def assignment (vs : scope) (pre_state : bool) : parser (list (expr × expr)) :=
do ts ← sep_by1 (tk ",") (vs.s_var pre_state) <* tk ":=",
   s  ← sep_by_exactly ts.length (tk ",")
             (if pre_state then vs.texpr else texpr),
   s' ← (mmap₂ (λ v e, do t ← infer_type v, to_expr ``(%%e : %%t)) ts s : tactic _),
   return $ zip ts s'

meta def parse_assignment (vs : scope) (pre_state : bool := tt) : parser (list (expr × expr)) :=
join <$> sep_by (tk ",") (assignment vs pre_state)

meta def clause (s : scope) : parser (name × pexpr) :=
prod.mk <$> ident <* tk ":" <*> s.texpr

meta def parse_event (vs : scope) : parser (name × expr) :=
do id ← ident,
   xs ← (tk "when" *> sep_by (tk ",") (clause vs) <* tk "then")
       <|> (tk "begin" *> return [ ]),
   acts ← parse_assignment vs,
   tk "end",
   let qual_id := id.update_prefix (vs.mch_nm <.> "event"),
   state  ← (resolve_name (vs.mch_nm <.> "state") >>= to_expr : tactic _),
   cs ← (mmapp (λ n t, to_expr t >>= mk_local_def n) xs : tactic (list expr)),
   let acts := mapp (λ (v : expr) (p : expr), (v.local_pp_name.unprimed, ``(%%v = %%p))) acts,
   coarse ← vs.mk_state_pred (qual_id <.> "coarse") xs,
   fine   ← vs.mk_state_pred (qual_id <.> "fine") [ ],
   step ← mk_step_spec qual_id vs cs [ ] acts,
   spec ← to_expr ``( { unitb.pointers.event
                      . coarse := %%coarse
                      , fine := %%fine
                      , step := %%step } : unitb.pointers.event %%state ),
   return (id, spec)

meta def variable_decl (n : name) : parser scope :=
do tk "variables",
   vs ← sep_by (tk ",") ident,
   let vs' : list (name × expr) := map (λ n, (n,`(Set.{0}))) vs,
   mk_scope n vs'

meta def init_section (s : scope) : parser (list expr) :=
do tk "initialization",
   vs ← parse_assignment s ff,
   rec ← s.state,
   let fs := mapp (λ x e : expr, (x.local_pp_name,``(%%x = %%e))) vs,
   let miss := foldl (λ (e : name_map _), e.erase ∘ prod.fst) s.vars fs,
   when (¬ miss.empty) $ fail format!"No initial value provided for {miss.keys}",
   mk_pred (s.mch_nm <.> "init") [rec] fs,
   (mmapp (λ n t, to_expr t >>= mk_local_def n) fs : tactic _) <* return ()

meta def invariant_section (s : scope) : parser (list expr) :=
do tk "invariants",
   invs ← sep_by (tk ",") (clause s),
   add_state_record s,
   add_inv_record s invs,
   (mmapp (λ n p, to_expr p >>= mk_local_def n) invs : tactic _) <* return ()

meta def event_section (s : scope) : parser expr :=
do tk "events",
   es ← many (parse_event s),
   add_enum_type (s.mch_nm <.> "event") (map prod.fst es),
   fin ← mk_finite_instance (s.mch_nm <.> "event"),
   inst ← mk_sched_instance fin,
   mk_event_spec s.mch_nm (map prod.snd es),
   return inst

end unitb.parser
