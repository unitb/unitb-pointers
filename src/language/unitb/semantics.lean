import meta.declaration
import meta.tactic

import language.unitb.scope

import unitb.models.pointers.basic

import util.data.generic

namespace unitb.parser

open tactic tactic.interactive list

meta def mk_finite_instance (n : name) : tactic expr :=
do t ← resolve_name n,
   gen ← to_expr ``(generic %%t),
   (_,inst) ← solve_aux gen mk_generic_instance,
   inst ← instantiate_mvars inst,
   inst_n ← mk_fresh_name,
   add_decl (mk_definition inst_n [ ] gen inst),
   set_basic_attribute `instance inst_n tt,
   cl ← to_expr ``(finite %%t),
   inst ← to_expr ``(finite_generic %%t),
   inst_n ← mk_fresh_name,
   add_decl (mk_definition inst_n [ ] cl inst),
   set_basic_attribute `instance inst_n tt,
   resolve_name inst_n >>= to_expr

meta def mk_sched_instance (e : expr) : tactic expr :=
(do `(finite %%t) ← infer_type e | failed,
    cl ← to_expr ``(scheduling.sched %%t),
    inst ← to_expr ``(scheduling.sched.fin %%e),
    n ← mk_fresh_name,
    add_decl (mk_definition n [ ] cl inst),
    set_basic_attribute `instance n tt,
    resolve_name n >>= to_expr)
<|>
(do `(infinite %%t) ← infer_type e | failed,
    cl ← to_expr ``(scheduling.sched %%t),
    inst ← to_expr ``(scheduling.sched.inf %%e),
    n ← mk_fresh_name,
    add_decl (mk_definition n [ ] cl inst),
    set_basic_attribute n `instance tt,
    resolve_name n >>= to_expr)

meta def add_inv_record (s : scope) (invs : list (name × pexpr)) : tactic unit :=
do s.mk_state_pred (s.mch_nm <.> "inv") invs, return ()

meta def add_state_record (s : scope) : tactic unit :=
do updateex_env $ λ e₀, return $ e₀.add_namespace s.mch_nm,
   add_record (s.mch_nm <.> "state") [ ] `(Type 1) s.local_consts

meta def mk_step_spec (qual_id : name) (vs : scope)
   (cs fs : list expr)
   (acts₀ : list (name × pexpr))
: tactic pexpr :=
do hp ← mk_local_def `hp `(heap),
   let hp_r := record_param.var hp,
   s  ← vs.state,
   s' ← vs.primed_state,
   hc ← mk_app (qual_id <.> "coarse") [s.local] >>= mk_local_def `hc,
   hf ← mk_app (qual_id <.> "fine") [s.local] >>= mk_local_def `hf,
   let acts₁ := foldl (λ (e : name_map _), e.erase ∘ prod.fst) vs.vars acts₀,
   let acts₂ := rb_map.zip_with (λ n v v', ``(%%v' = %%v)) acts₁ vs.primed_v,
   let coarse_r := record_param.record hc
                      (qual_id <.> "coarse")
                      (qual_id <.> "coarse'" <.> "drec_on") s.vars cs,
   let fine_r := record_param.record hf
                      (qual_id <.> "fine")
                      (qual_id <.> "fine'" <.> "drec_on") s.vars fs,
   mk_pred (qual_id <.> "step") [s,s',hp_r,coarse_r,fine_r] (acts₂.to_list ++ acts₀)

meta def mk_event_spec (n : name) (rs : list expr) : tactic unit :=
do e ← get_env,
   decl ← e.get (n <.> "state"),
   let ls := decl.univ_params,
   let state : expr := expr.const (n <.> "state") (map level.param ls),
   event ← resolve_name (n <.> "event") >>= to_expr,
   evt_struct ← to_expr ``(unitb.pointers.event %%state),
   t ← to_expr ``(%%event → unitb.pointers.event %%state),
   rec ← resolve_name (n <.> "event" <.> "rec") >>= to_expr,
   e ← mk_local_def `e event,
   let d := rec.mk_app rs,
   infer_type d >>= unify t,
   d ← instantiate_mvars d,
   add_decl (mk_definition (n <.> "event" <.> "spec") ls t d)

meta def mk_machine_spec (n : name) (evt_sch : expr) : tactic unit :=
do state ← resolve_name (n <.> "state") >>= to_expr,
   inv   ← resolve_name (n <.> "inv"),
   init  ← resolve_name (n <.> "init"),
   evts     ← resolve_name (n <.> "event"),
   evt_spec ← resolve_name (n <.> "event" <.> "spec"),
   t ← mk_app `unitb.pointers.program [ state ],
   d ← to_expr ``( { unitb.pointers.program
                   . lbl := %%evts
                   , first  := %%init
                   , firsth := λ _, separation.emp
                   , lbl_is_sched := %%evt_sch
                   , inv := %%inv
                   , shape := λ _, separation.emp
                   , events := %%evt_spec } ),
   add_decl (mk_definition (n <.> "spec") [ ] t d)

meta def mk_machine_correctness (n : name) : tactic unit :=
-- do state ← resolve_name (n <.> "state") >>= to_expr,
--    inv   ← resolve_name (n <.> "inv"),
--    init  ← resolve_name (n <.> "init"),
--    evts     ← resolve_name (n <.> "event"),
--    evt_spec ← resolve_name (n <.> "event" <.> "spec"),
do mch ← resolve_name (n <.> "spec") >>= to_expr,
   t ← mk_app `unitb.pointers.machine_correctness [ mch ],
   d ← to_expr ``( { init := sorry
                   , initp := sorry
                   , events := sorry } : unitb.pointers.machine_correctness %%mch ),
   add_decl (mk_definition (n <.> "correctness") [ ] t d)

end unitb.parser
