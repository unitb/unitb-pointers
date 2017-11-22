import meta.tactic
import util.control.applicative
import util.meta.tactic

namespace tactic

open list applicative (mmapp)

meta def add_selector (obj : expr) (fs : list name) (n : name) (ft : expr) : tactic unit :=
do let t := (obj.imp ft),
   (_,val) ← solve_aux t (do
       x ← intro1, vs ← induction x fs, get_local n >>= apply),
   val ← instantiate_mvars val,
   add_decl $ mk_theorem (obj.const_name ++ n) [ ] t val

meta def const_pis : list (expr × expr) → expr → tactic expr
 | [ ] e := return e
 | ((c, t) :: vs) e :=
   do expr.const v _ ← pure c,
      l ← mk_local_def v t,
      const_pis vs ((e.subst c l).abstract_local v)

meta def mk_implicit (bi : binder_info) : expr → expr
 | (expr.local_const n u _ t) := expr.local_const n u bi t
 | e := e

meta def mk_rec_of (c : name) : tactic (expr × list name) :=
do env  ← get_env,
   let r := c <.> "rec",
   decl ← env.get r,
   let ps := decl.univ_params,
   return (expr.const r $ map level.param ps, ps)

meta def mk_cases_on (n : name) (ps : list expr) (cs : list (list expr)) : tactic unit :=
do r ← tactic.mk_app n ps,
   let u := level.param `l,
   C ← mk_local' `C binder_info.implicit (expr.sort u),
   rec ← resolve_name (n <.> "rec"),
   let ps' := map (mk_implicit binder_info.implicit) ps,
   let inds := map (λ fs, expr.pis fs C) cs,
   vs ← mmap (mk_local_def `_) inds,
   let t := expr.pis (ps' ++ [C]) (r.imp (expr.pis vs C)),
   i ← mk_local_def `i r,
   d' ← to_expr ``(%%(foldl expr.app rec $ map to_pexpr vs) %%i : %%C),
   let d := expr.lambdas (map (mk_implicit binder_info.implicit) ps ++ [C,i] ++ vs) d',
   add_decl (mk_definition (n <.> "cases_on") [`l] t d)

meta def mk_drec (n : name) (ps : list expr) (fs : list expr) : tactic unit :=
do r ← tactic.mk_app n ps,
   (rec,ls) ← mk_rec_of (n),
   let u := level.param ls.head,
   C ← mk_local' `C binder_info.implicit (r.imp (expr.sort u)),
   mk ← mk_const (n <.> "mk"),
   let C' : expr := C $ mk.mk_app (ps ++ fs),
   let ind := expr.pis fs C',
   let ind_val := expr.pis fs C',
   let ps' := map (mk_implicit binder_info.implicit) ps,
   let fs' := map (mk_implicit binder_info.implicit) fs,
   i ← mk_local_def `i r,
   h ← mk_local_def `h ind,
   let t' := expr.pis (ps' ++ [C]) (expr.pis [i] (ind.imp $ C i)),
   let t := expr.pis (ps' ++ [C]) (ind.imp (expr.pis [i] $ C i)),
   h' ← to_expr ``(%%(h.mk_app fs) : %%C'),
   let d' := (rec.mk_app ps (C i)) (expr.lambdas fs h') i,
   d ← instantiate_mvars $ expr.lambdas (ps' ++ [C,h,i]) d',
   infer_type d >>= unify t,
   add_decl (mk_definition (n <.> "drec") [`l] t d),
   (_,d') ← solve_aux t' (intros >> apply d ; auto),
   d' ← instantiate_mvars d',
   add_decl (mk_definition (n <.> "drec_on") [`l] t' d')

meta def add_enum_type (n : name) (vals : list name) : tactic unit :=
do updateex_env $ λ e₀, return $ e₀.add_namespace n,
   let t : expr := expr.const n [ ],
   let constrs := map (λ c : name, (c.update_prefix n, t)) vals,
   add_inductive n [ ] 0 `(Type) constrs ff,
   mk_cases_on n [ ] ([ ] <$ vals)

meta def add_record
  (n : name) (ps : list expr) (rt : expr)
  (fs : list expr)
  (gen_drec : bool := ff)
: tactic unit :=
do updateex_env $ λ e₀, return $ e₀.add_namespace n,
   let t : expr := expr.mk_app (expr.const n [ ]) ps,
   let ts := expr.pis fs t,
   let ts := expr.pis ps ts,
   let type_type := expr.pis ps rt,
   add_inductive n [ ] ps.length type_type [(n <.> "mk", ts)] ff,
   mk_cases_on n ps [fs],
   when gen_drec $ mk_drec n ps fs

meta inductive record_param
 | var : expr → record_param
 | record (var : expr) (record : name) (cases_on : name) (params fields : list expr) : record_param

meta def record_param.params : record_param → list expr
 | (record_param.var _) := [ ]
 | (record_param.record _ _ _ ps _) := ps

meta def record_param.vars : record_param → list expr
 | (record_param.var x) := [x]
 | (record_param.record _ _ _ _ fs) := fs

meta def record_param.local : record_param → expr
 | (record_param.var x) := x
 | (record_param.record x _ _ _ _) := x

meta def cases_on_records' : list record_param → expr → list expr → tactic unit
 | (record_param.var x :: xs) e vs := intro1 >>= λ v, cases_on_records' xs e (v :: vs)
 | (record_param.record v n c ps fs :: xs) e₀ vs :=
 do v' ← intro1,
    cs ← induction v',
    mmap' (λ c : list _ × _, cases_on_records' xs e₀ $ c.1.reverse ++ vs) cs
 | [ ] e vs :=
   do exact $ e.mk_app vs.reverse

meta def record_param.primed : record_param → tactic record_param
 | (record_param.var v) := record_param.var <$> primed_local v
 | (record_param.record v n cases ps vs) :=
do v' ← primed_local v,
   record_param.record v' n cases ps <$> mmap primed_local vs

meta def mk_pred (n : name) (ps : list record_param) (pred : list (name × pexpr)) : tactic pexpr :=
do let vars := ps.bind record_param.vars,
   pred' ← mmapp (λ n t, to_expr t >>= mk_local_def n) pred,
   add_record n.primed vars `(Prop) pred' tt,
   pred ← resolve_name n.primed >>= to_expr,
   let vs := map record_param.local ps,
   let t := expr.pis vs `(Prop),
   (_,d) ← solve_aux t $ cases_on_records' ps pred [ ],
   infer_type d >>= unify t,
   d ← instantiate_mvars d,
   add_decl (mk_definition n [ ] t d),
   resolve_name n

end tactic
