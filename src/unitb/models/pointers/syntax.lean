import unitb.models.pointers.basic

import theories.set_theory

namespace unitb.parser

open lean lean.parser
open interactive.types
open interactive

meta def clause : parser (name × pexpr) :=
prod.mk <$> ident <* tk ":" <*> parser.pexpr 0

precedence `invariants` : 0
precedence `events` : 0
precedence `when` : 0
notation when := _root_.when
open list tactic

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
   -- let ls := num.iterate _ 0,
   return (expr.const r $ map level.param ps, ps)

meta def mk_cases_on (n : name) (ps : list expr) (fs : list expr) : tactic unit :=
do r ← tactic.mk_app n ps,
   let u := level.param `l,
   C ← mk_local' `C binder_info.implicit (expr.sort u),
   rec ← resolve_name (n <.> "rec"),
   let ind := expr.pis fs C,
   let ps' := map (mk_implicit binder_info.implicit) ps,
   let t := expr.pis (ps' ++ [C]) (r.imp (ind.imp C)),
   i ← mk_local_def `i r,
   h ← mk_local_def `h ind,
   d' ← to_expr ``(%%rec %%h %%i : %%C),
   let d := expr.lambdas (map (mk_implicit binder_info.implicit) ps ++ [C,i,h]) d',
   add_decl (mk_definition (n <.> "cases_on") [`l] t d)

meta def mk_drec (n : name) (ps : list expr) (fs : list expr) : tactic unit :=
do r ← tactic.mk_app n ps,
   (rec,ls) ← mk_rec_of (n),
   let u := level.param ls.head,
   C ← mk_local' `C binder_info.implicit (r.imp (expr.sort u)),
   mk ← mk_const (n <.> "mk"),
   let C' := C $ mk.mk_app (ps ++ fs),
   let ind := expr.pis fs C',
   let ind_val := expr.pis fs C',
   let ps' := map (mk_implicit binder_info.implicit) ps,
   let fs' := map (mk_implicit binder_info.implicit) fs,
   i ← mk_local_def `i r,
   h ← mk_local_def `h ind,
   let t := expr.pis (ps' ++ [C]) (ind.imp (expr.pis [i] $ C i)),
   h' ← to_expr ``(%%(h.mk_app fs) : %%C'),
   let d' := (rec.mk_app ps (C i)) (expr.lambdas fs h') i,
   d ← instantiate_mvars $ expr.lambdas (ps' ++ [C,h,i]) d',
   infer_type d >>= unify t,
   add_decl (mk_definition (n <.> "drec") [`l] t d)

meta def add_record
  (n : name) (ps : list expr) (rt : expr)
  (fields : list (name × expr))
  (gen_drec : bool := ff)
: tactic unit :=
do updateex_env $ λ e₀, return $ e₀.add_namespace n,
   let t : expr := expr.mk_app (expr.const n [ ]) ps,
   fs ← mmap (λ x : _ × _, mk_local_def x.1 x.2) fields,
   let ts := expr.pis fs t,
   let ts := expr.pis ps ts,
   let type_type := expr.pis ps rt,
   add_inductive n [ ] ps.length type_type [(n <.> "mk", ts)] ff,
   mk_cases_on n ps fs,
   when gen_drec $ mk_drec n ps fs

meta def mk_subst_list : list (name × expr) → tactic (list (expr × expr)) :=
mmap $ λ ⟨n,t⟩, prod.mk (expr.const n [ ]) <$> mk_local_def n t

meta def subst_const {elab : bool} (c : name) (to : expr elab) : expr elab → tactic (expr elab)
| e :=
(do (expr.const v _) ← pure e | fail "failed here",
    guard (v = c),
    return to)
<|> expr.traverse subst_const e

meta def subst_consts : list (expr × expr) → pexpr → tactic pexpr
| [ ] e       := return e
| ((c,l) :: cs) e := subst_const c.const_name (to_pexpr l) e >>= subst_consts cs

meta def add_inv_record (n : name) (vars : list expr) (invs : list (name × pexpr)) : tactic unit :=
do invs' ← mmap ((λ ⟨n,t⟩, prod.mk n <$> to_expr t) : name × pexpr → tactic (name × expr)) invs <|> fail "this failed",
   add_record (n <.> "inv'") vars `(Prop) invs' tt,
   state ← resolve_name (n <.> "state") >>= to_expr,
   -- p ← to_expr ``(λ _ : %%state, Prop),
   state_rec ← resolve_name (n <.> "state" <.> "rec"),
   inv ← resolve_name (n <.> "inv'"),
   let t := expr.pi `_ binder_info.default state `(Prop),
   d ← to_expr ``(λ x : %%state, (%%state_rec %%inv x : Prop)),
   add_decl (mk_definition (n <.> "inv") [ ] t d)

meta def add_state_record (n : name) (vars : list (name × expr)) : tactic unit :=
do updateex_env $ λ e₀, return $ e₀.add_namespace n,
   add_record (n <.> "state") [ ] `(Type 1) vars

meta def add_symbols : list (name × expr) → environment → exceptional environment
 | list.nil d := return d
 | ((n , t) :: xs) d := d.add (declaration.cnst n [ ] t ff) >>= add_symbols xs

open lean (parser)

meta def parse_event : parser name :=
do id ← ident,
   xs ← (tk "when" *> sep_by (tk ",") clause <* tk "then")
       <|> (tk "begin" *> return [ ]),
   tk "end",
   trace xs,
   return id

@[user_command]
meta def unitb_machine (meta_info : decl_meta_info) (_ : parse $ tk "machine") : parser unit :=
do n ← ident,
   updateex_env $ λ e₀, return $ e₀.add_namespace n,
   tk "variables",
   vs ← sep_by (tk ",") ident,
   tk "invariants",
   let vs' : list (name × expr) := map (λ n, (n,`(Set.{0}))) vs,
   vars ← mk_subst_list vs',
   e ← tactic.get_env,
   updateex_env $ add_symbols vs',
   invs' ← sep_by (tk ",") clause,
   invs ← mmap (λ x : _ × _, prod.mk x.1 <$> subst_consts vars x.2) invs',
   tk "events",
   es ← many parse_event,
   set_env e,
   add_state_record n vs',
   add_inv_record n (map prod.snd vars) invs,
   trace es,
   tk "end"

end unitb.parser

machine foo
variables x, y
invariants
  bar: x ∪ y ⊆ x
events
  move
    when grd1 : ∅ ∈ x
    then end
  add_x begin end
end

example (s : foo.state) (J : foo.inv s) : true :=
begin
  induction s,
  dunfold foo.inv at J,
  induction J,
  admit
end

example (k : foo.state) : true :=
begin
  induction k,
  admit
end
