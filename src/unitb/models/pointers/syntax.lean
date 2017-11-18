import unitb.models.pointers.basic

import theories.set_theory

namespace lean.parser
open lean list nat applicative
variables {α : Type}

meta def sep_by1 (sep : parser unit) (p : parser α) : parser (list α) :=
cons <$> p <*> many (sep *> p)

meta def sep_by_exactly : ℕ → parser unit → parser α → parser (list α)
 | 0 _ _ := pure [ ]
 | (succ n) s p := (::) <$> p <*> replicate n (s *> p)

end lean.parser

meta def name.primed : name → name
 | (name.mk_string x y) := name.mk_string (x ++ "'") y
 | x := x

namespace unitb.parser

open lean lean.parser
open interactive.types
open interactive

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
   -- h ← mk_local_def `h ind,
   d' ← to_expr ``(%%(foldl expr.app rec $ map to_pexpr vs) %%i : %%C),
   let d := expr.lambdas (map (mk_implicit binder_info.implicit) ps ++ [C,i] ++ vs) d',
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

meta def add_symbols : list (name × expr) → environment → exceptional environment
 | list.nil d := return d
 | ((n , t) :: xs) d := d.add (declaration.cnst n [ ] t ff) >>= add_symbols xs

-- @[reducible]
meta structure scope :=
  (mch_nm : name)
  (vars : list (expr × expr))
  (names : list name)
  (env : environment)

meta def scope.local_consts (s : scope) : list expr :=
map prod.snd s.vars

meta def scope.texpr (s : scope) : parser pexpr :=
do env₀ ← (tactic.get_env : parser _),
   set_env s.env,
   e ← texpr,
   set_env env₀,
   subst_consts s.vars e

meta def scope.mk_state_pred (s : scope) (n : name) (pred : list (name × pexpr)) : tactic pexpr :=
do let vars := s.local_consts,
   pred' ← mmap ((λ ⟨n,t⟩, to_expr t >>= mk_local_def n) : name × pexpr → tactic expr) pred,
   add_record n.primed vars `(Prop) pred' tt,
   state ← resolve_name (s.mch_nm <.> "state") >>= to_expr,
   state_rec ← resolve_name (s.mch_nm <.> "state" <.> "rec"),
   pred ← resolve_name n.primed,
   let t := expr.pi `_ binder_info.default state `(Prop),
   d ← to_expr ``(λ x : %%state, (%%state_rec %%pred x : Prop)),
   add_decl (mk_definition n [ ] t d),
   resolve_name n

meta def mk_scope (n : name) (vs : list (name × expr)) : parser scope :=
do env ← tactic.get_env,
   vars ← mk_subst_list vs,
   env' ← add_symbols vs env,
   return { mch_nm := n, vars := vars, env := env', names := map prod.fst vs }

meta def scope.s_var (s : scope) : parser name :=
do v ← ident,
   when (v ∉ s.names) $
     fail format!"Invalid state variable: {v}\nExpecting: {s.names}",
   return v

meta def clause (s : scope) : parser (name × pexpr) :=
prod.mk <$> ident <* tk ":" <*> s.texpr

-- ∀ s s' s'', s(Next)s' ∧ s(Next)s'' ⟹ s' = s''
meta def add_inv_record (s : scope) (invs : list (name × pexpr)) : tactic unit :=
do s.mk_state_pred (s.mch_nm <.> "inv") invs, return ()
-- do let vars := s.local_consts,
--    invs' ← mmap ((λ ⟨n,t⟩, prod.mk n <$> to_expr t) : name × pexpr → tactic (name × expr)) invs,
--    add_record (s.mch_nm <.> "inv'") vars `(Prop) invs' tt,
--    state ← resolve_name (s.mch_nm <.> "state") >>= to_expr,
--    state_rec ← resolve_name (s.mch_nm <.> "state" <.> "rec"),
--    inv ← resolve_name (s.mch_nm <.> "inv'"),
--    let t := expr.pi `_ binder_info.default state `(Prop),
--    d ← to_expr ``(λ x : %%state, (%%state_rec %%inv x : Prop)),
--    add_decl (mk_definition (s.mch_nm <.> "inv") [ ] t d)

meta def add_state_record (s : scope) : tactic unit :=
do updateex_env $ λ e₀, return $ e₀.add_namespace s.mch_nm,
   add_record (s.mch_nm <.> "state") [ ] `(Type 1) s.local_consts

open lean (parser)

-- and `p ⇒ q` is regular propositional implication
-- ∃ D, C * D ⇒ A * true

-- So what I chose as a definition of data refinement of pointer structures is: `∃ D, C * D ⇒ A * true` where `C` is the concrete data structure, `A` is the abstract one and `D` is whatever we delete.
-- ∃ ⊑ ⊒

-- ```
--   (∃ r, q ≠ 0 * q ↦ (x,p ⊕ r)) * XList(q,r,xs))
-- ⊒ (∃ r q', q' ≠ 0 * q' ↦ (x,p,r) * DList(q',r,xs))
-- ```

meta def assignment (vs : scope) : parser (list (name × pexpr)) :=
do ts ← sep_by1 (tk ",") vs.s_var <* tk ":=",
   s  ← sep_by_exactly ts.length (tk ",") vs.texpr,
   return $ zip ts s
open predicate
meta def parse_event (vs : scope) : parser (name × expr) :=
do id ← ident,
   xs ← (tk "when" *> sep_by (tk ",") (clause vs) <* tk "then")
       <|> (tk "begin" *> return [ ]),
   acts ← sep_by (tk ",") (assignment vs),
   tk "end",
   -- trace "parse_event",
   -- trace xs,
   -- trace acts,
   coarse ← vs.mk_state_pred (id.update_prefix (vs.mch_nm <.> "event") <.> "coarse") xs,
   state ← (resolve_name (vs.mch_nm <.> "state") >>= to_expr : tactic _),
   spec ← to_expr ``( { unitb.pointers.event
                      . coarse := %%coarse
                      , fine := True
                      , step := sorry } : unitb.pointers.event %%state ),
   return (id, spec)

-- DList (p,q,[])    := q = 0
-- DList (p,q,x::xs) := ∃ r, q ≠ 0 * q ↦ (x,p,r) * DList(q,r,xs)
--  ⊑
-- XList (p,q,[])    := q = 0
-- XList (p,q,x::xs) := ∃ r, q ≠ 0 * q ↦ (x,p ⊕ r) * XList(q,r,xs)

-- ∀ xs, DList (p,q,xs) ⊑ XList (p,q,xs)

--   q ≠ 0 * q ↦ (x,p,r) * DList(q,r,xs)
-- ⊑ q ≠ 0 * q ↦ (x,p ⊕ r) * XList(q,r,xs))

--   q ↦ (x,p,r)
-- ⊑ q ↦ (x,p ⊕ r)

--   q ↦ (x,p,r) * true
-- ← ∃ D, q ↦ (x,p ⊕ r) * D

--   q ↦ x * q+1 ↦ p * q+2 ↦ r * true
-- ← ∃ D, q ↦ x * q+1 ↦ p⊕r * D

meta def mk_event_spec (n : name) (rs : list expr) : tactic unit :=
do e ← get_env,
   decl ← e.get (n <.> "state"),
   let ls := decl.univ_params,
   -- trace "state",
   -- trace ls,
   let state : expr := expr.const (n <.> "state") (map level.param ls),
   event ← resolve_name (n <.> "event") >>= to_expr <|> fail "B",
   -- infer_type event,
   evt_struct ← to_expr ``(unitb.pointers.event %%state),
   t ← to_expr ``(%%event → unitb.pointers.event %%state),
   -- rec ← mk_const (n <.> "event" <.> "rec"),
   -- decl ← e.get (n <.> "event" <.> "rec"),
   -- trace "event.rec",
   -- trace decl.univ_params,
   rec ← resolve_name (n <.> "event" <.> "rec") >>= to_expr,
   -- trace event,
   -- infer_type event >>= trace,
   -- infer_type rec >>= trace,
   e ← mk_local_def `e event,
   -- trace "trace",
   -- mmap (trace ∘ expr.to_raw_fmt) rs,
   let d := rec.mk_app (rs),
   -- trace t,
   -- infer_type d >>= trace,
   infer_type d >>= unify t,
   d ← instantiate_mvars d,
   trace d,
   add_decl (mk_definition (n <.> "event" <.> "spec") ls t d)

meta def event_section (s : scope) : parser unit :=
do tk "events",
   es ← many (parse_event s),
   add_enum_type (s.mch_nm <.> "event") (map prod.fst es),
   trace "add_enum_type",
   mk_event_spec s.mch_nm (map prod.snd es),
   trace "mk_event_spec"

-- #check unitb.pointers.event
meta def mk_machine_spec (n : name) : tactic unit :=
do state ← resolve_name (n <.> "state") >>= to_expr,
   inv   ← resolve_name (n <.> "inv"),
   infer_type state >>= trace,
   trace "babish",
   evts     ← resolve_name (n <.> "event"),
   evt_spec ← resolve_name (n <.> "event" <.> "spec"),
   t ← mk_app `unitb.pointers.program [ state ],
   trace "plumbus",
   d ← to_expr ``( { unitb.pointers.program
                   . lbl := %%evts
                   , first  := sorry
                   , firsth := sorry
                   , lbl_is_sched := sorry
                   , inv := %%inv
                   , shape := sorry
                   , events := %%evt_spec } ), -- <|> fail "during spec type checking",
   trace d,
   add_decl (mk_definition (n <.> "spec") [ ] t d)

precedence `invariants` : 0
precedence `events` : 0
precedence `when` : 0
notation when := _root_.when

@[user_command]
meta def unitb_machine (meta_info : decl_meta_info) (_ : parse $ tk "machine") : parser unit :=
do n ← ident,
   updateex_env $ λ e₀, return $ e₀.add_namespace n,
   tk "variables",
   vs ← sep_by (tk ",") ident,
   tk "invariants",
   let vs' : list (name × expr) := map (λ n, (n,`(Set.{0}))) vs,
   s ← mk_scope n vs',
   invs ← sep_by (tk ",") (clause s),
   add_state_record s,
   add_inv_record s invs,
   event_section s,
   mk_machine_spec n,
   tk "end"

end unitb.parser
-- p ↦ (a,b,c)
-- p ↦ a * p+1 ↦ b * p+2 ↦ c
-- p ↦ { value := a, next := b, prev := c }
-- p.'value ↦ a * p.'next ↦ b * p.'prev ↦ c
-- ℕ × string

machine foo
variables x, y
invariants
  bar: x ∪ y ⊆ x
events
  move
    when grd1 : ∅ ∈ x
    then end
  add_x begin end
  swap begin x,y := y,x end
end

#print prefix foo
#print foo.event.spec
#print foo.event.add_x.coarse'

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
