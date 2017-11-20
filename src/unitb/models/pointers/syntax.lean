import unitb.models.pointers.basic
import util.control.monad
import theories.set_theory

universes u v w k

namespace list

variables {m : Type w → Type k}
variables [applicative m]
variables {α : Type u}
variables {β : Type v}
variables {γ : Type w}

def mapp (f : α → β → γ) : list (α × β) → list γ
 | [ ] := [ ]
 | ((x,y) :: xs) := f x y :: mapp xs

def mmapp (f : α → β → m γ) : list (α × β) → m (list γ)
 | [ ] := pure [ ]
 | ((x,y) :: xs) := (::) <$> f x y <*> mmapp xs

end list

namespace rb_map

variables {k : Type}
variables {α : Type}
variables {β : Type}
variables {γ : Type}
variables [has_ordering k]
private def list_zip_with (f : k → α → β → γ) : list (k × α) → list (k × β) → list (k × γ)
| ((k₀,x)::xs) ((k₁,y)::ys) :=
 match has_ordering.cmp k₀ k₁ with
  | ordering.gt := list_zip_with xs ((k₁,y)::ys)
  | ordering.lt := list_zip_with ((k₀,x)::xs) ys
  | ordering.eq := (k₀,f k₀ x y) :: list_zip_with xs ys
 end
| _ _ := [ ]

meta def zip_with (f : k → α → β → γ) (m₀ : rb_map k α) (m₁ : rb_map k β) : rb_map k γ :=
rb_map.of_list (list_zip_with f m₀.to_list m₁.to_list)

end rb_map

namespace lean.parser
open lean list nat applicative
variables {α : Type}

meta def sep_by1 (sep : parser unit) (p : parser α) : parser (list α) :=
cons <$> p <*> many (sep *> p)

meta def sep_by_exactly : ℕ → parser unit → parser α → parser (list α)
 | 0 _ _ := pure [ ]
 | (succ n) s p := (::) <$> p <*> replicate n (s *> p)

end lean.parser

namespace tactic

meta def trace_type (tag : string) (e : expr) : tactic unit :=
do e' ← tactic.pp e,
   t' ← infer_type e >>= tactic.pp,
   trace format!"* {tag} \n  - {e'} \n  : {t'}"

end tactic

meta def name.primed : name → name
 | (name.mk_string x y) := name.mk_string (x ++ "'") y
 | x := x

meta def name.unprimed : name → name
 | (name.mk_string x y) := name.mk_string x.pop_back y
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
   let C' := C $ mk.mk_app (ps ++ fs),
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

meta def mk_subst_list : list (name × expr) → tactic (list (name × expr)) :=
mmapp $ λ n t, prod.mk n <$> mk_local_def n t

meta def subst_consts (s : name_map expr) : pexpr → tactic pexpr
| (expr.const n ls) := to_pexpr <$> s.find n <|> return (expr.const n ls)
| e := expr.traverse subst_consts e

meta def add_symbols : list (name × expr) → environment → exceptional environment
 | list.nil d := return d
 | ((n , t) :: xs) d := d.add (declaration.cnst n [ ] t ff) >>= add_symbols xs

meta inductive record_param
 | var : expr → record_param
 | record (var : expr) (record : name) (cases_on : name) (params fields : list expr) : record_param

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

meta def cases_on_records : list record_param → expr → tactic expr
 | (record_param.var x :: xs) e := expr.lambdas [x] <$> cases_on_records xs e
 | (record_param.record v n c ps fs :: xs) e₀ :=
   do e  ← cases_on_records xs e₀,
      c'← resolve_name c >>= to_expr,
      mv ← mk_mvar,
      let e' := c'.mk_app ([v,expr.lambdas fs e]),
      instantiate_mvars $ expr.lambdas [v] e'
 | [ ] e := return e

meta def primed_local : expr → tactic expr
 | (expr.local_const _ n bi t) := mk_local' n.primed bi t
 | _ := fail "not a local constant"

meta def record_param.primed : record_param → tactic record_param
 | (record_param.var v) := record_param.var <$> primed_local v
 | (record_param.record v n cases ps vs) :=
do v' ← primed_local v,
   record_param.record v' n cases ps <$> mmap primed_local vs

meta def expr.local_consts (e : expr) : list expr :=
e.fold [ ] (λ e i xs, if e.is_local_constant then e :: xs else xs)

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

meta def scope.s_var (s : scope) (pre_state : bool) : parser expr :=
do v ← ident,
   (if pre_state
      then s.primed_v.find v
      else s.vars.find v)
       <|> fail format!"Invalid state variable: {v}\nExpecting: {s.names}"

meta def clause (s : scope) : parser (name × pexpr) :=
prod.mk <$> ident <* tk ":" <*> s.texpr

meta def add_inv_record (s : scope) (invs : list (name × pexpr)) : tactic unit :=
do s.mk_state_pred (s.mch_nm <.> "inv") invs, return ()

meta def add_state_record (s : scope) : tactic unit :=
do updateex_env $ λ e₀, return $ e₀.add_namespace s.mch_nm,
   add_record (s.mch_nm <.> "state") [ ] `(Type 1) s.local_consts

open lean (parser)  monad (mmap₂) predicate

meta def assignment (vs : scope) (pre_state : bool) : parser (list (expr × expr)) :=
do ts ← sep_by1 (tk ",") (vs.s_var pre_state) <* tk ":=",
   s  ← sep_by_exactly ts.length (tk ",")
             (if pre_state then vs.texpr else texpr),
   s' ← (mmap₂ (λ v e, do t ← infer_type v, to_expr ``(%%e : %%t)) ts s : tactic _),
   return $ zip ts s'

meta def parse_assignment (vs : scope) (pre_state : bool := tt) : parser (list (expr × expr)) :=
join <$> sep_by (tk ",") (assignment vs pre_state)

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

meta def event_section (s : scope) : parser unit :=
do tk "events",
   es ← many (parse_event s),
   add_enum_type (s.mch_nm <.> "event") (map prod.fst es),
   mk_event_spec s.mch_nm (map prod.snd es)

meta def mk_machine_spec (n : name) : tactic unit :=
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
                   , lbl_is_sched := sorry
                   , inv := %%inv
                   , shape := λ _, separation.emp
                   , events := %%evt_spec } ),
   add_decl (mk_definition (n <.> "spec") [ ] t d)

meta def variable_decl (n : name) : parser scope :=
do tk "variables",
   vs ← sep_by (tk ",") ident,
   let vs' : list (name × expr) := map (λ n, (n,`(Set.{0}))) vs,
   mk_scope n vs'

meta def init_section (s : scope) : parser unit :=
do tk "initialization",
   vs ← parse_assignment s ff,
   rec ← s.state,
   let fs := mapp (λ x e : expr, (x.local_pp_name,``(%%x = %%e))) vs,
   let miss := foldl (λ (e : name_map _), e.erase ∘ prod.fst) s.vars fs,
   when (¬ miss.empty) $ fail format!"No initial value provided for {miss.keys}",
   mk_pred (s.mch_nm <.> "init") [rec] fs *> return ()

meta def invariant_section (s : scope) : parser unit :=
do tk "invariants",
   invs ← sep_by (tk ",") (clause s),
   add_state_record s,
   add_inv_record s invs

precedence `initialization` : 0
precedence `invariants` : 0
precedence `events` : 0
precedence `when` : 0
notation when := _root_.when

@[user_command]
meta def unitb_machine (meta_info : decl_meta_info) (_ : parse $ tk "machine") : parser unit :=
do n ← ident,
   updateex_env $ λ e₀, return $ e₀.add_namespace n,
   s ← variable_decl n,
   invariant_section s,
   init_section s,
   event_section s,
   mk_machine_spec n,
   tk "end"

end unitb.parser

machine foo
variables x, y
invariants
  bar: x ∪ y ⊆ x
initialization
  x := ∅, y := ∅
events
  move
    when grd1 : ∅ ∈ x
    then end
  add_x begin x := y end
  swap begin x,y := y,x end
end

#print prefix foo.event.swap
#print prefix foo.event.move
#print foo.event.swap.step'
#print foo.event.add_x.step'
#print foo.event.move.step'
#print foo.event.spec
#print foo.init'
#print foo.spec

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
