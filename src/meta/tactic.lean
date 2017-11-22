import util.control.monad

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

meta def name.primed : name → name
 | (name.mk_string x y) := name.mk_string (x ++ "'") y
 | x := x

meta def name.unprimed : name → name
 | (name.mk_string x y) := name.mk_string x.pop_back y
 | x := x

namespace tactic

meta def trace_type (tag : string) (e : expr) : tactic unit :=
do e' ← tactic.pp e,
   t' ← infer_type e >>= tactic.pp,
   trace format!"* {tag} \n  - {e'} \n  : {t'}"

meta def primed_local : expr → tactic expr
 | (expr.local_const _ n bi t) := mk_local' n.primed bi t
 | _ := fail "not a local constant"

end tactic
