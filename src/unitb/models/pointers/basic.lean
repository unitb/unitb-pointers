
import unitb.logic
import unitb.scheduling

import separation.specification

namespace unitb.pointers
open unitb separation

section definitions

parameter σ : Type

private def pred := σ → Prop

parameter {σ}
variable inv : pred
variable shape : σ → hprop

structure event :=
  (coarse : pred)
  (fine : pred)
  (step : ∀ (s s' : σ) (h h' : heap), coarse s → fine s → Prop)

parameter σ
structure program :=
  (lbl : Type)
  (first : pred)
  (firsth : σ → hprop)
  (lbl_is_sched : scheduling.sched lbl)
  (inv : σ → Prop)
  (shape : σ → hprop)
  (events : lbl → event)

parameter {σ}
parameter M : program
def xσ := σ × heap
private def pred' := xσ → Prop

def program.init (p : pred') : Prop :=
∀ s h,
M.first s → (M.firsth s).apply h → p (s,h)

def program.step : xσ → xσ → Prop
| ⟨s,hp⟩ ⟨s',hp'⟩ :=
(s,hp) = (s',hp') ∨ ∃ e hc hf, (M.events e).step s s' hp hp' hc hf

def program.step_of (e : M.lbl) : xσ → xσ → Prop
| ⟨s,hp⟩ ⟨s',hp'⟩ :=
∃ hc hf, (M.events e).step s s' hp hp' hc hf

def program.coarse_sch_of (act : M.lbl) : pred' :=
(M.events act).coarse ∘ prod.fst

def program.fine_sch_of (act : M.lbl) : pred' :=
(M.events act).fine ∘ prod.fst

open program

structure program.falsify (act : M.lbl) (p q : pred') : Prop :=
  (enable : q ⟹ coarse_sch_of act)
  (schedule : p ⟹ fine_sch_of act)
  (negate' : ⦃ •q ⟶ ⟦ step_of act ⟧ ⟶ ⊙-•q ⦄)

open program predicate

def program.transient (p q : pred') : Prop :=
q ⟹ False ∨
∃ (act : M.lbl), falsify act p q

open program temporal

lemma program.transient_false (p : pred')
: transient p False :=
by { left, refl }

-- todo: use monotonicity
lemma program.transient_antimono (p q p' q' : pred')
  (hp : p' ⟹ p)
  (hq : q' ⟹ q)
  (h : transient p q)
: transient p' q' :=
begin
  revert h,
  apply or.imp,
  { apply entails_imp_entails_left hq },
  intros_mono e,
  intros h,
  cases h,
  constructor,
  { revert enable,
    apply entails_imp_entails_left hq },
  { revert schedule,
    apply entails_imp_entails_left hp },
  { revert negate',
    apply ew_imp_ew _,
    apply p_imp_entails_p_imp _ _,
    { apply temporal.init_entails_init hq, },
    { apply p_imp_entails_p_imp_right _,
      apply next_imp_next _,
      apply p_not_entails_p_not_right,
      apply temporal.init_entails_init hq, } }
end

structure event_correctness (e : event) :=
  (step_fis : ∀ s hp hc hf, (shape s).apply hp →
               ∃ s' hp', e.step s s' hp hp' hc hf)
  (step_inv : ∀ (s s' : σ) (hp hp' : heap) hc hf,
                inv s → (shape s).apply hp →
                e.step s s' hp hp' hc hf →
                inv s ∧ (shape s).apply hp)

structure machine_correctness (m : program) :=
  (init : m.first ⟹ m.inv)
  (initp : ∀ s, m.first s → m.firsth s =*> m.shape s)
  (events : ∀ e, event_correctness m.inv m.shape (m.events e))

end definitions

instance (σ : Type) : system (program σ) :=
{ system .
  transient_antimono := program.transient_antimono
, transient_false := program.transient_false
, init := program.init
, transient := program.transient
, step := program.step
, σ := xσ }

instance (σ : Type) : system_sem (program σ) :=
sorry

end unitb.pointers
