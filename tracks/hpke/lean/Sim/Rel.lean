/-
Relational Hoare triples over two Aeneas programs, and the lockstep bind rules.
`rel m₁ m₂ R`: the real program `m₁` succeeds with some `a`, the reference `m₂`
succeeds with some `b`, and `R a b`.
-/
module
public import Aeneas
import all Aeneas.Std.WP
@[expose] public section
open Aeneas Aeneas.Std Result WP

namespace Sim

unseal Result in
/-- A total-correctness spec over `Result` pins the result: `Result` programs are deterministic. -/
theorem spec_eq_ok {α : Type} {m : Result α} {p : Post α} (h : spec m p) : ∃ v, m = ok v ∧ p v := by
  unfold spec at h
  exact Data.Coinductive.DWP.induction (θ := effectWP)
    (P := fun t _ => ∃ v, t = Data.Coinductive.ITree.ret v ∧ p v)
    (fun v _ hv => ⟨v, rfl, hv⟩)
    (fun eff _ _ hw => by cases eff; exact hw.elim)
    h

/-- Relational triple: real `m₁` and reference `m₂` both succeed, with related results. -/
def rel {α β : Type} (m₁ : Result α) (m₂ : Result β) (R : α → β → Prop) : Prop :=
  m₁ ⦃ a => m₂ ⦃ b => R a b ⦄ ⦄

theorem rel_ok {α β : Type} {a : α} {b : β} {R : α → β → Prop} (h : R a b) : rel (ok a) (ok b) R := by
  simp [rel, h]

/-- Lockstep rule: a matched pair of calls. -/
theorem rel_bind {α β γ δ : Type} {m₁ : Result α} {m₂ : Result β} {k₁ : α → Result γ} {k₂ : β → Result δ}
    {R₁ : α → β → Prop} {R₂ : γ → δ → Prop}
    (h : rel m₁ m₂ R₁) (hk : ∀ a b, R₁ a b → rel (k₁ a) (k₂ b) R₂) :
    rel (Std.bind m₁ k₁) (Std.bind m₂ k₂) R₂ := by
  obtain ⟨a, ha, h2⟩ := spec_eq_ok h
  obtain ⟨b, hb, hR⟩ := spec_eq_ok h2
  subst ha hb
  simpa [rel] using hk a b hR

/-- A step on the real side only. -/
theorem rel_bind_left {α γ δ : Type} {m₁ : Result α} {k₁ : α → Result γ} {m₂ : Result δ}
    {P : α → Prop} {R : γ → δ → Prop}
    (h : m₁ ⦃ a => P a ⦄) (hk : ∀ a, P a → rel (k₁ a) m₂ R) :
    rel (Std.bind m₁ k₁) m₂ R :=
  spec_bind h hk

/-- A step on the reference side only. -/
theorem rel_bind_right {β γ δ : Type} {m₁ : Result γ} {m₂ : Result β} {k₂ : β → Result δ}
    {Q : β → Prop} {R : γ → δ → Prop}
    (h : m₂ ⦃ b => Q b ⦄) (hk : ∀ b, Q b → rel m₁ (k₂ b) R) :
    rel m₁ (Std.bind m₂ k₂) R := by
  obtain ⟨b, hb, hQ⟩ := spec_eq_ok h
  subst hb
  simpa using hk b hQ

theorem rel_mono {α β : Type} {m₁ : Result α} {m₂ : Result β} {R R' : α → β → Prop}
    (h : rel m₁ m₂ R) (hR : ∀ a b, R a b → R' a b) : rel m₁ m₂ R' := by
  obtain ⟨a, ha, h2⟩ := spec_eq_ok h
  obtain ⟨b, hb, hr⟩ := spec_eq_ok h2
  subst ha hb
  simpa [rel] using hR a b hr

end Sim
