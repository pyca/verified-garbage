module
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Candidate
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo


/-!
# What two runs of the key generator share (x86)

`pubOf s₀`: the entry's stack pointer, its eleven arguments and q's
bytes, which two runs with related entry states share. Everything the code
uses as an address or count is a function of it (`pub_*`). `At P a t`: some
entry state with public data `a` and state `t` satisfy `P`.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- The public data of an entry state. -/
structure Pub where
  esp : BitVec 32
  args : List (BitVec 32)
  qBytes : List Byte

def pubOf (s₀ : State) : Pub := ⟨s₀.gpr .esp, (List.range 11).map (X86.arg s₀), rQBytes s₀⟩

/-- Some entry state with public data `a` relates to `t` by `P`. -/
def At (P : State → State → Prop) (a : Pub) (t : State) : Prop :=
  ∃ s₀, KeyABI s₀ ∧ pubOf s₀ = a ∧ P s₀ t

section
variable {s₁ s₂ : State} (h : pubOf s₁ = pubOf s₂)
include h

theorem pub_esp : s₁.gpr .esp = s₂.gpr .esp := congrArg Pub.esp h
theorem pub_arg (j : Nat) (hj : j < 11) : X86.arg s₁ j = X86.arg s₂ j := by
  have := congrArg (fun a => a.args[j]?) h
  simpa only [pubOf, List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] using this
theorem pub_qBytes : rQBytes s₁ = rQBytes s₂ := congrArg Pub.qBytes h
theorem pub_rLow : rLow s₁ = rLow s₂ := by rw [rLow, rLow, pub_esp h]
theorem pub_rBase : rBase s₁ = rBase s₂ := by rw [rBase, rBase, pub_rLow h]
theorem pub_rQ : rQ s₁ = rQ s₂ := by rw [rQ, rQ, pub_arg h 3 (by decide), pub_arg h 5 (by decide)]
theorem pub_rWidth : rWidth s₁ = rWidth s₂ := by rw [rWidth, rWidth, pub_qBytes h]
theorem pub_rLead : rLead s₁ = rLead s₂ := by rw [rLead, rLead, pub_qBytes h]
theorem pub_rq : rq s₁ = rq s₂ := by rw [rq, rq, pub_qBytes h]
theorem pub_randLen : (rInput s₁).rand.length = (rInput s₂).rand.length := by
  simp only [rInput, rBytes_length, pub_arg h 8 (by decide)]
end

/-- Two states whose frames have the same base agree on `esp`. -/
theorem esp_of_rf {t₁ t₂ : State} {B : Addr} (h₁ : RF t₁ B) (h₂ : RF t₂ B) : t₁.gpr .esp = t₂.gpr .esp := by
  apply BitVec.eq_of_toNat_eq
  rw [h₁.esp_toNat, h₂.esp_toNat]

theorem At.esp {P : State → State → Prop} (hr : ∀ s₀ t, P s₀ t → Ready s₀ t) {a : Pub} {t₁ t₂ : State}
    (h₁ : At P a t₁) (h₂ : At P a t₂) : t₁.gpr .esp = t₂.gpr .esp := by
  obtain ⟨s₁, -, e₁, p₁⟩ := h₁
  obtain ⟨s₂, -, e₂, p₂⟩ := h₂
  exact esp_of_rf (hr _ _ p₁).rf ((pub_rBase (e₁.trans e₂.symm)) ▸ (hr _ _ p₂).rf)

/-- `esp` is pinned. -/
theorem pins_esp {α : Type} {Φ : α → State → Prop} (f : α → Pub) {P : α → State → State → Prop}
    (hΦ : ∀ a t, Φ a t → At (P a) (f a) t) (hr : ∀ a s₀ t, P a s₀ t → Ready s₀ t) : Pins Φ [.esp] := by
  intro a t₁ t₂ h₁ h₂ r hr'
  rw [List.mem_singleton] at hr'; subst hr'
  exact At.esp (hr a) (hΦ a t₁ h₁) (hΦ a t₂ h₂)

end VG.Proof.Dsa.X86.KeyRandom
