import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCorrect
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: two runs

Two runs whose public data agree (the pointers and lengths, `n` and `e`)
have the same layout, so between the frames' pushes and pops they are
related by `Two`: both satisfy what correctness says of that point (`Φ`),
with the same layout, whatever their secrets. A block is checked by the
taint analysis from the registers both runs agree on there (`two`), which
`Φ` fixes as functions of the layout; a call is constant time for its
callee's contract, whose public data agree too (`two_call`).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt

/-- `n` and `e` agree in the two runs' memories. -/
def LeakEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
  Spec.Rsa.bytesAt m₁ L.n L.k.toNat = Spec.Rsa.bytesAt m₂ L.n L.k.toNat ∧
    Spec.Rsa.bytesAt m₁ L.e L.el.toNat = Spec.Rsa.bytesAt m₂ L.e L.el.toNat

/-- The layout of two runs, and what each has on entry. -/
structure Env where
  L : Lay
  g₁ : Reg → BitVec 64
  g₂ : Reg → BitVec 64
  v₁ : VReg → BitVec 128
  v₂ : VReg → BitVec 128
  m₁ : Mem
  m₂ : Mem

/-- What correctness says of a point of the code. -/
abbrev Inv := Lay → (Reg → BitVec 64) → (VReg → BitVec 128) → Mem → State → Prop

/-- Two runs in the layout of `e`, each satisfying `Φ`. -/
def TwoE (S : Nat) (Φ : Inv) (e : Env) (a b : State) : Prop :=
  e.L.Ok ∧ e.L.P = S + 1 ∧ LeakEq e.L e.m₁ e.m₂ ∧ Φ e.L e.g₁ e.v₁ e.m₁ a ∧ Φ e.L e.g₂ e.v₂ e.m₂ b

/-- Two runs with the same layout, each satisfying `Φ`. -/
def Two (S : Nat) (Φ : Inv) (a b : State) : Prop := ∃ e : Env, TwoE S Φ e a b

/-- A piece of code, from two runs each satisfying `Φ`: constant time for a
fixed layout, and establishing `Ψ` by correctness. -/
theorem two_wp {S : Nat} {c : Prog isa} {Φ Ψ : Inv} (hct : ∀ e, RelCT isa (TwoE S Φ e) c fun _ _ => True)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → L.P = S + 1 → Φ L g vv m₀ t → WP isa c t (Ψ L g vv m₀)) :
    RelCT isa (Two S Φ) c (Two S Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨e, hp⟩ e₁ e₂
  obtain ⟨ht, -⟩ := hct e _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨hL, hP, hk, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ _ s₁ hL hP f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ _ s₂ hL hP f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hP, hk, y₁, y₂⟩

/-- Code checked by the taint analysis from the registers `rs`, which `Φ`
fixes as functions of the layout, with `sp`. -/
theorem two {S : Nat} {c : Prog isa} {Φ Ψ : Inv} (rs : List Reg) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ (L : Lay) g₁ g₂ v₁ v₂ m₁ m₂ (a b : State), L.Ok → Φ L g₁ v₁ m₁ a → Φ L g₂ v₂ m₂ b →
      a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → L.P = S + 1 → Φ L g vv m₀ t → WP isa c t (Ψ L g vv m₀)) :
    RelCT isa (Two S Φ) c (Two S Ψ) :=
  two_wp (fun _ => RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ ⟨hL, _, _, f₁, f₂⟩ => by
    obtain ⟨hsp, hr⟩ := hag _ _ _ _ _ _ _ _ _ hL f₁ f₂
    exact ⟨hsp, fun r hr' => hr r (Taint.mem_ofRegs.mp hr')⟩) h) hw

/-- Two runs' registers, each a function of the layout. -/
theorem pin {a b : State} {r : Reg} {x : BitVec 64} (ha : a.gpr r = x) (hb : b.gpr r = x) :
    a.gpr r = b.gpr r := ha.trans hb.symm

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
