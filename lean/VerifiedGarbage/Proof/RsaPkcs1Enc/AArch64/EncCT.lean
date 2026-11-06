module
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncTail
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncTail
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: constant time

Two runs whose public data agree (`encK.pub`: the pointers and lengths, `n`
and `e`) have the same layout, so between the frames' pushes and pops they
are related by `Two`: both satisfy what correctness says of that point
(`Φ`), with the same layout, whatever their secrets. Each piece of code
between the call is checked by the taint analysis from the registers both
runs agree on there (pointers and counters, which the layout fixes; never
`PS`, the zero test or the mask), and correctness carries `Two` past it
(`two_wp`); the call is constant time for its callee's contract, whose
public data agree too (`RelCT.call`). The frames leak only `sp`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

/-- `n`, `e` and the words of the buffers `X` agree in the two runs'
memories. -/
def LeakEq (L : Lay) (m₁ m₂ : Mem) : Prop :=
  Spec.Rsa.bytesAt m₁ L.n L.k.toNat = Spec.Rsa.bytesAt m₂ L.n L.k.toNat ∧
    Spec.Rsa.bytesAt m₁ L.e L.el.toNat = Spec.Rsa.bytesAt m₂ L.e L.el.toNat ∧
    ∀ R ∈ L.X, Spec.Rsa.wordsAt m₁ R.base (R.len / 8) = Spec.Rsa.wordsAt m₂ R.base (R.len / 8)

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

/-- Two runs with the same layout, with `S` bytes of stack for the callee,
each satisfying `Φ`, and with entry memories satisfying `Q`. -/
def Two (Q : Lay → Mem → Prop) (S : Nat) (Φ : Inv) (a b : State) : Prop :=
  ∃ e : Env, e.L.Ok ∧ e.L.P = S ∧ LeakEq e.L e.m₁ e.m₂ ∧ RegsOf e.L e.g₁ ∧ RegsOf e.L e.g₂ ∧
    Φ e.L e.g₁ e.v₁ e.m₁ a ∧ Φ e.L e.g₂ e.v₂ e.m₂ b ∧ Q e.L e.m₁ ∧ Q e.L e.m₂

variable {Q : Lay → Mem → Prop}

/-- Code whose runs leak the same, and which establishes `Ψ`. -/
theorem two_wp {S : Nat} {c : Prog isa} {Φ Ψ : Inv} (hct : RelCT isa (Two Q S Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → L.P = S → RegsOf L g → Q L m₀ → Φ L g vv m₀ t →
      WP isa c t (Ψ L g vv m₀)) :
    RelCT isa (Two Q S Φ) c (Two Q S Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨e, hL, hP, hk, r₁, r₂, f₁, f₂, q₁, q₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ _ s₁ hL hP r₁ q₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ _ s₂ hL hP r₂ q₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hP, hk, r₁, r₂, y₁, y₂, q₁, q₂⟩

/-- Code checked by the taint analysis from the registers `rs`, which both
runs agree on, with `sp`. -/
theorem two_taint {S : Nat} {c : Prog isa} {Φ : Inv} (rs : List Reg) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ (L : Lay) g₁ g₂ v₁ v₂ m₁ m₂ (a b : State), L.Ok → Φ L g₁ v₁ m₁ a → Φ L g₂ v₂ m₂ b →
      a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r) :
    RelCT isa (Two Q S Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ ⟨_, hL, _, _, _, _, f₁, f₂, _, _⟩ => by
    obtain ⟨hsp, hr⟩ := hag _ _ _ _ _ _ _ _ _ hL f₁ f₂
    exact ⟨hsp, fun r hr' => hr r (Taint.mem_ofRegs.mp hr')⟩) h

/-- Both of the pieces. -/
theorem two {S : Nat} {c : Prog isa} {Φ Ψ : Inv} (rs : List Reg) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ (L : Lay) g₁ g₂ v₁ v₂ m₁ m₂ (a b : State), L.Ok → Φ L g₁ v₁ m₁ a → Φ L g₂ v₂ m₂ b →
      a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r)
    (hw : ∀ (L : Lay) g vv m₀ (t : State), L.Ok → L.P = S → RegsOf L g → Q L m₀ → Φ L g vv m₀ t →
      WP isa c t (Ψ L g vv m₀)) :
    RelCT isa (Two Q S Φ) c (Two Q S Ψ) :=
  two_wp (two_taint rs h hag) hw

/-! ## The pieces -/

theorem psLoop_ct (S : Nat) :
    RelCT isa (Two Q S fun L g vv m₀ t => PsInv L g vv m₀ 0 t) psLoop
      (Two Q S fun L g vv m₀ t => PsInv L g vv m₀ L.pl.toNat t) :=
  two [.x11, .x12, .x13] (by taint_decide) (fun _ _ _ _ _ _ _ _ _ _ f₁ f₂ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      exacts [f₁.x11.trans f₂.x11.symm, f₁.x12.trans f₂.x12.symm, f₁.x13.trans f₂.x13.symm]⟩)
    fun _ _ _ _ _ hL _ _ _ h => psLoop_ok hL h

theorem sep_ct (S : Nat) :
    RelCT isa (Two Q S fun L g vv m₀ t => PsInv L g vv m₀ L.pl.toNat t) (.block sep)
      (Two Q S fun L g vv m₀ t => MsgInv L g vv m₀ 0 t) :=
  two [.x13] (by taint_decide) (fun _ _ _ _ _ _ _ _ _ _ f₁ f₂ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl
      exact f₁.x13.trans f₂.x13.symm⟩)
    fun _ _ _ _ _ hL _ hg _ h => sep_inv hL ⟨hg.2.2.2.2.2.2.1.symm, hg.2.2.2.2.2.2.2.symm⟩ h

theorem msgCopy_ct (S : Nat) :
    RelCT isa (Two Q S fun L g vv m₀ t => MsgInv L g vv m₀ 0 t) msgCopy
      (Two Q S fun L g vv m₀ t => MsgInv L g vv m₀ L.ml.toNat t) :=
  two [.x6, .x7, .x13] (by taint_decide) (fun _ _ _ _ _ _ _ _ _ _ f₁ f₂ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      exacts [f₁.x6.trans f₂.x6.symm, f₁.x7.trans f₂.x7.symm, f₁.x13.trans f₂.x13.symm]⟩)
    fun _ _ _ _ _ hL _ _ _ h => msgCopy_ok hL h

theorem maskArgs_ct (S : Nat) :
    RelCT isa (Two Q S CalledF) (.block maskArgs)
      (Two Q S fun L g vv m₀ t => ∃ y r z, MaskInv L g vv m₀ y r z 0 t) :=
  two [] (by taint_decide) (fun _ _ _ _ _ _ _ _ _ _ f₁ f₂ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ _ _ t _ _ _ _ h => WP.mono (maskArgs_inv h) fun _ h' => ⟨_, _, _, h'⟩

theorem maskLoop_ct (S : Nat) :
    RelCT isa (Two Q S fun L g vv m₀ t => ∃ y r z, MaskInv L g vv m₀ y r z 0 t) maskLoop fun _ _ => True :=
  two_taint [.x11, .x12, .x13] (by taint_decide) fun _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, f₁⟩ ⟨_, _, _, f₂⟩ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      exacts [f₁.x11.trans f₂.x11.symm, f₁.x12.trans f₂.x12.symm, f₁.x13.trans f₂.x13.symm]⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Enc
