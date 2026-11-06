module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyFrame
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyFrame

/-!
# `vg_rsa_pkcs1_recover` on AArch64: constant time

Everything the function reads is public, but the taint analysis cannot see
it of the bytes it loads: the branches on the call's result, on `encode`'s
and on `compare`'s are pinned by correctness (`two_ite`), and the code
between them is checked by the taint analysis (`two_taint`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.Rec

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Recover
open VG.Impl.RsaPkcs1Sig.AArch64 (encode compare)
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 restore)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite two_alloc)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stackArgs_three fb eval_zero' leak_eq4)
open VG.Proof.MlKem.AArch64 (Only eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The taint checks -/

section
variable {α : Type} {Φ : α → State → Prop}

theorem lenCheck_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block lenCheck) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem zeroArgs_taint (h : Pins Φ [.x0, .x1]) : RelCT isa (Two Φ) zeroArgs fun _ _ => True :=
  two_taint [.x0, .x1] h (by taint_decide)

theorem restore_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block restore) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem zeroKept_taint (h : Pins Φ [.x19, .x20]) : RelCT isa (Two Φ) zeroKept fun _ _ => True :=
  two_taint [.x19, .x20] h (by taint_decide)

theorem encode_taint (h : Pins Φ [.x8, .x9, .x10, .x11, .x12]) : RelCT isa (Two Φ) encode fun _ _ => True :=
  two_taint [.x8, .x9, .x10, .x11, .x12] h (by taint_decide)

end


/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, `hash`, and the bytes of `n`, `e` and the signature. -/
structure PubR (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x7], s.gpr r = a.gpr r
  h6 : (s.gpr .x6).setWidth 32 = (a.gpr .x6).setWidth 32
  args : ∀ i < 3, stackArg s i = stackArg a i
  bn : Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat
  be : Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x4) (a.gpr .x5).toNat
  bg : Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .x7) (stackArg a 0).toNat

theorem PubR.refl (s : State) : PubR s s :=
  ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem leak_eq3 {a b c a' b' c' : List Byte} (ha : a.length = a'.length) (hb : b.length = b'.length)
    (h : (a ++ b ++ c).map (·.toNat) = (a' ++ b' ++ c').map (·.toNat)) : a = a' ∧ b = b' ∧ c = c' := by
  have hi : a ++ b ++ c = a' ++ b' ++ c' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  obtain ⟨h₁, rfl⟩ := List.append_inj hi (by simp [ha, hb])
  obtain ⟨rfl, rfl⟩ := List.append_inj h₁ ha
  exact ⟨rfl, rfl, rfl⟩

/-! ## The points of the code -/

/-- An entry state with the anchor's public data. -/
def E (K : Nat) (a s : State) : Prop := PreR K s ∧ PubR a s

theorem E.fb {K : Nat} {a s : State} (h : E K a s) : fb s = fb a := by
  show s.sp - _ = a.sp - _; rw [h.2.sp]

theorem E.gpr {K : Nat} {a s : State} (h : E K a s) {r : Reg} (hr : r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x7]) :
    s.gpr r = a.gpr r := h.2.g r hr

theorem E.valA {K : Nat} {a s : State} (h : E K a s) : valA s = valA a := by
  show Ver.fb s + _ = Ver.fb a + _; rw [h.fb, h.gpr (r := .x3) (by decide), h.gpr (r := .x1) (by decide)]

theorem pins_sub {α : Type} {Φ : α → State → Prop} {rs rs' : List Reg} (h : Pins Φ rs)
    (hs : ∀ r ∈ rs', r ∈ rs := by decide) : Pins Φ rs' := fun a s₁ s₂ h₁ h₂ =>
  ⟨(h a s₁ s₂ h₁ h₂).1, fun r hr => (h a s₁ s₂ h₁ h₂).2 r (hs r hr)⟩

theorem pins_and {α : Type} {Φ : α → State → Prop} {P : State → Prop} {rs : List Reg} (h : Pins Φ rs) :
    Pins (fun a s => Φ a s ∧ P s) rs := fun a s₁ s₂ h₁ h₂ => h a s₁ s₂ h₁.1 h₂.1

end VG.Proof.RsaPkcs1Sig.AArch64.Rec
