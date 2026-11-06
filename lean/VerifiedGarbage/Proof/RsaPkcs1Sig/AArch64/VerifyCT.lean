module

import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCall
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_pkcs1_verify` on AArch64: constant time
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.Ver

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Verify
open VG.Impl.RsaPkcs1Sig.AArch64 (encode compare)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite two_alloc)
open VG.Proof.MlKem.AArch64 (Only)

/-! ## The taint checks -/

section
variable {α : Type} {Φ : α → State → Prop}

theorem lenCheck_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block lenCheck) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem ret0_taint (h : Pins Φ []) : RelCT isa (Two Φ) ret0 fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem restore_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block restore) fun _ _ => True :=
  two_taint [] h (by taint_decide)

end

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, `hash`, and the bytes of `n`, `e`, the hash value and
the signature. -/
structure PubV (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x5, .x6, .x7], s.gpr r = a.gpr r
  h4 : (s.gpr .x4).setWidth 32 = (a.gpr .x4).setWidth 32
  args : ∀ i < 3, stackArg s i = stackArg a i
  bn : Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x0) (a.gpr .x1).toNat
  be : Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat
  bd : Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .x5) (a.gpr .x6).toNat
  bg : Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .x7) (stackArg a 0).toNat

theorem PubV.refl (s : State) : PubV s s :=
  ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem leak_eq4 {a b c d a' b' c' d' : List Byte} (ha : a.length = a'.length) (hb : b.length = b'.length)
    (hc : c.length = c'.length)
    (h : (a ++ b ++ c ++ d).map (·.toNat) = (a' ++ b' ++ c' ++ d').map (·.toNat)) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hi : a ++ b ++ c ++ d = a' ++ b' ++ c' ++ d' :=
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  obtain ⟨h₁, rfl⟩ := List.append_inj hi (by simp [ha, hb, hc])
  obtain ⟨h₂, rfl⟩ := List.append_inj h₁ (by simp [ha, hb])
  obtain ⟨rfl, rfl⟩ := List.append_inj h₂ ha
  exact ⟨rfl, rfl, rfl, rfl⟩

end VG.Proof.RsaPkcs1Sig.AArch64.Ver
