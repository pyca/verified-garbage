module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverFrame
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Wp

/-!
# `vg_rsa_pkcs1_recover` on AArch64: the call of `vg_rsa_public_checked`

RSAVP1 of the signature, as the entry state gives it (`pubOut`); `EM₁` in
the frame (`em1R`, `em1_sub`); and the values in `x19`–`x22` and the saved
slots in the frame (`Mid`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.Rec

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Recover
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 saved)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stk sR aR kR fb kb fb_eq off_fb frame_sub frame_sub0 below_fb in_frame
  in_frame0 saved_offs bytes_of_frame)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)

/-- `EM₁`, of `k` bytes. -/
abbrev em1R (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .x3).toNat⟩

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (s.gpr .x3).toNat)

/-- In the frame, from the entry state `s`: the registers saved, `x19`–`x22`
holding `out`, `out_len`, `k` and `hash`. -/
structure Mid (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x19 : t.gpr .x19 = s.gpr .x0
  x20 : t.gpr .x20 = s.gpr .x1
  x21 : t.gpr .x21 = s.gpr .x3
  x22 : t.gpr .x22 = ((s.gpr .x6).setWidth 32).setWidth 64
  hi : ∀ r ∈ [Reg.x23, .x24, .x25, .x26, .x27, .x28], t.gpr r = s.gpr r
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  sv : Spill.Saved (fb s) s.gpr saved t.mem

/-- `EM₁` is in the frame. -/
theorem em1_sub {K : Nat} {s : State} (hp : PreR K s) : Region.Sub (em1R s) (kR K s) :=
  frame_sub K s (by have := hp.k2; unfold oEM1 frameBytes; omega)

end VG.Proof.RsaPkcs1Sig.AArch64.Rec
