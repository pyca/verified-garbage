module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyFrame
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Wp

/-!
# `vg_rsa_pkcs1_verify` on AArch64: the call of `vg_rsa_public_checked`

RSAVP1 of the signature, as the entry state gives it (`pubOut`); `EM₁` in
the frame (`em1R`, `em1_sub`); the values in `x19`–`x22`, the saved slots
and every buffer of the caller but the working space in the frame (`Mid`,
`bytes_of_frame`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.Ver

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.Verify
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)

/-- `EM₁`, of `k` bytes. -/
abbrev em1R (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .x1).toNat⟩

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (s.gpr .x1).toNat)

/-- In the frame, from the entry state `s`: the registers saved, `x19`–`x22`
holding `k`, `hash`, `digest` and `digest_len`, memory changed only in the
stack the function uses and the working space. -/
structure Mid (K : Nat) (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x19 : t.gpr .x19 = s.gpr .x1
  x20 : t.gpr .x20 = ((s.gpr .x4).setWidth 32).setWidth 64
  x21 : t.gpr .x21 = s.gpr .x5
  x22 : t.gpr .x22 = s.gpr .x6
  hi : ∀ r ∈ [Reg.x23, .x24, .x25, .x26, .x27, .x28], t.gpr r = s.gpr r
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [kR K s, sR s] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem

/-- `EM₁` is in the frame. -/
theorem em1_sub {K : Nat} {s : State} (hp : PreV K s) : Region.Sub (em1R s) (kR K s) :=
  frame_sub K s (by have := hp.k2; unfold oEM1 frameBytes; omega_arith)

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {K : Nat} {s : State} {m : Mem} (hf : Frame [kR K s, sR s] s.mem m) {p : Addr}
    {len : Nat} (hk : (kR K s).Disjoint ⟨p, len⟩) (hs : (sR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hk.symm
  · exact hs.symm

end VG.Proof.RsaPkcs1Sig.AArch64.Ver
