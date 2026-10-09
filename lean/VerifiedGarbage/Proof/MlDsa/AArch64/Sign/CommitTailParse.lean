import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailSaved

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_movz)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack (polyRegion)

def parseRegs : List Reg := .x1::decodeRegs

theorem parse_ok {s : State}
    (hin : InRegions (s.rd++s.wr) (s.gpr .x0) 640)
    (hout : InRegions s.wr (s.gpr .x4) 1024)
    (hsep : (Region.mk (s.gpr .x0) 640).Disjoint (polyRegion (s.gpr .x4))) :
    WP isa (.seq (.block [.movz .x .x1 640 0]) Impl.MlDsa.AArch64.Pack.bitUnpack) s fun t =>
      RegKeep parseRegs s t ∧ Frame [polyRegion (s.gpr .x4)] s.mem t.mem ∧
      PolyIs t.mem (s.gpr .x4) (toRq (bitUnpack (Spec.Sha3.bytesAt s.mem (s.gpr .x0) 640) 524287 524288)) := by
  rw [WP.seq_iff]
  refine wp_movz fun a ha => WP.block_nil_iff.mpr ?_
  refine WP.mono (decode_access_ok (s:=a) ha.gpr
    (by rw [ha.rd,ha.wr,ha.other .x0 (by decide)]; exact hin)
    (by rw [ha.wr,ha.other .x4 (by decide)]; exact hout)
    (by rw [ha.other .x0 (by decide),ha.other .x4 (by decide)]; exact hsep))
    fun t ⟨hc,hf,hk⟩ => ?_
  simp only [ha.mem,ha.other .x0 (by decide),ha.other .x4 (by decide)] at hc hf
  refine ⟨?_,hf,decode_poly hc⟩
  have hb : RegKeep decodeRegs a t := ⟨hk.gpr,hk.rd,hk.wr,hk.sp⟩
  exact ((RegKeep.upd ha).trans hb).mono (by simp [parseRegs])

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
