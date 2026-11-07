module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairLoop

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- What the commitment needs of the layout. -/
def cChk (p : Params) : Bool :=
  masksPairChk p && (List.range p.k).all (wChk p) && (List.range p.k).all (hChk p) &&
    hashChk (sgR p) (sgW p) [⟨.x26, 0, 64⟩, ⟨.x28, oW1, p.k * w1Len p⟩] ⟨.x28, oCT, cLen p⟩ &&
    icwChk p [(sc 0, 200), (sc 200, 640), (sc oCT, cLen p)] p.k

theorem cChk_ok {p : Params} (h : Ok3 p) : cChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

end VG.Proof.MlDsa.AArch64.Sign
