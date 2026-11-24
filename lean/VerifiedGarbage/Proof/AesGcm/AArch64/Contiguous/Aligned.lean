module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.EmptyCtr
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.TailRun
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericAlignedCT
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Tail

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Tail
open VG VG.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous.Tail (aligned)
open DirectGather.Generic (Encrypted)
variable {wn R P n : Nat} {Ctx St W SP D O : Addr} {k l : Reg → Addr} {iv : Spec.Gcm.Block} {s t : State}

theorem aligned_ok (L : Lay wn Ctx St W) (v : GcmImpl) (a : CrInG wn true Ctx St W SP k R P D O n s)
    (hP : P%16=0) (hc : Proof.Gcm.Ctr s.mem (St+48) (St+64) (ciphOf s.mem Ctx R) iv P)
    (hv : v.ctr.scratch ≤ wn-512) :
    WP isa (aligned v.callees) s (Encrypted wn Ctx St W SP k R iv P D O n s.mem) := by
  refine DirectGather.Generic.alignedWith_ok (fun h1 h2 h3 h4 h5 h6 h7 h8 => words_ok h1 h2 h3 h4 h5 h6 h7 h8)
    L v a hP hc (fun u => ?_) hv
  exact first_ok L v u (ciph_frame u.frame (ctx_crFrame L (OutAt.dataW a.outAt a.data)) a.rounds) hv

theorem aligned_rel (L : Lay wn Ctx St W) (v : GcmImpl) (a : CrInG wn true Ctx St W SP k R P D O n s)
    (b : CrInG wn true Ctx St W SP l R P D O n t) (hP : P%16=0) (hv : v.ctr.scratch ≤ wn-512) :
    RelCT isa (Eq2 s t) (aligned v.callees) TT := by
  apply DirectGather.Generic.alignedWith_rel L v a b hP hv
  · intro a b I C Src Dst W R k scratch h x y sp
    exact first_rel v x y h sp
  · intro u k' m c h
    exact first_ok L v c h hv
  · exact ⟨_,by taint_decide⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Tail
