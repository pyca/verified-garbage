import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Verified
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5CT

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64

theorem rejNTT4Avx2_verified : Verified X86_64.target Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2
    (Spec.MlDsa.rejNTT4Contract X86_64.abi 24) := rej4_verified _ correct ct

theorem rejNTT4Avx2_ret {s s' : State} {t : List Leak} (h : (Spec.MlDsa.rejNTT4Contract X86_64.abi 24).pre s)
    (e : Exec isa Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 s t s') :
    (s'.gpr .rax).setWidth 32 = rej4Res s.mem (s.gpr .rdi) := rej4_ret correct h e

end VG.Proof.MlDsa.X86_64.Rej4.Segment
