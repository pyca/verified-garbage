import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedHashCall

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Sign.Cached (hashArgs)
open VG.Impl.MlDsa.AArch64.Call (sc callAt)
open VG.Spec.Sha3 (bytesAt)

abbrev hashWritePtrs (p : Params) := [(sc oCT,cLen p),(t1P,2048),(t4P,1024)]

theorem hashReady_post {p : Params} (hp : p=mlDsa65 ∨ p=mlDsa87)
    {S : Nat} (hS : S<2^64) {s : State} (L : Lay S (sgR p) (sgW p) s) :
    WP isa (callAt (if p.ℓ=5 then "vg_mldsa_commit_tail65" else "vg_mldsa_commit_tail87")
      (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*w1Len p) (cLen p)) (hashArgs p)) s
      (fun u => PPostB S s u (hashWritePtrs p) ∧
        bytesAt u.mem (pa s (sc oCT)) (cLen p)=
          H (bytesAt s.mem (pa s (.x26,0)) 64 ++
            bytesAt s.mem (pa s (sc oW1)) (p.k*w1Len p)) (cLen p) ∧
        PolyIs u.mem (pa s t4P)
          (toRq (bitUnpack (H (commitTailSeed s.mem (pa s (sc oMS)) (s.gpr .x9)) 640)
            524287 524288))) := by
  refine WP.mono (hashReady_ok hp hS L) fun u ⟨hP,s1,h1,hq⟩ => ⟨hP.b,?_⟩
  sig_post [commitTailContract,commitTailSig,AArch64.abi,VG.AArch64.argRegs] at hq
  rw [h1.ptr (r:=.x0) (p:=(.x26,0)) (by simp [hashArgs]),
    h1.ptr (r:=.x1) (p:=sc oW1) (by simp [hashArgs]),
    h1.ptr (r:=.x2) (p:=sc oCT) (by simp [hashArgs]),
    h1.ptr (r:=.x4) (p:=sc oMS) (by simp [hashArgs]),
    h1.ptr (r:=.x5) (p:=(.x9,0)) (by simp [hashArgs]),
    h1.ptr (r:=.x6) (p:=t4P) (by simp [hashArgs]),Args.mem h1] at hq
  simpa only [pa,BitVec.add_zero] using hq

end VG.Proof.MlDsa.AArch64.Sign.Cached
