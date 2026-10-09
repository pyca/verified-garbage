import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixExpansion

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message

 theorem expandA_depth {P : Prims} {S : Nat} (hp : PrimsOk P S) (p : Params) :
    16*(Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p).aarch64Depth≤S := by
  have hr : DLe (S/16) P.rejNTT := ⟨by have := hp.rejNTT.fd; omega⟩
  have h4 : DLe (S/16) P.rej4 := ⟨by have := hp.rej4.fd; omega⟩
  have h2 : DLe (S/16) Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code := by
    have hd : Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code.aarch64Depth=0 := by decide +kernel
    exact ⟨by rw [hd]; omega⟩
  have hd : DLe (S/16) (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) := by
    unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA
    split
    · unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.tail
      dle_tac
    · unfold Impl.MlDsa.AArch64.Sign.expandA
      dle_tac
  have := hd.le
  omega

 theorem rooted_expandA_ok {P : Prims} {S : Nat} (hp : PrimsOk P S) {p : Params}
    (h3 : Ok3 p) (hc : aChk p=true) {σ s : State} (hs : RootedSt p S σ s)
    (hf : s.gpr .x24=1) : WP isa (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) s
      fun t=>IA p S σ (p.k*p.ℓ) t ∧ StaticRoots S t :=
  hs.2.phase (expandA_depth hp p) hp.s64 (expandA_ok hp h3 hc hs.1 hf)

end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
