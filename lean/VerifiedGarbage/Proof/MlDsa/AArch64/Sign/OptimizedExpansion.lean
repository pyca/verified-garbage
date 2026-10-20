module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallResident
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message

theorem expandA_depth {P : Prims} {S : Nat} (hp : PrimsOk P S) (p : Params) :
    16*(Impl.MlDsa.AArch64.Sign.expandA P p).aarch64Depth≤S := by
  have hr : DLe (S/16) P.rejNTT := ⟨by have := hp.rejNTT.fd; omega⟩
  have h4 : DLe (S/16) P.rej4 := ⟨by have := hp.rej4.fd; omega⟩
  have hd : DLe (S/16) (Impl.MlDsa.AArch64.Sign.expandA P p) := by
    unfold Impl.MlDsa.AArch64.Sign.expandA
    dle_tac
  have := hd.le
  omega

/-- Matrix expansion retains the immutable root tables without changing
its sampled values, public failure behavior, or instruction sequence. -/
theorem rooted_expandA_ok {P : Prims} {S : Nat} (hp : PrimsOk P S) {p : Params}
    (h3 : Ok3 p) (hc : aChk p=true) {σ s : State} (hs : RootedSt p S σ s)
    (hf : s.gpr .x24=1) : WP isa (Impl.MlDsa.AArch64.Sign.expandA P p) s
      fun t => IA p S σ (p.k*p.ℓ) t ∧ StaticRoots S t :=
  hs.2.phase (expandA_depth hp p) hp.s64 (expandA_ok hp h3 hc hs.1 hf)

end VG.Proof.MlDsa.AArch64.Sign
