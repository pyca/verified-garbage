module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsEntry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsPrologue
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFold
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBatchTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailReadyTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowMemory
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

theorem paired_prologue {p : Params} {S : Nat} {σ : State} (hp : Ok3 p) (hS : S<2^64)
    (h : (signK p S).pre σ) (hr : StaticRoots S σ) (rp : PairedRoots S σ) :
    WP isa (.block pro) σ fun s=>(RootedSt p S σ s ∧ s.gpr .x24=1) ∧ PairedRoots S s :=
  WP.pairedRoots (rooted_prologue hp h hr) rp (Nat.zero_le _) hS

theorem paired_prologue_contract {p : Params} {S : Nat} {σ : State}
    (hpos : 0<S) (hS : S<2^64) (hp : Ok3 p)
    (h : (signContractT p (abi.withConsts pairedSignRootConsts) S).pre σ) :
    WP isa (.block pro) σ fun s=>(RootedSt p S σ s ∧ s.gpr .x24=1) ∧ PairedRoots S s := by
  obtain ⟨h,hr,rp⟩ := pairedRoots_entry hpos h
  exact paired_prologue hp hS h hr rp

end VG.Proof.MlDsa.AArch64.Sign
