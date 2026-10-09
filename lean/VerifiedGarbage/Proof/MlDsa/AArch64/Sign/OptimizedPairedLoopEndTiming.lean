import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTrace
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEndTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

abbrev PairedIX (p : Params) (S t : Nat) (x y : State) : Prop :=
  PositiveIX p S t x y ∧ PairedRoots S x ∧ PairedRoots S y ∧
    x.syms "VG_MLDSA_INV_PAIR"=y.syms "VG_MLDSA_INV_PAIR"

theorem pairedEndPF_tr {p : Params} {S : Nat} (hp : Ok3 p) (hS : S<2^64) {t : Nat} :
    RelCT isa (PairedRS p S (LeakEq p t) fun σ s=>PositiveEP p S σ t s ∨ PositiveEF p S σ t s)
      (.block cntDec) (PairedIX p S t) :=
  paired_trace_frame (Nat.zero_le _) hS
    (RelCT.mono (positiveEndPF_tr hp (paramsOk hp) (lChk_ok hp))
      (fun _ _ h=>⟨h,trivial⟩) (fun _ _ h=>h))

theorem pairedEndB_tr {p : Params} {S : Nat} (hp : Ok3 p) (hS : S<2^64) {t : Nat} :
    RelCT isa (PairedRS p S (LeakEq p t) (PositiveEB p S · t))
      (.block cntDec) (PairedIX p S t) :=
  paired_trace_frame (Nat.zero_le _) hS
    (RelCT.mono (positiveEndB_tr hp (paramsOk hp) (lChk_ok hp))
      (fun _ _ h=>⟨h,trivial⟩) (fun _ _ h=>h))

theorem PairedIX.next {p : Params} {S t : Nat} {x y : State}
    (h : PairedIX p S t x y) (hz : x.gpr .x9≠0) :
    PairedRS p S (LeakEq p (t+1)) (PositiveIL p S · (t+1)) x y :=
  PairedRS.of_root (h.1.2.1 hz) h.2.1 h.2.2.1 h.2.2.2

end VG.Proof.MlDsa.AArch64.Sign
