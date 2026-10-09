import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedLowLayout
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLowCheck
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedLow

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign

def pairedLowChk (p : Params) (i : Nat) : Bool :=
  inB (sgR p++sgW p) cP 1024 && inB (sgR p++sgW p) (s2P p i) 2048 &&
  inB (sgR p++sgW p) (wP p i) 2048 && inB (sgR p++sgW p) (hP i) 2048 &&
  inB (sgR p++sgW p) t1P 2176 && inB (sgW p) (wP p i) 2048 &&
  inB (sgW p) (hP i) 2048 && inB (sgW p) t1P 2176 &&
  sepB (sgR p) (sgW p) cP 1024 (wP p i) 2048 &&
  sepB (sgR p) (sgW p) cP 1024 (hP i) 2048 &&
  sepB (sgR p) (sgW p) cP 1024 t1P 2176 &&
  sepB (sgR p) (sgW p) (s2P p i) 2048 (wP p i) 2048 &&
  sepB (sgR p) (sgW p) (s2P p i) 2048 (hP i) 2048 &&
  sepB (sgR p) (sgW p) (s2P p i) 2048 t1P 2176 &&
  sepB (sgR p) (sgW p) (wP p i) 2048 (hP i) 2048 &&
  sepB (sgR p) (sgW p) (wP p i) 2048 t1P 2176 &&
  sepB (sgR p) (sgW p) (hP i) 2048 t1P 2176 &&
  stChk p [(wP p i,2048),(hP i,2048),(t1P,2176)]

theorem pairedLowChk_ok {p : Params} (hp : Ok3 p) : ∀i<p.k-1,pairedLowChk p i=true := by
  rcases hp with rfl|rfl|rfl <;> decide

end VG.Proof.MlDsa.AArch64.Sign
