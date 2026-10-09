import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowPassFlags
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowHalfOutput

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowPairAccept_halves (g : Nat) (v : Values) (out : Addr) (c : LowConstants)
    (m : Mem) (e : Nat) (i : LowIndex) :
    lowPairAccept g v out c m e i ↔
      ∀h:Fin 2,lowMask g m (lowAddr out i h) (lowHalfValue v i h) c e=0 := by
  constructor
  · intro hp h
    fin_cases h
    · exact hp.1
    · exact hp.2
  · intro hp
    exact ⟨hp 0,hp 1⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
