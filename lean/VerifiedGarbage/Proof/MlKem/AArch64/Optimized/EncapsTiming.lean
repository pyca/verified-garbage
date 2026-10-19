module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps

/-! # Constant-time encapsulation with paired matrix sampling -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Kem
variable {P : KemLay} {keccak : Sha3.AArch64.Permutation}

theorem matrix_table_of_kb {L : Layout} {s t : State} (hp : Pre P L s) (kb : KB P L s t) (tb : Tables t) :
    MatrixTable P L s t := by
  have scratch : Covers [⟨kA s L.sc,P.scl⟩] t.wr := by
    have hh := cov_w hp kb (b:=L.sc) (o:=0) (l:=P.scl) ⟨hp.scw,hp.scb⟩ (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  exact ⟨tb.shuffle,tb.shuffleRead,apart_of_covers tb.shuffleApart scratch⟩

end VG.Proof.MlKem.AArch64.Optimized
