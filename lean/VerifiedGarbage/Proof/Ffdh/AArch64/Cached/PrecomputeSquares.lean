module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeSquareLoop
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.CounterInit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete precomputation of the next comb tooth using the shared squaring kernel. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def basisSquareRanges (w : Nat) : List (Nat × Nat) := squareRanges w++[(slot w 5,8*(w+2))]

theorem precomputeSquares_ok (M : Mont) {s : State} {p : Parameters} {E n : Nat}
 (basis : Basis p E s) (rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 n) (positive : 0<n) (size : n<2^64) :
 WP isa (Precompute.squares M.mm) s fun t =>
 Basis p (E*2^n) t ∧ Power p (E*2^n) t ∧
 Frm p.B (basisSquareRanges p.w) s.mem t.mem ∧ Keep mmRegs s t := by
 unfold Precompute.squares
 rw [WP.seq_iff]
 refine WP.mono (basis_to_power basis) ?_
 rintro a ⟨powerA,_,frameA,restA⟩
 rw [WP.seq_iff]
 refine WP.mono (counterInit_ok powerA.good p.room ((arrays_header frameA (by decide)).trans rows)) ?_
 rintro b ⟨goodB,counterB,frameB,restB⟩
 have powerB := powerA.after_header goodB frameB (by decide : sI<32)
 rw [WP.seq_iff]
 refine WP.mono (precomputeSquareLoop_ok M powerB counterB positive size) ?_
 rintro c ⟨powerC,_,frameC,restC⟩
 refine WP.mono (power_to_basis powerC) ?_
 rintro t ⟨basisT,powerT,frameT,restT⟩
 have first : Frm p.B (basisSquareRanges p.w) s.mem a.mem :=
  Frm.of_arrays frameA (by simp [basisSquareRanges,squareRanges])
 have second : Frm p.B (basisSquareRanges p.w) a.mem b.mem :=
  Frm.of_outside frameB (by simp [basisSquareRanges,squareRanges])
 have third : Frm p.B (basisSquareRanges p.w) b.mem c.mem :=
  frameC.mono (fun r hr => List.mem_append_left _ hr)
 have fourth : Frm p.B (basisSquareRanges p.w) c.mem t.mem :=
  Frm.of_arrays frameT (by simp [basisSquareRanges])
 exact ⟨basisT,powerT,((first.trans second).trans third).trans fourth,
  (((restA.trans restB).trans restC).trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
