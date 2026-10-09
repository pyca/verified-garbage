import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowWriteValues

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

def lowMask (g : Nat) (m : Mem) (out : Addr) (raw : BitVec 128) (c : LowConstants) (e : Nat) : BitVec 32 :=
  normMask (reduceWord (lowInputValues m out raw e-
    lowHighWord g (lowInputValues m out raw e)*vword c.scale e)) (vword c.lower e) (vword c.width e)

/-- Both paired coefficient checks contribute to the rejection accumulator. -/
theorem lowPair_flag (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) {e : Nat} (he : e<4) :
    vword (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).flags e=
      (vword d.flags e ||| lowMask g d.mem out0 raw0 c e) ||| lowMask g d.mem out1 raw1 c e := by
  simp only [lowPairStep,lowMask,laneVector_word _ he]

theorem lowPair_flag_zero (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) {e : Nat} (he : e<4) :
    vword (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).flags e=0 ↔
      (vword d.flags e=0 ∧ lowMask g d.mem out0 raw0 c e=0) ∧ lowMask g d.mem out1 raw1 c e=0 := by
  rw [lowPair_flag _ _ _ _ _ _ _ _ _ he]
  exact BitVec.or_eq_zero_iff.trans (and_congr_left fun _ => BitVec.or_eq_zero_iff)

theorem lowRun_flag_zero_initial (g : Nat) (v : Values) (out aux : Addr)
    (c : LowConstants) (d : CheckData) (is : List LowIndex) {e : Nat} (he : e<4)
    (hz : vword (lowRun g v out aux c d is).flags e=0) : vword d.flags e=0 := by
  induction is generalizing d with
  | nil => exact hz
  | cons i is ih => exact ((lowPair_flag_zero _ _ _ _ _ _ _ _ _ he).mp (ih _ hz)).1.1

end VG.Proof.MlDsa.AArch64.Optimized.Paired
