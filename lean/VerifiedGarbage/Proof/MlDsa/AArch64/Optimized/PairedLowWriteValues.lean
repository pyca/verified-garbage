import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowRead

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (laneVector reduceWord)

private theorem read128_write_self (m : Mem) (a : Addr) (v : BitVec 128) :
    (m.write a 16 v).read a 16=v := by
  simpa only [Mem.readW,Mem.writeW,BitVec.setWidth_eq] using
    Mem.readW_writeW_self m a 16 v (by decide)

def lowHighOutput (g : Nat) (m : Mem) (out : Addr) (raw : BitVec 128) : BitVec 128 :=
  laneVector fun e => lowHighWord g (lowInputValues m out raw e)

def lowLowOutput (g : Nat) (m : Mem) (out : Addr) (raw : BitVec 128) (c : LowConstants) : BitVec 128 :=
  laneVector fun e => reduceWord (lowInputValues m out raw e-
    lowHighWord g (lowInputValues m out raw e)*vword c.scale e)

theorem lowPair_mem (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem=
      (((d.mem.write out0 16 (lowHighOutput g d.mem out0 raw0)).write out1 16
        (lowHighOutput g d.mem out1 raw1)).write aux0 16
        (lowLowOutput g d.mem out0 raw0 c)).write aux1 16 (lowLowOutput g d.mem out1 raw1 c) := rfl

/-- The first high output survives all three subsequent stores. -/
theorem lowPair_read_high0 (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData)
    (h1 : Mem.Sep out0 16 out1 16) (h2 : Mem.Sep out0 16 aux0 16) (h3 : Mem.Sep out0 16 aux1 16) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read out0 16=lowHighOutput g d.mem out0 raw0 := by
  rw [lowPair_mem,Mem.read_write_sep h3 (by decide),Mem.read_write_sep h2 (by decide),
    Mem.read_write_sep h1 (by decide)]
  exact read128_write_self _ _ _

theorem lowPair_read_high1 (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData)
    (h2 : Mem.Sep out1 16 aux0 16) (h3 : Mem.Sep out1 16 aux1 16) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read out1 16=lowHighOutput g d.mem out1 raw1 := by
  rw [lowPair_mem,Mem.read_write_sep h3 (by decide),Mem.read_write_sep h2 (by decide)]
  exact read128_write_self _ _ _

theorem lowPair_read_low0 (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) (h3 : Mem.Sep aux0 16 aux1 16) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read aux0 16=lowLowOutput g d.mem out0 raw0 c := by
  rw [lowPair_mem,Mem.read_write_sep h3 (by decide)]
  exact read128_write_self _ _ _

theorem lowPair_read_low1 (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) :
    (lowPairStep g raw0 raw1 out0 out1 aux0 aux1 c d).mem.read aux1 16=lowLowOutput g d.mem out1 raw1 c := by
  rw [lowPair_mem]
  exact read128_write_self _ _ _

end VG.Proof.MlDsa.AArch64.Optimized.Paired
