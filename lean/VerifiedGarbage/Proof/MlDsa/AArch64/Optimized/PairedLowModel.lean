import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowShape
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckModel

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (laneVector reduceWord normMask)

structure LowConstants where
  scale : BitVec 128
  lower : BitVec 128
  width : BitVec 128

def lowConstantsAt (s : State) : LowConstants := ⟨s.v .v15,s.v .v9,s.v .v10⟩

def lowInputValues (m : Mem) (addr : Addr) (raw : BitVec 128) (e : Nat) : BitVec 32 :=
 Inverse.signCorrected (reduceWord (vword (m.read addr 16) e-vword raw e))

/-- Both source vectors are read before the four writes, exactly as in the pipeline.
The model does not impose nonalias assumptions. -/
def lowPairStep (g : Nat) (raw0 raw1 : BitVec 128) (out0 out1 aux0 aux1 : Addr)
    (c : LowConstants) (d : CheckData) : CheckData :=
 let a := lowInputValues d.mem out0 raw0
 let b := lowInputValues d.mem out1 raw1
 let ha := fun e => lowHighWord g (a e)
 let hb := fun e => lowHighWord g (b e)
 let la := fun e => reduceWord (a e-ha e*vword c.scale e)
 let lb := fun e => reduceWord (b e-hb e*vword c.scale e)
 { mem := (((d.mem.write out0 16 (laneVector ha)).write out1 16 (laneVector hb)).write
     aux0 16 (laneVector la)).write aux1 16 (laneVector lb)
   flags := laneVector fun e =>
     (vword d.flags e ||| normMask (la e) (vword c.lower e) (vword c.width e)) |||
       normMask (lb e) (vword c.lower e) (vword c.width e)
   count := d.count }
end VG.Proof.MlDsa.AArch64.Optimized.Paired
