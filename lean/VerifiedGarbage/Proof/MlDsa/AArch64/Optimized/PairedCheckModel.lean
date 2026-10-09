import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPartition

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (laneVector reduceWord normMask hintWord)

structure CheckData where
  mem : Mem
  flags : BitVec 128
  count : BitVec 128

structure CheckConstants where
  gamma : BitVec 128
  lower : BitVec 128
  width : BitVec 128

/-- The exact scalar-vector state after one measured z or h check. The memory
reads deliberately use the current memory, so the model requires no nonalias premise. -/
def checkStep (hint : Bool) (raw : BitVec 128) (out aux : Addr)
    (c : CheckConstants) (d : CheckData) : CheckData :=
  let low := d.mem.read out 16
  let high := d.mem.read aux 16
  let reduced := fun e => reduceWord (if hint then vword raw e else vword raw e+vword low e)
  let output := fun e => if hint then
    hintWord (vword c.gamma e) (reduced e+vword low e) (vword high e) else reduced e
  { mem := d.mem.write out 16 (laneVector output)
    flags := laneVector fun e => vword d.flags e ||| normMask (reduced e) (vword c.lower e) (vword c.width e)
    count := if hint then laneVector (fun e => vword d.count e+output e) else d.count }

def checkRun (hint : Bool) (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) : List (Fin 2 × Fin 8) → CheckData
  | [] => d
  | (p,j)::js => checkRun hint v out aux c
      (checkStep hint ((v p)[j.val])
        (out+BitVec.ofNat 64 (1024*p.val+128*j.val))
        (aux+BitVec.ofNat 64 (1024*p.val+128*j.val)) c d) js

def dataAt (s : State) : CheckData := ⟨s.mem,s.v .v30,s.v .v14⟩
def constantsAt (s : State) : CheckConstants := ⟨s.v .v11,s.v .v9,s.v .v10⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
