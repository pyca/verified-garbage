module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def expandedVals : List Nat :=
 let first := (List.range 8).flatMap fun block =>
  [1,2,4,8,16].flatMap fun len =>
   (List.range (if len<4 then 4 else 16/len)).flatMap fun g =>
    let idx := 256/len-1-(32*block)/(2*len)-(if len=1 then 4*g else if len=2 then 2*g else g)
    let zs := if len=1 then (List.range 4).map fun j => PairedBase.z (idx-j)
     else if len=2 then [PairedBase.z idx,PairedBase.z idx,PairedBase.z (idx-1),PairedBase.z (idx-1)]
     else List.replicate 4 (PairedBase.z idx)
    zs ++ zs.map PairedBase.bar
 let last := (List.range 8).flatMap fun j =>
  let z := if j=7 then 16382 else if j=6 then (PairedBase.z 1*16382)%8380417 else PairedBase.z (7-j)
  List.replicate 4 z ++ List.replicate 4 (PairedBase.bar z)
 first ++ last
def expandedWords : List (BitVec 64) :=
 (List.range (expandedVals.length/2)).map fun j => BitVec.ofNat 64 (expandedVals[2*j]!+2^32*expandedVals[2*j+1]!)

end VG.Impl.MlDsa.AArch64.Optimized.Paired
