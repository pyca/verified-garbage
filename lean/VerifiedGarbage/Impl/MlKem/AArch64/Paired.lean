module

public import VerifiedGarbage.Impl.MlKem.AArch64.Rej8
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem
public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2

/-! # Paired SHAKE128 matrix generation for ML-KEM

Each pair starts with three SHAKE128 blocks. If either rejection stream
needs more candidates, it continues for at most two additional blocks.
Only the public matrix seed controls these retries. A final singleton uses
the same paired permutation, retaining only its first stream.

Scratch occupies the existing 2048-byte sampler region. The paired Keccak
states occupy bytes 0..400, stream buffers 400..1408, permutation scratch
1536..1672, continuation counters 1680..1712, and saved registers 1800..1864.
All output coefficients are initialized on either success or bounded failure.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Rej8

def saved : List Reg := [.x19,.x20,.x21,.x22,.x23,.x30]
def initCore (sb a b k : Nat) : List Instr :=
 [.vop (.movi0 .v0)] ++
 ((List.range 25).map fun i => .strq .v0 .x19 (16*i)) ++
 ((List.range 4).flatMap fun i => [.ldr .x .x6 .x28 (sb+8*i), .vop (.dup .d2 .v0 .x6), .strq .v0 .x19 (16*i)]) ++
 [.movz .x .x6 (BitVec.ofNat 16 ((a%k)+256*(a/k))) 0,.movk .x .x6 31 1,
  .movz .x .x7 (BitVec.ofNat 16 ((b%k)+256*(b/k))) 0,.movk .x .x7 31 1,
  .vop (.dup .d2 .v0 .x6),.vop (.ins .d2 .v0 1 .x7),.strq .v0 .x19 64,
  .movz .x .x6 0x8000 3,.vop (.dup .d2 .v0 .x6),.strq .v0 .x19 320]

def init (sb ss a b k : Nat) : List Instr :=
 ptrTo .x2 .x28 ss ++ (saved.zipIdx.map fun (r,i) => .str .x r .x2 (1800+8*i)) ++
 [mov .x19 .x2] ++ initCore sb a b k ++
 [.addImm .x .x20 .x19 400,.addImm .x .x21 .x19 904,.movz .x .x22 3 0]

def squeeze : Prog isa :=
 .loop (.seq (VG.Impl.Sha3.AArch64.Neon.X2.call true .x19 .x19 1536)
  (.block (VG.Impl.Sha3.AArch64.Neon.X2.squeeze 21 .x19 .x20 .x21 ++
   [.addImm .x .x20 .x20 168,.addImm .x .x21 .x21 168,.subImm .x .x22 .x22 1]))) (.nonzero .x .x22)
def reject (buf out : Nat) (flag : Reg) (w16 : Bool := false) : Prog isa :=
 .seq (.block (ptrTo .x3 .x28 out ++ [.addImm .x .x2 .x19 buf,.movz .x .x4 256 0,
 .movz .x .x5 168 0,.movz .x .x9 3329 0,.movz .x .x10 15 0]))
 (.seq (rejLoop w16) (.block [mov flag .x0]))
def fullInit (sb ss a k : Nat) : List Instr :=
 [.str .x .x22 .x19 1848,.str .x .x23 .x19 1856] ++
 (init sb ss a a k).take 1 ++ (init sb ss a a k).drop 7 ++ [.movz .x .x22 5 0]

def fullSample (L : KemLay) (kg : Bool) (a : Nat) (w16 : Bool := false) : Prog isa :=
 let sb := if kg then KG.SB else KEM.SB
 let ss := if kg then KG.SS else KEM.SS
 let off := if kg then KG.AH else KEM.AH
 seqs [.block (fullInit sb ss a L.k),
 .loop (.seq (VG.Impl.Sha3.AArch64.Neon.X2.call true .x19 .x19 1536)
  (.block ((List.range 21).flatMap (fun i => [.ldr .x .x6 .x19 (16*i),.str .x .x6 .x20 (8*i)]) ++
   [.addImm .x .x20 .x20 168,.subImm .x .x22 .x22 1]))) (.nonzero .x .x22),
 .block (rejConsts ++ [.movz .x .x9 0 0,.str .x .x9 .x19 1240] ++ ptrTo .x3 .x28 (off+1024*a) ++
 [.addImm .x .x2 .x19 400,.movz .x .x4 256 0,.movz .x .x5 280 0,.movz .x .x9 3329 0,.movz .x .x10 15 0]),
 rejLoop w16,
 .block [.logic .and .x .x24 .x24 .x0],
 .ite (.zero .x .x4) (.block [])
  (.loop (.block [.movz .x .x13 0 0,.str .w .x13 .x3 0,.addImm .x .x3 .x3 (if w16 then 2 else 4),.subImm .x .x4 .x4 1]) (.nonzero .x .x4)),
 .block [.ldr .x .x22 .x19 1848,.ldr .x .x23 .x19 1856]]

def extraReject (buf slot : Nat) (flag : Reg) (w16 : Bool := false) : Prog isa :=
 seqs [.block [.ldr .x .x3 .x19 slot,.ldr .x .x4 .x19 (slot+8)],
 .ite (.zero .x .x4) (.block [.movz .x flag 1 0])
  (seqs [.block [.addImm .x .x2 .x19 buf,.movz .x .x5 56 0,.movz .x .x9 3329 0,.movz .x .x10 15 0],
   rejLoop w16,.block [mov flag .x0,.str .x .x3 .x19 slot,.str .x .x4 .x19 (slot+8)]])]
def extraStep (w16 : Bool := false) : Prog isa :=
 seqs [.block [.addImm .x .x20 .x19 400,.addImm .x .x21 .x19 904],
 VG.Impl.Sha3.AArch64.Neon.X2.call true .x19 .x19 1536,
 .block (VG.Impl.Sha3.AArch64.Neon.X2.squeeze 21 .x19 .x20 .x21 ++ rejConsts),
 extraReject 400 1680 .x22 w16,extraReject 904 1696 .x23 w16,
 .block [.logic .and .x .x6 .x22 .x23]]
def zeroExtra (slot : Nat) (w16 : Bool := false) : Prog isa :=
 .seq (.block [.ldr .x .x3 .x19 slot,.ldr .x .x4 .x19 (slot+8)])
 (.ite (.zero .x .x4) (.block [])
  (.loop (.block [.movz .x .x13 0 0,.str .w .x13 .x3 0,.addImm .x .x3 .x3 (if w16 then 2 else 4),.subImm .x .x4 .x4 1]) (.nonzero .x .x4)))
def extraPair (w16 : Bool := false) : Prog isa :=
 seqs [extraStep w16,.ite (.zero .x .x6) (extraStep w16) (.block []),
 .block [.logic .and .x .x24 .x24 .x6],zeroExtra 1680 w16,zeroExtra 1696 w16]

def pair (L : KemLay) (keygen : Bool) (a : Nat) (w16 : Bool := false) : Prog isa :=
 let sb := if keygen then KG.SB else KEM.SB
 let ss := if keygen then KG.SS else KEM.SS
 let off := if keygen then KG.AH else KEM.AH
 seqs [.block (init sb ss a (a+1) L.k), squeeze, .block rejConsts,
  reject 400 (off+1024*a) .x22 w16,
  .block [.str .x .x3 .x19 1680,.str .x .x4 .x19 1688],
  reject 904 (off+1024*(a+1)) .x23 w16,
  .block [.str .x .x3 .x19 1696,.str .x .x4 .x19 1704,.logic .and .x .x6 .x22 .x23],
  .ite (.zero .x .x6) (extraPair w16) (.block []),
  .block ((saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i)))]
def lastSample (L : KemLay) (keygen : Bool) (w16 : Bool := false) : Prog isa :=
 let sb := if keygen then KG.SB else KEM.SB
 let ss := if keygen then KG.SS else KEM.SS
 let off := if keygen then KG.AH else KEM.AH
 let a := L.k*L.k-1
 seqs [.block (init sb ss a a L.k),squeeze,.block rejConsts,
  reject 400 (off+1024*a) .x22 w16,
  .ite (.zero .x .x22) (fullSample L keygen (L.k*L.k-1) w16) (.block []),
  .block (saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i))]
def matrix (L : KemLay) (kg : Bool) (w16 : Bool := false) : Prog isa :=
 seqs (((List.range (L.k*L.k/2)).map fun i => pair L kg (2*i) w16) ++
  (if L.k*L.k%2=1 then [lastSample L kg w16] else []))

end VG.Impl.MlKem.AArch64.Paired
