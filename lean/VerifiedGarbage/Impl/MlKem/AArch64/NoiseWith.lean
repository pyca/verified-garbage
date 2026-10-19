module
public import VerifiedGarbage.Impl.MlKem.AArch64.Noise
public import VerifiedGarbage.Impl.MlKem.AArch64.Cbd16
@[expose] public section
namespace VG.Impl.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64

/-- `SamplePolyCBD₂` of the PRF output at `x0` into `x1`, with 16-bit coefficients. -/
def cbdCall : Prog isa := .call "vg_mlkem16_cbd2" Cbd16.code16
def noiseOutWith (nttAt : Nat→Nat→Prog isa) (L : KemLay) (kg : Bool) (n buf : Nat) :
    Prog isa :=
 let off := if n<L.k then (if kg then KG.sOff L n else KEM.yOff L n) else noiseOff L (n-L.k)
 let ns := if kg then KG.NS else KEM.NS
 seqs [.block (([.addImm .x .x0 .x19 buf] : List Instr)++ptrTo .x1 .x28 off),
   cbdCall,if kg || n<L.k then nttAt off ns else .block []]

def noisePairWith (nttAt : Nat→Nat→Prog isa) (L : KemLay) (kg : Bool) (n : Nat) :
    Prog isa :=
 seqs [.block (noiseInit L kg n),squeezePair,noiseOutWith nttAt L kg n 400,
   noiseOutWith nttAt L kg (n+1) 528,
   .block (Paired.saved.zipIdx.reverse.map fun (r,i)=>.ldr .x r .x19 (1800+8*i))]

def noiseAllWith (nttAt : Nat→Nat→Prog isa) (L : KemLay) (kg : Bool) : Prog isa :=
 seqs ((List.range L.k).map fun i=>noisePairWith nttAt L kg (2*i))

end VG.Impl.MlKem.AArch64.Noise
