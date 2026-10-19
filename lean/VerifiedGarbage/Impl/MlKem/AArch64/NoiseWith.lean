module
public import VerifiedGarbage.Impl.MlKem.AArch64.Noise
public import VerifiedGarbage.Impl.MlKem.AArch64.Cbd16
@[expose] public section
namespace VG.Impl.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64

/-- `SamplePolyCBD₂` of the PRF output at `x0` into `x1`, with 16-bit coefficients (`w16`) or
32-bit ones. -/
def cbdCall (w16 : Bool := false) : Prog isa :=
 if w16 then .call "vg_mlkem16_cbd2" Cbd16.code16 else .call "vg_mlkem_cbd2" cbd2
def noiseOutWith (nttAt : Nat→Nat→Prog isa) (L : KemLay) (kg : Bool) (n buf : Nat) (w16 : Bool := false) :
    Prog isa :=
 let off := if n<L.k then (if kg then KG.sOff L n else KEM.yOff L n) else noiseOff L (n-L.k)
 let ns := if kg then KG.NS else KEM.NS
 seqs [.block (([.addImm .x .x0 .x19 buf] : List Instr)++ptrTo .x1 .x28 off),
   cbdCall w16,if kg || n<L.k then nttAt off ns else .block []]

def noisePairWith (nttAt : Nat→Nat→Prog isa) (L : KemLay) (kg : Bool) (n : Nat) (w16 : Bool := false) :
    Prog isa :=
 seqs [.block (noiseInit L kg n),squeezePair,noiseOutWith nttAt L kg n 400 w16,
   noiseOutWith nttAt L kg (n+1) 528 w16,
   .block (Paired.saved.zipIdx.reverse.map fun (r,i)=>.ldr .x r .x19 (1800+8*i))]

def noiseAllWith (nttAt : Nat→Nat→Prog isa) (L : KemLay) (kg : Bool) (w16 : Bool := false) : Prog isa :=
 seqs ((List.range L.k).map fun i=>noisePairWith nttAt L kg (2*i) w16)

def originalNttAt (off ns : Nat) : Prog isa :=
 .seq (.block (ptrTo .x0 .x28 off++ptrTo .x1 .x28 ns)) (.call "vg_mlkem_ntt" Ntt16.ntt)

theorem noiseOutWith_original (L : KemLay) (kg : Bool) (n buf : Nat) :
 noiseOutWith originalNttAt L kg n buf=noiseOut L kg n buf := rfl
theorem noisePairWith_original (L : KemLay) (kg : Bool) (n : Nat) :
 noisePairWith originalNttAt L kg n=noisePair L kg n := rfl
theorem noiseAllWith_original (L : KemLay) (kg : Bool) :
 noiseAllWith originalNttAt L kg=noiseAll L kg := rfl
end VG.Impl.MlKem.AArch64.Noise
