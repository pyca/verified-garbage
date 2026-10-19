module
public import VerifiedGarbage.Impl.Bignum.AArch64.Core


/-! Scheduled triangular products within an eight-limb square tile.
Each off-diagonal product is formed once; two product pairs are issued
before their dependent additions. No operand-dependent control flow. -/

@[expose] public section
namespace VG.Impl.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def pairs (k : Nat) : List (Nat × Nat) :=
 ((List.range 8).flatMap fun i => (List.range 8).map fun j => (i,j)).filter
  fun (i,j) => i < j && i+j == k
def inputs : List Reg := [.x2,.x3,.x4,.x5,.x6,.x9,.x11,.x27]
def lows : List Reg := [.x13,.x28]
def highs : List Reg := [.x14,.x30]
def product (ps : List (Nat × Nat)) (j : Nat) : List Instr :=
 if j < ps.length then
  let (a,b) := ps[j]!
  [.mul .x lows[j%2]! inputs[a]! inputs[b]!, .umulh highs[j%2]! inputs[a]! inputs[b]!]
 else []
def column (k : Nat) : List Instr :=
 let ps := pairs k
 product ps 0 ++ product ps 1 ++
 (List.range ps.length).flatMap (fun j =>
  [.adds .x .x19 .x19 lows[j%2]!, .adcs .x .x20 .x20 highs[j%2]!, .adc .x .x21 .x21 .x7] ++ product ps (j+2)) ++
 [st .x19 .x16 (8*k), mov .x19 .x20, mov .x20 .x21, movi .x21 0]
def code : List Instr :=
 (inputs.zipIdx.map fun (r,i) => ld r .x8 (8*i)) ++
 [movi .x19 0, movi .x20 0, movi .x21 0] ++ (List.range 13).flatMap (fun k => column (k+1)) ++
 [st .x19 .x16 112]

end VG.Impl.Bignum.AArch64.SquareEight
