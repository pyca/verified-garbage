module
public import VerifiedGarbage.Impl.Bignum.AArch64.Core


/-! The triangular products of an eight-limb square tile, by rows: row `j`
adds `a_j (a_0 + … + a_{j-1} 2^(64(j-1)))` at word `j`, its low halves by
one carry chain into the words `j … 2j - 1`, the carry into the new word
`2j`, then its high halves by another chain into the words `j + 1 … 2j`, all
held in rotating accumulator registers (word `k` in `accs[k % 8]`). Each
product is formed into one temporary just before the addition that uses it.
Word `j` is final after row `j` and is stored; words 8 to 14 after the last
row. No operand-dependent control flow. -/

@[expose] public section
namespace VG.Impl.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def inputs : List Reg := [.x2,.x3,.x4,.x5,.x6,.x9,.x11,.x27]
def accs : List Reg := [.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26]
/-- The register of word `k`. -/
def acc (k : Nat) : Reg := accs[k % 8]!
def inp (i : Nat) : Reg := inputs[i]!
/-- The temporary holding each product. -/
def tmp : Reg := .x13

/-- `R i := S i + half(x · Y i) + c` for `i < n`, the low (`hi = false`) or
high halves, from the carry clear. -/
def chain (hi : Bool) (x : Reg) (Y R S : Nat → Reg) (n : Nat) : List Instr :=
  (List.range n).flatMap fun i =>
    [if hi then .umulh tmp x (Y i) else .mul .x tmp x (Y i),
      (if i = 0 then Instr.adds else Instr.adcs) .x (R i) (S i) tmp]

/-- The low halves of row `j` into the words `j … 2j - 1`, the last of them
new, and the carry into the new word `2j`. -/
def low (j : Nat) : List Instr :=
  chain false (inp j) inp (fun i => acc (j + i)) (fun i => if i + 1 = j then .x7 else acc (j + i)) j ++
    [.adc .x (acc (2 * j)) .x7 .x7]
/-- The high halves of row `j` into the words `j + 1 … 2j`. -/
def high (j : Nat) : List Instr :=
  chain true (inp j) inp (fun i => acc (j + 1 + i)) (fun i => acc (j + 1 + i)) j
def row (j : Nat) : List Instr := low j ++ high j ++ [st (acc j) .x16 (8 * j)]

def loads : List Instr := inputs.zipIdx.map fun (r,i) => ld r .x8 (8*i)
def stores : List Instr := (List.range 7).map fun i => st (acc (i + 8)) .x16 (8 * (i + 8))
def code : List Instr := loads ++ (List.range 7).flatMap (fun j => row (j + 1)) ++ stores

end VG.Impl.Bignum.AArch64.SquareEight
