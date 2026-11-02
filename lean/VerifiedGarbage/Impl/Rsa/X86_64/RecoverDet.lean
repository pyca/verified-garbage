module

public import VerifiedGarbage.Impl.Rsa.X86_64.Recover

/-!
# `vg_rsa_recover_primes_det` on x86-64

`vg_rsa_recover_primes`' arguments, entry and failure (`Recover.lean`), and
SP 800-56B Rev. 2 Appendix C.2 without a branch on a secret, in the working
space of `Keys.lean` at two widths, which the header gives (`width`):
narrow numbers of `v = ⌈k / 8⌉ + 1` words, the modulus and three bits more,
and wide numbers of `W = 2 v + 2` words, wide array `j` being narrow arrays
`2 j` and `2 j + 1`. A wide loop in the narrow layout doubles `r12` after
`ws` (`wideR`).

* `d e` (`Recover.prod`), then `x = d e - 1` and whether `d e ≥ 2` (`deMinus`);
* `x₂ = x mod 2^(64 v)`, `u = n - 1`, and `64 v` steps that halve `u` while
  it is even, and while `x₂` is even too halve it and double `x` (`twosBody`);
* `g = gcd(u, x₂)` by the batched inverse (`Keys.inverse`);
* `a = g x mod 2^(64 W)` (`Recover.prod` on the wide arrays), `m = ⌊a / n⌋`
  and `r = a mod n` (`Keys.divmod`), and whether `m < n` (`divA`);
* `m + 1` and `n - r`, their quotient `b - 1` and remainder, and whether it
  is zero (`divB`);
* `b² - 4 n`, and whether `b² > 4 n` (`minus4n`);
* its integer square root, two bits at a time from the top, in `32 W`
  steps (`sqrtBody`), and whether the remainder is zero;
* `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, written under the mask of every
  check (`sMask`).

Every loop's count is a public length.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.Keys.RecoverDet

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover (sP sQ sD sDl aE aD aM prod)

/-! ## Header slots -/

/-- A loop's count, the mask of `u` odd, the mask of `u` and `x₂` both
even, and a borrow of the square root. -/
def sCt : Nat := sFn 9
def sU : Nat := sFn 10
def sB2 : Nat := sFn 11
def sC : Nat := sFn 14

/-! ## Widths -/

/-- The narrow width `v = ⌈k / 8⌉ + 1`, or the wide `2 v + 2`, into `r12`,
the header's `w`, the arrays' bases and the stride. -/
def width (wide : Bool) : List Instr :=
  ([.mov .r12 (.mem (hdr sK)), .alu .add .r12 (.imm 7), .shift .shr .r12 3, .alu .add .r12 (.imm 1)] : List Instr) ++
  (if wide then ([.alu .add .r12 (.reg .r12), .alu .add .r12 (.imm 2)] : List Instr) else []) ++
  ([.store (hdr sW) .r12] : List Instr) ++ setBases ++
  ([.mov .rax (.reg .r12), .alu .add .rax (.imm 2), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .store (hdr sStride) .rax] : List Instr)

/-- The narrow width, and the mask all ones. -/
def head : List Instr := width false ++ ([.mov .rax (.imm (BitVec.ofInt 32 (-1))), .store (hdr sMask) .rax] : List Instr)

/-- `r12 := 2 r12 + 2`: the wide width, from the narrow one. -/
def wideR : List Instr := [.alu .add .r12 (.reg .r12), .alu .add .r12 (.imm 2)]

/-! ## Pieces over arrays by their index -/

/-- `[t] := [a] - [b]`, `rbp` the mask of its borrow. -/
def subA (t a b : Nat) : Prog isa :=
  .seq (.block (ws ++ ([.mov32 .rbp (.imm 0)] : List Instr) ++ base a .r8 ++ base b .r10 ++ base t .rsi))
    (wordLoop 0 subBody)

/-- `[o] := [a] + [b]`, modulo `2^(64 w)`. -/
def addA (o a b : Nat) : Prog isa :=
  .seq (.block (ws ++ ([.mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov32 .rbp (.imm 0)] : List Instr) ++
    base b .r10 ++ base a .r8 ++ base o .rbx)) (wordLoop 0 addMBody)

/-- `[j] := [j] / 2` (its word `w` zero). -/
def shrA (j : Nat) : Prog isa := .seq (.block (ws ++ base j .r8 ++ base j .rsi)) (wordLoop 0 shrBody)

/-- `[j] := 2 [j] + c` modulo `2^(64 w)`, for the carry in `rbp` that `pre` leaves, `w`
doubled first if `wide`. -/
def shlA (wide : Bool) (j : Nat) (pre : List Instr) : Prog isa :=
  .seq (.block (ws ++ (if wide then wideR else []) ++ base j .rbx ++ pre)) (wordLoop 0 shlBody)

/-- The mask of `rbp` (all ones or zero) and'ed into `sMask`. -/
def andNz : List Instr := [.alu .and .rbp (.mem (hdr sMask)), .store (hdr sMask) .rbp]

/-- The count less one, and `ZF` if it is zero. -/
def countNext : List Instr := [.mov .rax (.mem (hdr sCt)), .alu .sub .rax (.imm 1), .store (hdr sCt) .rax]

/-- `64 w` (the narrow width's bits) into the count. -/
def countN : List Instr := ws ++ ([.mov .rax (.reg .r12), .shift .shl .rax 6, .store (hdr sCt) .rax] : List Instr)

/-- `32 W = 64 (w + 1)` (half the wide width's bits) into the count. -/
def countW : List Instr :=
  ws ++ ([.mov .rax (.reg .r12), .alu .add .rax (.imm 1), .shift .shl .rax 6, .store (hdr sCt) .rax] : List Instr)

/-! ## The arrays

Narrow: `n` (0), zero (1, so that wide 0 is `n`), one (2, wide 1), `x`
(wide 2), `x₂` (6), `u` (7), `g` (12, wide 6), a temporary (14, wide 7);
`e`, `d` and `d e` as `Recover.prod` takes them (8, 9 and wide 5). -/

/-! ## `d e - 1` (wide) -/

def deMinus : List (Prog isa) := [zeroA 1, .block (setOneA 1),
  subA 2 5 1, .block CrtValues.andZero, subA 3 2 1, .block CrtValues.andZero]

/-! ## The halvings (narrow) -/

/-- `x₂` and `u = n - 1`, cleared above their words; `g`'s arrays cleared;
the count. -/
def twosInit : List (Prog isa) := [zeroA 6, copyA 6 4, zeroA 7, subA 7 0 2, zeroA 12, zeroA 13, .block countN]

/-- The masks of `u` odd and of `u` and `x₂` both even. -/
def twosFlags : List Instr :=
  ws ++ base 7 .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .store (hdr sU) .rdx] : List Instr) ++ base 6 .rbx ++
  ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax),
    .alu .or .rcx (.reg .rdx), .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1))), .store (hdr sB2) .rcx] : List Instr)

/-- `[j] := [j] / 2` unless the mask `keep` that `pre` leaves in `rbp`, through
array 14. -/
def halfIf (j : Nat) (pre : List Instr) : List (Prog isa) :=
  [.seq (.block (ws ++ base j .r8 ++ base 14 .rsi)) (wordLoop 0 shrBody),
    .seq (.block (ws ++ base j .r8 ++ base 14 .rsi ++ pre)) (wordLoop 0 selBody)]

/-- `x := 2 x` (wide) if `u` and `x₂` are both even, through wide array 7. -/
def dblIf : List (Prog isa) :=
  [.seq (.block (ws ++ wideR ++ ([.mov .r15 (.mem (hdr sB2)), .mov32 .rbp (.imm 0)] : List Instr) ++ base 4 .r10 ++
      base 4 .r8 ++ base 14 .rbx)) (wordLoop 0 addMBody),
    .seq (.block (ws ++ wideR ++ base 4 .r8 ++ base 14 .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr))) (wordLoop 0 selBody)]

def twosBody : Prog isa := seqs ([.block twosFlags] ++ halfIf 7 [.mov .rbp (.mem (hdr sU))] ++
  halfIf 6 [.mov .rbp (.mem (hdr sB2)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))] ++ dblIf ++
  [.block countNext])

/-! ## `a`, `m`, `r` and whether `m < n` (wide) -/

/-- `e`'s length `8 v = 4 W - 8`, for `Recover.prod`'s multiplier of `v` words. -/
def setEl : List Instr :=
  ws ++ ([.mov .rax (.reg .r12), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .sub .rax (.imm 8),
    .store (hdr sElen) .rax] : List Instr)

def divA : List (Prog isa) := [.block setEl, copyA 8 6, copyA 9 2] ++ prod ++
  [divmod 10 12 0 13, subA 14 10 0, .block andNz, copyA 7 10, copyA 6 12]

/-! ## `m + 1`, `n - r`, `b` (narrow) -/

def divB : List (Prog isa) := [zeroA 4, addA 4 14 2, zeroA 5, subA 5 0 12, divmod 5 6 4 7] ++ eqA 6 3 ++
  [.block CrtValues.andZero, zeroA 8, addA 8 5 2, zeroA 9]

/-! ## `b² - 4 n` (wide) -/

def minus4n : List (Prog isa) := [copyA 8 4, copyA 9 4] ++ prod ++
  [shlA false 0 [.mov32 .rbp (.imm 0)], shlA false 0 [.mov32 .rbp (.imm 0)],
    subA 12 10 0, .block CrtValues.andZero, subA 13 12 1, .block CrtValues.andZero, copyA 7 12]

/-! ## The square root (narrow)

`32 W` steps, two bits of `X` (wide array 7) at a time from its top: the
remainder (4) takes them, and the root (5) a bit, one if `4 y + 1` (6) fits
in the remainder (7 the difference). -/

def sqrtBody : Prog isa := seqs [
  shlA true 14 [.mov32 .rbp (.imm 0)], shlA false 4 [],
  shlA true 14 [.mov32 .rbp (.imm 0)], shlA false 4 [],
  copyA 6 5, shlA false 6 [.mov32 .rbp (.imm 0)], shlA false 6 [.mov .rbp (.imm (BitVec.ofInt 32 (-1)))],
  subA 7 4 6, .block [.store (hdr sC) .rbp],
  .seq (.block (ws ++ base 4 .r8 ++ base 7 .rsi ++ ([.mov .rbp (.mem (hdr sC))] : List Instr))) (wordLoop 0 selBody),
  shlA false 5 [.mov .rbp (.mem (hdr sC)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))],
  .block countNext]

def sqrt : List (Prog isa) := [zeroA 4, zeroA 5, .block countW, .loop sqrtBody .ne] ++ eqA 4 3 ++
  [.block CrtValues.andZero]

/-! ## The factors (narrow) -/

def factors : List (Prog isa) := [zeroA 10, addA 10 8 5, shrA 10, zeroA 11, subA 11 8 5, shrA 11] ++
  storeA 10 sP sK sMask ++ storeA 11 sQ sK sMask ++ [.block retMask]

/-! ## The function -/

/-- The computation, once `n` is known valid. -/
def main : Prog isa := seqs ([.block head] ++ loadA aN sN sK ++ [zeroA 1] ++ loadA aE sE sElen ++ loadA aD sD sDl ++
  prod ++ [.block (width true)] ++ deMinus ++
  [.block (width false)] ++ twosInit ++ [.loop twosBody .ne, inverse 6 12 15 7] ++
  [.block (width true)] ++ divA ++ [.block (width false)] ++ divB ++
  [.block (width true)] ++ minus4n ++ [.block (width false)] ++ sqrt ++ factors)

/-- `vg_rsa_recover_primes_det`. -/
def code : Prog isa :=
  .seq (.block (Recover.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid))
    (.ite .ne Recover.fail main)

end VG.Impl.Rsa.X86_64.Keys.RecoverDet
