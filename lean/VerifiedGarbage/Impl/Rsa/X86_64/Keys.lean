import VerifiedGarbage.Impl.Rsa.X86_64

/-!
# RSA private keys on x86-64: the shared routines and `vg_rsa_crt_values`

The working space is `vg_rsa_public`'s (`Impl/Bignum/X86_64.lean`): a header
of 32 words and arrays of `w + 2` words after it, array `j` at byte
`256 + 8 (w + 2) j`. Arrays 0 to 7 have their bases in the header, as
`vg_rsa_public`'s; the routines here compute every base from `rdi` and the
stride `8 (w + 2)` (in `r9`, from the header), so that they need no other
register from the header but `w` (in `r12`): their addresses and branches
depend only on `rdi`, `w` and the stride, all public.

* `divmod q r d t`: the remainder and the quotient of `[q]` by `[d]`
  (`w` words each), by `64 w` steps of bit-serial division: `([r], [q])`
  shifted left a bit, then `[t] = [r] - [d]` over `w + 1` words and `[r]`
  replaced by `[t]` and `[q]`'s low bit set if it does not borrow. `[r]`
  ends as the remainder and `[q]` as the quotient.
* `inverse u v x₁ x₂ m t`: `128 w` steps of the binary extended Euclidean
  algorithm modulo the odd `[m]`: from `([u], [v], [x₁], [x₂]) =
  (a, m, 1, 0)`, `[v]` ends as `gcd(a, m)` and `[x₂]` with
  `[x₂] a ≡ [v] (mod m)`. Each step, under masks from the low bit of `[u]`
  and the borrow of `[u] - [v]`: `(u, v, x₁, x₂)` swapped to
  `(v, u, x₂, x₁)` if `u` is odd and below `v`, then
  `u -= v` and `x₁ -= x₂ (mod m)` if `u` is odd, then `u` and `x₁` halved
  (`x₁ + m` if `x₁` is odd).

`vg_rsa_crt_values(dp, dp_len, dq, dq_len, qinv, qinv_len, n, n_len, p,
p_len, q, q_len, d, d_len, scratch, scratch_len)`: the first six arguments
in registers, the others on the stack. `n` is checked as `vg_rsa_public`
checks it (it is public); then `p q = n` gives a mask, `qInv` is computed
by `inverse` (and'ing `gcd(q, p) = 1` into the mask), and `dP` and `dQ` by
`divmod` (with the divisor `p` or `q` with its low bit cleared: `p - 1` for
an odd `p`, which `p q = n` implies). Each result is written out masked.
`p q = n` is checked by `divmod` too, as `n mod p = 0`, `n / p = q` and `p`
odd.
-/

namespace VG.Impl.Rsa.X86_64.Keys

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64

/-! ## Arrays by their index -/

/-- The header slot of the stride `8 (w + 2)`. -/
def sStride : Nat := sFn 12
/-- A header slot for the routines' own masks. -/
def sMo : Nat := sFn 13

/-- `w` into `r12` and the stride into `r9`. -/
def ws : List Instr := [.mov .r12 (.mem (hdr sW)), .mov .r9 (.mem (hdr sStride))]

/-- The base of array `j` into `r`: `rdi + 256 + j · r9`. -/
def base (j : Nat) (r : Reg) : List Instr :=
  ([.mov r (.reg .rdi), .alu .add r (.imm (BitVec.ofNat 32 hdrBytes))] : List Instr) ++ List.replicate j (.alu .add r (.reg .r9))

/-- `[j] := 0` (`w + 2` words). -/
def zeroA (j : Nat) : Prog isa := .seq (.block (ws ++ base j .r8)) zeroAccLoop

/-- `[o] := [a]` over `w` words. -/
def copyA (o a : Nat) : Prog isa := .seq (.block (ws ++ base a .rsi ++ base o .rbx)) copyWords

/-! ## Loops over the words -/

/-- `[rbx] := 2 [rbx] + c` with the carry chain in `rbp`. -/
def shlBody : List Instr :=
  [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.reg .rax), .store (ix .rbx .r14) .rax, cfToRbp]

/-- `[rsi] := [r8] - [r10]` with the borrow chain in `rbp` (`subMod`'s). -/
def subBody : List Instr :=
  [cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), .store (ix .rsi .r14) .rax,
    cfToRbp]

/-- `[r8] := rbp ? [r8] : [rsi]`. -/
def selBody : List Instr :=
  [.mov .rax (.mem (ix .r8 .r14)), .mov .rdx (.mem (ix .rsi .r14)), .alu .xor .rax (.reg .rdx),
    .alu .and .rax (.reg .rbp), .alu .xor .rax (.reg .rdx), .store (ix .r8 .r14) .rax]

/-- `[rsi] := [r8] - ([r10] & r15)` with the borrow chain in `rbp`. -/
def subMBody : List Instr :=
  [.mov .rax (.mem (ix .r10 .r14)), .alu .and .rax (.reg .r15), .mov .rdx (.mem (ix .r8 .r14)), cfFromRbp,
    .alu .sbb .rdx (.reg .rax), .store (ix .rsi .r14) .rdx, cfToRbp]

/-- `[rbx] := ([r10] & r15) + [r8]` with the carry chain in `rbp`
(`subModArr`'s second loop). -/
def addMBody : List Instr :=
  [.mov .rax (.mem (ix .r10 .r14)), .alu .and .rax (.reg .r15), cfFromRbp, .alu .adc .rax (.mem (ix .r8 .r14)),
    .store (ix .rbx .r14) .rax, cfToRbp]

/-- `[rsi] := [r8] / 2`, word `i` from words `i` and `i + 1` of `[r8]` (the
low bit of word `i + 1` added as the top bit of word `i`). -/
def shrBody : List Instr :=
  [.mov .rax (.mem (ix .r8 .r14)), .shift .shr .rax 1, .mov .rdx (.mem (ix .r8 .r14 8)), .alu .and .rdx (.imm 1),
    .shift .ror .rdx 1, .alu .add .rax (.reg .rdx), .store (ix .rsi .r14) .rax]

/-- `[rbx], [r10] := [r10], [rbx]` under the mask `r15`. -/
def cswapBody : List Instr :=
  [.mov .rax (.mem (ix .rbx .r14)), .mov .rdx (.mem (ix .r10 .r14)), .alu .xor .rax (.reg .rdx),
    .alu .and .rax (.reg .r15), .mov .rdx (.mem (ix .rbx .r14)), .alu .xor .rdx (.reg .rax),
    .store (ix .rbx .r14) .rdx, .mov .rdx (.mem (ix .r10 .r14)), .alu .xor .rdx (.reg .rax),
    .store (ix .r10 .r14) .rdx]

/-- `rbp |= [rbx] ^ [r10]`. -/
def xorBody : List Instr :=
  [.mov .rax (.mem (ix .rbx .r14)), .alu .xor .rax (.mem (ix .r10 .r14)), .alu .or .rbp (.reg .rax)]

/-! ## Division -/

/-- `([r], [q]) := 2 ([r], [q])`, `[r]` over `w + 1` words (`r12` left at
`w + 1`). -/
def divShiftP (iQ iR : Nat) : List (Prog isa) := [
  .block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base iQ .rbx),
  wordLoop 0 shlBody,
  .block (base iR .rbx ++ ([.alu .add .r12 (.imm 1)] : List Instr)),
  wordLoop 0 shlBody]

/-- `[t] := [r] - [d]` over `w + 1` words, then `[r] := [t]` if it does not
borrow, `rbp` the mask of the borrow. -/
def divSubP (iR iD iT : Nat) : List (Prog isa) := [
  .block (([.alu .sub .r12 (.imm 1), .mov32 .rbp (.imm 0)] : List Instr) ++ base iR .r8 ++ base iD .r10 ++ base iT .rsi),
  wordLoop 0 subBody,
  .block [.mov .rax (.mem (ix .r8 .r12)), cfFromRbp, .alu .sbb .rax (.imm 0), .store (ix .rsi .r12) .rax, cfToRbp,
    .alu .add .r12 (.imm 1)],
  wordLoop 0 selBody]

/-- `[q] += 1` if it did not borrow, `r12 := w`, and the step counter `r13`
against `r11`. -/
def divBitP (iQ : Nat) : List Instr :=
  ([.alu .sub .r12 (.imm 1), .mov .rax (.reg .rbp), .alu .add .rax (.imm 1)] : List Instr) ++ base iQ .rbx ++
    ([.mov .rdx (.mem (at0 .rbx)), .alu .add .rdx (.reg .rax), .store (at0 .rbx) .rdx,
      .alu .add .r13 (.imm 1), .alu .cmp .r13 (.reg .r11)] : List Instr)

/-- One step of the division. -/
def divStep (iQ iR iD iT : Nat) : Prog isa := seqs (divShiftP iQ iR ++ (divSubP iR iD iT ++ [.block (divBitP iQ)]))

/-- `w` and the stride, `r8 := [r]`, `r11 := 64 w`, `r13 := 0`. -/
def divInit (iR : Nat) : List Instr :=
  ws ++ base iR .r8 ++ ([.mov .r11 (.reg .r12)] : List Instr) ++ List.replicate 6 (.alu .add .r11 (.reg .r11)) ++
    ([.mov32 .r13 (.imm 0)] : List Instr)

/-- `[r] := [q] mod [d]` and `[q] := [q] / [d]`, `[t]` working space:
`64 w` steps. -/
def divmod (iQ iR iD iT : Nat) : Prog isa :=
  seqs [.block (divInit iR), zeroAccLoop, .loop (divStep iQ iR iD iT) .ne]

/-! ## The binary extended Euclidean algorithm -/

/-- The mask of `u` odd into `sMo`, the mask of `u < v` into `rbp`, and the
swaps of `(u, v)` and `(x₁, x₂)` under both. -/
def invSwapP (iU iV iX₁ iX₂ : Nat) : List (Prog isa) := [
  .block (base iU .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .store (hdr sMo) .rdx] : List Instr) ++ base iV .r10 ++ ([.mov32 .rbp (.imm 0)] : List Instr)),
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp],
  .block [.mov .r15 (.reg .rbp), .alu .and .r15 (.mem (hdr sMo))],
  wordLoop 0 cswapBody,
  .block (base iX₁ .rbx ++ base iX₂ .r10),
  wordLoop 0 cswapBody]

/-- `u -= v`, if `u` is odd. -/
def invSubUP (iU iV : Nat) : List (Prog isa) := [
  .block (([.mov .r15 (.mem (hdr sMo)), .mov32 .rbp (.imm 0)] : List Instr) ++ base iU .r8 ++ base iV .r10 ++ base iU .rsi),
  wordLoop 0 subMBody]

/-- `x₁ -= x₂ (mod m)`, if `u` is odd (the mask in `r15`). -/
def invSubXP (iX₁ iX₂ iM iT : Nat) : List (Prog isa) := [
  .block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base iX₁ .r8 ++ base iX₂ .r10 ++ base iT .rsi),
  wordLoop 0 subMBody,
  .block (([.mov .r15 (.reg .rbp), .mov32 .rbp (.imm 0)] : List Instr) ++ base iT .r8 ++ base iM .r10 ++ base iX₁ .rbx),
  wordLoop 0 addMBody]

/-- `u -= v` and `x₁ -= x₂ (mod m)`, if `u` is odd. -/
def invSubP (iU iV iX₁ iX₂ iM iT : Nat) : List (Prog isa) := invSubUP iU iV ++ invSubXP iX₁ iX₂ iM iT

/-- `u /= 2`. -/
def invHalfUP (iU : Nat) : List (Prog isa) := [.block (base iU .r8 ++ base iU .rsi), wordLoop 0 shrBody]

/-- `x₁ := x₁ / 2 (mod m)`: `t := x₁ + m` if `x₁` is odd (`w + 1` words),
then `x₁ := t / 2`. -/
def invHalfXP (iX₁ iM iT : Nat) : List (Prog isa) := [
  .block (base iX₁ .r8 ++ ([.mov .rax (.mem (at0 .r8)), .alu .and .rax (.imm 1), .mov32 .r15 (.imm 0),
    .alu .sub .r15 (.reg .rax), .mov32 .rbp (.imm 0)] : List Instr) ++ base iM .r10 ++ base iT .rbx),
  wordLoop 0 addMBody,
  .block (([.mov32 .rax (.imm 0), cfFromRbp, .alu .adc .rax (.imm 0), .store (ix .rbx .r12) .rax] : List Instr) ++ base iT .r8 ++
    base iX₁ .rsi),
  wordLoop 0 shrBody]

/-- `u /= 2` and `x₁ := x₁ / 2 (mod m)`. -/
def invHalfP (iU iX₁ iM iT : Nat) : List (Prog isa) := invHalfUP iU ++ invHalfXP iX₁ iM iT

/-- The step counter `r13` against `r11`. -/
def countP : List Instr := [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.reg .r11)]

/-- One step of `inverse`. -/
def invStep (iU iV iX₁ iX₂ iM iT : Nat) : Prog isa :=
  seqs (invSwapP iU iV iX₁ iX₂ ++ (invSubP iU iV iX₁ iX₂ iM iT ++ (invHalfP iU iX₁ iM iT ++ [.block countP])))

/-- `w` and the stride, `r11 := 128 w`, `r13 := 0`. -/
def invInit : List Instr :=
  ws ++ ([.mov .r11 (.reg .r12)] : List Instr) ++ List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr)

/-- `128 w` steps of the binary extended Euclidean algorithm. -/
def inverse (iU iV iX₁ iX₂ iM iT : Nat) : Prog isa :=
  .seq (.block invInit) (.loop (invStep iU iV iX₁ iX₂ iM iT) .ne)

/-! ## Masks -/

/-- `rbp = 0` iff `[a] = [b]` over `w` words. -/
def eqA (a b : Nat) : List (Prog isa) :=
  [.block (ws ++ base a .rbx ++ base b .r10 ++ ([.mov32 .rbp (.imm 0)] : List Instr)), wordLoop 0 xorBody]

/-- `[j] := 1`, for `[j] = 0`. -/
def setOneA (j : Nat) : List Instr := ws ++ base j .rbx ++ ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr)

/-- The low word of `[j]` minus one (`[j] - 1` for a `[j]` whose low word
is not zero). -/
def decA (j : Nat) : List Instr :=
  ws ++ base j .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .sub .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr)

/-! ## Bytes -/

/-- `[j] := ` the number of the bytes whose pointer and length are in the
header slots `sPtr` and `sLen`. -/
def loadA (j sPtr sLen : Nat) : List (Prog isa) :=
  [zeroA j, .block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen))] : List Instr)), loadBE]

/-- `[j]` masked by the header slot `sMsk`, to the bytes whose pointer and
length are in the header slots `sPtr` and `sLen`. -/
def storeA (j sPtr sLen sMsk : Nat) : List (Prog isa) :=
  [.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen)),
    .mov .r15 (.mem (hdr sMsk))] : List Instr)), storeBE]

/-- Zeros to the bytes whose pointer and length are in the header slots
`sPtr` and `sLen` (at least one). -/
def zeroOut (sPtr sLen : Nat) : Prog isa :=
  .seq (.block [.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen)), .mov32 .rax (.imm 0)])
    (.loop (.block [.store8 (at0 .rsi) .rax, .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne)

/-- The mask's low bit returned, and the saved registers restored. -/
def retMask : List Instr := ([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit

/-! ## `vg_rsa_crt_values` -/

namespace CrtValues

/-- Header slots: `n`'s pointer and length in `vg_rsa_public`'s `sN` and
`sK`, the mask in its `sMask`. -/
def sDp : Nat := sFn 0
def sDq : Nat := sFn 3
def sQi : Nat := sFn 4
def sPl : Nat := sFn 5
def sQl : Nat := sFn 7
def sP : Nat := sFn 8
def sQ : Nat := sFn 9
def sD : Nat := sFn 10
def sDl : Nat := sFn 11

/-- The arrays: `n` (0), `p` (1), `divmod`'s quotient and remainder or
`inverse`'s `u` and `v` (2 and 3), `q` (4), `d` (5), `inverse`'s `x₁` and
`x₂` (6 and 7), the working array (8) and a constant or the divisor (9,
`aC`). -/
def aP : Nat := 1
def aQ : Nat := 4
def aD : Nat := 5
def aU : Nat := 2
def aV : Nat := 3
def aX₁ : Nat := 6
def aX₂ : Nat := 7
def aT : Nat := 8

/-- The stack argument `i` (from 1). -/
def stk (i : Nat) : MemOp := { base := .rsp, disp := 8 * i }

/-- Save the callee-saved registers and the arguments in the header at
`scratch`, with its base in `rdi`. `dp_len` and `dq_len` are `p_len` and
`q_len`. -/
def entry : List Instr :=
  ([.mov .r11 (.mem (stk 9))] : List Instr) ++
  (saved.zipIdx.map fun (r, i) => .store { base := .r11, disp := 8 * i } r) ++
  ([.store { base := .r11, disp := 8 * sDp } .rdi, .store { base := .r11, disp := 8 * sPl } .rsi,
    .store { base := .r11, disp := 8 * sDq } .rdx, .store { base := .r11, disp := 8 * sQl } .rcx,
    .store { base := .r11, disp := 8 * sQi } .r8,
    .mov .rax (.mem (stk 1)), .store { base := .r11, disp := 8 * sN } .rax,
    .mov .rax (.mem (stk 2)), .store { base := .r11, disp := 8 * sK } .rax,
    .mov .rax (.mem (stk 3)), .store { base := .r11, disp := 8 * sP } .rax,
    .mov .rax (.mem (stk 5)), .store { base := .r11, disp := 8 * sQ } .rax,
    .mov .rax (.mem (stk 7)), .store { base := .r11, disp := 8 * sD } .rax,
    .mov .rax (.mem (stk 8)), .store { base := .r11, disp := 8 * sDl } .rax, .mov .rdi (.reg .r11)] : List Instr)

/-- Zeros to `dp`, `dq` and `qinv`, and 0 returned. -/
def fail : Prog isa := seqs [zeroOut sDp sPl, zeroOut sDq sQl, zeroOut sQi sPl, .block (([.mov32 .rax (.imm 0)] : List Instr) ++ exit)]

/-- `w`, the arrays' bases and the stride, and the mask all ones. -/
def head : List Instr :=
  ([.mov .rcx (.mem (hdr sK)), .mov .r12 (.reg .rcx), .alu .add .r12 (.imm 7), .shift .shr .r12 3,
    .store (hdr sW) .r12] : List Instr) ++ setBases ++
  ([.mov .rax (.reg .r12), .alu .add .rax (.imm 2), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .store (hdr sStride) .rax, .mov .rax (.imm (BitVec.ofInt 32 (-1))),
    .store (hdr sMask) .rax] : List Instr)

/-- The constant array `aC` (9): zero, or one. -/
def aC : Nat := 9

/-- The mask of `rbp = 0` and'ed into `sMask`. -/
def andZero : List Instr :=
  [.alu .cmp .rbp (.imm 1), .alu .sbb .rbp (.reg .rbp), .alu .and .rbp (.mem (hdr sMask)), .store (hdr sMask) .rbp]

/-- The mask of `[j]` odd and'ed into `sMask`. -/
def andOdd (j : Nat) : List Instr :=
  ws ++ base j .rbx ++ ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .alu .and .rdx (.mem (hdr sMask)), .store (hdr sMask) .rdx] : List Instr)

/-- The mask of `p q = n` and'ed into `sMask`, as `n mod p = 0`,
`n / p = q` and `p` odd (which `p q = n` implies, `n` being odd). -/
def pqCheck : List (Prog isa) :=
  [zeroA aU, copyA aU aN, divmod aU aV aP aT] ++ eqA aU aQ ++ [.block andZero, zeroA aC] ++ eqA aV aC ++
    [.block andZero, .block (andOdd aP)]

/-- `inverse`'s start: `(u, v, x₁, x₂) := (q, p, 1, 0)`. -/
def invSetup : List (Prog isa) :=
  [zeroA aU, copyA aU aQ, zeroA aV, copyA aV aP, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂]

/-- `qInv = q⁻¹ mod p` into `aX₂`, and `gcd(q, p) = 1` and'ed into `sMask`. -/
def invPart : List (Prog isa) :=
  invSetup ++ ([inverse aU aV aX₁ aX₂ aP aT, zeroA aC, .block (setOneA aC)] ++ (eqA aV aC ++ [.block andZero]))

/-- `[aC] := [j] - 1` (for an odd `[j]`, whose low word is not zero), then `[aU] := d`. -/
def divisor (j : Nat) : List (Prog isa) :=
  [zeroA aC, copyA aC j, .block (decA aC), zeroA aU, copyA aU aD]

/-- The computation, once `n` is known valid. -/
def main : Prog isa := seqs ([
  .block head] ++ loadA aN sN sK ++ loadA aP sP sPl ++ loadA aQ sQ sQl ++ loadA aD sD sDl ++ pqCheck ++ invPart ++
  -- `dP = d mod (p - 1)` into `aX₁` and `dQ = d mod (q - 1)` in `aV`.
  divisor aP ++ [divmod aU aV aC aT, zeroA aX₁, copyA aX₁ aV] ++ divisor aQ ++ [divmod aU aV aC aT] ++
  storeA aX₂ sQi sPl sMask ++ storeA aX₁ sDp sPl sMask ++ storeA aV sDq sQl sMask ++
  [.block retMask])

/-- `vg_rsa_crt_values`. -/
def code : Prog isa :=
  .seq (.block (entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid)) (.ite .ne fail main)

end CrtValues

end VG.Impl.Rsa.X86_64.Keys
