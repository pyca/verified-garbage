import VerifiedGarbage.Impl.Rsa.X86_64
import VerifiedGarbage.Impl.Bignum.X86_64.Adx

/-!
# RSA with the CRT private key on x86-64

`vg_rsa_private_crt(out, out_len, n, n_len, input, input_len, p, p_len, q,
q_len, dp, dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`: the
first six arguments in registers, the others on the stack.

The working space holds three workspaces, each a header and eight arrays as
`vg_rsa_public`'s (`Impl/Bignum/X86_64.lean`): one for `n` (`w` words), at
`scratch`, then one for `p` and one for `q` (`max(2, ⌈len / 8⌉)` words each).
The code runs in one at a time, its base in `rdi`; the headers of `p`'s and
`q`'s link back to `n`'s.

1. `n` is checked as `vg_rsa_public` checks it (it is public, so the code
   branches on it), and loaded with the input `c`, `-n⁻¹`, `R² mod n`, the
   number 1 and `c` in Montgomery form.
2. `p`, `q` and `qInv` are loaded, and the mask of `c < n`, `p q = n` and
   `qInv < p` computed; where it is clear, `p` and `q` are replaced by 3 and
   `qInv` by 0, so that what follows computes with valid values either way,
   and the result is masked at the end.
3. For `X = q`, then `X = p`: `c R_X mod X` (`R_X = 2^(64 w_X)`) without
   `R_X² mod X`, as `X` divides `n`: `G = 2^E mod n` for
   `E = 64 w_X (K + 1)` and `K = ⌈w / w_X⌉` (by squarings and doublings
   mod `n`), then `x G mod n` reduced by `K` Montgomery steps mod `X`
   (`redc`): `x R_X mod X`.
4. `m_X = c^d_X mod X` by squaring and multiplying at every bit of `d_X`,
   the product selected by the bit (`expLoop`); `h = (m_p - m_q) qInv mod p`
   and `m = m_q + q h`, written out masked.
-/

namespace VG.Impl.Rsa.X86_64.Crt

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64

/-! ## Header slots

`n`'s workspace keeps `vg_rsa_public`'s `sOut`, `sN`, `sK`, `sIn`, `sMask`
and `sCnt`. -/

def sP : Nat := sFn 3
def sPlen : Nat := sFn 4
def sQ : Nat := sFn 7
def sQlen : Nat := sFn 8
def sDp : Nat := sFn 9
def sDq : Nat := sFn 11
def sQinv : Nat := sFn 12
/-- The bases of `p`'s and `q`'s workspaces. -/
def sWsP : Nat := sFn 13
def sWsQ : Nat := sFn 14
/-- The exponent `E - 64 w` of `G`. -/
def sD : Nat := sFn 15

/-- In `p`'s and `q`'s workspaces: the base of `n`'s, the exponent's pointer
and length, its byte index, its bits left, its byte, the words left and the
source of `redc`, and the mask. -/
def sLink : Nat := sFn 0
def sExp : Nat := sFn 1
def sExpLen : Nat := sFn 2
def sI : Nat := sFn 3
def sBit : Nat := sFn 4
def sV : Nat := sFn 5
def sRem : Nat := sFn 6
def sSrc : Nat := sFn 7
def sMaskX : Nat := sFn 8

/-- The arrays of `p`'s and `q`'s workspaces, besides `X` (`aN`), the
accumulator and the temporary: `redc`'s chunk and `qInv` (1), `x R_X`
(4), the product `Y X` (5), `Y` (6) and the number 1 (7). -/
def aChunk : Nat := 1
def aXc : Nat := 4
def aT : Nat := 5

/-- `[b + 8 i]`, header slot `i` of the workspace at `b`. -/
def ws (b : Reg) (i : Nat) : MemOp := { base := b, disp := 8 * i }

/-- The stack argument `i` (from 1). -/
def stk (i : Nat) : MemOp := { base := .rsp, disp := 8 * i }

/-! ## Entry -/

/-- Save the callee-saved registers and the arguments in the header at
`scratch`, with its base in `rdi`. -/
def entry : List Instr :=
  [.mov .r11 (.mem (stk 11))] ++
  (saved.zipIdx.map fun (r, i) => .store { base := .r11, disp := 8 * i } r) ++
  [.store (ws .r11 sOut) .rdi, .store (ws .r11 sN) .rdx, .store (ws .r11 sK) .rcx, .store (ws .r11 sIn) .r8,
    .mov .rax (.mem (stk 1)), .store (ws .r11 sP) .rax, .mov .rax (.mem (stk 2)), .store (ws .r11 sPlen) .rax,
    .mov .rax (.mem (stk 3)), .store (ws .r11 sQ) .rax, .mov .rax (.mem (stk 4)), .store (ws .r11 sQlen) .rax,
    .mov .rax (.mem (stk 5)), .store (ws .r11 sDp) .rax, .mov .rax (.mem (stk 7)), .store (ws .r11 sDq) .rax,
    .mov .rax (.mem (stk 9)), .store (ws .r11 sQinv) .rax, .mov .rdi (.reg .r11)]

/-! ## `n`'s workspace -/

/-- `n`, the input `c`, the mask of `c < n`, `-n⁻¹`, the number 1, `R² mod n`
(as `vg_rsa_public_precompute` computes it) and `c R mod n`. -/
def nSetup (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  .block head,
  loadBE,
  .block [.mov .rsi (.mem (hdr sIn)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))],
  loadBE,
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
    .mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
    cfToRbp],
  .block ([.store (hdr sMask) .rbp, .mov .rbx (.mem (at0 .r10))] ++ minv ++
    [.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]),
  setWord aOne .rcx,
  .block [.mov .rax (.mem (ix .r10 .r12 (-8)))],
  topBit,
  .block [.store (hdr sCnt) .rcx, .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 1)],
  setWord aR2 .rcx,
  .block [.mov .rcx (.mem (hdr sCnt)), .alu .add .rcx (.mem (hdr sW))],
  doubles aN aAcc aTmp aR2 sCnt,
  mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2,
  mul aXm aX aR2]

/-! ## The prime workspaces -/

/-- `rax := ` the end of the arrays of the workspace at `rdx`: its last
array's base plus `8 (w + 2)`. -/
def wsEnd : List Instr :=
  [.mov .rax (.mem (ws .rdx (sArr aOne))), .mov .rdx (.mem (ws .rdx sW)), .alu .add .rdx (.imm 2),
    .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx)]

/-- A workspace at `rax` (its base stored in slot `slotWs`) for a number of
the byte length in slot `slotLen`: `w = max(2, ⌈len / 8⌉)`, its arrays'
bases, and its link to `n`'s; `rdi` stays `n`'s. -/
def wsNew (slotWs slotLen : Nat) : List (Prog isa) := [
  .block [.store (hdr slotWs) .rax, .mov .r12 (.mem (hdr slotLen)), .alu .add .r12 (.imm 7), .shift .shr .r12 3,
    .alu .cmp .r12 (.imm 2)],
  .ite .b (.block [.mov32 .r12 (.imm 2)]) (.block []),
  .block ([.mov .rsi (.reg .rdi), .mov .rdi (.reg .rax), .store (hdr sLink) .rsi, .store (hdr sW) .r12] ++ setBases ++
    [.mov .rdi (.reg .rsi)])]

/-- `[j] := 0` in the current workspace (`w + 2` words). -/
def zeroArr (j : Nat) : Prog isa :=
  .seq (.block [.mov .r8 (.mem (hdr (sArr j))), .mov .r12 (.mem (hdr sW))]) zeroAccLoop

/-- In a prime workspace: `[j] := ` the number of the bytes whose pointer and
length are in `n`'s header slots `slotPtr` and `slotLen`. -/
def loadArr (j slotPtr slotLen : Nat) : List (Prog isa) := [
  zeroArr j,
  .block [.mov .rax (.mem (hdr sLink)), .mov .rsi (.mem (ws .rax slotPtr)), .mov .rcx (.mem (ws .rax slotLen)),
    .mov .rbx (.mem (hdr (sArr j)))],
  loadBE]

/-- Into `p`'s and `q`'s workspaces, from `n`'s. -/
def enterP : Instr := .mov .rdi (.mem (hdr sWsP))
def enterQ : Instr := .mov .rdi (.mem (hdr sWsQ))
def leave : Instr := .mov .rdi (.mem (hdr sLink))

/-- The workspaces, `p`, `q` and `qInv` (into `p`'s chunk array). -/
def primesSetup : List (Prog isa) :=
  [.block ([.mov .rdx (.reg .rdi)] ++ wsEnd)] ++ wsNew sWsP sPlen ++
  [.block ([.mov .rdx (.mem (hdr sWsP))] ++ wsEnd)] ++ wsNew sWsQ sQlen ++
  [.block [enterP]] ++ loadArr aN sP sPlen ++ loadArr aChunk sQinv sPlen ++ [.block [leave, enterQ]] ++
  loadArr aN sQ sQlen ++ [.block [leave]]

/-! ## The checks -/

/-- `acc := 0` over `2 w + 2` words from `n`'s accumulator. -/
def zeroAccs : List (Prog isa) :=
  [.block [.mov .r8 (.mem (hdr (sArr aAcc))), .mov .rbx (.mem (hdr sW))], Adx.zeroWin]

/-- `acc += [r11] [r9]`: rows `acc[r13 ..] += [r11]_{r13} [r9]` (`r12` words) for
`r13` from 0 to `r10 - 1`, `r8` the row's base. -/
def mulRows : Prog isa :=
  .seq (.block [.mov32 .r13 (.imm 0)])
    (.loop (.seq (.block [.mov .rcx (.mem (ix .r11 .r13))])
      (.seq mulAddRow (.block [.alu .add .r8 (.imm 8), .alu .add .r13 (.imm 1), .alu .cmp .r13 (.reg .r10)]))) .ne)

/-- `p q` into `n`'s accumulators. -/
def pqProduct : List (Prog isa) := zeroAccs ++ [
  .block [.mov .rax (.mem (hdr sWsP)), .mov .r11 (.mem (ws .rax (sArr aN))), .mov .r10 (.mem (ws .rax sW)),
    .mov .rax (.mem (hdr sWsQ)), .mov .r9 (.mem (ws .rax (sArr aN))), .mov .r12 (.mem (ws .rax sW)),
    .mov .r8 (.mem (hdr (sArr aAcc)))],
  mulRows]

/-- The mask of `p q = n`, and'ed into `sMask`: the OR of the words of the
product's `XOR` with `n` over `w` words and of its words `w` to `2 w + 1`,
then all ones if it is zero. -/
def eqCheck : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aAcc))), .mov .r10 (.mem (hdr (sArr aN))),
    .mov32 .rbp (.imm 0)],
  wordLoop 0 [.mov .rax (.mem (ix .rbx .r14)), .alu .xor .rax (.mem (ix .r10 .r14)), .alu .or .rbp (.reg .rax)],
  .block [.mov .rax (.reg .r12), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rbx (.reg .rax), .alu .add .r12 (.imm 2)],
  wordLoop 0 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .rbp (.reg .rax)],
  .block [.alu .cmp .rbp (.imm 1), .alu .sbb .rbp (.reg .rbp), .alu .and .rbp (.mem (hdr sMask)),
    .store (hdr sMask) .rbp]]

/-- In `p`'s workspace: the mask of `qInv < p`, and'ed into `n`'s `sMask`. -/
def qinvCheck : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aChunk))), .mov .r10 (.mem (hdr (sArr aN))),
    .mov32 .rbp (.imm 0)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp],
  .block [.mov .rax (.mem (hdr sLink)), .alu .and .rbp (.mem (ws .rax sMask)), .store (ws .rax sMask) .rbp]]

/-- `[j] &= sMaskX` over `w` words. -/
def maskArr (j : Nat) : List (Prog isa) := [
  .block [.mov .r15 (.mem (hdr sMaskX)), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr j)))],
  wordLoop 0 [.mov .rax (.mem (ix .rbx .r14)), .alu .and .rax (.reg .r15), .store (ix .rbx .r14) .rax]]

/-- In a prime workspace: the mask from `n`'s; `X := mask ? X : 3`; `-X⁻¹`;
the number 1. -/
def primeFix : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr sLink)), .mov .rax (.mem (ws .rax sMask)), .store (hdr sMaskX) .rax]] ++
  maskArr aN ++
  [.block ([.mov .rax (.reg .r15), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rax (.imm 3),
      .alu .or .rax (.mem (at0 .rbx)), .store (at0 .rbx) .rax, .mov .rbx (.reg .rax)] ++ minv ++
      [.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]),
    setWord aOne .rcx]

/-- The checks and the fixes. -/
def checks : List (Prog isa) :=
  pqProduct ++ eqCheck ++ [.block [enterP]] ++ qinvCheck ++ primeFix ++ [.block [leave, enterQ]] ++ primeFix ++
  [.block [leave]]

/-! ## Arithmetic modulo a prime -/

/-- `[o] = [a] + [b] mod m` for `[a], [b] < m`: the sum into the
accumulator (`w + 1` words), then the subtraction of `m` selected as in
`montMul`. -/
def addMod (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .rbx (.mem (hdr (sArr a))), .mov .r9 (.mem (hdr (sArr b))), .mov .r10 (.mem (hdr (sArr aN))),
      .mov .r8 (.mem (hdr (sArr aAcc))), .mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aTmp))),
      .mov32 .rbp (.imm 0)])
    (.seq (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.mem (ix .r9 .r14)),
      .store (ix .r8 .r14) .rax, cfToRbp])
    (.seq (.block [.mov32 .rax (.imm 0), cfFromRbp, .alu .adc .rax (.imm 0), .store (ix .r8 .r12) .rax,
      .mov .rbx (.mem (hdr (sArr o)))])
    (.seq subMod selectAcc)))

/-- `[o] = [a] - [b] mod m` for `[a], [b] < m`: the difference into the
accumulator (as `subMod`'s loop), then `m` added under the mask of its
borrow. -/
def subModArr (o a b : Nat) : List (Prog isa) := [
  .block [.mov .r8 (.mem (hdr (sArr a))), .mov .r10 (.mem (hdr (sArr b))), .mov .rsi (.mem (hdr (sArr aAcc))),
    .mov .r12 (.mem (hdr sW)), .mov32 .rbp (.imm 0)],
  wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
    .store (ix .rsi .r14) .rax, cfToRbp],
  .block [.mov .r15 (.reg .rbp), .mov32 .rbp (.imm 0), .mov .r10 (.mem (hdr (sArr aN))),
    .mov .r8 (.mem (hdr (sArr aAcc))), .mov .rbx (.mem (hdr (sArr o)))],
  wordLoop 0 [.mov .rax (.mem (ix .r10 .r14)), .alu .and .rax (.reg .r15), cfFromRbp,
    .alu .adc .rax (.mem (ix .r8 .r14)), .store (ix .rbx .r14) .rax, cfToRbp]]

/-- `[o] := [a]` over `w` words. -/
def copyArr (o a : Nat) : List (Prog isa) :=
  [.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr a))), .mov .rbx (.mem (hdr (sArr o)))], copyWords]

/-- In a prime workspace: `[aXc] := x R_X^(-K) mod X` for the `w_n` words at
`n`'s array `j` (`x = Σ x_k R_X^k`, chunks of `w_X` words): `acc := 0`;
for each chunk, `acc := acc R_X⁻¹ + x_k R_X⁻¹ mod X`. -/
def redc (mul : Nat → Nat → Nat → Prog isa) (j : Nat) : List (Prog isa) := [
  zeroArr aXc,
  .block [.mov .rax (.mem (hdr sLink)), .mov .rdx (.mem (ws .rax (sArr j))), .store (hdr sSrc) .rdx,
    .mov .rdx (.mem (ws .rax sW)), .store (hdr sRem) .rdx],
  .loop (seqs [
    zeroArr aChunk,
    .block [.mov .r12 (.mem (hdr sRem)), .alu .cmp .r12 (.mem (hdr sW))],
    .ite .b (.block []) (.block [.mov .r12 (.mem (hdr sW))]),
    .block [.mov .rsi (.mem (hdr sSrc)), .mov .rbx (.mem (hdr (sArr aChunk)))],
    copyWords,
    .block [.mov .rax (.mem (hdr sRem)), .alu .sub .rax (.reg .r12), .store (hdr sRem) .rax,
      .alu .add .r12 (.reg .r12), .alu .add .r12 (.reg .r12), .alu .add .r12 (.reg .r12),
      .alu .add .r12 (.mem (hdr sSrc)), .store (hdr sSrc) .r12],
    mul aXc aXc aOne,
    mul aT aChunk aOne,
    addMod aXc aXc aT,
    .block [.mov .rax (.mem (hdr sRem)), .alu .test .rax (.reg .rax)]]) .ne]

/-- In `n`'s workspace: `[aY] := G = 2^E mod n` for `E = 64 w_X (K + 1)`,
`K = ⌈w / w_X⌉`, the prime workspace's base in slot `slotWs`: `D = E - 64 w`,
then `Y = R mod n` and for each bit of `D` from the top, `Y := Y² R⁻¹`
and doubled if the bit is set: `Y = 2^D R`. -/
def gPow (mul : Nat → Nat → Nat → Prog isa) (slotWs : Nat) : List (Prog isa) := [
  .block [.mov .rax (.mem (hdr slotWs)), .mov .rax (.mem (ws .rax sW)), .mov .r12 (.mem (hdr sW)),
    .mov32 .rcx (.imm 0)],
  .loop (.block [.alu .add .rcx (.reg .rax), .alu .cmp .rcx (.reg .r12)]) .b,
  .block [.alu .add .rcx (.reg .rax), .alu .sub .rcx (.reg .r12), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .store (hdr sD) .rcx, .mov .rax (.reg .rcx)],
  topBit,
  .block [.store (hdr sCnt) .rdx],
  mul aY aR2 aOne,
  .loop (seqs [
    mul aY aY aY,
    .block [.mov .rax (.mem (hdr sD)), .alu .and .rax (.mem (hdr sCnt))],
    .ite .ne (double aN aAcc aTmp aY) (.block []),
    .block [.mov .rax (.mem (hdr sCnt)), .shift .shr .rax 1, .store (hdr sCnt) .rax, .alu .test .rax (.reg .rax)]]) .ne]

/-! ## The exponentiation -/

/-- One bit of the exponent: `Y := Y² R⁻¹`, `T := Y [aXc] R⁻¹`, and
`Y := T` if the bit (the top of the byte in `sV`) is set. -/
def expBit (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  mul aY aY aY,
  mul aT aY aXc,
  .block [.mov .rdx (.mem (hdr sV)), .mov .rax (.reg .rdx), .alu .add .rax (.reg .rax), .store (hdr sV) .rax,
    .shift .shr .rdx 7, .alu .and .rdx (.imm 1), .mov32 .rbp (.imm 0), .alu .sub .rbp (.reg .rdx),
    .mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aT))), .mov .rsi (.mem (hdr (sArr aY))),
    .mov .rbx (.mem (hdr (sArr aY)))],
  selectAcc,
  .block [.mov .rax (.mem (hdr sBit)), .alu .sub .rax (.imm 1), .store (hdr sBit) .rax]]

/-- `Y := Y^d` (`Y` and `[aXc]` in Montgomery form) for the exponent whose
pointer and length are in `n`'s header slots `slotPtr` and `slotLen`, its
bytes most significant first. -/
def expLoop (mul : Nat → Nat → Nat → Prog isa) (slotPtr slotLen : Nat) : List (Prog isa) := [
  .block [.mov .rax (.mem (hdr sLink)), .mov .rdx (.mem (ws .rax slotPtr)), .store (hdr sExp) .rdx,
    .mov .rdx (.mem (ws .rax slotLen)), .store (hdr sExpLen) .rdx, .mov32 .rdx (.imm 0), .store (hdr sI) .rdx],
  .loop (seqs [
    .block [.mov .rax (.mem (hdr sExp)), .mov .rcx (.mem (hdr sI)), .movzx8 .rax { base := .rax, index := some .rcx },
      .store (hdr sV) .rax, .mov32 .rax (.imm 8), .store (hdr sBit) .rax],
    .loop (seqs (expBit mul)) .ne,
    .block [.mov .rax (.mem (hdr sI)), .alu .add .rax (.imm 1), .store (hdr sI) .rax,
      .alu .cmp .rax (.mem (hdr sExpLen))]]) .ne]

/-! ## The primes -/

/-- `q`: `m_q = c^dQ mod q` into `q`'s `aY`. -/
def qPhase (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  gPow mul sWsQ ++ [.block [enterQ]] ++ redc mul aY ++ copyArr aY aXc ++ [.block [leave], mul aY aXm aY,
    .block [enterQ]] ++ redc mul aY ++ expLoop mul sDq sQlen ++ [mul aY aY aOne, .block [leave]]

/-- `p`: `m_p R_p` into `p`'s `aY`, `m_q R_p` into its `aXc`, their
difference into `aT`, `qInv` again (masked) into its chunk array, and
`h = (m_p - m_q) qInv mod p` into its `aY`. -/
def pPhase (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  gPow mul sWsP ++ [.block [enterP]] ++ redc mul aY ++ copyArr aY aXc ++ [.block [leave], zeroArr aX,
    .block [.mov .rax (.mem (hdr sWsQ)), .mov .rsi (.mem (ws .rax (sArr aY))), .mov .r12 (.mem (ws .rax sW)),
      .mov .rbx (.mem (hdr (sArr aX)))],
    copyWords, mul aX aX aR2, mul aX aX aY, mul aY aXm aY, .block [enterP]] ++
  redc mul aY ++ expLoop mul sDp sPlen ++ [.block [leave]] ++ [.block [enterP]] ++ redc mul aX ++
  subModArr aT aY aXc ++ loadArr aChunk sQinv sPlen ++ maskArr aChunk ++ [mul aY aT aChunk, .block [leave]]

/-! ## The result -/

/-- `m = m_q + q h` into `n`'s accumulators, written out masked, and the
mask's low bit returned. -/
def finish : List (Prog isa) := zeroAccs ++ [
  .block [.mov .rax (.mem (hdr sWsQ)), .mov .rsi (.mem (ws .rax (sArr aY))), .mov .r12 (.mem (ws .rax sW)),
    .mov .rbx (.mem (hdr (sArr aAcc)))],
  copyWords,
  .block [.mov .rax (.mem (hdr sWsP)), .mov .r11 (.mem (ws .rax (sArr aY))), .mov .r10 (.mem (ws .rax sW)),
    .mov .rax (.mem (hdr sWsQ)), .mov .r9 (.mem (ws .rax (sArr aN))), .mov .r12 (.mem (ws .rax sW)),
    .mov .r8 (.mem (hdr (sArr aAcc)))],
  mulRows,
  .block [.mov .rbx (.mem (hdr (sArr aAcc))), .mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)),
    .mov .r15 (.mem (hdr sMask))],
  storeBE,
  .block ([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] ++ exit)]

/-- The computation, once `n` is known valid. -/
def main (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs (nSetup mul ++ primesSetup ++ checks ++ qPhase mul ++ pPhase mul ++ finish)

/-- `vg_rsa_private_crt`. -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block (entry ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] ++ invalid))
    (.ite .ne fail (main mul))

end VG.Impl.Rsa.X86_64.Crt
