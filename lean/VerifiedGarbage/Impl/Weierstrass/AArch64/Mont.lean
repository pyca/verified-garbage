import VerifiedGarbage.Impl.Mont.AArch64
import VerifiedGarbage.Spec.Weierstrass.Mont
import VerifiedGarbage.TCB.AArch64.Target

/-!
# Montgomery products modulo a curve's `p` or `n`, as functions, on AArch64

`vg_<curve>_mul_mod_<p|n>(ws, o, a, b)` (`Spec/Weierstrass/Mont.lean`;
AAPCS64: `ws` in `x0`, the offsets `o`, `a` and `b` in `w1`–`w3`) for a
modulus `m` of `n` 64-bit words, word-by-word Montgomery multiplication (the
rows of `Impl/Mont/AArch64.lean`) with every word it multiplies by in a
register:

1. the offsets are zero-extended (their upper halves are unspecified), the
   callee-saved registers the function writes are saved in lanes of
   `v16`–`v20` (`saveCode`), the pointers `ro = ws + o` and `ra = ws + a`
   computed, and all of `[b]` loaded into registers (`bRegsF`);
2. each round loads one word of `[a]` through `ra` (`roundF`), and its
   reduction needs none of the modulus's words: P-384's `p` is sparse
   (`redSparse`: `u p = u (2^384 + 2^32) - u (2^128 + 2^96 + 1)`, by shifts, an
   addition and a subtraction), and P-521's friendly (by shifts);
3. the result is reduced below `m` against the modulus's words, built in
   registers (`mLoadCode`, `csubM`), stored through `ro`, and the saved
   registers restored.

The inline products (`Impl/Mont/AArch64.lean`) keep only four words of `[b]`
in registers and load the rest, and multiply by P-384's modulus word by word:
the function has the callee-saved registers to spare, and one multiplication
per round of P-384's reduction instead of thirteen, which pays for its call.
The function writes neither `x19` nor `x20`, which callers keep public across
a call (loop counters and pointers), leaves `x0 = ws`, and writes only `[o]`
of `ws`. Every address is `ws` plus a constant or one of the offsets (plus a
constant), so only the pointer and the offsets may affect timing.
-/

namespace VG.Impl.Weierstrass.AArch64.Mont

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64

/-- `-m⁻¹ mod 2⁶⁴`, for odd `m`, by Newton's iteration. -/
def minv (m : Nat) : Nat :=
  let inv := (List.range 6).foldl (fun x _ => x * ((2 + 2 ^ 64 - m * x % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) 1
  (2 ^ 64 - inv) % 2 ^ 64

/-- The function's own working space ends at byte 4096; its last `16 n`
bytes, from `moAt n`, are where a caller's temporary area may be, which a
call may change (`callOf`). -/
def moAt (n : Nat) : Nat := 4096 - 16 * n

/-- The modulus `m` of `n` words, as the multiplication takes it. -/
def mod (n m : Nat) : Mod where
  n := n
  mo := moAt n
  tmp := moAt n - 8 * n
  minv := BitVec.ofNat 64 (minv m)
  red := Red.ofModulus n m
  tight := tightOk n m

/-- Word `j` of `m`. -/
def mWord (m j : Nat) : BitVec 64 := BitVec.ofNat 64 (m >>> (64 * j))

/-- The registers holding the words of `[b]`: four caller-saved ones, then
callee-saved ones, and `x6` for nine words (whose friendly modulus needs no
constant in it). -/
def bRegsF (n : Nat) : List Reg :=
  (if n ≤ 6 then [.x4, .x5, .x16, .x17, .x21, .x22]
    else [.x4, .x5, .x16, .x17, .x6, .x24, .x25, .x26, .x27]).take n

/-- The registers for the modulus's distinct words, free once the rounds are
done. -/
def mPool (n : Nat) : List Reg := if n ≤ 6 then [.x23, .x24, .x25, .x26] else [.x26, .x27, .x28]

/-- The pointer to `[a]`. -/
def raF (n : Nat) : Reg := if n ≤ 6 then .x27 else .x28

/-- The pointer to `[o]`: `x30` for nine words, saved like the callee-saved
registers, for want of another. -/
def roF (n : Nat) : Reg := if n ≤ 6 then .x28 else .x30

/-- The distinct words of `m`, in order. -/
def mDistinct (n m : Nat) : List (BitVec 64) :=
  (List.range n).foldl (fun ds j => if mWord m j ∈ ds then ds else ds ++ [mWord m j]) []

/-- The register holding word `j` of `m`. -/
def mReg (n m j : Nat) : Reg := (mPool n).getD ((mDistinct n m).idxOf (mWord m j)) .x23

/-- The registers holding the words of `m`, in order. -/
def mRegs (n m : Nat) : List Reg := (List.range n).map (mReg n m)

/-- Each distinct word of `m` and its register. -/
def mLoads (n m : Nat) : List (Reg × BitVec 64) := (mPool n).zip (mDistinct n m)

/-- The modulus's words into their registers. -/
def mLoadCode (n m : Nat) : List Instr := (mLoads n m).flatMap fun p => const64 p.1 p.2

/-- Words in registers, as a row multiplies by them. -/
def regWords (rs : List Reg) : List RWord := rs.map fun r => .gen (.reg r)

/-- `u (2^384 + 2^32)`'s multiplicand: `2^32`, then `2^384`. -/
def sparseWords : List RWord := [.pow2 32, .zero, .zero, .zero, .zero, .zero, .one]

/-- `ts -= rs`, word by word in place, with `subs` on the first word and
`sbcs` on the others. -/
def subsIn (first : Bool) : List Reg → List Reg → List Instr
  | t :: ts, r :: rs => (if first then .subs .x t t r else .sbcs .x t t r) :: subsIn false ts rs
  | _, _ => []

/-- A round's reduction for P-384's `p = 2^384 - 2^128 - 2^96 + 2^32 - 1`:
`u = t₀ m'` (`x1`), `T += u (2^384 + 2^32)` (shifts), and `T -= u (2^128 + 2^96 + 1)`,
whose words `u`, `u 2^32 mod 2^64` (`x2`) and `⌊u / 2^32⌋ + u` (`x3`, and its
carry in `x23`) the subtraction takes. -/
def redSparse (n i : Nat) : List Instr :=
  .mul .x .x1 (win n i 0) .x6 :: (row .x0 .x1 (wins n i) sparseWords ++
    (([.lsl .x .x2 .x1 32, .lsr .x .x3 .x1 32, .adds .x .x3 .x3 .x1, .adcs .x .x23 .x7 .x7] : List Instr) ++
      subsIn true (wins n i) ([.x1, .x2, .x3, .x23] ++ List.replicate (n - 2) .x7)))

/-- Round `i`: `T += a_i [b]`, `[a]` through `ra` and `[b]` in `bRegsF`, then
`T += u m`: sparse for P-384 (`redSparse`), by shifts for a friendly modulus
(as the inline product), the only moduli the function takes. -/
def roundF (n m i : Nat) : List Instr :=
  let M := mod n m
  [.ldr .x .x1 (raF n) (8 * i)] ++ row .x0 .x1 (prodWins M i) (regWords (bRegsF n)) ++
    if sparseOk n m then redSparse n i else
    match M.red with
    | .general => []
    | .friendly ws =>
      row .x0 (win n i 0) (wins n i).tail (ws.map (fWord (firstGen ws))) ++ [.movz .x (win n i 0) 0 0]

/-- `ds = ts - m`, word by word, against the modulus's words in the registers
`ms`, with `subs` on the first word and `sbcs` on the others. -/
def diffsM (first : Bool) : List Reg → List Reg → List Reg → List Instr
  | t :: ts, d :: ds, r :: ms =>
    (if first then .subs .x d t r else .sbcs .x d t r) :: diffsM false ts ds ms
  | _, _, _ => []

/-- `ts` (and the top word `top`), below `2m`, reduced modulo `m` against its
words in `ms`: as `csubR`, the difference into `dRegs n` and selected where
it did not borrow. -/
def csubM (n : Nat) (ts : List Reg) (top : Reg) (ms : List Reg) : List Instr :=
  diffsM true ts (dRegs n) ms ++ [.sbcs .x .x2 top .x7] ++ selectsR ts (dRegs n)

/-- The callee-saved registers the function writes. -/
def saved (n : Nat) : List Reg :=
  ((acc n ++ dRegs n ++ bRegsF n ++ mPool n ++ [raF n, roF n]).filter fun r => r ∈ preserved).eraseDups

/-- The vector register and lane that saves the `i`-th of them. -/
def slot (i : Nat) : VReg × Nat :=
  ([VReg.v16, .v17, .v18, .v19, .v20].getD (i / 2) .v16, i % 2)

/-- The registers saved in their lanes. -/
def saveCode (n : Nat) : List Instr :=
  (saved n).zipIdx.map fun (r, i) => .vop (.ins .d2 (slot i).1 (slot i).2 r)

/-- The registers restored from their lanes. -/
def restoreCode (n : Nat) : List Instr :=
  (saved n).zipIdx.map fun (r, i) => .umov .x r (slot i).1 (slot i).2

/-- The offsets zero-extended (as 32-bit additions of zero). -/
def zextCode : List Instr := [.addImm .w .x1 .x1 0, .addImm .w .x2 .x2 0, .addImm .w .x3 .x3 0]

/-- After the offsets are zero-extended: the registers saved, the pointers
`ro = ws + o`, `ra = ws + a` and `x3 = ws + b`, `[b]` into `bRegsF`, the
reduction's constant into `x6`, `x7` and the accumulator cleared. -/
def entryRest (n m : Nat) : List Instr :=
  saveCode n ++
    [.add .x (roF n) .x0 .x1, .add .x (raF n) .x0 .x2, .add .x .x3 .x0 .x3] ++
    loadsR .x3 (bRegsF n) 0 ++ mulConst (mod n m) ++ zero7 :: zeros (acc n)

/-- The entry. -/
def entry (n m : Nat) : List Instr := zextCode ++ entryRest n m

/-- The low words of the accumulator after the rounds. -/
def lowF (n : Nat) : List Reg := (List.range n).map (win n n)

/-- After the rounds: the modulus's words into their registers, the result
reduced and stored through `ro`, the registers restored. -/
def exitCode (n m : Nat) : List Instr :=
  mLoadCode n m ++ csubM n (lowF n) (win n n n) (mRegs n m) ++
    storesR (roF n) (lowF n) 0 ++ restoreCode n

/-- `vg_<curve>_mul_mod_<p|n>`: the entry, the rounds, the exit. -/
def mulFn (n m : Nat) : Prog isa :=
  .seq (.block zextCode)
    (.block (entryRest n m ++ (List.range n).flatMap (roundF n m) ++ exitCode n m))

open Spec.Weierstrass.Mont in
/-- The moduli whose products are functions on AArch64: P-384's and P-521's
`p`. A product of four words is short enough inline that calls do not pay,
and the products modulo `n` are few. -/
def fns : List Modulus := [p384p, p521p]

/-- The function computing the products of the modulus `M` (its name and its
modulus), if any: one of `fns` of `M.n` words and `M.minv`, if `M`'s
temporary area is in the function's own working space (at `moAt`), which a
call may change. -/
def callOf (M : Mod) : Option (String × Nat) :=
  if M.tmp = moAt M.n then
    (fns.find? fun S => S.k == M.n && BitVec.ofNat 64 (minv S.m) == M.minv).map fun S => (S.fn "mul", S.m)
  else none

end VG.Impl.Weierstrass.AArch64.Mont
