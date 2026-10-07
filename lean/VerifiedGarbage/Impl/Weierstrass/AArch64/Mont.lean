import VerifiedGarbage.Impl.Mont.AArch64
import VerifiedGarbage.Spec.Weierstrass.Mont
import VerifiedGarbage.TCB.AArch64.Target

/-!
# Montgomery products modulo a curve's `p` or `n`, as functions, on AArch64

`vg_<curve>_mul_mod_<p|n>(ws, o, a, b)` (`Spec/Weierstrass/Mont.lean`;
AAPCS64: `ws` in `x0`, the offsets `o`, `a` and `b` in `w1`–`w3`) for a
modulus `m` of `n` 64-bit words, by the multiplication of
`Impl/Mont/AArch64.lean` through pointers (`mulR`):

1. the offsets are zero-extended (their upper halves are unspecified), the
   callee-saved registers the function writes are saved in lanes of
   `v16`–`v19` (`saveCode`), the pointers `ra = ws + a`, `rb = ws + b` and
   `ro = ws + o` computed, and the modulus stored at `ws + 4096 - 16 n`
   (`moAt`), in the function's own working space, where `ldr` reaches it
   from `x0`;
2. the product (`mulR`) reads `[a]` and `[b]` through `ra` and `rb` and
   writes `[o]` through `ro`;
3. the registers are restored from the vector lanes.

The pointers are `x14`, `x15` and `x26` for four words, whose accumulator
leaves `x14` and `x15` free, and `x26`–`x28` otherwise. The function writes
neither `x19` nor `x20`, which callers keep public across a call (loop
counters and pointers), and leaves `x0 = ws`; of `ws`, it writes only `[o]`
and the `8 n` bytes of the modulus. Every address is `ws` plus a constant or
one of the offsets (plus a constant), so only the pointer and the offsets
may affect timing.
-/

namespace VG.Impl.Weierstrass.AArch64.Mont

open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64

/-- `-m⁻¹ mod 2⁶⁴`, for odd `m`, by Newton's iteration. -/
def minv (m : Nat) : Nat :=
  let inv := (List.range 6).foldl (fun x _ => x * ((2 + 2 ^ 64 - m * x % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) 1
  (2 ^ 64 - inv) % 2 ^ 64

/-- Where the function stores the modulus: `8 n` bytes of its own working
space (`4096 - 64 n` to `4096`), below the last `8 n`. -/
def moAt (n : Nat) : Nat := 4096 - 16 * n

/-- The modulus `m` of `n` words, as the multiplication takes it. -/
def mod (n m : Nat) : Mod where
  n := n
  mo := moAt n
  tmp := moAt n - 8 * n
  minv := BitVec.ofNat 64 (minv m)
  red := Red.ofModulus n m
  tight := tightOk n m

/-- The pointers to `[a]`, `[b]` and `[o]`. -/
def ptrs (n : Nat) : Reg × Reg × Reg := if n ≤ 4 then (.x14, .x15, .x26) else (.x26, .x27, .x28)

/-- The callee-saved registers the function writes: the pointers' and, for
more than six words, those of the accumulator (`acc`) and of the
conditional subtraction (`dRegs`). -/
def saved (n : Nat) : List Reg :=
  ((acc n ++ dRegs n).filter fun r => r ∈ preserved) ++
    [(ptrs n).1, (ptrs n).2.1, (ptrs n).2.2].filter fun r => r ∈ preserved

/-- The vector register and lane that saves the `i`-th of them. -/
def slot (i : Nat) : VReg × Nat :=
  ([VReg.v16, .v17, .v18, .v19].getD (i / 2) .v16, i % 2)

/-- The registers saved in their lanes. -/
def saveCode (n : Nat) : List Instr :=
  (saved n).zipIdx.map fun (r, i) => .vop (.ins .d2 (slot i).1 (slot i).2 r)

/-- The registers restored from their lanes. -/
def restoreCode (n : Nat) : List Instr :=
  (saved n).zipIdx.map fun (r, i) => .umov .x r (slot i).1 (slot i).2

/-- Word `j` of `x`. -/
abbrev wordOf (x j : Nat) : BitVec 64 := BitVec.ofNat 64 (x >>> (64 * j))

/-- `[x0 + o + 8 j] =` word `j` of `x`, through `x1`, which already holds it
if it equals word `j - 1` (most of P-521's are all ones). -/
def constStep (o x j : Nat) : List Instr :=
  (if 0 < j ∧ wordOf x j = wordOf x (j - 1) then [] else const64 .x1 (wordOf x j)) ++
    [st .x1 (o + 8 * j)]

/-- `[x0 + o] = x`, `n` words, through `x1`. -/
def setConst (n : Nat) (o x : Nat) : List Instr := (List.range n).flatMap (constStep o x)

/-- The offsets zero-extended (as 32-bit additions of zero). -/
def zextCode : List Instr := [.addImm .w .x1 .x1 0, .addImm .w .x2 .x2 0, .addImm .w .x3 .x3 0]

/-- After the offsets are zero-extended: the registers saved, the pointers
`ro = ws + o`, `ra = ws + a`, `rb = ws + b`, and the modulus stored. -/
def entryRest (n m : Nat) : List Instr :=
  saveCode n ++
    [.add .x (ptrs n).2.2 .x0 .x1, .add .x (ptrs n).1 .x0 .x2, .add .x (ptrs n).2.1 .x0 .x3] ++
    setConst n (moAt n) m

/-- The entry. -/
def entry (n m : Nat) : List Instr := zextCode ++ entryRest n m

/-- `vg_<curve>_mul_mod_<p|n>`: the entry, the product, the registers
restored. -/
def mulFn (n m : Nat) : Prog isa :=
  .seq (.block zextCode)
    (.block (entryRest n m ++ mulR (mod n m) (ptrs n).1 (ptrs n).2.1 (ptrs n).2.2 0 0 0 ++ restoreCode n))

open Spec.Weierstrass.Mont in
/-- The moduli whose products are functions on AArch64: P-384's and P-521's
`p`. A product of four words is short enough inline that calls do not pay,
and the products modulo `n` are few. -/
def fns : List Modulus := [p384p, p521p]

/-- The function computing the products of the modulus `M` (its name and its
modulus), if any: one of `fns` of `M.n` words and `M.minv`, if `M`'s
temporary area is where the function stores its modulus (`moAt`), which a
call may then change. -/
def callOf (M : Mod) : Option (String × Nat) :=
  if M.tmp = moAt M.n then
    (fns.find? fun S => S.k == M.n && BitVec.ofNat 64 (minv S.m) == M.minv).map fun S => (S.fn "mul", S.m)
  else none

end VG.Impl.Weierstrass.AArch64.Mont
