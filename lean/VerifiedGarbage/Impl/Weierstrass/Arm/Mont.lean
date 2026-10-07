import VerifiedGarbage.Impl.Mont.Arm
import VerifiedGarbage.Spec.Weierstrass.Mont

/-!
# Montgomery arithmetic modulo a curve's `p` or `n`, as functions, on 32-bit ARM

`vg_<curve>_{mul,add,sub}_mod_<p|n>(ws, o, a, b)` (`Spec/Weierstrass/Mont.lean`;
AAPCS: `ws`, `o`, `a` and `b` in `r0`–`r3`) for a modulus `m` of `n` 64-bit
words, with the operations of `Impl/Mont/Arm.lean` on the working space `ws`:

1. `r12` takes `ws`, the callee-saved registers `r4`–`r9` and `lr` are saved
   in the function's own working space, and the modulus is stored there
   (`setConst`), whose accumulator, temporary area and modulus are all below
   byte 4096, so that `ldr` and `str` reach them from `r12`;
2. `lr`, `r1` and a register `rb` point to `[o]`, `[a]` and `[b]` (`r4` for
   the product, whose rows leave it alone, `r2` for the sum and the
   difference);
3. the operation (`mulR`, `addR` or `subR`) reads `[a]` and `[b]` and writes
   `[o]` through the pointers;
4. the registers are restored, and the function returns.

The functions never write `r10` or `r11`, so that a caller can keep values
there that a constant-time analysis of its code knows to be public across a
call (`callOp`: the caller keeps `lr` in `r10`, and its loops count in
`r11`), and leave `r12 = ws`.

The own working space is the `64 n` bytes from `own n = 4096 - 64 n`: the
accumulator (`32 n + 8` bytes), the temporary area and the modulus (`8 n`
each), and the saved registers (28 bytes), which fit for `n ≥ 3`. Every
address is `ws` plus a constant or one of `o`, `a` and `b` (plus a constant,
or a counter), so only the pointer and the offsets may affect timing.
-/

namespace VG.Impl.Weierstrass.Arm.Mont

open VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm

/-- `-m⁻¹ mod 2⁶⁴`, for odd `m`, by Newton's iteration. -/
def minv (m : Nat) : Nat :=
  let inv := (List.range 6).foldl (fun x _ => x * ((2 + 2 ^ 64 - m * x % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) 1
  (2 ^ 64 - inv) % 2 ^ 64

/-- The start of the own working space: the accumulator. -/
def own (n : Nat) : Nat := Spec.Weierstrass.Mont.ownAt n

/-- The temporary area. -/
def tmpAt (n : Nat) : Nat := own n + (32 * n + 8)

/-- The modulus. -/
def moAt (n : Nat) : Nat := tmpAt n + 8 * n

/-- The saved registers. -/
def saveAt (n : Nat) : Nat := moAt n + 8 * n

/-- The modulus `m` of `n` words, as the operations have it. -/
def mod (n m : Nat) : Mod := { n := n, mo := moAt n, tmp := tmpAt n, minv := BitVec.ofNat 64 (minv m) }

/-- The registers the operations change that the function must restore (the
callee-saved `r4`–`r9`, and `lr`, which points to `[o]`), and their offsets
in the area that saves them. -/
def savedRegs : List (Reg × Nat) :=
  [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20), (.lr, 24)]

/-- Where they are saved. -/
def saves (n : Nat) : List (Reg × Nat) := savedRegs.map fun p => (p.1, saveAt n + p.2)

/-- Saves them, through `r12`. -/
def saveCode (n : Nat) : List Instr := (saves n).map fun p => .str p.1 wb p.2

/-- Restores them, through `r12`. -/
def restoreCode (n : Nat) : List Instr := (saves n).map fun p => .ldr p.1 wb p.2

/-- `r12 = ws`; the registers saved; the modulus stored (through `r4`); the
pointers `lr = ws + o`, `r1 = ws + a` and `rb = ws + b`. -/
def entry (n m : Nat) (rb : Reg) : List Instr :=
  .mov wb (.reg .r0) :: saveCode n ++ setConst n (moAt n) m ++
    [.dp .add .lr wb (.reg .r1), .dp .add .r1 wb (.reg .r2), .dp .add rb wb (.reg .r3)]

/-- The function of the operation `op`, with `[b]` at `rb`: the entry, `op`,
the registers restored. -/
def fn (n m : Nat) (rb : Reg) (op : Prog isa) : Prog isa :=
  .seq (.block (entry n m rb)) <| .seq op <| .block (restoreCode n)

/-- `vg_<curve>_mul_mod_<p|n>`. -/
def mulFn (n m : Nat) : Prog isa := fn n m .r4 (mulR (mod n m) (own n) 0 0 0 .r1 .r4 .lr)

/-- `vg_<curve>_add_mod_<p|n>`. -/
def addFn (n m : Nat) : Prog isa := fn n m .r2 (.block (addR (mod n m) (own n) 0 0 0 .r1 .r2 .lr))

/-- `vg_<curve>_sub_mod_<p|n>`. -/
def subFn (n m : Nat) : Prog isa := fn n m .r2 (.block (subR (mod n m) (own n) 0 0 0 .r1 .r2 .lr))

/-! ## Calls of the functions -/

/-- `[o] = f([a], [b])` by a call of the function `f`, whose code is `body`,
on the working space at `r12`: `lr`, which the call changes, is kept in
`r10`, which the functions do not write (nor `r11`, and they leave `r12`),
and the arguments are `ws = r12` and the offsets (below `2¹⁶`). -/
def callOp (f : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .r10 (.reg .lr), .mov .r0 (.reg wb), .movw .r1 (BitVec.ofNat 16 o),
      .movw .r2 (BitVec.ofNat 16 a), .movw .r3 (BitVec.ofNat 16 b)]) <|
    .seq (.call f body) (.block [.mov .lr (.reg .r10)])

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`. -/
def mulCall (S : Spec.Weierstrass.Mont.Modulus) (o a b : Nat) : Prog isa :=
  callOp (S.fn "mul") (mulFn S.k S.m) o a b

/-- `[o] = [a] + [b] mod m` by a call of `vg_<curve>_add_mod_<p|n>`. -/
def addCall (S : Spec.Weierstrass.Mont.Modulus) (o a b : Nat) : Prog isa :=
  callOp (S.fn "add") (addFn S.k S.m) o a b

/-- `[o] = [a] - [b] mod m` by a call of `vg_<curve>_sub_mod_<p|n>`. -/
def subCall (S : Spec.Weierstrass.Mont.Modulus) (o a b : Nat) : Prog isa :=
  callOp (S.fn "sub") (subFn S.k S.m) o a b

end VG.Impl.Weierstrass.Arm.Mont
