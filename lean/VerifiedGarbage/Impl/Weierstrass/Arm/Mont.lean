module

public import VerifiedGarbage.Impl.Mont.Arm
public import VerifiedGarbage.Impl.Mont.ArmPacked
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-!
# Montgomery arithmetic modulo a curve's `p` or `n`, as functions, on 32-bit ARM

`vg_<curve>_{mul,add,sub}_mod_<p|n>(ws, o, a, b)` (`Proof/Weierstrass/MontContract.lean`;
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

`vg_<curve>_{add,sub}_mod_<p|n>_umaal` (`addFnU`, `subFnU`; the CPU feature
`umaal`) add and subtract 32-bit words, a `umaal` each, whose high word is
the carry: with a register that holds 1, `umaal lo, c, x, one` leaves
`lo + x + c` in `c:lo`. They store no modulus (its words are immediates,
loaded only where a word differs from the one before), save only the
registers they change beyond `r0`–`r3`, and never write `r9`–`r11` or `lr`:

* the sum: the words of `[a] + [b]` go to the temporary area, and a second
  carry, of their sum with `2^(64 n) - m`, says whether `[a] + [b] ≥ m`; then
  `[o]` is the temporary area plus `2^(64 n) - m` times that bit
  (`umaal lo, c, x, bit`);
* the difference: the words of `[a] + (2^(64 n) - 1 - [b]) + 1` go to the
  temporary area, whose carry out says whether `[a] ≥ [b]`; then `[o]` is the
  temporary area plus `m` times that carry's negation.

`[o]` is written only after `[a]` and `[b]` are read, so the result may
overlap either operand.

The own working space is the `64 n` bytes from `own n = 4096 - 64 n`: the
accumulator (`32 n + 8` bytes), the temporary area and the modulus (`8 n`
each), and the saved registers (28 bytes), which fit for `n ≥ 3`. Every
address is `ws` plus a constant or one of `o`, `a` and `b` (plus a constant,
or a counter), so only the pointer and the offsets may affect timing.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Arm.Mont

open VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm

/-- `-m⁻¹ mod 2⁶⁴`, for odd `m`, by Newton's iteration. -/
def minv (m : Nat) : Nat :=
  let inv := (List.range 6).foldl (fun x _ => x * ((2 + 2 ^ 64 - m * x % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) 1
  (2 ^ 64 - inv) % 2 ^ 64

/-- The start of the own working space: the accumulator. -/
def own (n : Nat) : Nat := Impl.Weierstrass.Mont.ownAt n

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
def mulFn16 (n m : Nat) : Prog isa := fn n m .r4 (mulR (mod n m) (own n) 0 0 0 .r1 .r4 .lr)

/-- Larger curves scan packed 32-bit words, preserving the curve calling convention. -/
def mulFn (n m : Nat) : Prog isa :=
  if n = 6 ∨ n = 8 ∨ n = 9 then fn n m .r4 (Packed.mulR (mod n m) (own n)) else mulFn16 n m

/-- `vg_<curve>_mul_mod_<p|n>_umaal`: the packed words' rows with one `umaal`
a word (`Packed.rowU`; the CPU feature `umaal`). -/
def mulFnU (n m : Nat) : Prog isa := fn n m .r4 (Packed.mulR (mod n m) (own n) true)

/-- `mulFn`, or with `u` `mulFnU`. -/
def mulFnWith (u : Bool) (n m : Nat) : Prog isa := if u then mulFnU n m else mulFn n m

/-- `vg_<curve>_add_mod_<p|n>`. -/
def addFn (n m : Nat) : Prog isa := fn n m .r2 (.block (addR (mod n m) (own n) 0 0 0 .r1 .r2 .lr))

/-- `vg_<curve>_sub_mod_<p|n>`. -/
def subFn (n m : Nat) : Prog isa := fn n m .r2 (.block (subR (mod n m) (own n) 0 0 0 .r1 .r2 .lr))

/-! ## The sum and the difference with `umaal` -/

/-- Word `i` of `x`. -/
def wordAt (x i : Nat) : Nat := x / 2 ^ (32 * i) % 2 ^ 32

/-- `r = x mod 2³²`, in one instruction where one does. -/
def loadImm (r : Reg) (x : Nat) : List Instr :=
  if x % 2 ^ 32 < 2 ^ 16 then [.movw r (BitVec.ofNat 16 x)]
  else if encodable (~~~BitVec.ofNat 32 x) then [.mvn r (.imm (~~~BitVec.ofNat 32 x))]
  else [.movw r (BitVec.ofNat 16 x), .movt r (BitVec.ofNat 16 (x >>> 16))]

/-- `r = ` word `i` of `x`, which `r` holds already if word `i - 1` is the same. -/
def loadWord (r : Reg) (x i : Nat) : List Instr :=
  if 0 < i ∧ wordAt x (i - 1) = wordAt x i then [] else loadImm r (wordAt x i)

/-- Word `i` of `[r2] + [r3]` to `[t]` (its carry in `r5`), and of that sum
plus `x` (its carry in `r6`); `r8 = 1`. -/
def addStepU (t x i : Nat) : List Instr :=
  ([.ldr .r0 .r2 (4 * i), .ldr .r4 .r3 (4 * i), .umaal .r4 .r5 .r0 .r8, .str .r4 wb (t + 4 * i)] : List Instr) ++
    loadWord .r7 x i ++ ([.umaal .r4 .r6 .r7 .r8] : List Instr)

/-- Word `i` of `[r2] + (2^(32 w) - 1 - [r3])` to `[t]` (its carry in `r5`); `r6 = 1`. -/
def subStepU (t i : Nat) : List Instr :=
  [.ldr .r0 .r2 (4 * i), .ldr .r4 .r3 (4 * i), .mvn .r4 (.reg .r4), .umaal .r4 .r5 .r0 .r6,
    .str .r4 wb (t + 4 * i)]

/-- Word `i` of `[t] + r6 · x` to `[r1]` (its carry in `r5`). -/
def mulAddStepU (t x i : Nat) : List Instr :=
  ([.ldr .r4 wb (t + 4 * i)] : List Instr) ++ loadWord .r0 x i ++
    ([.umaal .r4 .r5 .r0 .r6, .str .r4 .r1 (4 * i)] : List Instr)

/-- `[r1] = [t] + r6 · x`, `w` words, with `r1` first made a pointer. -/
def mulAddU (t x w : Nat) : List Instr :=
  ([.mov .r5 (.imm 0), .dp .add .r1 wb (.reg .r1)] : List Instr) ++ (List.range w).flatMap (mulAddStepU t x)

/-- `[r1] = [r2] + [r3] mod m`, numbers of `w` words below `m` (`r1` an
offset), through `[t]`, for `x = 2^(32 w) - m`. -/
def addU (t x w : Nat) : List Instr :=
  ([.mov .r8 (.imm 1), .mov .r5 (.imm 0), .mov .r6 (.imm 0)] : List Instr) ++
    (List.range w).flatMap (addStepU t x) ++ ([.dp .add .r6 .r5 (.reg .r6)] : List Instr) ++ mulAddU t x w

/-- `[r1] = [r2] - [r3] mod m`, numbers of `w` words below `m` (`r1` an
offset), through `[t]`. -/
def subU (t m w : Nat) : List Instr :=
  ([.mov .r6 (.imm 1), .mov .r5 (.imm 1)] : List Instr) ++ (List.range w).flatMap (subStepU t) ++
    ([.dp .eor .r6 .r5 (.imm 1)] : List Instr) ++ mulAddU t m w

/-- The first `k` of the registers `saves` has: `r4` to `r(3 + k)`. -/
def savesU (n k : Nat) : List (Reg × Nat) := (saves n).take k

/-- The function of the operation `op`, which changes the first `k` saved
registers: `r12 = ws`, they are saved, `r2 = ws + a` and `r3 = ws + b`
(`r1 = o`); `op`; they are restored. -/
def fnU (n k : Nat) (op : List Instr) : Prog isa :=
  .block (.mov wb (.reg .r0) :: (savesU n k).map (fun p => .str p.1 wb p.2) ++
    ([.dp .add .r2 wb (.reg .r2), .dp .add .r3 wb (.reg .r3)] : List Instr) ++ op ++
    (savesU n k).map fun p => .ldr p.1 wb p.2)

/-- `vg_<curve>_add_mod_<p|n>_umaal`. -/
def addFnU (n m : Nat) : Prog isa := fnU n 5 (addU (tmpAt n) (2 ^ (64 * n) - m) (2 * n))

/-- `vg_<curve>_sub_mod_<p|n>_umaal`. -/
def subFnU (n m : Nat) : Prog isa := fnU n 3 (subU (tmpAt n) m (2 * n))

/-- `addFn`, or with `u` `addFnU`. -/
def addFnWith (u : Bool) (n m : Nat) : Prog isa := if u then addFnU n m else addFn n m

/-- `subFn`, or with `u` `subFnU`. -/
def subFnWith (u : Bool) (n m : Nat) : Prog isa := if u then subFnU n m else subFn n m

/-! ## Calls of the functions -/

/-- `[o] = f([a], [b])` by a call of the function `f`, whose code is `body`,
on the working space at `r12`: `lr`, which the call changes, is kept in
`r10`, which the functions do not write (nor `r11`, and they leave `r12`),
and the arguments are `ws = r12` and the offsets (below `2¹⁶`). -/
def callOp (f : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .r10 (.reg .lr), .mov .r0 (.reg wb), .movw .r1 (BitVec.ofNat 16 o),
      .movw .r2 (BitVec.ofNat 16 a), .movw .r3 (BitVec.ofNat 16 b)]) <|
    .seq (.call f body) (.block [.mov .lr (.reg .r10)])

/-- The name of `vg_<curve>_mul_mod_<p|n>`, or with `u` of its `_umaal` variant. -/
def mulName (u : Bool) (S : Impl.Weierstrass.Mont.Modulus) : String :=
  if u then S.fn "mul" ++ "_umaal" else S.fn "mul"

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`, or with
`u` of `vg_<curve>_mul_mod_<p|n>_umaal`. -/
def mulCall (S : Impl.Weierstrass.Mont.Modulus) (o a b : Nat) (u : Bool := false) : Prog isa :=
  callOp (mulName u S) (mulFnWith u S.k S.m) o a b

/-- The name of `vg_<curve>_add_mod_<p|n>`, or with `u` of its `_umaal` variant. -/
def addName (u : Bool) (S : Impl.Weierstrass.Mont.Modulus) : String :=
  if u then S.fn "add" ++ "_umaal" else S.fn "add"

/-- The name of `vg_<curve>_sub_mod_<p|n>`, or with `u` of its `_umaal` variant. -/
def subName (u : Bool) (S : Impl.Weierstrass.Mont.Modulus) : String :=
  if u then S.fn "sub" ++ "_umaal" else S.fn "sub"

/-- `[o] = [a] + [b] mod m` by a call of `vg_<curve>_add_mod_<p|n>`, or with
`u` of `vg_<curve>_add_mod_<p|n>_umaal`. -/
def addCall (S : Impl.Weierstrass.Mont.Modulus) (o a b : Nat) (u : Bool := false) : Prog isa :=
  callOp (addName u S) (addFnWith u S.k S.m) o a b

/-- `[o] = [a] - [b] mod m` by a call of `vg_<curve>_sub_mod_<p|n>`, or with
`u` of `vg_<curve>_sub_mod_<p|n>_umaal`. -/
def subCall (S : Impl.Weierstrass.Mont.Modulus) (o a b : Nat) (u : Bool := false) : Prog isa :=
  callOp (subName u S) (subFnWith u S.k S.m) o a b

end VG.Impl.Weierstrass.Arm.Mont
