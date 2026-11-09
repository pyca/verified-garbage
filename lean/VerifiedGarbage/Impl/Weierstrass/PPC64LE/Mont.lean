module

public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-!
# Montgomery arithmetic modulo a curve's `p` or `n`, as functions, on PPC64LE

`vg_<curve>_{mul,add,sub}_mod_<p|n>(ws, o, a, b)` (`Proof/Weierstrass/MontContract.lean`;
ELFv2: `ws`, `o`, `a` and `b` in `r3`–`r6`) for a modulus `m` of `n` 64-bit
words, with the operations of `Impl/Mont/PPC64LE.lean` on the working space
`ws`:

1. the offsets are zero-extended from their low 32 bits (the ABI leaves the
   high half of a 32-bit argument unspecified), and `r4`, `r5` and `r6`
   point to `[o]`, `[a]` and `[b]`; for more than four words, the modulus
   is stored in the function's own working space (`setConst`);
2. the operation reads `[a]` and `[b]` and writes `[o]` through the
   pointers, and the function returns. For at most four words it is
   `rmul4`, `add4` or `sub4`, which take the modulus's words as immediates;
   for more, `rmul`, `add` or `sub`, which read it from memory. Each
   choice is inside the operation's blocks (`rmulSel`), so the code's shape
   does not depend on it.

The functions write only the volatile registers `r0` and `r4`–`r12` (and
neither the stack nor `LR`), so they need no frame; `r3` keeps `ws`. The
multiplication keeps its accumulator in `r15`–`r(15 + n)` (and, for at most
four words, `[b]` in the next `n`), which it saves in its own working space
first and restores last.

The own working space is the `64 n` bytes from `own n = 4096 - 64 n`: the
accumulator of `add` and `sub`, or the saved registers and `m'` of `rmul`
(`16 n + 8` bytes), the temporary area and the modulus (`8 n` each; the
modulus's is unused for at most four words). Every address is `ws` plus a constant or one of `o`, `a` and `b`
(plus a constant, or a counter), so only the pointer and the offsets may
affect timing.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.PPC64LE.Mont

open VG.PPC64LE VG.Impl.Mont VG.Impl.Mont.PPC64LE

/-- `-m⁻¹ mod 2⁶⁴`, for odd `m`, by Newton's iteration. -/
def minv (m : Nat) : Nat :=
  let inv := (List.range 6).foldl (fun x _ => x * ((2 + 2 ^ 64 - m * x % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) 1
  (2 ^ 64 - inv) % 2 ^ 64

/-- The start of the own working space: the accumulator. -/
def own (n : Nat) : Nat := Impl.Weierstrass.Mont.ownAt n

/-- The temporary area. -/
def tmpAt (n : Nat) : Nat := own n + (16 * n + 8)

/-- The modulus. -/
def moAt (n : Nat) : Nat := tmpAt n + 8 * n

/-- The modulus `m` of `n` words, as the operations have it. -/
def mod (n m : Nat) : Mod := { n := n, mo := moAt n, tmp := tmpAt n, minv := BitVec.ofNat 64 (minv m) }

/-- The offsets zero-extended from their low 32 bits. -/
def zext : List Instr := [.rotr .w .r4 .r4 0, .rotr .w .r5 .r5 0, .rotr .w .r6 .r6 0]

/-- The pointers `r4 = ws + o`, `r5 = ws + a`, `r6 = ws + b`, and, for
more than four words, the modulus stored (through `r11`). -/
def entry (n m : Nat) : List Instr :=
  [.add .r4 wb .r4, .add .r5 wb .r5, .add .r6 wb .r6] ++ if n ≤ 4 then [] else setConst n (moAt n) m

/-- The function of the operation `op`: the offsets zero-extended, the
entry, then `op`. -/
def fn (n m : Nat) (op : Prog isa) : Prog isa := .seq (.block zext) (.seq (.block (entry n m)) op)

/-- `vg_<curve>_mul_mod_<p|n>`. -/
def mulFn (n m : Nat) : Prog isa := fn n m (rmulSel (mod n m) m (own n))

/-- `vg_<curve>_add_mod_<p|n>`. -/
def addFn (n m : Nat) : Prog isa := fn n m (.block (if n ≤ 4 then add4 n m else add (mod n m) (own n)))

/-- `vg_<curve>_sub_mod_<p|n>`. -/
def subFn (n m : Nat) : Prog isa := fn n m (.block (if n ≤ 4 then sub4 n m else sub (mod n m) (own n)))

end VG.Impl.Weierstrass.PPC64LE.Mont
