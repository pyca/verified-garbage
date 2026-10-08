import VerifiedGarbage.Impl.Mont.X86
import VerifiedGarbage.Spec.Weierstrass.Mont

/-!
# Montgomery arithmetic modulo a curve's `p` or `n`, as functions, on x86 (32-bit)

`vg_<curve>_{mul,add,sub}_mod_<p|n>(ws, o, a, b)` (`Spec/Weierstrass/Mont.lean`;
cdecl: the arguments at `[esp + 4]` to `[esp + 16]`) for a modulus `m` of `k`
64-bit words (`N = 2k` 32-bit words), on the working space `ws`. The
functions use the `64 k` bytes below byte 4096 of `ws` for themselves
(`own k`): the accumulator (`2N + 1` words), the temporary area (`N` words,
`tmpAt`) and the saved registers (`saveAt`). The
modulus is in the code (immediates), so it is not stored.

* `mulFn`: Montgomery's product by coarsely integrated operand scanning, as
  `Impl/Mont/X86.lean`'s `mul`, but with its rows unrolled: `ebx`, `esi`,
  `edi` and `ebp` are saved in the own working space, `ebp` holds `ws`,
  `esi` points to `[b]` and `edi` to `[a]`; row `i` adds `a_i [b]`
  (`mulRowB`) and `q m` (`redRowI`: P-256's
  sparse reduction for its `p`, else a row of the modulus's words as
  immediates) to the accumulator's words from `i`, whose low word becomes
  zero. The accumulator's words from `N` are then below `2m`, reduced by a
  conditional subtraction (`diffsI`, `maskTop`, `selectsP`) into `[o]`,
  through `ecx`. `esi` and `edi` are restored before the result is stored,
  `ebx` and `ebp` after.
* `addFn`, `subFn`: `[a] ± [b]` into the accumulator through pointers in
  `ecx` and `edx` (`chainP`), then a conditional subtraction (the sum) or
  addition of `m` under the mask of the borrow (the difference) into
  `[o]`. Only `eax`, `ecx`, `edx` and `ebp` are written; `ebp` is saved in
  the own working space.

The functions never write `esi` or `edi` but to restore them before any
store at an address that depends on an offset (`o`): every other store is at
`ws` plus a constant. So a constant-time analysis of a caller, which analyses
the callee's code at each call, still knows the caller's `esi` and `edi`
(its loop counter and its working space) to be public after a call (the
callee's stores at computed addresses make it forget what it knew of memory).

Every address is `ws`, `ws` plus an offset or `esp`, plus a constant: only the
pointer and the offsets may affect timing.

`callOp` is a call of such a function from code whose working space is at
`edi`, with constant offsets: the arguments pushed (in a frame that `pop eax`
releases), last to first.
-/

namespace VG.Impl.Weierstrass.X86.Mont

open VG.X86 VG.Impl.Mont VG.Impl.Mont.X86

/-- `-m⁻¹ mod 2⁶⁴`, for odd `m`, by Newton's iteration. -/
def minv (m : Nat) : Nat :=
  let inv := (List.range 6).foldl (fun x _ => x * ((2 + 2 ^ 64 - m * x % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) 1
  (2 ^ 64 - inv) % 2 ^ 64

/-- The start of the own working space: the accumulator, `2N + 1` words. -/
def own (k : Nat) : Nat := Spec.Weierstrass.Mont.ownAt k

/-- The temporary area, `N` words. -/
def tmpAt (k : Nat) : Nat := own k + (16 * k + 4)

/-- The saved `ebx`, `esi`, `edi` and `ebp`. -/
def saveAt (k : Nat) : Nat := tmpAt k + 8 * k

/-- The modulus `m` of `k` words, as `Impl/Mont/X86.lean`'s operations have
it (its words are not in memory: `mo` is unused). -/
def mod (k m : Nat) : Mod :=
  { n := k, mo := 0, tmp := tmpAt k, minv := BitVec.ofNat 64 (minv m), red := p256RedChoice k m }

/-- 32-bit word `j` of `m`. -/
def mw (m j : Nat) : BitVec 32 := BitVec.ofNat 32 (m >>> (32 * j))

/-- `[ebp + d]`. -/
def bp (d : Nat) : MemOp := at_ .ebp d

/-! ## The product -/

/-- A step of a row: `[ebp + acc + 4j] += ecx · y + ebx` for the word `y` at
`ys`, its carry word to `ebx` (it never overflows). -/
def stepG (ys : Src) (acc j : Nat) : List Instr :=
  [.mov .eax ys, .mul .ecx, .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
    .alu .add .eax (.mem (bp (acc + 4 * j))), .alu .adc .edx (.imm 0),
    .store (bp (acc + 4 * j)) .eax, .mov .ebx (.reg .edx)]

/-- The first step of a row, with no carry in. -/
def step0G (ys : Src) (acc : Nat) : List Instr :=
  [.mov .eax ys, .mul .ecx, .alu .add .eax (.mem (bp acc)), .alu .adc .edx (.imm 0),
    .store (bp acc) .eax, .mov .ebx (.reg .edx)]

/-- Steps `1 … r` of a row whose words `y_j` are at `ys j`. -/
def stepsG (ys : Nat → Src) (acc : Nat) : Nat → List Instr
  | 0 => []
  | r + 1 => stepsG ys acc r ++ stepG (ys (r + 1)) acc (r + 1)

/-- The carry word `ebx` added to word `N` of the window, whose word `N + 1`
becomes the carry out (its old value unread). -/
def carryUp1 (acc N : Nat) : List Instr :=
  [.mov .eax (.mem (bp (acc + 4 * N))), .alu .add .eax (.reg .ebx), .store (bp (acc + 4 * N)) .eax,
    .mov .eax (.imm 0), .alu .adc .eax (.imm 0), .store (bp (acc + 4 * N + 4)) .eax]

/-- The window at `[ebp + acc]` `+= ecx · Y`, `N` words of `Y` at `ys`, with
its carry into words `N` and `N + 1` (`carry`: `carryUp`, or `carryUp1` if
word `N + 1` is not yet written). -/
def rowG (ys : Nat → Src) (acc N : Nat) (carry : List Instr) : List Instr :=
  step0G (ys 0) acc ++ stepsG ys acc (N - 1) ++ carry

/-- Row 0's steps: `[ebp + acc + 4j] = ecx · [esi + 4j] + ebx` (the window
not yet written), its carry word to `ebx`. -/
def stepZ (acc j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi (4 * j))), .mul .ecx, .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
    .store (bp (acc + 4 * j)) .eax, .mov .ebx (.reg .edx)]

/-- Steps `1 … r` of row 0. -/
def stepsZ (acc : Nat) : Nat → List Instr
  | 0 => []
  | r + 1 => stepsZ acc r ++ stepZ acc (r + 1)

/-- Row 0's product: the window at `[ebp + acc]` `= ecx · [esi]`, `N + 2`
words (the top one zero). -/
def rowZ (acc N : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .mul .ecx, .store (bp acc) .eax, .mov .ebx (.reg .edx)] ++
    stepsZ acc (N - 1) ++
    [.store (bp (acc + 4 * N)) .ebx, .mov .eax (.imm 0), .store (bp (acc + 4 * N + 4)) .eax]

/-- `[esi + 4j]`. -/
def bWord (j : Nat) : Src := .mem (at_ .esi (4 * j))

/-- `m_j`. -/
def mWord (m j : Nat) : Src := .imm (mw m j)

/-- The window `+= q m`, `q` in `ecx`: P-256's sparse identity when certified,
else a row of the modulus's words. -/
def redRowI (M : Mod) (m acc : Nat) : List Instr :=
  if p256RedEnabled M then p256Red acc else rowG (mWord m) acc (words M) (carryUp acc (words M))

/-- Row `i`: `ecx = a_i` (through `edi`), the window at `own + 4i`
`+= a_i [b]` (row 0 writes it), then `+= q m` for `q = t₀ m' mod 2³²`. -/
def rowF (k m i : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ .edi (4 * i)))] ++
    (if i = 0 then rowZ (own k) (2 * k)
      else rowG bWord (own k + 4 * i) (2 * k) (carryUp1 (own k + 4 * i) (2 * k))) ++
    redDigit (mod k m) (own k + 4 * i) ++ redRowI (mod k m) m (own k + 4 * i)

/-- The rows `0 … r - 1`. -/
def rowsF (k m : Nat) : Nat → List Instr
  | 0 => []
  | r + 1 => rowsF k m r ++ rowF k m r

/-! ## The conditional subtraction, and the result -/

/-- `[ebp + tmp] = [ebp + src] - m`, `N` words, with its borrow, through `eax`. -/
def diffsI (m src tmp N : Nat) : List Instr :=
  (List.range N).flatMap fun j =>
    [.mov .eax (.mem (bp (src + 4 * j))), .alu (if j = 0 then .sub else .sbb) .eax (.imm (mw m j)),
      .store (bp (tmp + 4 * j)) .eax]

/-- The mask `eax`: all ones if the number at `[ebp + src]` (`N` words and the
top word) is at least `m` (the top word does not borrow). -/
def maskTop (src N : Nat) : List Instr :=
  [.mov .eax (.mem (bp (src + 4 * N))), .alu .sbb .eax (.imm 0), .alu .sbb .eax (.reg .eax),
    .alu .xor .eax (.imm (-1))]

/-- `ecx = ws + o`. -/
def outPtr : List Instr := [.mov .ecx (.mem (at_ .esp 8)), .alu .add .ecx (.reg .ebp)]

/-- `[ecx] = [ebp + tmp]` where the mask `eax` is all ones, else `[ebp + src]`,
`N` words, through `edx`. -/
def selectsP (src tmp N : Nat) : List Instr :=
  (List.range N).flatMap fun j =>
    [.mov .edx (.mem (bp (src + 4 * j))), .alu .xor .edx (.mem (bp (tmp + 4 * j))), .alu .and .edx (.reg .eax),
      .alu .xor .edx (.mem (bp (src + 4 * j))), .store (at_ .ecx (4 * j)) .edx]

/-- The number below `2m` at `[ebp + src]` reduced modulo `m` into `[ecx]`
(`ecx = ws + o`, formed after the mask), with `rest` (restoring registers
that the stores through `ecx` must not lose) before the stores. -/
def csubOut (k m src : Nat) (rest : List Instr) : List Instr :=
  diffsI m src (tmpAt k) (2 * k) ++ maskTop src (2 * k) ++ outPtr ++ rest ++ selectsP src (tmpAt k) (2 * k)

/-! ## The functions -/

/-- `vg_<curve>_mul_mod_<p|n>`'s entry: `ebx`, `esi`, `edi` and `ebp` saved,
`ebp = ws`, `esi = ws + b`, `edi = ws + a`. -/
def mulEntry (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esp 4)), .store (at_ .eax (saveAt k)) .ebx, .store (at_ .eax (saveAt k + 4)) .esi,
    .store (at_ .eax (saveAt k + 8)) .edi, .store (at_ .eax (saveAt k + 12)) .ebp,
    .mov .ebp (.reg .eax),
    .mov .esi (.mem (at_ .esp 16)), .alu .add .esi (.reg .ebp),
    .mov .edi (.mem (at_ .esp 12)), .alu .add .edi (.reg .ebp)]

/-- `esi` and `edi` restored. -/
def mulRestoreSI (k : Nat) : List Instr :=
  [.mov .esi (.mem (bp (saveAt k + 4))), .mov .edi (.mem (bp (saveAt k + 8)))]

/-- `ebx` and `ebp` restored (`ebp` last). -/
def restoreBP (k : Nat) : List Instr :=
  [.mov .ebx (.mem (bp (saveAt k))), .mov .ebp (.mem (bp (saveAt k + 12)))]

/-- `vg_<curve>_mul_mod_<p|n>`. -/
def mulFn (k m : Nat) : Prog isa :=
  .block (mulEntry k ++ rowsF k m (2 * k) ++
    csubOut k m (own k + 4 * (2 * k)) (mulRestoreSI k) ++ restoreBP k)

/-- The entry of `add` and `sub`: `ebp` saved, `ebp = ws`, `ecx = ws + a`,
`edx = ws + b`. -/
def asEntry (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esp 4)), .store (at_ .eax (saveAt k + 12)) .ebp, .mov .ebp (.reg .eax),
    .mov .ecx (.mem (at_ .esp 12)), .alu .add .ecx (.reg .ebp),
    .mov .edx (.mem (at_ .esp 16)), .alu .add .edx (.reg .ebp)]

/-- `[ebp + acc] = [ecx] op [edx]`, `N` words, with `op` on the first word and
`op'` on the others, through `eax`. -/
def chainP (op op' : AluOp) (acc N : Nat) : List Instr :=
  (List.range N).flatMap fun j =>
    [.mov .eax (.mem (at_ .ecx (4 * j))), .alu (if j = 0 then op else op') .eax (.mem (at_ .edx (4 * j))),
      .store (bp (acc + 4 * j)) .eax]

/-- `ebp` restored. -/
def restoreP (k : Nat) : List Instr := [.mov .ebp (.mem (bp (saveAt k + 12)))]

/-- `vg_<curve>_add_mod_<p|n>`: the sum and its carry word, then the
conditional subtraction. -/
def addFn (k m : Nat) : Prog isa :=
  .block (asEntry k ++ chainP .add .adc (own k) (2 * k) ++
    [.mov .eax (.imm 0), .alu .adc .eax (.imm 0), .store (bp (own k + 4 * (2 * k))) .eax] ++
    csubOut k m (own k) [] ++ restoreP k)

/-- `[ebp + tmp] = m` masked with `eax`, `N` words, through `edx`. -/
def maskedI (m tmp N : Nat) : List Instr :=
  (List.range N).flatMap fun j =>
    [.mov .edx (.imm (mw m j)), .alu .and .edx (.reg .eax), .store (bp (tmp + 4 * j)) .edx]

/-- `[ecx] = [ebp + src] + [ebp + tmp]`, `N` words, through `edx`. -/
def addOut (src tmp N : Nat) : List Instr :=
  (List.range N).flatMap fun j =>
    [.mov .edx (.mem (bp (src + 4 * j))), .alu (if j = 0 then .add else .adc) .edx (.mem (bp (tmp + 4 * j))),
      .store (at_ .ecx (4 * j)) .edx]

/-- `vg_<curve>_sub_mod_<p|n>`: the difference, and `m` added under the mask
of its borrow, into `[o]`. -/
def subFn (k m : Nat) : Prog isa :=
  .block (asEntry k ++ chainP .sub .sbb (own k) (2 * k) ++ [.alu .sbb .eax (.reg .eax)] ++
    maskedI m (tmpAt k) (2 * k) ++ outPtr ++ addOut (own k) (tmpAt k) (2 * k) ++ restoreP k)

/-! ## Calls of the functions -/

/-- `[o] = f([a], [b])` by a call of the function `f`, whose code is `body`,
on the working space at `edi`: its arguments `(edi, o, a, b)` pushed last to
first, in a frame that `pop eax` releases. -/
def callOp (f : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 b)), .mov .ecx (.imm (BitVec.ofNat 32 a)),
      .mov .edx (.imm (BitVec.ofNat 32 o))])
    (.frame (.push [.eax, .ecx, .edx, .edi]) (.call f body) (.pop .eax 4))

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`. -/
def mulCall (S : Spec.Weierstrass.Mont.Modulus) (o a b : Nat) : Prog isa :=
  callOp (S.fn "mul") (mulFn S.k S.m) o a b

/-- `[o] = [a] + [b] mod m` by a call of `vg_<curve>_add_mod_<p|n>`. -/
def addCall (S : Spec.Weierstrass.Mont.Modulus) (o a b : Nat) : Prog isa :=
  callOp (S.fn "add") (addFn S.k S.m) o a b

/-- `[o] = [a] - [b] mod m` by a call of `vg_<curve>_sub_mod_<p|n>`. -/
def subCall (S : Spec.Weierstrass.Mont.Modulus) (o a b : Nat) : Prog isa :=
  callOp (S.fn "sub") (subFn S.k S.m) o a b

end VG.Impl.Weierstrass.X86.Mont
