import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Impl.X25519.X86_64.Adx

/-!
# Montgomery arithmetic modulo an odd multiword modulus, on x86-64

Arithmetic modulo an odd `m < 2^(64 n)`, `n` 64-bit words, on
numbers below `m` held in the working space as `n` little-endian words at a
constant offset from its base, which is in `rdi`. The modulus is in the
working space too, at `M.mo`; `M.minv` is `-m⁻¹ mod 2⁶⁴`. With
`R = 2^(64 n)`:

* `mul o a b`: `[o] = [a] [b] R⁻¹ mod m`, by coarsely integrated operand
  scanning (CIOS): for each word `a_i` of `[a]`, the accumulator
  `t += a_i [b]`, then `t += u m` for `u = t₀ m' mod 2⁶⁴`, which makes the
  low word zero, and `t /= 2⁶⁴`. The `n + 2` accumulator words are
  registers (`acc n`); the division renames them (round `i`'s words are
  `win n i 0`, `win n i 1`, …), so it costs nothing. For a modulus
  `m ≡ -1 (mod 2⁶⁴)` (`Red.friendly`, P-256's `p`), `u = t₀` and
  `t + t₀ m = (t - t₀) + 2⁶⁴ t₀ m'` with `m' = (m + 1) / 2⁶⁴`, so the words
  above `t₀` get `t₀ m'`, one product per word of `m'` but those of zero
  (`redWords`); for `p`, whose `m'` is `2³² + 2¹²⁸ (2⁶⁴ − 2³² + 1)`, no
  product at all, but shifts and subtractions (`shiftRed`). With BMI2 and ADX (`M.adx`), a row
  is `mulx` for each word, its low half added through OF (`adox`) and its
  high half through CF (`adcx`), two carry chains that do not wait for each
  other (`roundX`). The accumulator stays below `2m`, and the result is
  reduced by `csub`. A square of four words for `p` with BMI2 and ADX
  (`sqrRX`) is X25519's `sqrX`'s product `a²` instead, each product of two
  different words computed once and doubled, into eight registers, then the
  four reductions by `shiftRed`.
* `add o a b`, `sub o a b`: `[a] ± [b] mod m`, with a conditional
  subtraction (`csub`) or addition of `m`.
* `csub`: a number below `2m` in `n` registers and a top word (0 or 1)
  reduced below `m`: the difference with `m` is computed, and taken if it
  did not borrow. For at most four words it is computed in `rax`, `rcx`,
  `rdx` and `rbp` and taken by `cmovae` (`csubC`); for more, into the
  temporary area `[M.tmp]`, and selected by `cmovae` (`csubM`).

For `n ≤ 6` the accumulator is in registers (`mulR`, `addR`, `subR`). For
more words (P-521's 9) it does not fit, and `mulW`, `addW` and `subW` keep
its `n` low words in the temporary area `[M.tmp]` and its two top words in
`r9` and `r10`:

* `mulW o a b`: CIOS as above, each row adding into `[M.tmp]` word by word
  through `r8` (`memRow`), and the division by `2⁶⁴` moving the words down
  (`shiftDown`); then `csubW`.
* `csubW`: the accumulator (below `2m`, its top word in `r9`) reduced below
  `m`: the difference with `m` is computed into `[o]` (`chainW`, word by
  word through `r8`), and the accumulator selected instead under a mask if
  it borrowed.
* `addW`, `subW`: the sum (and its carry in `r9`) or the difference into
  `[M.tmp]`, then `csubW`, or `m` added under the mask of the borrow (through
  `[o]`).

* `mulP o a b`: for P-521's `p = 2⁵²¹ - 1` (its friendly reduction's words,
  `p521Ws`), Montgomery multiplication by columns (product scanning), the
  three-word accumulator in registers, each column's products loaded from
  `[a]` and `[b]`; the reduction's `u_k`, the low words of the first nine
  columns, need no multiplication by `-p⁻¹` and add `512 u_k` to column
  `k + 8`; then `csubW`. `sqrP o a`, `mulP o a a` with each product of two
  different words computed once and added twice.

* `mulF o a b`: for any other modulus of nine words (P-521's order),
  Montgomery multiplication by columns too, each column also adding the
  reduction's `u_k m_j` and the first nine computing their `u` (Koç, Acar and
  Kaliski's FIPS).

`mul`, `add` and `sub` choose by `n` (and `mul` by the reduction, and whether
it squares). Every multiplication is `mul` or `mulx`, every
selection a mask or conditional move, and every address `rdi` plus a constant: nothing but `rdi`
may affect timing. The operations use the registers `rax`, `rcx`, `rdx`,
`rbp` and `acc n` (`r8`–`r13` for `n = 4`, and `r14`, `r15` for `sqrRX`;
`r8`–`r15` from `n = 6`), and
write only `[o]` and `[M.tmp]`.
-/

namespace VG.Impl.Mont.X86_64

open VG.X86_64

/-- `[rdi + d]`: byte `d` of the working space. -/
def sc (d : Nat) : MemOp := { base := .rdi, disp := d }

/-- The accumulator's registers: `n + 2` of `r8`–`r15`. -/
def acc (n : Nat) : List Reg := [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15].take (n + 2)

/-- Word `j` of the accumulator in round `i`: the registers rotate by one
word each round. -/
def win (n i j : Nat) : Reg := (acc n).getD ((i + j) % (n + 2)) .r8

/-- `t:c = t + c + ai · src` (a multiply-accumulate step; it never
overflows). -/
def mulStep (t c ai : Reg) (src : Src) : List Instr :=
  [.mov .rax src, .mul ai, .alu .add .rax (.reg c), .alu .adc .rdx (.imm 0),
    .alu .add t (.reg .rax), .alu .adc .rdx (.imm 0), .mov c (.reg .rdx)]

/-- `ts, carry rbp += rcx · [d], …`: a multiply-accumulate step for each of
the words `ts` and the words at `d`, `d + 8`, …. -/
def mulSteps : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, d => mulStep t .rbp .rcx (.mem (sc d)) ++ mulSteps ts (d + 8)

/-- `ts += rcx · [d]`, its carry word in `rbp`. -/
def mulRow (ts : List Reg) (d : Nat) : List Instr := .mov32 .rbp (.imm 0) :: mulSteps ts d

/-- The carry word `rbp` added into `t_n` and its carry into `t_{n+1}`. -/
def carryUp (tn tn1 : Reg) : List Instr := [.alu .add tn (.reg .rbp), .alu .adc tn1 (.imm 0)]

/-- The words of round `i`'s accumulator, low to high. -/
def wins (n i : Nat) : List Reg := (List.range (n + 2)).map (win n i)

/-- `ts += t₀ w` (`ts` of at least two words): the product `rdx:rax` added
to the first two words, and its carry up the others. -/
def addProd (t0 : Reg) (w : BitVec 64) : List Reg → List Instr
  | t :: t' :: rest => [.movImm64 .rax w, .mul t0, .alu .add t (.reg .rax), .alu .adc t' (.reg .rdx)] ++
      rest.map fun r => .alu .adc r (.imm 0)
  | _ => []

/-- `ts += t₀ m'` for the words `ws` of `m'`: each word but zero multiplied by
`t₀` and added at its place. -/
def redWords (t0 : Reg) : List MWord → List Reg → List Instr
  | [], _ => []
  | w :: ws, ts => (if w = .zero then [] else addProd t0 (BitVec.ofNat 64 w.val) ts) ++ redWords t0 ws ts.tail

/-- `k` if `m'`'s words are `2ᵏ, 0, 2⁶⁴ − 2ᵏ + 1, 0` (P-256's `p`, `k = 32`),
which `shiftRed` multiplies by without `mul`. -/
def shiftK? : List MWord → Option Nat
  | [.pow2 k, .zero, .gen v, .zero] => if 0 < k ∧ k < 64 ∧ v = 2 ^ 64 - 2 ^ k + 1 then some k else none
  | _ => none

/-- `rdx:rax = t₀ 2ᵏ` (`t₀ << k`, `t₀ >> (64 − k)`) and `rbp:rcx = t₀ (2⁶⁴ − 2ᵏ + 1)`:
without BMI2, as `2⁶⁴ t₀ + t₀ − t₀ 2ᵏ` (`t₀ − rax`, then `t₀ − rdx` less
the borrow); with it (`x`), by `mulx`, which waits on no borrow. -/
def shiftProd (x : Bool) (t0 : Reg) (k : Nat) : List Instr :=
  if x then
    [.mov .rdx (.reg t0), .movImm64 .rcx (BitVec.ofNat 64 (2 ^ 64 - 2 ^ k + 1)), .mulx .rbp .rcx (.reg .rcx),
      .mov .rax (.reg t0), .shift .shl .rax k, .shift .shr .rdx (64 - k)]
  else
    [.mov .rax (.reg t0), .shift .shl .rax k, .mov .rdx (.reg t0), .shift .shr .rdx (64 - k),
      .mov .rcx (.reg t0), .alu .sub .rcx (.reg .rax), .mov .rbp (.reg t0), .alu .sbb .rbp (.reg .rdx)]

/-- `ts += t₀ m'` for `m' = 2ᵏ + 2¹²⁸ (2⁶⁴ − 2ᵏ + 1)`, without `mul`
(`shiftProd`); the four words are added to the first four of `ts` in one
carry chain, its carry up the others. -/
def shiftRed (x : Bool) (t0 : Reg) (k : Nat) : List Reg → List Instr
  | w1 :: w2 :: w3 :: w4 :: rest =>
    shiftProd x t0 k ++ [.alu .add w1 (.reg .rax), .alu .adc w2 (.reg .rdx), .alu .adc w3 (.reg .rcx),
      .alu .adc w4 (.reg .rbp)] ++ rest.map fun r => .alu .adc r (.imm 0)
  | _ => []

/-- `ts += t₀ m'` for the words `ws` of `m'`: by `shiftRed` if it applies, else
by `redWords`. -/
def redFriendly (x : Bool) (t0 : Reg) (ws : List MWord) (ts : List Reg) : List Instr :=
  match shiftK? ws with
  | some k => shiftRed x t0 k ts
  | none => redWords t0 ws ts

/-- The reduction of round `i`: `t += u m` with `u = t₀ m' mod 2⁶⁴`, after
which `t₀ = 0`; or, for a friendly modulus, the words above `t₀` get `t₀ m'`
and `t₀ = 0`. -/
def redRound (M : Mod) (i : Nat) : List Instr :=
  let t := win M.n i
  match M.red with
  | .general => [.mov .rax (.reg (t 0)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax)] ++
      mulRow ((List.range M.n).map t) M.mo ++ carryUp (t M.n) (t (M.n + 1))
  | .friendly ws => redFriendly false (t 0) ws (wins M.n i).tail ++ [.mov32 (t 0) (.imm 0)]

/-- Round `i` of `mul o a b` by `mul`: `t += a_i [b]`, then the reduction. -/
def roundM (M : Mod) (a b i : Nat) : List Instr :=
  let t := win M.n i
  let low := (List.range M.n).map t
  [.mov .rcx (.mem (sc (a + 8 * i)))] ++ mulRow low b ++ carryUp (t M.n) (t (M.n + 1)) ++ redRound M i

/-! ### With BMI2 and ADX -/

/-- `xor ebp, ebp`: `rbp = 0`, and both carries (CF and OF) clear. -/
def clearX : Instr := .alu32 .xor .rbp (.reg .rbp)

/-- `mulx rcx, rax, src`, `adox x, rax`, `adcx y, rcx`: `rdx · src` added at
`x` and `y` (the next word), the low half through OF and the high half
through CF. -/
def madd (x y : Reg) (src : Src) : List Instr :=
  [.mulx .rcx .rax src, .adox x (.reg .rax), .adcx y (.reg .rcx)]

/-- `k` products `rdx · [d]`, `rdx · [d + 8]`, … added along the words `ts`. -/
def maddSteps : Nat → List Reg → Nat → List Instr
  | k + 1, x :: y :: rest, d => madd x y (.mem (sc d)) ++ maddSteps k (y :: rest) (d + 8)
  | _, _, _ => []

/-- The carries left by `maddSteps` (`rbp = 0`): OF into `tn`, then CF and
OF into `tn1`. -/
def carriesX (tn tn1 : Reg) : List Instr :=
  [.adox tn (.reg .rbp), .adcx tn1 (.reg .rbp), .adox tn1 (.reg .rbp)]

/-- `ts += rdx · [d]`, `n` words, for `n + 2` words `ts`. -/
def rowX (n : Nat) (ts : List Reg) (d : Nat) : List Instr :=
  clearX :: maddSteps n ts d ++ carriesX (ts.getD n .r8) (ts.getD (n + 1) .r8)

/-- Round `i` of `mul o a b` with BMI2 and ADX: `t += a_i [b]` (`rowX`), then
the reduction: `t += u m` by `rowX`, `u = t₀ m' mod 2⁶⁴` in `rdx`, or as
`redRound` for a friendly modulus. -/
def roundX (M : Mod) (a b i : Nat) : List Instr :=
  let t := win M.n i
  [.mov .rdx (.mem (sc (a + 8 * i)))] ++ rowX M.n (wins M.n i) b ++
  match M.red with
  | .general => [.mov .rax (.reg (t 0)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rdx (.reg .rax)] ++
      rowX M.n (wins M.n i) M.mo
  | .friendly ws => redFriendly true (t 0) ws (wins M.n i).tail ++ [.mov32 (t 0) (.imm 0)]

/-- Round `i` of `mul o a b`. -/
def round (M : Mod) (a b i : Nat) : List Instr := if M.adx then roundX M a b i else roundM M a b i

/-- `[tmp + d] = ts - [mo + d]`, word by word, with `op` (`sub`, then
`sbb`) on the first word, through `rax`. -/
def diffs (op : AluOp) : List Reg → Nat → Nat → List Instr
  | [], _, _ => []
  | t :: ts, mo, tmp => [.mov .rax (.reg t), .alu op .rax (.mem (sc mo)), .store (sc tmp) .rax] ++
    diffs .sbb ts (mo + 8) (tmp + 8)

/-- Replace `ts` by `[tmp]` when the subtraction did not borrow, preserving
its carry flag across all words. -/
def selects : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, tmp => [.cmov .ae t (.mem (sc tmp))] ++ selects ts (tmp + 8)

/-- `ts` (and the top word `top`), below `2m`, reduced modulo `m`: the
difference with `m` is computed into `[tmp]`; its final borrow selects it. -/
def csubM (M : Mod) (ts : List Reg) (top : Reg) : List Instr :=
  diffs .sub ts M.mo M.tmp ++
  [.mov .rax (.reg top), .alu .sbb .rax (.imm 0)] ++ selects ts M.tmp

/-- The registers `csubC` computes the difference in. -/
def cregs : List Reg := [.rax, .rcx, .rdx, .rbp]

/-- `ds = ts - [mo]`, word by word, with `op` (`sub`, then `sbb`) on the
first word: its borrow is in CF. -/
def diffsC (op : AluOp) : List Reg → List Reg → Nat → List Instr
  | t :: ts, d :: ds, mo => [.mov d (.reg t), .alu op d (.mem (sc mo))] ++ diffsC .sbb ts ds (mo + 8)
  | _, _, _ => []

/-- `ts = ds` if CF is clear (`cmovae`). -/
def cmovs : List Reg → List Reg → List Instr
  | t :: ts, d :: ds => .cmov .ae t (.reg d) :: cmovs ts ds
  | _, _ => []

/-- `csubM` in registers, for at most four words: the difference with `m` in
`cregs`, the top word's borrow, and the difference moved to `ts` if it did not
borrow. -/
def csubC (M : Mod) (ts : List Reg) (top : Reg) : List Instr :=
  diffsC .sub ts cregs M.mo ++ [.alu .sbb top (.imm 0)] ++ cmovs ts cregs

/-- `ts` (and the top word `top`), below `2m`, reduced modulo `m`: by `csubC`
for at most four words, else by `csubM`. -/
def csub (M : Mod) (ts : List Reg) (top : Reg) : List Instr :=
  if ts.length ≤ 4 then csubC M ts top else csubM M ts top

/-- `[o] = ts`. -/
def stores : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, o => .store (sc o) t :: stores ts (o + 8)

/-- `ts = [a]`. -/
def loads : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, a => .mov t (.mem (sc a)) :: loads ts (a + 8)

/-- `ts := 0`. -/
def zeros (ts : List Reg) : List Instr := ts.map fun t => .mov32 t (.imm 0)

/-- The words of `sqrRX`'s result, `(a² + U m) / 2²⁵⁶`, but its top one, `r8`. -/
def sqLow : List Reg := [.r12, .r13, .r14, .r15]

/-- `[o] = [a]² R⁻¹ mod m` for four words and `m' = 2ᵏ + 2¹²⁸ (2⁶⁴ − 2ᵏ + 1)`
(P-256's `p`), with BMI2 and ADX: `a²` into `r8`–`r15` as X25519's `sqrX`
computes it, then `shiftRed` adds `t_i m'` to the words above `t_i`, for each of
the four low words `t_i` in turn. Only the last can carry out of `r15`, into
`r8`, cleared by then. -/
def sqrRX (M : Mod) (k o a : Nat) : List Instr :=
  Impl.X25519.X86_64.sqrA a ++ Impl.X25519.X86_64.sqrB a ++ Impl.X25519.X86_64.sqrC a ++
    Impl.X25519.X86_64.sqrD a ++
    shiftRed true .r8 k [.r9, .r10, .r11, .r12, .r13, .r14, .r15] ++
    shiftRed true .r9 k [.r10, .r11, .r12, .r13, .r14, .r15] ++
    shiftRed true .r10 k [.r11, .r12, .r13, .r14, .r15] ++ [.mov32 .r8 (.imm 0)] ++
    shiftRed true .r11 k (sqLow ++ [.r8]) ++ csub M sqLow .r8 ++ stores sqLow o

/-- `some k` if `mul o a a` is a square that `sqrRX` computes: four words, BMI2
and ADX, and the friendly reduction by `shiftRed`. -/
def sqrK? (M : Mod) (a b : Nat) : Option Nat :=
  if M.adx ∧ M.n = 4 ∧ a = b then
    match M.red with
    | .friendly ws => shiftK? ws
    | .general => none
  else none

/-- `[o] = [a] [b] R⁻¹ mod m` (`o` may be `a` or `b`), the accumulator in
registers; a square by `sqrRX` if it applies. -/
def mulR (M : Mod) (o a b : Nat) : List Instr :=
  match sqrK? M a b with
  | some k => sqrRX M k o a
  | none =>
    let low := (List.range M.n).map (win M.n M.n)
    zeros (acc M.n) ++ (List.range M.n).flatMap (round M a b) ++
      csub M low (win M.n M.n M.n) ++ stores low o

/-- `ts op= [b]`, word by word, with `op` on the first word and `op'` on the
others (`add` and `adc`, `sub` and `sbb`). -/
def chain (op op' : AluOp) : List Reg → Nat → List Instr
  | [], _ => []
  | t :: ts, b => .alu op t (.mem (sc b)) :: chain op' op' ts (b + 8)

/-- The low words and the top word of the sums and differences. -/
def low (n : Nat) : List Reg := (acc n).take n
def top (n : Nat) : Reg := (acc n).getD n .r8

/-- `[o] = [a] + [b] mod m`, in registers. -/
def addR (M : Mod) (o a b : Nat) : List Instr :=
  loads (low M.n) a ++ [.mov32 (top M.n) (.imm 0)] ++ chain .add .adc (low M.n) b ++
    [.alu .adc (top M.n) (.imm 0)] ++ csub M (low M.n) (top M.n) ++ stores (low M.n) o

/-- `[tmp] = [mo]` masked with `rax`, `n` words. -/
def masked : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, mo, tmp => [.mov .rdx (.mem (sc mo)), .alu .and .rdx (.reg .rax),
      .store (sc tmp) .rdx] ++ masked k (mo + 8) (tmp + 8)

/-- `[o] = [a] - [b] mod m`: the difference, and `m` added under the mask
`rax` of its borrow (through `[tmp]`), in registers. -/
def subR (M : Mod) (o a b : Nat) : List Instr :=
  loads (low M.n) a ++ chain .sub .sbb (low M.n) b ++ [.alu .sbb .rax (.reg .rax)] ++
    masked M.n M.mo M.tmp ++ chain .add .adc (low M.n) M.tmp ++ stores (low M.n) o

/-! ## More than six words: the accumulator in the temporary area -/

/-- `[t] = [t] + rcx · src + rbp` and its carry word in `rbp`, through `r8`. -/
def memStep (t : Nat) (src : Src) : List Instr :=
  .mov .r8 (.mem (sc t)) :: mulStep .r8 .rbp .rcx src ++ [.store (sc t) .r8]

/-- `k` words at `t`, `t + 8`, … `+= rcx · [d]`, …, the carry word in `rbp`. -/
def memSteps : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, t, d => memStep t (.mem (sc d)) ++ memSteps k (t + 8) (d + 8)

/-- `[t] += rcx · [d]` (`k` words), its carry word in `rbp`. -/
def memRow (k t d : Nat) : List Instr := .mov32 .rbp (.imm 0) :: memSteps k t d

/-- `[t] = [t + 8]`, …: `k` words moved down by one word, through `r8`. -/
def moveDown : Nat → Nat → List Instr
  | 0, _ => []
  | k + 1, t => [.mov .r8 (.mem (sc (t + 8))), .store (sc t) .r8] ++ moveDown k (t + 8)

/-- The accumulator divided by `2⁶⁴` (its low word is zero): its words moved
down, `r9` stored on top, and `r10` moved into `r9`. -/
def shiftDown (M : Mod) : List Instr :=
  moveDown (M.n - 1) M.tmp ++ [.store (sc (M.tmp + 8 * (M.n - 1))) .r9, .mov .r9 (.reg .r10),
    .mov32 .r10 (.imm 0)]

/-- Round `i` of `mulW o a b`: `T += a_i [b]`, then `T += u m` with
`u = t₀ m' mod 2⁶⁴`, after which `t₀ = 0`, and `T /= 2⁶⁴`. -/
def roundW (M : Mod) (a b i : Nat) : List Instr :=
  [.mov .rcx (.mem (sc (a + 8 * i)))] ++ memRow M.n M.tmp b ++ carryUp .r9 .r10 ++
  [.mov .r8 (.mem (sc M.tmp)), .mov .rax (.reg .r8), .movImm64 .rcx M.minv, .mul .rcx,
    .mov .rcx (.reg .rax)] ++
    memRow M.n M.tmp M.mo ++ carryUp .r9 .r10 ++ shiftDown M

/-- `k` words of zeros at `t`, through `r8`. -/
def zeroWords (k t : Nat) : List Instr :=
  .mov32 .r8 (.imm 0) :: (List.range k).map fun j => .store (sc (t + 8 * j)) .r8

/-- `[t] = [a] op [b]`, word by word, with `op` on the first word and `op'`
on the others, through `r8`. -/
def chainW (op op' : AluOp) : Nat → Nat → Nat → Nat → List Instr
  | 0, _, _, _ => []
  | k + 1, t, a, b => [.mov .r8 (.mem (sc a)), .alu op .r8 (.mem (sc b)), .store (sc t) .r8] ++
    chainW op' op' k (t + 8) (a + 8) (b + 8)

/-- `[o] = [x]` where the mask `rax` is all zeros (`[o]` kept where it is all
ones), word by word. -/
def selectsW : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, x, o => [.mov .rdx (.mem (sc o)), .mov .r8 (.mem (sc x)), .alu .xor .rdx (.reg .r8),
      .alu .and .rdx (.reg .rax), .alu .xor .rdx (.reg .r8), .store (sc o) .rdx] ++
      selectsW k (x + 8) (o + 8)

/-- `[o] = T mod m` for `T = [tmp] + 2^(64 n) r9 < 2m`: the difference with
`m` into `[o]`, and `[tmp]` selected instead if it borrowed. -/
def csubW (M : Mod) (o : Nat) : List Instr :=
  chainW .sub .sbb M.n o M.tmp M.mo ++
  [.mov .rax (.reg .r9), .alu .sbb .rax (.imm 0), .alu .sbb .rax (.reg .rax),
    .alu .xor .rax (.imm (-1))] ++
  selectsW M.n M.tmp o

/-- `[o] = [a] [b] R⁻¹ mod m` (`o` may be `a` or `b`), the accumulator in
`[tmp]`, `r9` and `r10`. -/
def mulW (M : Mod) (o a b : Nat) : List Instr :=
  zeroWords M.n M.tmp ++ [.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0)] ++
    (List.range M.n).flatMap (roundW M a b) ++ csubW M o

/-- `[o] = [a] + [b] mod m`, the sum in `[tmp]` and `r9`. -/
def addW (M : Mod) (o a b : Nat) : List Instr :=
  [.mov32 .r9 (.imm 0)] ++ chainW .add .adc M.n M.tmp a b ++ [.alu .adc .r9 (.imm 0)] ++ csubW M o

/-- `[o] = [a] - [b] mod m`: the difference in `[tmp]`, then `m` masked with
the borrow into `[o]`, and their sum into `[o]`. -/
def subW (M : Mod) (o a b : Nat) : List Instr :=
  chainW .sub .sbb M.n M.tmp a b ++ [.alu .sbb .rax (.reg .rax)] ++ masked M.n M.mo o ++
    chainW .add .adc M.n o M.tmp o

/-! ## P-521's modulus: the product by columns -/

/-- The words of `(p + 1) / 2⁶⁴ = 2⁴⁵⁷` for P-521's `p = 2⁵²¹ - 1`, its friendly
reduction (`Red.ofModulus 9 p`). -/
def p521Ws : List MWord := [.zero, .zero, .zero, .zero, .zero, .zero, .zero, .pow2 9, .zero]

/-- The accumulator's registers in column `c` of `mulP`: they rotate, the low
word of one column becoming the top word of the next once stored. -/
def pAcc (c k : Nat) : Reg := [Reg.r9, .r10, .r11].getD ((c + k) % 3) .r9

/-- A term's second factor: the word at `d` (`some d`), or 512. -/
def pSrc : Option Nat → Src
  | some d => .mem (sc d)
  | none => .imm 512

/-- `[dx] · y` added to the accumulator of column `c`, `y` (`pSrc dy`) into
`rcx` and `[dx]` into `rax`. -/
def pTerm (c dx : Nat) (dy : Option Nat) : List Instr :=
  [.mov .rcx (pSrc dy), .mov .rax (.mem (sc dx)),
    .mul .rcx, .alu .add (pAcc c 0) (.reg .rax), .alu .adc (pAcc c 1) (.reg .rdx),
    .alu .adc (pAcc c 2) (.imm 0)]

/-- The terms of column `c` of `mulP o a b`: the products `[a + 8i] [b + 8j]`
with `i + j = c`, and for `8 ≤ c ≤ 16` the reduction's `512 u_{c-8}`, with
`u_{c-8}` in the temporary area. -/
def pTerms (M : Mod) (a b c : Nat) : List (Nat × Option Nat) :=
  ((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map (fun i => (a + 8 * i, some (b + 8 * (c - i)))) ++
    if 8 ≤ c ∧ c ≤ 16 then [(M.tmp + 8 * (c - 8), none)] else []

/-- Column `c` of `mulP o a b`: its terms, then its low word stored at
`[tmp + 8 (c mod 9)]` and cleared. -/
def pCol (M : Mod) (a b c : Nat) : List Instr :=
  (pTerms M a b c).flatMap (fun t => pTerm c t.1 t.2) ++
    [.store (sc (M.tmp + 8 * (c % 9))) (pAcc c 0), .mov32 (pAcc c 0) (.imm 0)]

/-- A Montgomery multiplication by columns into `[o]`: the accumulator
`r9`–`r11` cleared, the eighteen columns `col c`, then `csubW`. -/
def prodCols (M : Mod) (o : Nat) (col : Nat → List Instr) : List Instr :=
  [.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0)] ++ (List.range 18).flatMap col ++ csubW M o

/-- `[o] = [a] [b] R⁻¹ mod p` for P-521's `p = 2⁵²¹ - 1` (`o` may be `a` or
`b`), by Montgomery multiplication in product scanning: column `c` sums the
products `a_i b_j` with `i + j = c` in three registers (`pAcc`). As
`p ≡ -1 (mod 2⁶⁴)`, the reduction's `u_k` is the low word of column `k`
(`k ≤ 8`), stored at `[tmp + 8k]`, and adding `u_k p = 2^(521 + 64k) u_k - u_k`
clears it and adds `2⁹ u_k = 512 u_k` to column `k + 8`. Columns 9 to 17 are
the result, `(a b + U p) / 2⁵⁷⁶ < 2p`, stored over the `u`s no longer needed
(column `c` at `[tmp + 8 (c - 9)]`), with its top word in `r9`; `csubW`
reduces it into `[o]`. -/
def mulP (M : Mod) (o a b : Nat) : List Instr := prodCols M o (pCol M a b)

/-- A squaring's term `[dx] · y`, added twice if `two`: the product's
`rdx:rax` added again. -/
def sTerm (c dx : Nat) (dy : Option Nat) (two : Bool) : List Instr :=
  pTerm c dx dy ++ if two then [.alu .add (pAcc c 0) (.reg .rax), .alu .adc (pAcc c 1) (.reg .rdx),
    .alu .adc (pAcc c 2) (.imm 0)] else []

/-- The terms of column `c` of `sqrP o a`: the products `[a + 8i] [a + 8j]`
with `i < j`, `i + j = c`, twice, the square `[a + 4c]²` for even `c`, and
for `8 ≤ c ≤ 16` the reduction's `512 u_{c-8}`. -/
def sTerms (M : Mod) (a c : Nat) : List (Nat × Option Nat × Bool) :=
  ((List.range 9).filter fun i => 2 * i < c ∧ c - i < 9).map (fun i => (a + 8 * i, some (a + 8 * (c - i)), true)) ++
    (if c % 2 = 0 ∧ c / 2 < 9 then [(a + 8 * (c / 2), some (a + 8 * (c / 2)), false)] else []) ++
    if 8 ≤ c ∧ c ≤ 16 then [(M.tmp + 8 * (c - 8), none, false)] else []

/-- Column `c` of `sqrP o a`: its terms, then its low word stored at
`[tmp + 8 (c mod 9)]` and cleared. -/
def sCol (M : Mod) (a c : Nat) : List Instr :=
  (sTerms M a c).flatMap (fun t => sTerm c t.1 t.2.1 t.2.2) ++
    [.store (sc (M.tmp + 8 * (c % 9))) (pAcc c 0), .mov32 (pAcc c 0) (.imm 0)]

/-- `[o] = [a]² R⁻¹ mod p` for P-521's `p`: `mulP o a a`, but each product
of two different words computed once and added twice (`sTerm`), 45
products in place of 81. -/
def sqrP (M : Mod) (o a : Nat) : List Instr := prodCols M o (sCol M a)

/-! ## P-521's modulus with BMI2 and ADX: the product by rows -/

/-- The registers of `mulPX`'s accumulator. -/
def xRegs : List Reg := [.rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The register of word `k` of `mulPX`'s accumulator: the nine words of a
row's accumulator are in distinct registers, word `k + 9` taking the
register of word `k` once that is stored. -/
def xAcc (k : Nat) : Reg := xRegs.getD (k % 9) .rbp

/-- The nine registers of words `k` to `k + 8`. -/
def xWin (k : Nat) : List Reg := (List.range 9).map fun j => xAcc (k + j)

/-- `mov eax, 0`, `adox t, rax`: the carry OF added into `t`. -/
def xTail (t : Reg) : List Instr := [.mov32 .rax (.imm 0), .adox t (.reg .rax)]

/-- Row `i` of `mulPX o a b`: `rdx = a_i`, both carries cleared
(`xor eax, eax`), `t += a_i [b]` with the first product's word `i` stored at
`[tmp + 8i]` once final and its register cleared for word `i + 9`, then the
eight other products (`maddSteps`), and the carry OF into word `i + 9`. -/
def xRow (M : Mod) (a b i : Nat) : List Instr :=
  [.mov .rdx (.mem (sc (a + 8 * i))), .alu32 .xor .rax (.reg .rax)] ++
    madd (xAcc i) (xAcc (i + 1)) (.mem (sc b)) ++
    [.store (sc (M.tmp + 8 * i)) (xAcc i), .mov32 (xAcc i) (.imm 0)] ++
    maddSteps 8 (xWin (i + 1)) (b + 8) ++ xTail (xAcc (i + 9))

/-- The reduction of `mulPX`, for `P = a b` with its low words `P₀ … P₈` at
`[tmp]` and its high words in `xWin 9`: `(P + U p) / 2⁵⁷⁶` for
`U = P₀ … P₇, u₈` with `u₈ = P₈ + 512 P₀ mod 2⁶⁴` (stored over `P₈`), as
`U p = 2⁵²¹ U - U`: `512 U` added at word 8 (`rdx = 512`), the low words
cancelling. -/
def xRed (M : Mod) : List Instr :=
  [.mov32 .rdx (.imm 512), .alu32 .xor .rax (.reg .rax), .mulx .rcx .rax (.mem (sc M.tmp)),
    .adox .rax (.mem (sc (M.tmp + 64))), .store (sc (M.tmp + 64)) .rax, .adcx (xAcc 9) (.reg .rcx)] ++
    maddSteps 8 (xWin 9) (M.tmp + 8) ++ xTail (xAcc 17)

/-- `xWin 9`, a number `S < 2p` for P-521's `p = 2⁵²¹ - 1`, reduced and
stored at `[o]`: `S + 1` in place, whose bit 521 `c` (in `rax`) is whether
`S ≥ p`; then `1 - c` subtracted, which leaves `S + c`, and its bits from 521
cleared: `S - p` if `S ≥ p`, else `S`. -/
def xCanon (o : Nat) : List Instr :=
  .alu .add (xAcc 9) (.imm 1) :: (List.range 8).map (fun k => .alu .adc (xAcc (10 + k)) (.imm 0)) ++
    [.mov .rax (.reg (xAcc 17)), .shift .shr .rax 9, .alu .xor .rax (.imm 1),
      .alu .sub (xAcc 9) (.reg .rax)] ++
    (List.range 8).map (fun k => .alu .sbb (xAcc (10 + k)) (.imm 0)) ++
    [.alu .and (xAcc 17) (.imm 511)] ++ stores (xWin 9) o

/-- `[o] = [a] [b] R⁻¹ mod p` for P-521's `p = 2⁵²¹ - 1` (`o` may be `a` or
`b`), with BMI2 and ADX: the product `a b` by rows (operand scanning,
`xRow`), each row's `mulx` products added through the two carry chains
(`adox`, `adcx`) into nine registers, its low word stored in the temporary
area; then the reduction (`xRed`), which leaves `(a b + U p) / 2⁵⁷⁶ < 2p` in
the registers; then `xCanon`, which reduces it below `p` into `[o]`. -/
def mulPX (M : Mod) (o a b : Nat) : List Instr :=
  zeros xRegs ++ (List.range 9).flatMap (xRow M a b) ++ xRed M ++ xCanon o

/-! ## P-521's modulus with BMI2 and ADX: the square

The products of two different words by rows (`sRow`, 36 products), doubled
and the squares added in one pass (`sDiag`: CF doubles, OF adds), then
`mulPX`'s reduction and final reduction. -/

/-- The registers of row `i < 8` of `sqrPX`'s products: words `2i + 1 … i + 9`. -/
def sWin (i : Nat) : List Reg := (List.range (9 - i)).map fun j => xAcc (2 * i + 1 + j)

/-- Row `i < 8` of `sqrPX`'s products of two different words: word `i`, final,
stored at `[tmp + 8i]` and its register cleared for word `i + 9`; `rdx = a_i`,
both carries cleared, `t += a_i [a + 8 (i + 1)]` (`8 - i` products into words
`2i + 1 … i + 9`), and the carry OF into word `i + 9`. -/
def sRow (M : Mod) (a i : Nat) : List Instr :=
  [.store (sc (M.tmp + 8 * i)) (xAcc i), .mov32 (xAcc i) (.imm 0), .mov .rdx (.mem (sc (a + 8 * i))),
    .alu32 .xor .rax (.reg .rax)] ++ maddSteps (8 - i) (sWin i) (a + 8 * (i + 1)) ++ xTail (xAcc (i + 9))

/-- Word `w` of the square: `t_w = 2 t_w + d` (`adcx t, t`, `adox t, d`), in
the temporary area for `w ≤ 8` (through `rdx`), else in its register. -/
def sDbl (M : Mod) (w : Nat) (d : Reg) : List Instr :=
  if w ≤ 8 then
    [.mov .rdx (.mem (sc (M.tmp + 8 * w))), .adcx .rdx (.reg .rdx), .adox .rdx (.reg d),
      .store (sc (M.tmp + 8 * w)) .rdx]
  else [.adcx (xAcc w) (.reg (xAcc w)), .adox (xAcc w) (.reg d)]

/-- Step `k` of the squares: `a_k²` into `rcx:rax`, added to words `2k` and
`2k + 1` of twice the products (CF doubles, OF adds). -/
def sDiagK (M : Mod) (a k : Nat) : List Instr :=
  [.mov .rdx (.mem (sc (a + 8 * k))), .mulx .rcx .rax (.reg .rdx)] ++ sDbl M (2 * k) .rax ++
    sDbl M (2 * k + 1) .rcx

/-- Word 8 stored and its register cleared for word 17, both carries cleared,
then the squares. -/
def sDiag (M : Mod) (a : Nat) : List Instr :=
  [.store (sc (M.tmp + 64)) (xAcc 8), .mov32 (xAcc 17) (.imm 0), .alu32 .xor .rax (.reg .rax)] ++
    (List.range 9).flatMap (sDiagK M a)

/-- `[o] = [a]² R⁻¹ mod p` for P-521's `p`, with BMI2 and ADX: the products
of two different words by rows (`sRow`), doubled and the squares added
(`sDiag`), then `mulPX`'s reduction and final reduction. -/
def sqrPX (M : Mod) (o a : Nat) : List Instr :=
  zeros xRegs ++ (List.range 8).flatMap (sRow M a) ++ sDiag M a ++ xRed M ++ xCanon o

/-! ## P-521's modulus: the sum and the difference in registers

As `p = 2⁵²¹ - 1`, the sum or difference below `2p` is reduced in place by
`xCanon` (no load of `p`, no temporary area), and `p - [b]` is the complement
of `[b]`'s words but the top one. -/

/-- `[o] = [a] + [b] mod p` for P-521's `p = 2⁵²¹ - 1` and `[a] + [b] < 2p`:
the sum in `xWin 9` (`[a]` loaded, `[b]` added), reduced by `xCanon`. -/
def addMer (o a b : Nat) : List Instr :=
  loads (xWin 9) a ++ chain .add .adc (xWin 9) b ++ xCanon o

/-- The words `9 … 16` of the accumulator (`xWin 9` but its last). -/
def xLo8 : List Reg := (List.range 8).map fun k => xAcc (9 + k)

/-- `p - [b]` in `xWin 9` for `[b] < p`: as `p`'s words are all ones but the
top one, 511, its low words are the complements of `[b]`'s (`xor` with `-1`)
and its top word `511 - b₈`. -/
def negMer (b : Nat) : List Instr :=
  loads xLo8 b ++ (xLo8.map fun t => .alu .xor t (.imm (-1))) ++
    [.mov32 (xAcc 17) (.imm 511), .alu .sub (xAcc 17) (.mem (sc (b + 64)))]

/-- `[o] = [a] - [b] mod p` for P-521's `p` and `[a]`, `[b]` below `p`:
`[a] + (p - [b]) < 2p`, reduced by `xCanon`. -/
def subMer (o a b : Nat) : List Instr :=
  negMer b ++ chain .add .adc (xWin 9) a ++ xCanon o

/-! ## Nine words: the product by columns for any modulus -/

/-- The terms of column `c` of `mulF o a b`: the products `[a + 8i] [b + 8j]`
with `i + j = c`, and the reduction's `u_k [mo + 8j]` with `k + j = c` and
`k < c`, `u_k` in the temporary area. -/
def fTerms (M : Mod) (a b c : Nat) : List (Nat × Option Nat) :=
  ((List.range M.n).filter fun i => i ≤ c ∧ c - i < M.n).map (fun i => (a + 8 * i, some (b + 8 * (c - i)))) ++
    ((List.range M.n).filter fun k => k < c ∧ c - k < M.n).map
      (fun k => (M.tmp + 8 * k, some (M.mo + 8 * (c - k))))

/-- The end of column `c < n` of `mulF`: `u_c = t₀ m' mod 2⁶⁴` into `rcx` and
`[tmp + 8c]`, and `u_c [mo]` added, which clears the low word. -/
def fRed (M : Mod) (c : Nat) : List Instr :=
  [.mov .rax (.reg (pAcc (c + M.n) 0)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax),
    .store (sc (M.tmp + 8 * c)) .rcx, .mov .rax (.mem (sc M.mo)), .mul .rcx,
    .alu .add (pAcc (c + M.n) 0) (.reg .rax), .alu .adc (pAcc (c + M.n) 1) (.reg .rdx),
    .alu .adc (pAcc (c + M.n) 2) (.imm 0)]

/-- Column `c` of `mulF o a b`, its accumulator `pAcc (c + n)`: its terms,
then for `c < n` the reduction's `u_c` (`fRed`), and for `c ≥ n` its low word
stored at `[tmp + 8 (c - n)]` and cleared. -/
def fCol (M : Mod) (a b c : Nat) : List Instr :=
  (fTerms M a b c).flatMap (fun t => pTerm (c + M.n) t.1 t.2) ++
    if c < M.n then fRed M c
    else [.store (sc (M.tmp + 8 * (c - M.n))) (pAcc (c + M.n) 0), .mov32 (pAcc (c + M.n) 0) (.imm 0)]

/-- `[o] = [a] [b] R⁻¹ mod m` (`o` may be `a` or `b`) for a modulus of nine
words, by Montgomery multiplication in product scanning (Koç, Acar and
Kaliski's FIPS): column `c` sums the products `a_i b_j` and the reduction's
`u_k m_j` with `i + j = k + j = c` in three registers (`pAcc`); at the end of
column `c < n`, `u_c = t₀ m' mod 2⁶⁴` is stored at `[tmp + 8c]` and `u_c m_0`
clears the low word. Columns `n` to `2n - 1` are `(a b + U m) / R < 2m`,
stored over the `u`s no longer needed (column `c` at `[tmp + 8 (c - n)]`),
with its top word in `r9`; `csubW` reduces it into `[o]`. -/
def mulF (M : Mod) (o a b : Nat) : List Instr :=
  [.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0)] ++
    (List.range (2 * M.n)).flatMap (fCol M a b) ++ csubW M o

/-! ## The operations -/

/-- `[o] = [a] [b] R⁻¹ mod m` (`o` may be `a` or `b`). -/
def mul (M : Mod) (o a b : Nat) : List Instr :=
  if M.n < 7 then mulR M o a b
  else if M.red = .friendly p521Ws then
    (if M.adx then (if a = b then sqrPX M o a else mulPX M o a b)
      else if a = b then sqrP M o a else mulP M o a b)
  else if M.n = 9 then mulF M o a b else mulW M o a b

/-- `[o] = [a] + [b] mod m`. -/
def add (M : Mod) (o a b : Nat) : List Instr :=
  if M.n < 7 then addR M o a b else if M.red = .friendly p521Ws then addMer o a b else addW M o a b

/-- `[o] = [a] - [b] mod m`. -/
def sub (M : Mod) (o a b : Nat) : List Instr :=
  if M.n < 7 then subR M o a b else if M.red = .friendly p521Ws then subMer o a b else subW M o a b

end VG.Impl.Mont.X86_64
