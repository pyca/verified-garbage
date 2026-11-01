module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# The check of a public point on RISC-V

`vg_<curve>_check_point(ws)` (`Spec/Weierstrass/CheckPoint.lean`), for a
curve of `n` 64-bit words, on the layout of `Impl/Ecdsa/RISCV64.lean`:

1. `s0` and `ra` saved in slot 2 (the function's own working space), and
   the working space's base to `s0`;
2. the masks of `x < p` and `y < p` into the flag (`ltMask`: `x - p` word
   by word with borrows, whose last borrow is set if and only if `x < p`);
3. `x R mod p` and `y R mod p`, by multiplications by `R² mod p`, and
   `y² - (x³ + a x + b)` in Montgomery's form (`curveOps`), whose mask of
   being zero (`zeroMask`) goes into the flag;
4. the point the scalar multiplication takes: the public point's
   coordinates in Montgomery's form if the flag is set, else `G`'s, by the
   flag as a mask;
5. `ra` and `s0` restored.

Every address is `s0` plus a constant, and the only branches are in the
field functions, on their pointers: the function is constant time.

`vg_ecdh_<curve>(out, d, peer, scratch)` and
`vg_ec_<curve>_public_key(out, d, scratch)` share their pieces (`ecdhFn`,
`publicKeyFn`):

1. `s0`, `s1`, `s2` and `ra` saved in the working space's first 32 bytes,
   its base to `s0` and `out` to `s2`;
2. `d` read big-endian into `K`'s slot (`loadNum`: a doubleword at a time,
   a byte at a time, as the arguments' alignment is not known), the
   constants stored (`setConst`, from immediates);
3. for ECDH, the peer's `x` and `y` read into the check's slots, the flag set
   to the mask of the peer's first byte being `04`, and the check of the
   point called (its point, or `G`, to `R`'s first two slots); for the public
   key, the flag set and `G` copied there;
4. the masks of `d < n` and `d ≠ 0` anded into the flag, then `R = [d]P` by a
   call of `vg_<curve>_mul`, `Z^(p-2)` by `pow`, `x = X Z^(p-2)` (and `y`)
   out of Montgomery's form, and the mask of `Z ≠ 0` into the flag;
5. `x` (and `y`) stored big-endian to `out` under the flag's mask
   (`storeNum`), the flag's low bit returned, the registers restored.

Everything is computed whatever the flag: only the pointers may affect
timing.
-/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64

/-! Slots of the check (`Spec/Weierstrass/CheckPoint.lean`). -/
def CX := 33
def CXM := 34
def CYM := 35
def CY := 36
def W0 := 37
def CPX := 38
def R2P := 39
def BP := 40
def W1 := 41
def W2 := 42
def CPY := 43
def FLAG := 44

/-- Word `j` of `[a] - [m]` with the borrow in `t5` (into and out of it),
through `t3`, `t4`, `t6` and `a4`. -/
def ltWord (a m : Nat) : List Instr :=
  [.load .d .t3 wb a, .load .d .t4 wb m,
    .sltu .t6 .t3 .t4, .sub .t3 .t3 .t4, .sltu .a4 .t3 .t5, .sub .t3 .t3 .t5, .add .t5 .t6 .a4]

/-- The words of `[a] - [m]`, `k` of them, the borrow in `t5`. -/
def ltWords : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, a, m => ltWord a m ++ ltWords k (a + 8) (m + 8)

/-- The mask `a7` of `[a] < [m]` (all ones if it is), `n` words: the borrow out
of `[a] - [m]`, negated. -/
def ltMask (n a m : Nat) : List Instr :=
  [.li .t5 0] ++ ltWords n a m ++ [.li .t6 0, .sub .a7 .t6 .t5]

/-- The words of `[a]` or'ed into `t3`, through `t4`. -/
def orWords : Nat → Nat → List Instr
  | 0, _ => []
  | k + 1, a => [.load .d .t4 wb a, .logic .or .t3 .t3 .t4] ++ orWords k (a + 8)

/-- The mask `a7` of `[a] = 0` (all ones if it is), `n` words: the words
or'ed, the top bit of `x | -x` (set iff `x ≠ 0`), less one. -/
def zeroMask (n a : Nat) : List Instr :=
  [.li .t3 0] ++ orWords n a ++
    [.li .t4 0, .sub .t4 .t4 .t3, .logic .or .t4 .t4 .t3, .shift .srl .d .t4 .t4 63, .addi .a7 .t4 (-1)]

namespace Cfg

variable (c : Cfg)

/-- The flag `&=` the mask `a7`, through `t0`. -/
def andFlag : List Instr :=
  [.load .d .t0 wb (c.sl FLAG), .logic .and .t0 .t0 .a7, .store .d .t0 wb (c.sl FLAG)]

/-- `y² - (x³ + a x + b)`, from `x R` and `y R`, to `W1`. -/
def curveOps : List FOp :=
  [.mul (c.sl W0) (c.sl CYM) (c.sl CYM), .mul (c.sl W1) (c.sl CXM) (c.sl CXM),
    .mul (c.sl W2) (c.sl W1) (c.sl CXM), .mul (c.sl W1) (c.sl AP) (c.sl CXM),
    .add (c.sl CPX) (c.sl W2) (c.sl W1), .add (c.sl W2) (c.sl CPX) (c.sl BP),
    .sub (c.sl W1) (c.sl W0) (c.sl W2)]

/-- Where `vg_<curve>_check_point` keeps `s0` and `ra`: slot 2. -/
def checkSave : Nat := c.sl TMP

/-- `vg_<curve>_check_point(ws = a0)`. -/
def checkFn : Prog isa :=
  .seq (.block [.store .d .s0 .a0 (checkSave c), .store .d .ra .a0 (checkSave c + 8), .addi .s0 .a0 0]) <|
  .seq (.block (ltMask c.n (c.sl CX) (c.sl MP) ++ andFlag c ++ ltMask c.n (c.sl CY) (c.sl MP) ++ andFlag c)) <|
  .seq (mulCall c.FP (c.sl CXM) (c.sl CX) (c.sl R2P)) <|
  .seq (mulCall c.FP (c.sl CYM) (c.sl CY) (c.sl R2P)) <|
  .seq (fprog c.FP (curveOps c)) <|
  .block (zeroMask c.n (c.sl W1) ++ andFlag c ++ [.load .d .a7 wb (c.sl FLAG)] ++
    sel c.n (c.sl CPX) (c.sl GX) (c.sl CXM) ++ sel c.n (c.sl CPY) (c.sl GY) (c.sl CYM) ++
    [.load .d .ra .s0 (checkSave c + 8), .load .d .s0 .s0 (checkSave c)])

end Cfg

/-! ## Numbers as bytes, and constants -/

/-- `[o] = ` the `n`-word big-endian number at `p + off` (`8 n` bytes), a
doubleword at a time through `t0` and `t1`, from its most significant. -/
def loadNum : Nat → Nat → Reg → Nat → List Instr
  | 0, _, _, _ => []
  | k + 1, o, p, off =>
    Impl.Words.RISCV64.loadBE64 .t0 .t1 p off ++ [.store .d .t0 wb (o + 8 * k)] ++ loadNum k o p (off + 8)

/-- The `n`-word number at `a` under the mask `a7`, to `q + off` big-endian,
through `t0` and `t1`, from its most significant word. -/
def storeNum : Nat → Nat → Reg → Nat → List Instr
  | 0, _, _, _ => []
  | k + 1, a, q, off =>
    [.load .d .t0 wb (a + 8 * k), .logic .and .t0 .t0 .a7] ++ Impl.Words.RISCV64.storeBE 8 .t0 .t1 q off ++
      storeNum k a q (off + 8)

/-- `[o] = x mod 2^(64 n)`, `n` words, from immediates through `t0` and `t1`. -/
def setConst : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, o, x =>
    Impl.Words.RISCV64.li64 .t0 .t1 (BitVec.ofNat 64 x) ++ [.store .d .t0 wb o] ++ setConst k (o + 8) (x >>> 64)

/-- The mask `a7` of the byte at `[q]` being `04`, through `t0`: all ones iff
`byte ^ 4 = 0`, the top bit of `(byte ^ 4) - 1`, negated. -/
def leadMask (q : Reg) : List Instr :=
  [.load .b .t0 q 0, .logicImm .xor .t0 .t0 4, .addi .t0 .t0 (-1), .shift .srl .d .t0 .t0 63, .li .t1 0,
    .sub .a7 .t1 .t0]

/-- Slots ECDH and the public key add: `n`, `p - 2`, the result's
coordinates. -/
def MN := 1
def EXPP := 12
def XM := 17
def XO := 18
def YM := 19
def YO := 20

namespace Cfg

variable (c : Cfg)

/-- `x R mod p`. -/
def mont (x : Nat) : Nat := x * 2 ^ (64 * c.n) % c.C.p

/-- The constants: slots and values. -/
def consts : List (Nat × Nat) :=
  [(MP, c.C.p), (MN, c.C.n), (ZERO, 0), (ONE, 1), (ONEP, mont c 1), (AP, mont c c.C.a),
    (B3P, mont c (3 * c.C.b)), (GX, mont c c.C.gx), (GY, mont c c.C.gy), (EXPP, c.C.p - 2),
    (R2P, 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.p), (BP, mont c c.C.b)]

def constCode : List Instr := (consts c).flatMap fun (i, x) => setConst c.n (c.sl i) x

/-- The saves, at `[a]`, and `out` (`a0`) to `s2`, the working space to `s0`. -/
def saveCode (a : Reg) : List Instr :=
  [.store .d .s0 a 0, .store .d .s1 a 8, .store .d .s2 a 16, .store .d .ra a 24, .addi .s0 a 0,
    .addi .s2 .a0 0]

/-- The registers restored. -/
def restoreCode : List Instr :=
  [.load .d .ra .s0 24, .load .d .s2 .s0 16, .load .d .s1 .s0 8, .load .d .s0 .s0 0]

/-- `d` in `[1, n-1]`: the flag `&=` the masks of `d < n` and `d ≠ 0`. -/
def rangeCode : List Instr :=
  ltMask c.n (c.sl K) (c.sl MN) ++ andFlag c ++ zeroMask c.n (c.sl K) ++ [.logicImm .xor .a7 .a7 (-1)] ++
    andFlag c

/-- The power `Z^(p-2)`, into `ACC`. -/
def powP : PowCfg := ⟨c.MP', c.sl ACC, c.sl PT, c.sl RZ, c.sl ONEP, c.sl EXPP, 64 * c.n⟩

/-- A call of `f`, whose code is `body`, on the working space. -/
def wsCall (f : String) (body : Prog isa) : Prog isa := .seq (.block [.addi .a0 wb 0]) (.call f body)

/-- `[o] = [a] Z^(p-2)` out of Montgomery's form, through `t`. -/
def affineCoord (t o a : Nat) : Prog isa :=
  .seq (mulCall c.FP (c.sl t) (c.sl a) (c.sl ACC)) (mulCall c.FP (c.sl o) (c.sl t) (c.sl ONE))

/-- What follows the point's setup: the range of `d`, `R = [d]P` (`mul`, its
code `mulCode`), `Z^(p-2)`, and `x`. -/
def tail (mulName : String) (mulCode : Prog isa) : Prog isa :=
  .seq (.block (rangeCode c)) <|
  .seq (wsCall mulName mulCode) <|
  .seq (pow (powP c) c.FP) (affineCoord c XM XO RX)

/-- The flag `&=` the mask of `Z ≠ 0`, and the flag to `a7`. -/
def zCode : List Instr :=
  zeroMask c.n (c.sl RZ) ++ [.logicImm .xor .a7 .a7 (-1)] ++ andFlag c ++ [.load .d .a7 wb (c.sl FLAG)]

/-- The flag's low bit to `a0`, and the registers restored. -/
def retCode : List Instr := [.load .d .a0 wb (c.sl FLAG), .logicImm .and .a0 .a0 1] ++ restoreCode

/-- `vg_ecdh_<curve>(out = a0, d = a1, peer = a2, scratch = a3)`. -/
def ecdhFn (checkName mulName : String) (checkCode mulCode : Prog isa) : Prog isa :=
  .seq (.block (saveCode .a3 ++ loadNum c.n (c.sl K) .a1 0 ++ loadNum c.n (c.sl CX) .a2 1 ++
    loadNum c.n (c.sl CY) .a2 (1 + 8 * c.n) ++ leadMask .a2 ++ [.store .d .a7 wb (c.sl FLAG)] ++ constCode c)) <|
  .seq (wsCall checkName checkCode) <|
  .seq (.block (copy c.n (c.sl RX) (c.sl CPX) ++ copy c.n (c.sl RY) (c.sl CPY))) <|
  .seq (tail c mulName mulCode) <|
  .block (zCode c ++ storeNum c.n (c.sl XO) .s2 0 ++ retCode c)

/-- `vg_ec_<curve>_public_key(out = a0, d = a1, scratch = a2)`. -/
def publicKeyFn (mulName : String) (mulCode : Prog isa) : Prog isa :=
  .seq (.block (saveCode .a2 ++ loadNum c.n (c.sl K) .a1 0 ++
    [.li .t0 0, .addi .t0 .t0 (-1), .store .d .t0 wb (c.sl FLAG)] ++ constCode c ++
    copy c.n (c.sl RX) (c.sl GX) ++ copy c.n (c.sl RY) (c.sl GY))) <|
  .seq (tail c mulName mulCode) <|
  .seq (affineCoord c YM YO RY) <|
  .block (zCode c ++ [.li .t0 4, .logic .and .t0 .t0 .a7, .store .b .t0 .s2 0] ++
    storeNum c.n (c.sl XO) .s2 1 ++ storeNum c.n (c.sl YO) .s2 (1 + 8 * c.n) ++ retCode c)

end Cfg

end VG.Impl.Ecdh.RISCV64
