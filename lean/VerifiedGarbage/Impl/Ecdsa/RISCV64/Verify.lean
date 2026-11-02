module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Sign
public import VerifiedGarbage.Impl.Ecdh.P256.RISCV64

/-!
# ECDSA signature verification on RISC-V

`vg_ecdsa_<curve>_verify(public, digest, sig, scratch) -> a0`
(`Spec/Ecdsa/Verify/Generic.lean`), for a curve whose `n` has `64 n` bits,
with the pieces of ECDH (`Impl/Ecdh/RISCV64.lean`) and of signing
(`Impl/Ecdsa/RISCV64/Sign.lean`):

1. the registers saved, the public key's `x` and `y` read into the check's
   slots, the flag set to the mask of its first byte being `04`, the
   constants stored, `r`, `s` and the digest's `e` read (into slots the
   check keeps, before its call writes the argument registers), and the
   masks of `r` and `s` being in `[1, n-1]` anded into the flag;
2. the check of the key, by a call (`x < p`, `y < p` and the curve's
   equation into the flag; its point, or `G`, to `CPX` and `CPY`);
3. modulo `n`: `w = (s R)^(n-2)`, `u = e w` and `v = r w`, out of
   Montgomery's form;
4. `[u]G + [v]Q` by a joint ladder over two-bit windows of `u` and `v`
   (Straus): a table of the sixteen points `[a]G + [b]Q` (`a, b < 4`, entry
   `4 a + b`, `x`, `y` and `z` of `n` words each, `24 n` bytes) at `JT`, from
   `G`, `Q`, `2G`, `3G`, `2Q` and `3Q` in slots (`build`), by the complete
   addition; then from `R = O`, for the windows `j` from 127 down to 0 (the
   counter `s1`), the window's entry `4 u_j + v_j` selected from the sixteen
   without a secret address (the comb's tree of masks, `Comb.tree`, over
   entries at `a0 = s0 + JT`), and `R = 4 R + E` by three complete additions
   (`D = R + R`, `T = D + D`, `R = T + E`);
5. `Z^(p-2)` and `x = X Z^(p-2)`;
6. `x mod n` and `r mod n` (by additions of zero, both operands below `2n`),
   their difference modulo `n`, the masks of `Z ≠ 0` and of that difference
   being zero into the flag, whose low bit is returned.

Everything is computed whatever the flag, and only the pointers affect
timing, although the contract would let every input affect it.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.Verify

open VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdsa.RISCV64.Sign

/-! Slots: `e`, `r` and `s`, which the check keeps; `u` and `v`, in the
check's slots; and the values of the comparison. -/
def VE := 32
def VR := 10
def VS := 11
def UM := 22
def UU := 33
def VM := 24
def VV := 36
def XN := 19
def RN := 20
def WD := 21

/-! The joint ladder's slots, past the numbered ones but below byte 2048 (the
field's functions take offsets that `li` loads): `2G`, `3G`, `2Q`, `3Q`, and
the window's entry `E`; and the table's offset. -/
def G2X := 46
def G2Y := 47
def G2Z := 48
def G3X := 49
def G3Y := 50
def G3Z := 51
def Q2X := 52
def Q2Y := 53
def Q2Z := 54
def Q3X := 55
def Q3Y := 56
def Q3Z := 57
def EX := 58
def EY := 59
def EZ := 60
/-- The table's offset in the working space. -/
def JT : Nat := 2048
/-- The number of windows. -/
def NW : Nat := 128

namespace Cfg

variable (c : Cfg) (FN : Field)

/-- The saves, the public key's point and the flag, the constants, `r`, `s`
and `e`, and the masks of `r` and `s` in `[1, n-1]`. -/
def setup : List Instr :=
  Ecdh.RISCV64.Cfg.saveCode .a3 ++ loadNum c.n (c.sl CX) .a0 1 ++ loadNum c.n (c.sl CY) .a0 (1 + 8 * c.n) ++
    leadMask .a0 ++ sdAt .a7 wb (c.sl FLAG) ++ Ecdh.RISCV64.Cfg.constCode c ++
    loadNum c.n (c.sl VR) .a2 0 ++ loadNum c.n (c.sl VS) .a2 (8 * c.n) ++ loadNum c.n (c.sl VE) .a1 0 ++
    Ecdh.RISCV64.Cfg.rangeOf c VR ++ Ecdh.RISCV64.Cfg.rangeOf c VS

/-- `w = (s R)^(n-2)`, `u = e w` and `v = r w` modulo `n`. -/
def uv : Prog isa :=
  progs [mulCall FN (c.sl KM) (c.sl VS) (c.sl R2N), pow (Sign.Cfg.powN c) FN,
    mulCall FN (c.sl EM) (c.sl VE) (c.sl R2N), mulCall FN (c.sl UM) (c.sl EM) (c.sl ACC),
    mulCall FN (c.sl UU) (c.sl UM) (c.sl ONE), mulCall FN (c.sl RM) (c.sl VR) (c.sl R2N),
    mulCall FN (c.sl VM) (c.sl RM) (c.sl ACC), mulCall FN (c.sl VV) (c.sl VM) (c.sl ONE)]

/-- The bytes of an entry of the joint table. -/
def jb : Nat := 24 * c.n

/-- `[a6 + o] = [s0 + a]`, `k` 64-bit words, through `t0`. -/
def copyTo : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | k + 1, o, a => [.load .d .t0 wb a, .store .d .t0 .a6 o] ++ copyTo k (o + 8) (a + 8)

/-- `o = p + q` by the complete addition. -/
def addPt (p q o : Pt) : Prog isa := fprog c.FP (rcb c.rcbSlots p q o)

/-- The points `[a]G` and `[b]Q` (`a, b ∈ 1 … 3`) in slots. -/
def gPt : Nat → Pt
  | 1 => c.pt GX GY ONEP
  | 2 => c.pt G2X G2Y G2Z
  | _ => c.pt G3X G3Y G3Z

def qPt : Nat → Pt
  | 1 => c.pt CPX CPY ONEP
  | 2 => c.pt Q2X Q2Y Q2Z
  | _ => c.pt Q3X Q3Y Q3Z

/-- Entry `e` from the point `p` in slots. -/
def storePt (e : Nat) (p : Pt) : List Instr :=
  [.addi .a6 wb 2047, .addi .a6 .a6 1] ++ copyTo c.n (jb c * e) p.x ++
    copyTo c.n (jb c * e + 8 * c.n) p.y ++ copyTo c.n (jb c * e + 16 * c.n) p.z

/-- Entry `4 a + b` (`a, b ∈ 1 … 3`): `T = [a]G + [b]Q`, stored. -/
def mixed (a b : Nat) : Prog isa :=
  .seq (addPt c (gPt c a) (qPt c b) (c.pt TX TY TZ)) (.block (storePt c (4 * a + b) (c.pt TX TY TZ)))

/-- The table: `O`, `G` and `Q`; `2G`, `3G`, `2Q` and `3Q`, to their slots
and stored; then the nine entries of both. -/
def build : Prog isa :=
  .seq (.block (storePt c 0 (c.pt ZERO ONEP ZERO) ++ storePt c 4 (gPt c 1) ++ storePt c 1 (qPt c 1))) <|
  .seq (addPt c (gPt c 1) (gPt c 1) (gPt c 2)) <| .seq (.block (storePt c 8 (gPt c 2))) <|
  .seq (addPt c (gPt c 2) (gPt c 1) (gPt c 3)) <| .seq (.block (storePt c 12 (gPt c 3))) <|
  .seq (addPt c (qPt c 1) (qPt c 1) (qPt c 2)) <| .seq (.block (storePt c 2 (qPt c 2))) <|
  .seq (addPt c (qPt c 2) (qPt c 1) (qPt c 3)) <| .seq (.block (storePt c 3 (qPt c 3))) <|
  progs ((List.range 3).flatMap fun a => (List.range 3).map fun b => mixed c (a + 1) (b + 1))

/-- The window's entry number `4 u_j + v_j` into `t2`, for `j` in `s1`: the
two bits `2j`, `2j + 1` of `u` and of `v`, from their words `j >>> 5`. -/
def window : List Instr :=
  [.shift .srl .d .t1 ctr 5, .shift .sll .d .t1 .t1 3, .add .t1 .t1 wb,
   .load .d .t2 .t1 (c.sl UU), .load .d .t3 .t1 (c.sl VV),
   .shift .sll .d .t0 ctr 1, .shiftReg .srl .d .t2 .t2 .t0, .shiftReg .srl .d .t3 .t3 .t0,
   .logicImm .and .t2 .t2 3, .logicImm .and .t3 .t3 3,
   .shift .sll .d .t2 .t2 2, .logic .or .t2 .t2 .t3]

/-- Quadword `q` of the entry, selected by the masks of the entry number's
four bits from the sixteen at `a0`, to `E`'s word `q`. -/
def scanWord (q : Nat) : List Instr :=
  Comb.tree .a0 (jb c) 4 (8 * q) Comb.treeRegs ++ [.store .d .t0 wb (c.sl EX + 8 * q)]

/-- The window's entry to `E`: the number, the masks of its four bits, the
table's address in `a0`, and the `3 n` quadwords. -/
def select : List Instr :=
  window c ++ (List.range 4).flatMap Comb.Cfg.maskOfBit ++ [.addi .a0 wb 2047, .addi .a0 .a0 1] ++
    (List.range (3 * c.n)).flatMap (scanWord c)

/-- One step: `s1 -= 1`, the entry `E`, `D = R + R`, `T = D + D`, `R = T + E`. -/
def step : Prog isa :=
  .seq (.block (decCounter :: select c)) <|
  .seq (addPt c (c.pt RX RY RZ) (c.pt RX RY RZ) (c.pt DX DY DZ)) <|
  .seq (addPt c (c.pt DX DY DZ) (c.pt DX DY DZ) (c.pt TX TY TZ))
    (addPt c (c.pt TX TY TZ) (c.pt EX EY EZ) (c.pt RX RY RZ))

/-- `R = [u]G + [v]Q`: the table, `R = O`, then the steps. -/
def joint : Prog isa :=
  .seq (build c) <|
  .seq (.block (copy c.n (c.sl RX) (c.sl ZERO) ++ copy c.n (c.sl RY) (c.sl ONEP) ++ copy c.n (c.sl RZ) (c.sl ZERO) ++
    [.li ctr NW]))
    (.loop (step c) more)

/-- `x mod n`, `r mod n` and their difference. -/
def compare : Prog isa :=
  progs [addCall FN (c.sl XN) (c.sl XO) (c.sl ZERO), addCall FN (c.sl RN) (c.sl VR) (c.sl ZERO),
    subCall FN (c.sl WD) (c.sl XN) (c.sl RN)]

/-- The masks of `Z ≠ 0` and of the difference being zero into the flag, its
low bit returned, the registers restored. -/
def finish : List Instr :=
  Sign.Cfg.nonzeroFlag c RZ ++ zeroMask c.n (c.sl WD) ++ Ecdh.RISCV64.Cfg.andFlag c ++ Ecdh.RISCV64.Cfg.retCode c

/-- `vg_ecdsa_<curve>_verify(public = a0, digest = a1, sig = a2, scratch = a3)`,
with the check of the key `checkName` (its code `checkCode`). -/
def verify (checkName : String) (checkCode : Prog isa) : Prog isa :=
  .seq (.block (setup c)) <|
  .seq (Ecdh.RISCV64.Cfg.wsCall checkName checkCode) <|
  .seq (.block ((Sign.Cfg.nConsts c).flatMap (fun (i, x) => setConst c.n (c.sl i) x))) <|
  .seq (uv c FN) <|
  .seq (joint c) <|
  .seq (pow (Ecdh.RISCV64.Cfg.powP c) c.FP) <|
  .seq (Ecdh.RISCV64.Cfg.affineCoord c XM XO RX) <|
  .seq (compare c FN) (.block (finish c))

end Cfg

/-- `vg_ecdsa_p256_verify`. -/
def verifyP256 : Prog isa :=
  Cfg.verify p256 p256Order "vg_p256_check_point" Ecdh.RISCV64.checkP256

end VG.Impl.Ecdsa.RISCV64.Verify
