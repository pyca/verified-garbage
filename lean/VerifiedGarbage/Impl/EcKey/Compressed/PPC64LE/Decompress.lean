module

public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE
public import VerifiedGarbage.Impl.EcKey.PPC64LE
public import VerifiedGarbage.Spec.Weierstrass

/-!
# SEC 1 point decompression on PPC64LE

`vg_ec_<curve>_decompress_public_key(out, public, scratch) -> r3` (ELFv2:
the arguments in `r3`–`r5`), from the code of ECDH and the public key, as on
32-bit ARM (`Impl/EcKey/Compressed/Arm/Decompress.lean`):

1. `public` to `r12` and the signature's setup (`setup`);
2. `R² mod p` and `b R mod p` to their slots, `x` (from `public + 1`) to the
   hash's slot, the tag to `D`'s first word, and into the flag the masks of
   the tag being `02` or `03` and `x < p`;
3. `x³ + a x + b`, in Montgomery form, to `W2`;
4. a square root's candidate, in Montgomery form, to `ACC`: `rhs^((p+1)/4)`
   for `p ≡ 3 mod 4`, else Tonelli and Shanks's descent, with
   `p - 1 = q 2⁹⁶` (P-224), its counters in `r31`, which the calls keep: the
   round's (from 95 down) in the high word, the squarings' in the low one;
5. the candidate out of Montgomery form, and it or `p` minus it, by the
   tag's parity, to `QY`;
6. into the flag the masks of `y² = rhs` and of `y`'s parity being the
   tag's;
7. `04 ‖ x ‖ y` (or zeros, by the flag) to `out`, and the flag's low bit
   returned.

Everything is computed whatever the flag; the loops run a fixed number of
times.
-/

@[expose] public section
namespace VG.Impl.EcKey.Compressed.PPC64LE

open VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass
open VG.Impl.Ecdsa.PPC64LE
open VG.Impl.Ecdh.PPC64LE (R2P BP QXM QYM QY W0 W1 W2 W3)

/-- The odd part `q` of `p - 1 = q 2⁹⁶`, for the descent. -/
def rootQ (c : Cfg) : Nat := (c.C.p - 1) / 2 ^ 96

/-- The tag (the byte `r12` points to) to `D`'s first word, and the mask
`r5` of it being `02` or `03` (all ones iff `(tag | 1) ^ 3 = 0`), through
`r4`. -/
def decompressTag (c : Cfg) : List Instr :=
  [.lbz .r4 .r12 0, .store .d .r4 wb (c.sl D), .li .r5 1, .logic .or .r4 .r4 .r5, .li .r5 3,
    .logic .xor .r4 .r4 .r5, .subi .r4 .r4 1, .lsr .d .r4 .r4 63, .li .r5 0, .sub .r5 .r5 .r4]

/-- The constants, `x` (through `r6`, from `public + 1`), the tag, and the
checks of the tag and `x`. -/
def decompressPeer (c : Cfg) : List Instr :=
  (Ecdh.PPC64LE.Cfg.consts c).flatMap (fun (i, x) => VG.Impl.Mont.PPC64LE.setConst c.n (c.sl i) x) ++
  ([.addi .r6 .r12 1] : List Instr) ++ loadBytes c.C.len c.n (c.sl E) .r6 ++
  decompressTag c ++ c.andFlag ++ Ecdh.PPC64LE.Cfg.checkLtP c (c.sl E)

/-- `x R` to `QXM`, and `x³ + a x + b`, in Montgomery form, to `W2`. -/
def rhsOps (c : Cfg) : List FOp :=
  [.mul (c.sl QXM) (c.sl E) (c.sl R2P),
    .mul (c.sl W1) (c.sl QXM) (c.sl QXM), .mul (c.sl W2) (c.sl W1) (c.sl QXM),
    .mul (c.sl W1) (c.sl AP) (c.sl QXM), .add (c.sl W3) (c.sl W2) (c.sl W1),
    .add (c.sl W2) (c.sl W3) (c.sl BP)]

/-- The power of `W2` to `ACC`, with the bits of its exponent in table
`table`. -/
def rootPow (c : Cfg) (table : Nat) : PowCfg :=
  ⟨c.MP', c.sl ACC, c.sl PT, c.sl W2, c.sl ONEP, bitsAt c.n table, 64 * c.n⟩

/-- `ACC = W2^e`: `e` to `EXPP`, its bits to table `table`, and the power. -/
def rootPower (c : Cfg) (e table : Nat) : Prog isa :=
  progs [.block (VG.Impl.Mont.PPC64LE.setConst c.n (c.sl EXPP) e),
    bits (c.sl EXPP) (bitsAt c.n table) (8 * c.n), pow (rootPow c table) c.SP]

/-- One squaring of `T3`, and the low word of `r31` decremented. -/
def squareStep (c : Cfg) : Prog isa :=
  .seq (mulCall c.SP (c.sl T3) (c.sl T3) (c.sl T3)) (.block [decCounter])

/-- `T3` squared as many times as the low word of `r31`, which ends zero. -/
def squarePower (c : Cfg) : Prog isa :=
  .ite (.zero .w .r31) (.block []) (.loop (squareStep c) (.nonzero .w .r31))

/-- `T3 = T0`, and `j - 1` to the low word of `r31`, for the round's `j`
in its high word (through `r4`). -/
def descentStart (c : Cfg) : List Instr :=
  copy c.n (c.sl T3) (c.sl T0) ++ [.lsr .d .r4 .r31 32, .subi .r4 .r4 1, .logic .or .r31 .r31 .r4]

/-- `T3 = T0^(2^(j-1))`. -/
def descentPower (c : Cfg) : Prog isa := .seq (.block (descentStart c)) (squarePower c)

/-- The mask `r5` of `[a] = 0`, through `r4`. -/
def zeroMask (c : Cfg) (a : Nat) : List Instr :=
  c.nonzero a ++ [.li .r4 0, .sub .r5 .r4 .r5, .subi .r5 .r5 1]

/-- `T4 = 1` (in Montgomery form) if `T3 = 1`, else `T1`. -/
def descentChoose (c : Cfg) : Prog isa :=
  .seq (subCall c.SP (c.sl W0) (c.sl T3) (c.sl ONEP))
    (.block (zeroMask c (c.sl W0) ++ [mov .r10 .r5] ++ sel c.n (c.sl T4) (c.sl T1) (c.sl ONEP)))

/-- `r = r b`, `t = t b²`, `c = c²`. -/
def descentOps (c : Cfg) : List FOp :=
  [.mul (c.sl ACC) (c.sl ACC) (c.sl T4), .mul (c.sl T4) (c.sl T4) (c.sl T4),
    .mul (c.sl T0) (c.sl T0) (c.sl T4), .mul (c.sl T1) (c.sl T1) (c.sl T1)]

/-- The round's counter, the high word of `r31`, decremented (through
`r4`). -/
def descentCounter : List Instr := [.li .r4 1, .lsl .r4 .r4 32, .sub .r31 .r31 .r4]

/-- A round of the descent. -/
def descentRound (c : Cfg) : Prog isa :=
  progs [descentPower c, descentChoose c, fprog c.SP (descentOps c), .block descentCounter]

/-- `T5 = W2^((q+1)/2)` and `ACC = W2^q`. -/
def tonelliPowers (c : Cfg) : Prog isa :=
  progs [rootPower c ((rootQ c + 1) / 2) 1,
    .block (copy c.n (c.sl T5) (c.sl ACC)), rootPower c (rootQ c) 2]

/-- `T0 = t = W2^q`, `ACC = r = W2^((q+1)/2)`, `T1 = c = z^q` for the
nonresidue `z = 11`, and the round's counter 95 in `r31`'s high word. -/
def tonelliSetup (c : Cfg) : List Instr :=
  let zq := (Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)).val
  copy c.n (c.sl T0) (c.sl ACC) ++ copy c.n (c.sl ACC) (c.sl T5) ++
  VG.Impl.Mont.PPC64LE.setConst c.n (c.sl T1) (c.mont zq) ++ [.li .r31 95, .lsl .r31 .r31 32]

/-- The square root's candidate, in Montgomery form, to `ACC`. -/
def rootCandidate (c : Cfg) : Prog isa :=
  if c.C.p % 4 = 3 then rootPower c ((c.C.p + 1) / 4) 2
  else progs [tonelliPowers c, .block (tonelliSetup c), .loop (descentRound c) (.nonzero .d .r31)]

/-- The mask `r10` of `QY`'s parity differing from the tag's (in `D`),
through `r4` and `r5`. -/
def parityMask (c : Cfg) : List Instr :=
  [.load .d .r4 wb (c.sl QY), .load .d .r5 wb (c.sl D), .logic .xor .r5 .r5 .r4, .li .r4 1,
    .logic .and .r5 .r5 .r4, .li .r4 0, .sub .r10 .r4 .r5]

/-- The candidate out of Montgomery form to `QY`, `p` minus it to `W0`, and
`QY` the one of the tag's parity. -/
def selectRoot (c : Cfg) : Prog isa :=
  progs [mulCall c.SP (c.sl QY) (c.sl ACC) (c.sl ONE),
    subCall c.SP (c.sl W0) (c.sl ZERO) (c.sl QY),
    .block (parityMask c ++ sel c.n (c.sl QY) (c.sl QY) (c.sl W0))]

/-- `y² - rhs`, in Montgomery form, to `W3`. -/
def checkRootOps (c : Cfg) : List FOp :=
  [.mul (c.sl QYM) (c.sl QY) (c.sl R2P), .mul (c.sl W1) (c.sl QYM) (c.sl QYM),
    .sub (c.sl W3) (c.sl W1) (c.sl W2)]

/-- The mask `r5` of `r10` being zero, `-(r10 + 1)`, through `r4`. -/
def invertMask : List Instr := [.addi .r5 .r10 1, .li .r4 0, .sub .r5 .r4 .r5]

/-- Into the flag, the masks of `W3 = 0` and of `QY`'s parity being the
tag's. -/
def checkRootChecks (c : Cfg) : List Instr :=
  Ecdh.PPC64LE.Cfg.checkZero c (c.sl W3) ++ (parityMask c ++ (invertMask ++ c.andFlag))

/-- The checks of the root. -/
def checkRoot (c : Cfg) : Prog isa :=
  .seq (fprog c.SP (checkRootOps c)) (.block (checkRootChecks c))

/-- `04 ‖ x ‖ y` (or zeros) to `out`, the flag's low bit to `r3`, and the
callee-saved registers restored. -/
def decompressFinish (c : Cfg) : List Instr := EcKey.PPC64LE.Cfg.finishWith c E QY

/-- The root, its sign and its checks. -/
def recoverCoordinate (c : Cfg) : Prog isa :=
  .seq (rootCandidate c) (.seq (selectRoot c) (checkRoot c))

/-- `vg_ec_<curve>_decompress_public_key`. -/
def decompress (c : Cfg) : Prog isa :=
  progs [.block (setup c), .block (decompressPeer c), fprog c.SP (rhsOps c),
    recoverCoordinate c, .block (decompressFinish c)]

end VG.Impl.EcKey.Compressed.PPC64LE
