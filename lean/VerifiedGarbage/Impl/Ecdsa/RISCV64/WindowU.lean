module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.WindowA
public import VerifiedGarbage.Impl.Weierstrass.RISCV64.P521Unsat
public import VerifiedGarbage.Spec.P521

/-!
# `[k]Q` by four-bit windows on RISC-V, for P-521, in 58-bit limbs

`vg_p521_mul(ws)` as `Impl/Ecdsa/RISCV64/WindowA.lean` computes it for P-521
(the layout of `Impl/Ecdsa/P521/RISCV64.lean`'s `p521w`, the doublings `dblJ` for `a = -3`, the complete addition
`rcb` for any `a`), but with the field arithmetic of
`Impl/Weierstrass/RISCV64/P521Unsat.lean` (`P521Unsat.field`), on elements
of nine 58-bit limbs equal modulo `p` to what they stand for:

1. `a`, `3 b` and one, which the contract's caller provides in Montgomery's
   form at `AP`, `B3P` and `ONEP` and which the function may not write, and
   `Q` at `RX`, `RY`, to limbs (`toU`): unpacked, and multiplied by
   `2⁴⁶⁶ ≡ 2⁻⁵⁵`, since `R = 2⁵⁷⁶ ≡ 2⁵⁵` (`UC` holds the constant), into
   `UA`, `UB`, `UONE` and in place;
2. the table and the windows of `WindowA`, on those slots: with `Y = 1`
   where `Z` is zero, for `Z`'s residue packed into `T0` (`quad`);
3. `R` back in Montgomery's form (`fromU`): multiplied by `2⁵⁵` and packed.

The only branch is on the counter, and the field functions' on the pointers;
every address is `s0` plus a constant, plus `8 (j >>> 4)` for the nibble's
word.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.WindowU

open VG.RISCV64 VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Impl.Ecdsa.RISCV64.Window (windows)
open VG.Impl.Ecdsa.RISCV64.WindowA.Cfg (copyPt zeroPt select)

/-- The layout: P-521's for its windows, `p521w`'s (the table at 4096, `E`
in slots 46 to 48). -/
abbrev c : Cfg := { n := 9, C := Spec.P521.curve, FP := P521Unsat.field, jt := 4096, ve := 46, am3 := false }

/-! The slots of `a`, `3 b` and one in limbs, and of the conversions'
constant, past `E`'s. -/
def UA : Nat := 49
def UB : Nat := 50
def UONE : Nat := 51
def UC : Nat := 52

/-- The field's functions. -/
abbrev F : Field := P521Unsat.field

/-- The slots of the additions and doublings: `a` and `3 b` in limbs. -/
def S : RcbSlots := { c.rcbSlots with a := c.sl UA, b3 := c.sl UB }

/-- `o = p + q` by the complete addition for any `a`. -/
def addPt (p q o : Pt) : Prog isa := fprog F (rcb S p q o)

/-- `[e + 2]Q = [e + 1]Q + Q` in `T` from `D`, stored, and `D = T`, for
`e` from 0 up to `e`. -/
def adds : Nat → Prog isa
  | 0 => .block []
  | e + 1 => .seq (adds e) <|
    .seq (addPt (c.pt DX DY DZ) (c.pt RX RY UONE) (c.pt TX TY TZ))
      (.block (Verify.Cfg.storePt c (e + 2) (c.pt TX TY TZ) ++ copyPt c (c.pt DX DY DZ) (c.pt TX TY TZ)))

/-- The table: `O`, `Q`, then `[e]Q` for `e = 2 … 15`. -/
def build : Prog isa :=
  .seq (.block (Verify.Cfg.storePt c 0 (c.pt ZERO UONE ZERO) ++ Verify.Cfg.storePt c 1 (c.pt RX RY UONE) ++
    copyPt c (c.pt DX DY DZ) (c.pt RX RY UONE))) (adds 14)

/-- `[o] = [a]`'s residue, packed. -/
def packCall (o a : Nat) : Prog isa := callOp (F.S.fn "pack") P521Unsat.packFn P521Unsat.packFn o a 0

/-- `[o] = [a]`'s limbs. -/
def unpackCall (o a : Nat) : Prog isa := callOp (F.S.fn "unpack") P521Unsat.unpackFn P521Unsat.unpackFn o a 0

/-- `R = 16 R`: to Jacobian coordinates in `D`, four doublings between `D`
and `T`, back to `R`, then `Y = 1` where `Z`'s residue, packed into `T0`, is
zero. -/
def quad : Prog isa :=
  let R := c.pt RX RY RZ
  let D := c.pt DX DY DZ
  let T := c.pt TX TY TZ
  progs [fprog F (toJ S R (zeroPt c) D), fprog F (dblJ S D T), fprog F (dblJ S T D),
    fprog F (dblJ S D T), fprog F (dblJ S T D), fprog F (fromJ S D (zeroPt c) R), packCall (c.sl T0) (c.sl RZ),
    .block (Ecdh.RISCV64.zeroMask c.n (c.sl T0) ++ sel c.n (c.sl RY) (c.sl RY) (c.sl UONE))]

/-- One window: `s1 -= 1`, the entry `E` of the nibble, `R = 16 R`, and
`R = R + E`. -/
def step : Prog isa :=
  .seq (.block (decCounter :: select c)) <|
  .seq quad <|
  .seq (addPt (c.pt RX RY RZ) (c.pt c.EX c.EY c.EZ) (c.pt TX TY TZ))
    (.block (copyPt c (c.pt RX RY RZ) (c.pt TX TY TZ)))

/-- The body: the table, `R = O`, then the windows. -/
def body : Prog isa :=
  .seq build <|
  .seq (.block (copyPt c (c.pt RX RY RZ) (c.pt ZERO UONE ZERO) ++ [.li ctr (windows c)]))
    (.loop step more)

/-- `UC = v 2⁶⁴ʲ`, for `v < 2¹¹`: zero copied in, then the word `j`. -/
def setC (j : Nat) (v : List Instr) : List Instr :=
  copy 9 (c.sl UC) (c.sl ZERO) ++ v ++ sdAt .t0 wb (c.sl UC + 8 * j)

/-- `UC = 2⁴⁶⁶` in limbs: limb 8 is 4. -/
def setIn : List Instr := setC 8 [.li .t0 4]

/-- `UC = 2⁵⁵` in limbs. -/
def setOut : List Instr := setC 0 [.li .t0 1, .shift .sll .d .t0 .t0 55]

/-- `[o]` = the limbs of `[a]`, a number in Montgomery's form, times `2⁻⁵⁵`
(the constant at `UC`). -/
def toU (o a : Nat) : Prog isa := .seq (unpackCall o a) (mulCall F o o (c.sl UC))

/-- `[o]` = the limbs at `o` times `2⁵⁵` (the constant at `UC`), packed: the
number in Montgomery's form. -/
def fromU (o : Nat) : Prog isa := .seq (mulCall F o o (c.sl UC)) (packCall o o)

/-- In: `Q`, one, `a` and `3 b` to limbs. -/
def convIn : Prog isa :=
  .seq (.block setIn) <|
  progs [toU (c.sl RX) (c.sl RX), toU (c.sl RY) (c.sl RY), toU (c.sl UONE) (c.sl ONEP), toU (c.sl UA) (c.sl AP),
    toU (c.sl UB) (c.sl B3P)]

/-- Out: `R` to Montgomery's form. -/
def convOut : Prog isa :=
  .seq (.block setOut) (progs [fromU (c.sl RX), fromU (c.sl RY), fromU (c.sl RZ)])

/-- `vg_p521_mul(ws = a0)`: `s0`, `s1` and `ra` kept around the body, as
`WindowA.Cfg.mulFn` does, with the working space's base in `s0`. -/
def mulFn : Prog isa :=
  .seq (.block (sdAt .s0 .a0 c.mulSave ++ sdAt .s1 .a0 (c.mulSave + 8) ++ sdAt .ra .a0 (c.mulSave + 16) ++
    [.addi .s0 .a0 0])) <|
  .seq convIn <| .seq body <| .seq convOut
    (.block (ldAt .ra .s0 (c.mulSave + 16) ++ ldAt .s1 .s0 (c.mulSave + 8) ++ ldAt .s0 .s0 c.mulSave))

end VG.Impl.Ecdsa.RISCV64.WindowU
