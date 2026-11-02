module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mul

/-!
# Short Weierstrass curves on RISC-V: the working space, and `vg_<curve>_mul`

The layout of the working space that the RISC-V code of a curve shares (as
PPC64LE's, `Impl/Ecdsa/PPC64LE.lean`, and the one
`Proof/Weierstrass/MulContract.lean` states): numbers of `n` 64-bit words in slots
from byte 64 (`slot n i`), the field arithmetic's functions' own working
space at the end of the first 4096 bytes. A curve as the code has it
(`Cfg`): its words, its parameters, and the functions of its field.

`vg_<curve>_mul(ws)`: `R = [k]Q` (`Proof/Weierstrass/MulContract.lean`) by the ladder
of `Impl/Weierstrass/RISCV64.lean`, from `R = O = (0 : 1 : 0)` and the point
at `ACC`, `PT`, `ONEP` (a copy of `Q`, which the contract has in `R`'s first
two slots), over the bits of `k` at `K`'s slot. It keeps the callee-saved
registers it uses (`s0`, the working space's base, and `s1`, the counter)
and the return address past the numbered slots (`mulSave`, slot 45's place,
the start of the contract's tail), and returns with every callee-saved
register as it was.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64

open VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64

/-- Byte offset of slot `i` of numbers of `n` words. -/
def slot (n i : Nat) : Nat := 64 + 8 * n * i

/-! Slot numbers, as on PPC64LE. -/
def MP := 0
def TMP := 2
def ZERO := 3
def ONE := 4
def ONEP := 5
def AP := 6
def B3P := 7
def GX := 8
def GY := 9
def RX := 14
def RY := 15
def RZ := 16
def DX := 17
def DY := 18
def DZ := 19
def TX := 20
def TY := 21
def TZ := 22
def T0 := 23
def T1 := 24
def T2 := 25
def T3 := 26
def T4 := 27
def T5 := 28
def ACC := 29
def PT := 30
def K := 31
/-- The number of slots. -/
def nslots := 45

/-- A curve as the code has it: `n` words, its parameters, and the functions
of its arithmetic modulo `p`. -/
structure Cfg where
  n : Nat
  C : Spec.Weierstrass.Curve
  FP : Field
  /-- `-p⁻¹ mod 2⁶⁴`, which no code here reads (`Mod`'s). -/
  minv : Nat := 0

namespace Cfg

variable (c : Cfg)

def sl (i : Nat) : Nat := slot c.n i

def MP' : Mod := { n := c.n, mo := c.sl MP, tmp := c.sl TMP, minv := BitVec.ofNat 64 c.minv }

def pt (x y z : Nat) : Pt := ⟨c.sl x, c.sl y, c.sl z⟩

def rcbSlots : RcbSlots := ⟨c.sl AP, c.sl B3P, c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5⟩

/-- The ladder over every bit of the `n` words at `K`'s slot, from the
point at `ACC`, `PT`, `ONEP`. -/
def mulLadder : LadderCfg where
  M := c.MP'
  S := c.rcbSlots
  G := c.pt ACC PT ONEP
  R := c.pt RX RY RZ
  D := c.pt DX DY DZ
  T := c.pt TX TY TZ
  bits := c.sl K
  nbits := 64 * c.n

/-- Where `vg_<curve>_mul` keeps `s0`, `s1` and `ra`: past the numbered
slots. -/
def mulSave : Nat := c.sl nslots

/-- `vg_<curve>_mul`'s body: `Q` (in `R`'s first two slots) copied to `ACC`
and `PT`, `R = O = (0 : 1 : 0)` (from zero and one), then `R = [k]Q` by the
ladder. -/
def mulBody : Prog isa :=
  .seq (.block (copy c.n (c.sl ACC) (c.sl RX) ++ copy c.n (c.sl PT) (c.sl RY) ++
    copy c.n (c.sl RX) (c.sl ZERO) ++ copy c.n (c.sl RY) (c.sl ONEP) ++ copy c.n (c.sl RZ) (c.sl ZERO)))
    (ladder c.mulLadder c.FP)

/-- `vg_<curve>_mul(ws = a0)`: `s0`, `s1` and `ra` kept around the body,
with the working space's base in `s0`. -/
def mulFn : Prog isa :=
  .seq (.block (sdAt .s0 .a0 c.mulSave ++ sdAt .s1 .a0 (c.mulSave + 8) ++ sdAt .ra .a0 (c.mulSave + 16) ++
    [.addi .s0 .a0 0])) <|
  .seq c.mulBody (.block (ldAt .ra .s0 (c.mulSave + 16) ++ ldAt .s1 .s0 (c.mulSave + 8) ++
    ldAt .s0 .s0 c.mulSave))

end Cfg

end VG.Impl.Ecdsa.RISCV64
