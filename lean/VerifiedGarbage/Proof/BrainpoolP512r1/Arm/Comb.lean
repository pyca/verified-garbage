module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombI
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmComb
import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.BrainpoolP512r1.Comb7
import VerifiedGarbage.Proof.BrainpoolP512r1.Comb7Shape
import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP512r1
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# brainpoolP512r1's seven-bit comb on 32-bit ARM

Its layout (the comb with the addition inlined, on the signature's: the
ladder's `R`, `a`, `3b` and table of bits, the entry in its `T`, the sum and
`-y` in its `D`, zero at `ZERO`), the configuration the comb's proof takes,
and the memory of satisfiable contracts with its table: the table at 1 MiB,
the working space at zero.
-/

@[expose] public section
namespace VG.Proof.BrainpoolP512r1.Arm
open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm VG.Impl.BrainpoolP512r1
open VG.Impl.Ecdsa.Arm (GX GY)
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.BrainpoolP512r1

theorem comb_layout (u : Bool := false) : LayoutI (brainpoolp512r1CombWith u) where
  lad := pLadLay (px := GX) (py := GY) (brainpoolp512r1With_ok u) (by decide)
  wk := pLadWk (px := GX) (py := GY) (brainpoolp512r1With_ok u) (by decide)
  qT := by cases u <;> rfl
  negD := rfl
  zeroLe := by decide +revert
  zeroW := by decide +kernel +revert
  apart := ⟨by decide +kernel +revert, by decide +kernel +revert⟩

set_option exponentiation.threshold 512 in
theorem comb_config (hC : Law Spec.BrainpoolP512r1.curve) (u : Bool := false) :
    ConfigI (brainpoolp512r1CombWith u) Spec.BrainpoolP512r1.curve comb7 comb7Start where
  layout := comb_layout u
  fieldK := rfl
  fieldM := rfl
  modulus := Mont.brainpoolp512r1p_ok
  unit := unitMod_pow_two (by decide +kernel +revert) _
  tables := VG.Proof.BrainpoolP512r1.combOk7 hC
  one_lt := by decide +kernel +revert
  one := toM_one (unitMod_pow_two (by decide +kernel +revert) _)
  startX := rfl
  startY := rfl
  w1 := by decide +revert
  w9 := by decide +revert
  J1 := by decide +revert
  J32 := by decide +revert
  startBits := by decide +revert
  coverBits := by decide +revert
  bitsLow := by decide +revert
  bitsHigh := by decide +revert
  bitsFit := by decide +revert
  windowFit := by decide +revert
  encJ := by decide +revert
  encLast := by decide +revert
  encRow := by decide +revert
  encEntry := by decide +revert
  encH := by decide +revert

set_option exponentiation.threshold 512 in
theorem comb_words_length : brainpoolp512r1CombWords.length=75776 := by
  unfold brainpoolp512r1CombWords
  rw [VG.Proof.Weierstrass.tcombWords_length (H := 64) VG.Proof.BrainpoolP512r1.comb7_length
    VG.Proof.BrainpoolP512r1.comb7_rows]

/-- The memory of the witnesses with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def combSatMem : Mem := constMem 0x100000 brainpoolp512r1CombWords

theorem combSat_held : ∀ i<brainpoolp512r1CombWords.length,
    combSatMem.readW (0x100000+BitVec.ofNat 64 (8*i)) 64=brainpoolp512r1CombWords.getD i 0 :=
  by
    unfold combSatMem
    exact constMem_held _ _ (by rw [comb_words_length]; decide)

def combSatState : State where
  gpr r := match r with
    | .r0 => 0x10000 | .r1 => 0x12000 | .r2 => 0x14000 | .r3 => 0x16000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem := combSatMem
  rd := [⟨0x12000,64⟩,⟨0x14000,64⟩,⟨0x16000,64⟩,⟨0x20000,4⟩,⟨0x100000,606208⟩]
  wr := [⟨0x10000,128⟩,⟨0,8192⟩]
  syms _ := 0x100000

end VG.Proof.BrainpoolP512r1.Arm
