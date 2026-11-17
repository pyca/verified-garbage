module

public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConfig
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.ArmComb
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.BrainpoolP384r1.Comb7
import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP384r1
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# brainpoolP384r1's seven-bit comb on 32-bit ARM

Its layout (it reuses the ladder's accumulator and addition temporary), the
configuration the comb's proof takes, and the memory of satisfiable
contracts with its table: the table at 1 MiB, the working space at zero.
-/

@[expose] public section
namespace VG.Proof.BrainpoolP384r1.Arm
open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm VG.Impl.BrainpoolP384r1
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.TComb

theorem comb_layout (u : Bool := false) : Layout (brainpoolp384r1CombWith u) := by
  refine ⟨by decide +revert,by decide +revert,?_,?_,?_,?_,?_⟩
  · exact ⟨by decide +revert,by decide +revert⟩
  all_goals decide +kernel +revert

set_option exponentiation.threshold 512 in
theorem comb_config (hC : Law Spec.BrainpoolP384r1.curve) (u : Bool := false) :
    Config (brainpoolp384r1CombWith u) Spec.BrainpoolP384r1.curve comb7 comb7Start where
  layout := comb_layout u
  fieldK := rfl
  fieldM := rfl
  modulus := Mont.brainpoolp384r1p_ok
  unit := unitMod_pow_two (by decide +kernel +revert) _
  tables := VG.Proof.BrainpoolP384r1.combOk7 hC
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

theorem comb_words_length : brainpoolp384r1CombWords.length=42240 := by
  have len := VG.Proof.Weierstrass.tcombWords_length (n := 6) (R := 2^384)
    (p := Spec.BrainpoolP384r1.curve.p) (tbl := comb7)
    (J := 55) (H := 64) (by decide +kernel) (by decide +kernel)
  unfold brainpoolp384r1CombWords
  exact len

@[irreducible] def combSatMem : Mem := constMem 0x100000 brainpoolp384r1CombWords

theorem combSat_held : ∀ i<brainpoolp384r1CombWords.length,
    combSatMem.readW (0x100000+BitVec.ofNat 64 (8*i)) 64=brainpoolp384r1CombWords.getD i 0 :=
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
  rd := [⟨0x12000,48⟩,⟨0x14000,48⟩,⟨0x16000,48⟩,⟨0x20000,4⟩,⟨0x100000,337920⟩]
  wr := [⟨0x10000,96⟩,⟨0,8192⟩]
  syms _ := 0x100000

end VG.Proof.BrainpoolP384r1.Arm
