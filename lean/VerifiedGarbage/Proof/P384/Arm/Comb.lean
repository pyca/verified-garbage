module

public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConfig
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombLayout
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Proof.Weierstrass.Arm.MontModuli
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# P-384's seven-bit comb on 32-bit ARM

Its layout (it reuses the ladder's accumulator and addition temporary), the
configuration the comb's proof takes, and the memory of satisfiable
contracts with its table: the table at 1 MiB, the working space at zero.
-/

@[expose] public section
namespace VG.Proof.P384.Arm
open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm VG.Impl.P384
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.TComb

theorem comb_layout : Layout p384Comb := by
  refine ⟨by decide,by decide,?_,?_,?_,?_,?_⟩
  · exact ⟨by decide,by decide⟩
  all_goals decide +kernel

set_option exponentiation.threshold 512 in
theorem comb_config (hC : Law Spec.P384.curve) :
    Config p384Comb Spec.P384.curve p384Comb7 p384Comb7Start where
  layout := comb_layout
  fieldK := rfl
  fieldM := rfl
  modulus := Mont.p384p_ok
  unit := unitMod_pow_two (by decide +kernel) _
  tables := VG.Proof.P384.combOk7 hC
  one_lt := by decide +kernel
  one := toM_one (unitMod_pow_two (by decide +kernel) _)
  startX := rfl
  startY := rfl
  w1 := by decide
  w9 := by decide
  J1 := by decide
  J32 := by decide
  startBits := by decide
  coverBits := by decide
  bitsLow := by decide
  bitsHigh := by decide
  bitsFit := by decide
  windowFit := by decide
  encJ := by decide
  encLast := by decide
  encRow := by decide
  encEntry := by decide
  encH := by decide

theorem comb_words_length : p384CombWords.length=42240 := by
  have len := VG.Proof.Weierstrass.tcombWords_length (n := 6) (R := 2^384)
    (p := Spec.P384.curve.p) (tbl := p384Comb7)
    (J := 55) (H := 64) (by decide +kernel) (by decide +kernel)
  unfold p384CombWords
  exact len

@[irreducible] def combSatMem : Mem := constMem 0x100000 p384CombWords

theorem combSat_held : ∀ i<p384CombWords.length,
    combSatMem.readW (0x100000+BitVec.ofNat 64 (8*i)) 64=p384CombWords.getD i 0 :=
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

theorem combSat_stackArg : stackArg combSatState 0=0 := by
  have bytes : ∀ i<4,combSatMem (0x20000+BitVec.ofNat 64 i)=0 := by
    intro i hi
    unfold combSatMem constMem
    rw [comb_words_length]
    obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    all_goals decide

  change (combSatMem.read 0x20000 4).setWidth 32=0
  rw [Mem.read_eq_of_bytes (n := 4) (v := 0#32) (fun i hi => by
    rw [bytes i (by omega)]
    obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    all_goals decide)]
  rfl

end VG.Proof.P384.Arm
