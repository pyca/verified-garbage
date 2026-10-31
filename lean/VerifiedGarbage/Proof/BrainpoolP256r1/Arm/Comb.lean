module

public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConfig
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombLayout
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.BrainpoolP256r1.Comb7
import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP256r1
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# brainpoolP256r1's seven-bit comb on 32-bit ARM

Its layout (it reuses the ladder's accumulator and addition temporary), the
configuration the comb's proof takes, and the memory of satisfiable
contracts with its table: the table at 1 MiB, the working space at zero.
-/

@[expose] public section
namespace VG.Proof.BrainpoolP256r1.Arm
open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm VG.Impl.BrainpoolP256r1
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.TComb

theorem comb_layout (u : Bool := false) : Layout (brainpoolp256r1CombWith u) := by
  refine ⟨by decide +revert,by decide +revert,?_,?_,?_,?_,?_⟩
  · exact ⟨by decide +revert,by decide +revert⟩
  all_goals decide +kernel +revert

theorem comb_config (hC : Law Spec.BrainpoolP256r1.curve) (u : Bool := false) :
    Config (brainpoolp256r1CombWith u) Spec.BrainpoolP256r1.curve comb7 comb7Start where
  layout := comb_layout u
  fieldK := rfl
  fieldM := rfl
  modulus := Mont.brainpoolp256r1p_ok
  unit := unitMod_pow_two (by decide +kernel +revert) _
  tables := VG.Proof.BrainpoolP256r1.combOk7 hC
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

theorem comb_words_length : brainpoolp256r1CombWords.length=18944 := by
  have len := VG.Proof.Weierstrass.tcombWords_length (n := 4) (R := 2^256)
    (p := Spec.BrainpoolP256r1.curve.p) (tbl := comb7)
    (J := 37) (H := 64) (by decide +kernel) (by decide +kernel)
  unfold brainpoolp256r1CombWords
  exact len

@[irreducible] def combSatMem : Mem := constMem 0x100000 brainpoolp256r1CombWords

theorem combSat_held : ∀ i<brainpoolp256r1CombWords.length,
    combSatMem.readW (0x100000+BitVec.ofNat 64 (8*i)) 64=brainpoolp256r1CombWords.getD i 0 :=
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
  rd := [⟨0x12000,32⟩,⟨0x14000,32⟩,⟨0x16000,32⟩,⟨0x20000,4⟩,⟨0x100000,151552⟩]
  wr := [⟨0x10000,64⟩,⟨0,8192⟩]
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

end VG.Proof.BrainpoolP256r1.Arm
