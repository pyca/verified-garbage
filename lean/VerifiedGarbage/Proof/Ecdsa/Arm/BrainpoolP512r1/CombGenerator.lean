module

public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombI
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombCorrect
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.BrainpoolP512r1.Comb7
import VerifiedGarbage.Proof.BrainpoolP512r1.Comb7Shape
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `BrainpoolP512r1.Arm.Comb`, which this module and modules that import it used -/

section

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

end

end

/-! brainpoolP512r1's comb meets the ECDSA generator result and write frame, which
signing, public-key derivation and verification share. -/

@[expose] public section

-- Powers of two up to `2^512` are evaluated.
set_option exponentiation.threshold 512
namespace VG.Proof.Ecdsa.Arm.BrainpoolP512r1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Weierstrass.Arm.TComb

theorem comb_words_eq (u : Bool) : tableWords (brainpoolp512r1CombWith u) Spec.BrainpoolP512r1.curve
    VG.Impl.BrainpoolP512r1.comb7=brainpoolp512r1CombWords := by
  unfold brainpoolp512r1CombWords
  rfl

theorem comb_generator_ok (hC : Law Spec.BrainpoolP512r1.curve) {u : Bool} {s : State} {base T : Addr} {k : Nat}
    (hs : Scr s base size) (hf : Far s base 8192) {g : Reg → BitVec 32}
    (F : Fixed (brainpoolp512r1With u) base g s.mem)
    (ht : TableMem s T brainpoolp512r1CombWords) (sym : State.addr (s.syms (brainpoolp512r1CombWith u).tsym)=T)
    (hd : Region.Disjoint ⟨T,8*brainpoolp512r1CombWords.length⟩ ⟨base,4096⟩)
    (hk : k<2^512)
    (bits : ∀ i<512,s.mem (off base (bitsAt (brainpoolp512r1With u).n 0+i))=if k.testBit i then 1 else 0) :
    WP isa (mulGeneratorBrainpoolP512r1With u) s (GeneratorPost (brainpoolp512r1With u) base k s) := by
  have hc := brainpoolp512r1With_ok u
  have ht' : TableMem s T (tableWords (brainpoolp512r1CombWith u) Spec.BrainpoolP512r1.curve VG.Impl.BrainpoolP512r1.comb7) := by
    rw [comb_words_eq u]; exact ht
  have hd' : Region.Disjoint ⟨T,8*(tableWords (brainpoolp512r1CombWith u) Spec.BrainpoolP512r1.curve VG.Impl.BrainpoolP512r1.comb7).length⟩ ⟨base,4096⟩ := by
    rw [comb_words_eq u]; exact hd
  refine WP.mono (combI_ok (brainpoolp512r1CombWith u) (VG.Proof.BrainpoolP512r1.Arm.comb_config hC u) hC hc.onG
    hs hf (modP_of hc F.mp) ht' sym hd' hk F.zero bits F.ap F.b3p) fun t ⟨keep,unch,mod,lt,rep⟩ => ?_
  exact ⟨keep, unch.mono fun w hw => List.mem_append_left _ (List.mem_append_left _ hw), mod, lt, rep⟩

/-- Setup and bit extraction preserve the ROM used by either signing or key generation. -/
theorem comb_generator_stage (hC : Law Spec.BrainpoolP512r1.curve) {u : Bool} {s₀ s : State} {base T : Addr} {A : Args}
    (S : St₁ (brainpoolp512r1With u) A s₀ base s) (sy : s.syms=s₀.syms)
    (ht : TableMem s₀ T brainpoolp512r1CombWords) (sym : State.addr (s₀.syms (brainpoolp512r1CombWith u).tsym)=T)
    (hd : Region.Disjoint ⟨T,8*brainpoolp512r1CombWords.length⟩ ⟨base,8192⟩) :
    WP isa (mulGeneratorBrainpoolP512r1With u) s (GeneratorPost (brainpoolp512r1With u) base (kv (brainpoolp512r1With u) A s₀) s) := by
  have frame : Frame [⟨base,8192⟩] s₀.mem s.mem := outside_frame
    (S.whole.outside (o := 0) (n := 8192) (by simp)) (Nat.le_refl _)
  have ht' := ht.of_frame (by rw [S.rest.rd,S.rest.wr]) frame
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  exact comb_generator_ok hC S.scr S.far S.fixed ht' (by rw [sy]; exact sym)
    (hd.sub_right (Region.sub_prefix (by decide)))
    (by rw [← S.k]; exact wordsVal_lt _ _ _ _) S.t₀

end VG.Proof.Ecdsa.Arm.BrainpoolP512r1
