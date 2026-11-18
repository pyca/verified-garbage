module

import VerifiedGarbage.Proof.Weierstrass.Arm.TCombCorrect
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConfig
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Verified
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.BrainpoolP256r1.Comb7
import VerifiedGarbage.Proof.Weierstrass.Arm.MontBrainpoolP256r1
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `BrainpoolP256r1.Arm.Comb`, which this module and modules that import it used -/

section

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

end VG.Proof.BrainpoolP256r1.Arm

end

end

/-! brainpoolP256r1's comb meets the ECDSA generator result and write frame, which
signing, public-key derivation and verification share. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.BrainpoolP256r1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Weierstrass.Arm.TComb

theorem comb_words_eq (u : Bool) : tableWords (brainpoolp256r1CombWith u) Spec.BrainpoolP256r1.curve
    VG.Impl.BrainpoolP256r1.comb7=brainpoolp256r1CombWords := by
  unfold brainpoolp256r1CombWords
  rfl

theorem comb_writes_cover (u : Bool) : ∀ w ∈ writes (brainpoolp256r1CombWith u),
    ∃ v ∈ Point.ladWp (brainpoolp256r1With u).ladderCfg (brainpoolp256r1With u).wk,
      v.1≤w.1 ∧ w.1+w.2≤v.1+v.2 := by decide +kernel +revert

theorem comb_generator_ok (hC : Law Spec.BrainpoolP256r1.curve) {u : Bool} {s : State} {base T : Addr} {k : Nat}
    (hs : Scr s base size) (hf : Far s base 8192) {g : Reg → BitVec 32}
    (F : Fixed (brainpoolp256r1With u) base g s.mem)
    (ht : TableMem s T brainpoolp256r1CombWords) (sym : State.addr (s.syms (brainpoolp256r1CombWith u).tsym)=T)
    (hd : Region.Disjoint ⟨T,8*brainpoolp256r1CombWords.length⟩ ⟨base,4096⟩)
    (hk : k<2^256)
    (bits : ∀ i<256,s.mem (off base (bitsAt (brainpoolp256r1With u).n 0+i))=if k.testBit i then 1 else 0) :
    WP isa (mulGeneratorBrainpoolP256r1With u) s (GeneratorPost (brainpoolp256r1With u) base k s) := by
  have hc := brainpoolp256r1With_ok u
  have ht' : TableMem s T (tableWords (brainpoolp256r1CombWith u) Spec.BrainpoolP256r1.curve VG.Impl.BrainpoolP256r1.comb7) := by
    rw [comb_words_eq u]; exact ht
  have hd' : Region.Disjoint ⟨T,8*(tableWords (brainpoolp256r1CombWith u) Spec.BrainpoolP256r1.curve VG.Impl.BrainpoolP256r1.comb7).length⟩ ⟨base,4096⟩ := by
    rw [comb_words_eq u]; exact hd
  refine WP.mono (comb_ok (brainpoolp256r1CombWith u) (VG.Proof.BrainpoolP256r1.Arm.comb_config hC u) hC hc.onG
    hs hf ht' sym hd' hk F.zero bits F.ap F.b3p) fun t ⟨keep,unch,lt,rep⟩ => ?_
  have U := unch.cover (comb_writes_cover u)
  have U' := U
  rw [Point.ladWp,ladWx_eq] at U'
  have Ft := F.unch hc.n10 hs.nowrap (fixedOk_slWkP hc.n10 (by decide)) U'
  exact ⟨keep, U.mono fun w hw => List.mem_append_left _ hw, modP_of hc Ft.mp, lt, rep⟩

/-- Setup and bit extraction preserve the ROM used by either signing or key generation. -/
theorem comb_generator_stage (hC : Law Spec.BrainpoolP256r1.curve) {u : Bool} {s₀ s : State} {base T : Addr} {A : Args}
    (S : St₁ (brainpoolp256r1With u) A s₀ base s) (sy : s.syms=s₀.syms)
    (ht : TableMem s₀ T brainpoolp256r1CombWords) (sym : State.addr (s₀.syms (brainpoolp256r1CombWith u).tsym)=T)
    (hd : Region.Disjoint ⟨T,8*brainpoolp256r1CombWords.length⟩ ⟨base,8192⟩) :
    WP isa (mulGeneratorBrainpoolP256r1With u) s (GeneratorPost (brainpoolp256r1With u) base (kv (brainpoolp256r1With u) A s₀) s) := by
  have frame : Frame [⟨base,8192⟩] s₀.mem s.mem := outside_frame
    (S.whole.outside (o := 0) (n := 8192) (by simp)) (Nat.le_refl _)
  have ht' := ht.of_frame (by rw [S.rest.rd,S.rest.wr]) frame
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  exact comb_generator_ok hC S.scr S.far S.fixed ht' (by rw [sy]; exact sym)
    (hd.sub_right (Region.sub_prefix (by decide)))
    (by rw [← S.k]; exact wordsVal_lt _ _ _ _) S.t₀

end VG.Proof.Ecdsa.Arm.BrainpoolP256r1
