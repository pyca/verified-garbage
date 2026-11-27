module

import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Umaal
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombCorrect
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Impl.Ecdsa.P224.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Weierstrass.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P224.Comb7
import VerifiedGarbage.Proof.Weierstrass.Arm.MontModuli
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `P224.Arm.Comb`, which this module and modules that import it used -/

section

/-!
# P-224's seven-bit comb on 32-bit ARM

Its layout (it reuses the ladder's accumulator and addition temporary), the
configuration the comb's proof takes, and the memory of satisfiable
contracts with its table: the table at 1 MiB, the working space at zero.
-/

@[expose] public section
namespace VG.Proof.P224.Arm
open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm VG.Impl.P224
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.TComb

theorem comb_layout (u : Bool := false) : Layout (p224CombWith u) := by
  refine ⟨by decide +revert,by decide +revert,?_,?_,?_,?_,?_⟩
  · exact ⟨by decide +revert,by decide +revert⟩
  all_goals decide +kernel +revert

theorem comb_config (hC : Law Spec.P224.curve) (u : Bool := false) :
    Config (p224CombWith u) Spec.P224.curve p224Comb7x32 p224Comb7Start32 where
  layout := comb_layout u
  fieldK := rfl
  fieldM := rfl
  modulus := Mont.p224p_ok
  unit := unitMod_pow_two (by decide +kernel +revert) _
  tables := VG.Proof.P224.combOk7x32 hC
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

theorem comb_words_length : p224CombWords.length=16384 := by
  have len := VG.Proof.Weierstrass.tcombWords_length (n := 4) (R := 2^256)
    (p := Spec.P224.curve.p) (tbl := p224Comb7x32)
    (J := 32) (H := 64) (by decide +kernel) (by decide +kernel)
  unfold p224CombWords
  exact len

@[irreducible] def combSatMem : Mem := constMem 0x100000 p224CombWords

theorem combSat_held : ∀ i<p224CombWords.length,
    combSatMem.readW (0x100000+BitVec.ofNat 64 (8*i)) 64=p224CombWords.getD i 0 :=
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
  rd := [⟨0x12000,28⟩,⟨0x14000,28⟩,⟨0x16000,28⟩,⟨0x20000,4⟩,⟨0x100000,131072⟩]
  wr := [⟨0x10000,56⟩,⟨0,8192⟩]
  syms _ := 0x100000

end VG.Proof.P224.Arm

end

end

/-! P-224's comb meets the ECDSA generator result and write frame, which
signing, public-key derivation and verification share. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.P224
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Weierstrass.Arm.TComb

theorem comb_words_eq (u : Bool) : tableWords (p224CombWith u) Spec.P224.curve
    VG.Impl.P224.p224Comb7x32=p224CombWords := by
  unfold p224CombWords
  rfl

theorem comb_writes_cover (u : Bool) : ∀ w ∈ writes (p224CombWith u),
    ∃ v ∈ Point.ladWp (p224With u).ladderCfg (p224With u).wk,
      v.1≤w.1 ∧ w.1+w.2≤v.1+v.2 := by decide +kernel +revert

theorem comb_generator_ok (hC : Law Spec.P224.curve) {u : Bool} {s : State} {base T : Addr} {k : Nat}
    (hs : Scr s base size) (hf : Far s base 8192) {g : Reg → BitVec 32}
    (F : Fixed (p224With u) base g s.mem)
    (ht : TableMem s T p224CombWords) (sym : State.addr (s.syms (p224CombWith u).tsym)=T)
    (hd : Region.Disjoint ⟨T,8*p224CombWords.length⟩ ⟨base,4096⟩)
    (hk : k<2^224)
    (bits : ∀ i<224,s.mem (off base (bitsAt (p224With u).n 0+i))=if k.testBit i then 1 else 0) :
    WP isa (mulGeneratorP224With u) s (GeneratorPost (p224With u) base k s) := by
  have hc := p224With_ok u
  have ht' : TableMem s T (tableWords (p224CombWith u) Spec.P224.curve VG.Impl.P224.p224Comb7x32) := by
    rw [comb_words_eq u]; exact ht
  have hd' : Region.Disjoint ⟨T,8*(tableWords (p224CombWith u) Spec.P224.curve VG.Impl.P224.p224Comb7x32).length⟩ ⟨base,4096⟩ := by
    rw [comb_words_eq u]; exact hd
  refine WP.mono (comb_ok (p224CombWith u) (VG.Proof.P224.Arm.comb_config hC u) hC hc.onG
    hs hf ht' sym hd' hk F.zero bits F.ap F.b3p) fun t ⟨keep,unch,lt,rep⟩ => ?_
  have U := unch.cover (comb_writes_cover u)
  have U' := U
  rw [Point.ladWp,ladWx_eq] at U'
  have Ft := F.unch hc.n10 hs.nowrap (fixedOk_slWkP hc.n10 (by decide)) U'
  exact ⟨keep, U.mono fun w hw => List.mem_append_left _ hw, modP_of hc Ft.mp, lt, rep⟩

/-- Setup and bit extraction preserve the ROM used by either signing or key generation. -/
theorem comb_generator_stage (hC : Law Spec.P224.curve) {u : Bool} {s₀ s : State} {base T : Addr} {A : Args}
    (S : St₁ (p224With u) A s₀ base s) (sy : s.syms=s₀.syms)
    (ht : TableMem s₀ T p224CombWords) (sym : State.addr (s₀.syms (p224CombWith u).tsym)=T)
    (hd : Region.Disjoint ⟨T,8*p224CombWords.length⟩ ⟨base,8192⟩) :
    WP isa (mulGeneratorP224With u) s (GeneratorPost (p224With u) base (kv (p224With u) A s₀) s) := by
  have frame : Frame [⟨base,8192⟩] s₀.mem s.mem := outside_frame
    (S.whole.outside (o := 0) (n := 8192) (by simp)) (Nat.le_refl _)
  have ht' := ht.of_frame (by rw [S.rest.rd,S.rest.wr]) frame
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  exact comb_generator_ok hC S.scr S.far S.fixed ht' (by rw [sy]; exact sym)
    (hd.sub_right (Region.sub_prefix (by decide)))
    (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _)
      (VG.Proof.Weierstrass.ofBytes_bytesAt_lt _ _ Spec.P224.curve.len))
    fun i hi => S.t₀ i (by change i < 64 * 4; omega_using [hi])

end VG.Proof.Ecdsa.Arm.P224
