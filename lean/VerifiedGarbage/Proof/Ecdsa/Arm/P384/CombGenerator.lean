module

import VerifiedGarbage.Proof.Weierstrass.Arm.TCombCorrect
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConfig
public import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
import VerifiedGarbage.Proof.P384.Arm.Comb
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Verified
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! P-384's comb meets the ECDSA generator result and write frame, which
signing, public-key derivation and verification share. -/

@[expose] public section

-- Powers of two up to `2^384` are evaluated.
set_option exponentiation.threshold 512
namespace VG.Proof.Ecdsa.Arm.P384
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Weierstrass.Arm.TComb

theorem comb_words_eq : tableWords p384Comb Spec.P384.curve
    VG.Impl.P384.p384Comb7=p384CombWords := by
  unfold p384CombWords
  rfl

theorem comb_writes_cover : ∀ w ∈ writes p384Comb,
    ∃ v ∈ Point.ladWp p384.ladderCfg p384.wk,
      v.1≤w.1 ∧ w.1+w.2≤v.1+v.2 := by decide +kernel

theorem comb_generator_ok (hC : Law Spec.P384.curve) {s : State} {base T : Addr} {k : Nat}
    (hs : Scr s base size) (hf : Far s base 8192) {g : Reg → BitVec 32}
    (F : Fixed p384 base g s.mem)
    (ht : TableMem s T p384CombWords) (sym : State.addr (s.syms p384Comb.tsym)=T)
    (hd : Region.Disjoint ⟨T,8*p384CombWords.length⟩ ⟨base,4096⟩)
    (hk : k<2^384)
    (bits : ∀ i<384,s.mem (off base (bitsAt p384.n 0+i))=if k.testBit i then 1 else 0) :
    WP isa mulGeneratorP384 s (GeneratorPost p384 base k s) := by
  have hc := p384_ok
  have ht' : TableMem s T (tableWords p384Comb Spec.P384.curve VG.Impl.P384.p384Comb7) := by
    rw [comb_words_eq]; exact ht
  have hd' : Region.Disjoint ⟨T,8*(tableWords p384Comb Spec.P384.curve VG.Impl.P384.p384Comb7).length⟩ ⟨base,4096⟩ := by
    rw [comb_words_eq]; exact hd
  refine WP.mono (comb_ok p384Comb (VG.Proof.P384.Arm.comb_config hC) hC hc.onG
    hs hf ht' sym hd' hk F.zero bits F.ap F.b3p) fun t ⟨keep,unch,lt,rep⟩ => ?_
  have U := unch.cover comb_writes_cover
  have U' := U
  rw [Point.ladWp,ladWx_eq] at U'
  have Ft := F.unch hc.n10 hs.nowrap (fixedOk_slWkP hc.n10 (by decide)) U'
  exact ⟨keep, U.mono fun w hw => List.mem_append_left _ hw, modP_of hc Ft.mp, lt, rep⟩

/-- Setup and bit extraction preserve the ROM used by either signing or key generation. -/
theorem comb_generator_stage (hC : Law Spec.P384.curve) {s₀ s : State} {base T : Addr} {A : Args}
    (S : St₁ p384 A s₀ base s) (sy : s.syms=s₀.syms)
    (ht : TableMem s₀ T p384CombWords) (sym : State.addr (s₀.syms p384Comb.tsym)=T)
    (hd : Region.Disjoint ⟨T,8*p384CombWords.length⟩ ⟨base,8192⟩) :
    WP isa mulGeneratorP384 s (GeneratorPost p384 base (kv p384 A s₀) s) := by
  have frame : Frame [⟨base,8192⟩] s₀.mem s.mem := outside_frame
    (S.whole.outside (o := 0) (n := 8192) (by simp)) (Nat.le_refl _)
  have ht' := ht.of_frame (by rw [S.rest.rd,S.rest.wr]) frame
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  exact comb_generator_ok hC S.scr S.far S.fixed ht' (by rw [sy]; exact sym)
    (hd.sub_right (Region.sub_prefix (by decide)))
    (by rw [← S.k]; exact wordsVal_lt _ _ _ _) S.t₀

end VG.Proof.Ecdsa.Arm.P384
