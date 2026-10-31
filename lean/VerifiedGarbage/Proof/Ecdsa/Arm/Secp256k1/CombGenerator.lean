module

import VerifiedGarbage.Proof.Weierstrass.Arm.TCombCorrect
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConfig
public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
import VerifiedGarbage.Proof.Secp256k1.Arm.CombCorrect
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The comb meets the existing ECDSA generator result and write frame. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Weierstrass.Arm.TComb

theorem comb_words_eq (u : Bool) : tableWords (secp256k1CombWith u) Spec.Secp256k1.curve
    VG.Impl.Secp256k1.secp256k1Comb7=secp256k1CombWords := by
  unfold secp256k1CombWords
  rfl

theorem comb_writes_cover (u : Bool) : ∀ w ∈ writes (secp256k1CombWith u),
    ∃ v ∈ Point.ladWp (secp256k1With u).ladderCfg (secp256k1With u).wk,
      v.1≤w.1 ∧ w.1+w.2≤v.1+v.2 := by decide +kernel +revert

theorem comb_generator_ok (hC : Law Spec.Secp256k1.curve) {u : Bool} {s : State} {base T : Addr} {k : Nat}
    (hs : Scr s base size) (hf : Far s base 8192) {g : Reg → BitVec 32}
    (F : Fixed (secp256k1With u) base g s.mem)
    (ht : TableMem s T secp256k1CombWords) (sym : State.addr (s.syms (secp256k1CombWith u).tsym)=T)
    (hd : Region.Disjoint ⟨T,8*secp256k1CombWords.length⟩ ⟨base,4096⟩)
    (hk : k<2^256)
    (bits : ∀ i<256,s.mem (off base (bitsAt (secp256k1With u).n 0+i))=if k.testBit i then 1 else 0) :
    WP isa (mulGeneratorSecp256k1With u) s (GeneratorPost (secp256k1With u) base k s) := by
  have hc := secp256k1With_ok u
  have ht' : TableMem s T (tableWords (secp256k1CombWith u) Spec.Secp256k1.curve VG.Impl.Secp256k1.secp256k1Comb7) := by
    rw [comb_words_eq u]; exact ht
  have hd' : Region.Disjoint ⟨T,8*(tableWords (secp256k1CombWith u) Spec.Secp256k1.curve VG.Impl.Secp256k1.secp256k1Comb7).length⟩ ⟨base,4096⟩ := by
    rw [comb_words_eq u]; exact hd
  refine WP.mono (comb_ok (secp256k1CombWith u) (VG.Proof.Secp256k1.Arm.comb_config hC u) hC hc.onG
    hs hf ht' sym hd' hk F.zero bits F.ap F.b3p) fun t ⟨keep,unch,lt,rep⟩ => ?_
  have U := unch.cover (comb_writes_cover u)
  have U' := U
  rw [Point.ladWp,ladWx_eq] at U'
  have Ft := F.unch hc.n10 hs.nowrap (fixedOk_slWkP hc.n10 (by decide)) U'
  exact ⟨keep, U.mono fun w hw => List.mem_append_left _ hw, modP_of hc Ft.mp, lt, rep⟩

/-- Setup and bit extraction preserve the ROM used by either signing or key generation. -/
theorem comb_generator_stage (hC : Law Spec.Secp256k1.curve) {u : Bool} {s₀ s : State} {base T : Addr} {A : Args}
    (S : St₁ (secp256k1With u) A s₀ base s) (sy : s.syms=s₀.syms)
    (ht : TableMem s₀ T secp256k1CombWords) (sym : State.addr (s₀.syms (secp256k1CombWith u).tsym)=T)
    (hd : Region.Disjoint ⟨T,8*secp256k1CombWords.length⟩ ⟨base,8192⟩) :
    WP isa (mulGeneratorSecp256k1With u) s (GeneratorPost (secp256k1With u) base (kv (secp256k1With u) A s₀) s) := by
  have frame : Frame [⟨base,8192⟩] s₀.mem s.mem := outside_frame
    (S.whole.outside (o := 0) (n := 8192) (by simp)) (Nat.le_refl _)
  have ht' := ht.of_frame (by rw [S.rest.rd,S.rest.wr]) frame
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  exact comb_generator_ok hC S.scr S.far S.fixed ht' (by rw [sy]; exact sym)
    (hd.sub_right (Region.sub_prefix (by decide)))
    (by rw [← S.k]; exact wordsVal_lt _ _ _ _) S.t₀

end VG.Proof.Ecdsa.Arm.Secp256k1
