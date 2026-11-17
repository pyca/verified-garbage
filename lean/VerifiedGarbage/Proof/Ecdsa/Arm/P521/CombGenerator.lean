module

import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Umaal

public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombI
public import VerifiedGarbage.Impl.Ecdsa.P521.ArmComb
import VerifiedGarbage.Proof.P521.Arm.Comb
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! P-521's comb meets the ECDSA generator result and write frame, which
signing, public-key derivation and verification share. -/

@[expose] public section

-- Powers of two up to `2^576` are evaluated.
set_option exponentiation.threshold 1024
namespace VG.Proof.Ecdsa.Arm.P521
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Weierstrass.Arm.TComb

theorem comb_words_eq (u : Bool) : tableWords (p521CombWith u) Spec.P521.curve
    VG.Impl.P521.p521Comb7=p521CombWords := by
  unfold p521CombWords
  rfl

theorem comb_generator_ok (hC : Law Spec.P521.curve) {u : Bool} {s : State} {base T : Addr} {k : Nat}
    (hs : Scr s base size) (hf : Far s base 8192) {g : Reg → BitVec 32}
    (F : Fixed (p521With u) base g s.mem)
    (ht : TableMem s T p521CombWords) (sym : State.addr (s.syms (p521CombWith u).tsym)=T)
    (hd : Region.Disjoint ⟨T,8*p521CombWords.length⟩ ⟨base,4096⟩)
    (hk : k<2^576)
    (bits : ∀ i<576,s.mem (off base (bitsAt (p521With u).n 0+i))=if k.testBit i then 1 else 0) :
    WP isa (mulGeneratorP521With u) s (GeneratorPost (p521With u) base k s) := by
  have hc := p521With_ok u
  have ht' : TableMem s T (tableWords (p521CombWith u) Spec.P521.curve VG.Impl.P521.p521Comb7) := by
    rw [comb_words_eq u]; exact ht
  have hd' : Region.Disjoint ⟨T,8*(tableWords (p521CombWith u) Spec.P521.curve VG.Impl.P521.p521Comb7).length⟩ ⟨base,4096⟩ := by
    rw [comb_words_eq u]; exact hd
  refine WP.mono (combI_ok (p521CombWith u) (VG.Proof.P521.Arm.comb_config hC u) hC hc.onG
    hs hf (modP_of hc F.mp) ht' sym hd' hk F.zero bits F.ap F.b3p) fun t ⟨keep,unch,mod,lt,rep⟩ => ?_
  exact ⟨keep, unch.mono fun w hw => List.mem_append_left _ (List.mem_append_left _ hw), mod, lt, rep⟩

/-- Setup and bit extraction preserve the ROM used by either signing or key generation. -/
theorem comb_generator_stage (hC : Law Spec.P521.curve) {u : Bool} {s₀ s : State} {base T : Addr} {A : Args}
    (S : St₁ (p521With u) A s₀ base s) (sy : s.syms=s₀.syms)
    (ht : TableMem s₀ T p521CombWords) (sym : State.addr (s₀.syms (p521CombWith u).tsym)=T)
    (hd : Region.Disjoint ⟨T,8*p521CombWords.length⟩ ⟨base,8192⟩) :
    WP isa (mulGeneratorP521With u) s (GeneratorPost (p521With u) base (kv (p521With u) A s₀) s) := by
  have frame : Frame [⟨base,8192⟩] s₀.mem s.mem := outside_frame
    (S.whole.outside (o := 0) (n := 8192) (by simp)) (Nat.le_refl _)
  have ht' := ht.of_frame (by rw [S.rest.rd,S.rest.wr]) frame
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  exact comb_generator_ok hC S.scr S.far S.fixed ht' (by rw [sy]; exact sym)
    (hd.sub_right (Region.sub_prefix (by decide)))
    (by rw [← S.k]; exact wordsVal_lt _ _ _ _) S.t₀

end VG.Proof.Ecdsa.Arm.P521
