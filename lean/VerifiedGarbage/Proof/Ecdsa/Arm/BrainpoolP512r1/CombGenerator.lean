module


public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombI
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmComb
import VerifiedGarbage.Proof.BrainpoolP512r1.Arm.Comb
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Framework.PlainSimp

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
