module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPowerCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ChildCT
public import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPowerCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ChildCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Timing of fresh generator modulus setup -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Impl.Dsa.AArch64.Generation

def GeneratorModulusBefore (len : Nat) (p : GeneratorPlan) (s : State) : Prop :=
  Scr s p.B activeBytes ∧ s.gpr .x0 = p.B ∧
  Src s p.B activeBytes (off p.B VG.Impl.Dsa.Generation.Layout.p) p.pb ∧ p.len = len

def GeneratorModulusParent (len : Nat) (p : GeneratorPlan) (s : State) : Prop :=
  Good s p.B activeBytes outerWords 0 ∧
  Src s p.B activeBytes (off p.B VG.Impl.Dsa.Generation.Layout.p) p.pb ∧ p.len = len

def GeneratorPlan.childCall (p : GeneratorPlan) : ChildPublic where
  x := (p.powerCall 0).x
  ptr := off p.B VG.Impl.Dsa.Generation.Layout.p
  len := p.len
  extent := (p.powerCall 0).extent
  offset := (p.powerCall 0).offsetBound
  lo := (p.powerCall 0).childLow
  hi := (p.powerCall 0).childHigh
  widthPositive := (p.powerCall 0).lower
  widthParent := (p.powerCall 0).fits
  widthBound := (p.powerCall 0).upper
  positive := (p.powerCall 0).outputPositive
  lengthBound := (p.powerCall 0).outputBound
  width := (p.powerCall 0).outputWidth

theorem generatorModulus_parent {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorModulusBefore len p s) :
    WP isa (.block SignVerify.parent) s (GeneratorModulusParent len p) := by
  refine WP.mono (parent_ok h.1 h.2.1 (by decide)) fun t ⟨hg, hf, hk⟩ => ?_
  have ff : Frm p.B [(48, 80)] s.mem t.mem := Frm.of_outside hf (by simp)
  exact ⟨hg, h.2.2.1.congrK (InScr.of_frm ff (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; decide)) hk, h.2.2.2⟩

theorem generatorModulus_fields {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorModulusParent len p s) :
    WP isa (.block (generatorFields len)) s
      (ChildPre ⟨.input .p, .pLen⟩ p.childCall) := by
  have hl : len < 2 ^ 16 := by have he := h.2.2; rcases p.width with hh | hh | hh <;> omega
  refine WP.mono (generatorFields_ok h.1 (by decide) hl)
    fun t ⟨hg, hp, _, hlen, _, hf, hk⟩ => ?_
  have ff : Frm p.B [(256, 80)] s.mem t.mem := Frm.of_outside hf (by simp)
  have src := h.2.1.congrK (InScr.of_frm ff (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; decide)) hk
  refine ⟨⟨0, hg⟩, p.pb, hp, ?_, src, p.pLength⟩
  change word t.mem p.B 328 = BitVec.ofNat 64 p.pb.length
  rw [p.pLength, h.2.2]; exact hlen

theorem generatorModulus_ct (len : Nat) (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorModulusBefore len)) (generatorModulus len) (fun _ _ => True) := by
  unfold generatorModulus
  simp only [seqs]
  refine RelCT.seq (two_post (two_map (fun p : GeneratorPlan => p.B) (fun _ _ h => h.2.1) parent_ct)
    (fun _ _ h => generatorModulus_parent h)) ?_
  have fields : RelCT isa (Two (GeneratorModulusParent len)) (.block (generatorFields len))
      (fun _ _ => True) := by
    apply two_map (Φ' := BasePublic) (fun p : GeneratorPlan => p.B) (fun _ _ h => h.1.x0)
    rcases hl with rfl | rfl | rfl
    all_goals exact two_taint [.x0] pins_base (by taint_decide)
  refine RelCT.seq (two_post fields (fun _ _ h => generatorModulus_fields h)) ?_
  exact two_map GeneratorPlan.childCall (fun _ _ h => ⟨h, rfl⟩)
    (child_ct ⟨.input .p, .pLen⟩ (by trivial) pWorkspace (by taint_decide))

end VG.Proof.Dsa.AArch64.Generation
