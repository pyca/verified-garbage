module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Dsa.X86.Generation.PShapeArguments
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PHashes
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashOneCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashPrefix
import VerifiedGarbage.Proof.Dsa.X86.Generation.PShapeCT

/-! # Assemble all public seed contributions before shaping the p candidate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Pbkdf2.Stream.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Impl.Dsa.X86.Generation

def HashesShapeAt {H : Hash} (K : HashOK H) (G : ContributionPlan) (parent : BitVec 32) (s : State) : Prop :=
  ContributionReady K G s ∧ s.mem.readW (off G.frame 20) 32 = parent

theorem hashesBeforeShape_ct {H : Hash} {K : HashOK H} {G : ContributionPlan}
    (L : ContributionLayout K G) (width : G.seed.length = 20 ∨ G.seed.length = 32) (parent : BitVec 32) :
    RelCT isa (Two fun (_ : Unit) => HashesShapeAt K G parent) (pHashes H G.seed.length G.count)
      (Two fun (_ : Unit) => HashesShapeAt K G parent) := by
  refine two_post ((pHashPrefix_ct L width (G.count + 1) (by omega)).mono
    (fun _ _ => two_mono (fun _ _ h => h.1)) (fun _ _ _ => trivial)) ?_
  intro _ s R
  refine WP.mono (pHashPrefix_ok L R.1 (Nat.le_refl _)) fun t ⟨Rt, _, O, _⟩ => ?_
  refine ⟨Rt, ?_⟩
  rw [O.readW (r := ⟨G.frame, frameBytes⟩) (Offset.contains_base _ (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; decide) (by decide)) ?_ (by decide)]
  · exact R.2
  · intro r hr
    obtain ⟨j, hj, h⟩ := List.mem_flatMap.mp hr
    exact L.frameApart j (by have := List.mem_range.mp hj; omega) r h

theorem pHashesShape_ct {H : Hash} {K : HashOK H} {G : ContributionPlan}
    (L : ContributionLayout K G) (width : G.seed.length = 20 ∨ G.seed.length = 32)
    (parent : BitVec 32) (plen : Nat) :
    RelCT isa (Two fun (_ : Unit) => HashesShapeAt K G parent) (pHashesShape H G.seed.length G.count plen)
      (fun _ _ => True) := by
  unfold pHashesShape
  refine RelCT.seq (hashesBeforeShape_ct L width parent) (RelCT.seq
    (two_piece (Ψ := fun (_ : Unit) s =>
      s.gpr .esi = G.hashes + BitVec.ofNat 32 ((G.count + 1) * G.seed.length - plen) ∧
      s.gpr .edi = parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.shaped)
      [.esp] ?_ (hc := .block []) ?_ ?_) ?_)
  · intro _ s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.1.frame.esp_toNat.trans ht.1.frame.esp_toNat.symm)
  · exact (congrArg Option.isSome (VG.Proof.Mont.X86.Dynamic.check_of_erase_eq
      (.block (pShapeFromFrameArgs G.seed.length G.count plen)) (.block (pShapeFromFrameArgs 1 0 1))
      (τr [.esp]) (.block []) rfl rfl rfl)).trans (by rfl)
  · intro _ s R
    exact WP.mono (pShapeFromFrameArgs_ok R.1.frame R.1.hashes R.2 G.seed.length G.count plen) fun _ ⟨si, di, _, _⟩ => ⟨si, di⟩
  · refine (pShape_ct plen).mono ?_ (fun _ _ h => h)
    rintro s t ⟨_, hs, ht⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hs.2.trans ht.2.symm, hs.1.trans ht.1.symm]
end VG.Proof.Dsa.X86.Generation
