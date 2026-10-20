module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashCT
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PHashes
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashState
import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashPrefix

/-! # One contribution uses the plan's public pointers and preserves the search frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Pbkdf2.Stream.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Impl.Dsa.X86.Generation

def contributionHashPublic (G : ContributionPlan) (j : Nat) : PHashPublic :=
  ⟨G.source, ⟨G.wrapped, G.output j, G.scratch, G.frame.setWidth 32⟩⟩

theorem pContributionArgs_ct {H : Hash} (K : HashOK H) (G : ContributionPlan) (j : Nat) (bound : j ≤ G.count) :
    RelCT isa (Two fun (_ : Unit) => ContributionReady K G) (.block (pContributionArgs G.seed.length G.count j))
      (Two fun (_ : Unit) => PHashAt K G.seed.length (contributionHashPublic G j)) := by
  refine two_piece [.esp] ?_ (hc := .block []) ?_ ?_
  · intro _ s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.frame.esp_toNat.trans ht.frame.esp_toNat.symm)
  · exact (congrArg Option.isSome (VG.Proof.Mont.X86.Dynamic.check_of_erase_eq
      (.block (pContributionArgs G.seed.length G.count j)) (.block (pContributionArgs 1 0 0))
      (τr [.esp]) (.block []) rfl rfl rfl)).trans (by rfl)
  · intro _ s R
    refine WP.mono (pContributionArgs_ok R.frame G.seed.length G.count j) fun t ⟨si, di, _, dx, bp, _, Kt⟩ => ?_
    refine ⟨(R.resources j bound).keeps Kt (by decide), ?_, si.trans R.source, di.trans R.wrapped,
      dx.trans (congrArg (· + BitVec.ofNat 32 ((G.count - j) * G.seed.length)) R.hashes), bp.trans R.scratch⟩
    change t.gpr .esp = G.frame.setWidth 32
    rw [Kt.1 _ (by decide), ← R.frame.esp]; simp

theorem pHashOne_ct {H : Hash} {K : HashOK H} {G : ContributionPlan}
    (L : ContributionLayout K G) (width : G.seed.length = 20 ∨ G.seed.length = 32)
    (j : Nat) (bound : j ≤ G.count) :
    RelCT isa (Two fun (_ : Unit) => ContributionReady K G) (pHashOne H G.seed.length G.count j)
      (Two fun (_ : Unit) => ContributionReady K G) := by
  refine two_post (RelCT.seq (pContributionArgs_ct K G j bound)
    (two_map (fun _ : Unit => contributionHashPublic G j) (fun _ _ h => h) (pSeedHash_ct K G.seed.length width))) ?_
  intro _ s R
  exact WP.mono (pHashOneReady_ok L R bound) fun _ h => h.1

theorem pHashPrefix_ct {H : Hash} {K : HashOK H} {G : ContributionPlan}
    (L : ContributionLayout K G) (width : G.seed.length = 20 ∨ G.seed.length = 32)
    (k : Nat) (bound : k ≤ G.count + 1) :
    RelCT isa (Two fun (_ : Unit) => ContributionReady K G) (pHashPrefix H G.seed.length G.count k)
      (Two fun (_ : Unit) => ContributionReady K G) := by
  induction k with
  | zero => exact RelCT.nil (fun _ _ h => h)
  | succ k ih => exact RelCT.seq (ih (by omega)) (pHashOne_ct L width k (by omega))
end VG.Proof.Dsa.X86.Generation
