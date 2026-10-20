module

public import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Prefixes of the shared small-prime sieve -/

@[expose] public section
namespace VG.Proof.RsaKeyGen
open VG VG.Impl.RsaKeyGen

def entryDivides (c i : Nat) : Bool := decide (c % tabEntry i = 0)
def trialPrefix (c n : Nat) : Bool := (List.range n).any (entryDivides c)

theorem trialPrefix_zero (c : Nat) : trialPrefix c 0 = false := rfl

theorem trialPrefix_succ (c n : Nat) : trialPrefix c (n + 1) = (trialPrefix c n || entryDivides c n) := by
  simp only [trialPrefix, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]

theorem trialPrefix_hit {c i n : Nat} (index : i < n) (hit : entryDivides c i = true) : trialPrefix c n = true :=
  List.any_eq_true.mpr ⟨i, List.mem_range.mpr index, hit⟩

theorem trialPrefix_spec {c w : Nat} (large : 8161 < c) :
    trialPrefix c (if w ≤ 16 then 512 else 1024) = Spec.RsaKeyGen.obviouslyComposite (64 * w) c := by
  have equal : trialPrefix c (if w ≤ 16 then 512 else 1024) = trialAny (if 17 ≤ w then 256 else 128) c := by
    unfold trialPrefix trialAny entryDivides
    have length : (if w ≤ 16 then 512 else 1024) = 4 * (if 17 ≤ w then 256 else 128) := by split <;> split <;> omega
    rw [length]
    apply List.any_congr rfl
    intro i
    exact (Bool.beq_eq_decide_eq _ _).symm
  exact equal.trans (trialAny_eq large)

end VG.Proof.RsaKeyGen
