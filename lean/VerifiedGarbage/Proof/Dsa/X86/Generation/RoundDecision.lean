module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.RoundPolicy
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Completion requires both the blinded minimum and enough uniform draws. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont.X86

theorem round_decision {s : State} {i uniform checks : Nat}
    (hi : i < 2 ^ 32) (hu : uniform < 2 ^ 32) (hc : checks < 2 ^ 32)
    (index : s.gpr .ecx = BitVec.ofNat 32 i)
    (count : s.gpr .edx = BitVec.ofNat 32 uniform) :
    WP isa (roundDecision checks) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (if i < 17 ∨ uniform < checks then 4 else 1) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold roundDecision
  refine WP.seq (wp_cmpi fun a A carry _ => WP.block_nil ?_)
  have cf : a.cf = some (decide (i < 17)) := by
    rw [carry, index, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
    rfl
  refine WP.ite (decide (i < 17)) cf ?_ ?_
  · intro h
    have less : i < 17 := of_decide_eq_true h
    refine wp_movS rfl fun t T _ => WP.block_nil ?_
    exact ⟨by simp only [ite_eq_left (show i < 17 ∨ uniform < checks from Or.inl less)]; exact T.gpr,
      T.mem.trans A.mem, (A.keeps _).trans T.keeps⟩
  · intro h
    have large : ¬ i < 17 := of_decide_eq_false h
    refine WP.seq (wp_cmpi fun b B carry _ => WP.block_nil ?_)
    have cf : b.cf = some (decide (uniform < checks)) := by
      rw [carry, A.gpr, count, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hc]
    refine WP.ite (decide (uniform < checks)) cf ?_ ?_
    · intro h
      have less : uniform < checks := of_decide_eq_true h
      refine wp_movS rfl fun t T _ => WP.block_nil ?_
      exact ⟨by simp only [ite_eq_left (show i < 17 ∨ uniform < checks from Or.inr less)]; exact T.gpr,
        T.mem.trans (B.mem.trans A.mem), ((A.keeps _).trans (B.keeps _)).trans T.keeps⟩
    · intro h
      have enough : ¬ uniform < checks := of_decide_eq_false h
      refine wp_movS rfl fun t T _ => WP.block_nil ?_
      exact ⟨by simp only [ite_eq_right (show ¬ (i < 17 ∨ uniform < checks) by simp [large, enough])]; exact T.gpr,
        T.mem.trans (B.mem.trans A.mem), ((A.keeps _).trans (B.keeps _)).trans T.keeps⟩

end VG.Proof.Dsa.X86.Generation
