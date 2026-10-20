module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundFinishCT
import VerifiedGarbage.Proof.Mont.X86.Exponentiate
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundArithmeticCT

/-! # Public witness exponentiation feeds the adaptive primality-round checks -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

def RoundPowerAt (n e : Nat) (p : RoundPublic × Nat) (s : State) : Prop :=
  RoundBaseAt n p.1 s ∧ val32 s.mem p.1.base (slot n 8) e = p.2 ∧
    wordsVal s.mem p.1.base (slot n 5) n = p.1.value

def roundPowerResult (p : RoundPublic × Nat) : RoundPublic :=
  {p.1 with value := p.1.value ^ p.2 % p.1.modulus}

theorem roundPower_phase_ok {n e : Nat} (epos : 0 < e) (ebound : e ≤ 2 * n)
    {p : RoundPublic × Nat} {s : State} (R : RoundPowerAt n e p s) :
    WP isa (exponentiate n e) s (RoundFinishAt n (roundPowerResult p)) := by
  have width := R.1.width
  have fit : contextBytes n ≤ 2 ^ 64 := by have := R.1.context.size_le; have := R.1.context.scr.nowrap; omega
  refine WP.mono (exponentiate_ok R.1.context epos ebound (by omega) R.1.one R.1.r2)
    fun t ⟨C, value, O, _⟩ => ?_
  have r2 : wordsVal t.mem p.1.base (slot n 4) n = 2 ^ (128 * n) % p.1.modulus := by
    rw [← R.1.r2, wordsVal_eq_val32, wordsVal_eq_val32]
    apply O.val32
    · intro r hr
      simp only [exponentRanges, VG.Proof.Mont.X86.Dynamic.productRanges, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega
    · simp only [contextBytes, slot, stride] at fit ⊢; omega
  have count : t.mem.readW (off p.1.base roundCount) 32 = BitVec.ofNat 32 p.1.count := by
    rw [← R.1.count]
    apply BitVec.eq_of_toNat_eq
    have v := O.val32 (d := roundCount) (k := 1) (by
      intro r hr
      simp only [exponentRanges, VG.Proof.Mont.X86.Dynamic.productRanges, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride, roundCount] <;> omega) (by decide)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using v
  exact ⟨⟨C, width, R.1.room, (exponentRanges_one O fit).trans R.1.one, r2, count, R.1.bound⟩,
    by change wordsVal t.mem p.1.base (slot n 6) n = p.1.value ^ p.2 % p.1.modulus; rw [value, R.2.1, R.2.2]⟩

theorem round_ct (n e : Nat) (epos : 0 < e) (ebound : e ≤ 2 * n) :
    RelCT isa (Two (RoundPowerAt n e)) (round n e) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p => RoundFinishAt n (roundPowerResult p))
    ((exponentiate_ct n e epos).mono ?_ (fun _ _ h => h))
    (fun _ _ R => roundPower_phase_ok epos ebound R))
    (two_map roundPowerResult (fun _ _ h => h) (roundFinish_ct n))
  rintro s t ⟨p, hs, ht⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact BitVec.eq_of_toNat_eq (hs.1.context.scr.edi_toNat.trans ht.1.context.scr.edi_toNat.symm)
end VG.Proof.Dsa.X86.Generation
