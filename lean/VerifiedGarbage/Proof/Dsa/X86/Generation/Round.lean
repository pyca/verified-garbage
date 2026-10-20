module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundFinish
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Mont.X86.ExponentBody
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Mont.X86.Exponentiate

/-! # A native Miller–Rabin round, reusing the candidate's prepared modulus -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

def roundAllWrites (n e : Nat) : List (Nat × Nat) := exponentRanges n e ++ roundFinishWrites n

theorem round_ok {base : Addr} {n m size e a exponent witness : Nat} {s : State}
    (C : Context n m base size s) (width : n ≤ 48) (room : roundStatus + 4 ≤ size)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (r2 : wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % m)
    (epos : 1 < e) (ebound : e ≤ 2 * n) (apos : 1 ≤ a) (abound : a ≤ Spec.RsaKeyGen.bitLength m)
    (countbound : a - 1 < 2 ^ 32)
    (count : s.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 (a - 1))
    (exp : val32 s.mem base (slot n 8) e = exponent)
    (wit : wordsVal s.mem base (slot n 5) n = witness) :
    WP isa (round n e) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.mrIteration m a exponent witness).toNat ∧
      Outs base (roundAllWrites n e) s.mem t.mem ∧ Keeps powerClob s t := by
  have fit : contextBytes n ≤ 2 ^ 64 := by have := C.size_le; have := C.scr.nowrap; omega
  unfold round
  refine WP.seq (WP.mono (exponentiate_ok C epos ebound (by omega) one r2) fun u ⟨Cu, vu, Ou, Ku⟩ => ?_)
  have r2u : wordsVal u.mem base (slot n 4) n = 2 ^ (128 * n) % m := by
    rw [← r2, wordsVal_eq_val32, wordsVal_eq_val32]
    apply Ou.val32
    · intro r hr
      simp only [exponentRanges, VG.Proof.Mont.X86.Dynamic.productRanges, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega
    · simp only [contextBytes, slot, stride] at fit ⊢; omega
  have cu : u.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 (a - 1) := by
    rw [← count]
    apply BitVec.eq_of_toNat_eq
    have v := Ou.val32 (d := roundCount) (k := 1) (by
      intro r hr
      simp only [exponentRanges, VG.Proof.Mont.X86.Dynamic.productRanges, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride, roundCount] <;> omega) (by decide)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using v
  refine WP.mono (roundFinish_ok Cu width room ((exponentRanges_one Ou fit).trans one) r2u countbound cu)
    fun t ⟨result, Ot, Kt⟩ => ?_
  refine ⟨?_, (Ou.mono (by intro r hr; exact List.mem_append_left _ hr)).trans
    (Ot.mono (by intro r hr; exact List.mem_append_right _ hr)), Ku.trans (Kt.mono (by decide))⟩
  rw [result, vu, wit, exp, mrIteration_public apos abound]
  unfold roundAnswer publicMrIteration
  simp only [VG.Proof.Bignum.powMod_eq, Bool.or_eq_true, beq_iff_eq]
end VG.Proof.Dsa.X86.Generation
