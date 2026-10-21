module

public import VerifiedGarbage.Impl.Mont.X86.CombPower
import VerifiedGarbage.Proof.Mont.X86.CombDigitMath
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb

/-! Extract one fixed comb bit; its memory address is independent of its value. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Rsa.FixedBaseComb (bit)

theorem toothRead_ok {s : State} {base : Addr} {size o k p : Nat}
    (hs : Scr s base size) (ho : o+4*k≤size) (hp : p<32*k) :
    WP isa (.block (toothRead o p)) s fun t =>
      t.mem=s.mem ∧ (t.gpr .eax).toNat=bit (val32 s.mem base o k) p ∧ Keeps [.eax] s t := by
  unfold toothRead
  simp only [List.cons_append,List.nil_append]
  refine wp_movS (readSrc_sc hs (by omega)) fun u U _ => ?_
  have finish {v : State} (M : v.mem=s.mem) (K : Keeps [.eax] s v)
      (V : (v.gpr .eax).toNat = w32 s.mem base (o+4*(p/32)) / 2^(p%32)) :
      WP isa (.block [.alu .and .eax (imm 1)]) v fun t =>
        t.mem=s.mem ∧ (t.gpr .eax).toNat=bit (val32 s.mem base o k) p ∧ Keeps [.eax] s t := by
    refine wp_andi fun t T => WP.block_nil ⟨T.mem.trans M,?_,K.trans (T.keeps.mono (by decide))⟩
    rw [T.gpr,BitVec.toNat_and,show (1#32).toNat=1 from rfl,Nat.and_one_is_mod,V]
    exact word_bit hp
  by_cases zero : p%32=0
  · simp only [zero,beq_self_eq_true,ite_true,List.nil_append]
    apply finish U.mem (U.keeps.mono (by decide))
    rw [U.gpr,zero,Nat.pow_zero,Nat.div_one]
  · simp only [show (p%32 == 0)=false by exact beq_eq_false_iff_ne.mpr zero]
    refine wp_shr (by omega) fun v V _ => ?_
    apply finish (V.mem.trans U.mem) ((U.keeps.mono (by decide)).trans (V.keeps.mono (by decide)))
    rw [V.gpr,U.gpr,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

end VG.Proof.Mont.X86.Comb
