module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
import VerifiedGarbage.Proof.Mont.X86.PadWords
import VerifiedGarbage.Proof.Mont.X86.WindowSelect
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Bignum.Math

/-! Initialize the comb accumulator and zero-pad its exponent. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt tableValue)

theorem powerInit_ok {n e m g : Nat} {base : Addr} {s : State}
    (h : Supported n e) (C : Context n m base (layout n e).size s)
    (T : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem) :
    WP isa (VG.Impl.Mont.X86.Comb.powerInit n e (context n)) s fun t =>
      Context n m base (layout n e).size t ∧
      TableAt n (context n) m g (32*e) base (fun _ => True) t.mem ∧
      wordsVal t.mem base (slot n 6) n=2^(64*n)%m ∧
      val32 t.mem base (slot n 8) (expWords e)=val32 s.mem base (slot n 8) e ∧
      t.gpr .esi=BitVec.ofNat 32 (rows e) ∧
      Outs base (powerRanges n e) s.mem t.mem ∧ Keeps powerClob s t := by
  have shape : 0<n ∧ context n+16*n+8*n≤(layout n e).size ∧
      slot n 6+8*n≤(layout n e).size ∧ slot n 6+8*n≤context n+16*n ∧ e≤expWords e := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  unfold VG.Impl.Mont.X86.Comb.powerInit VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine WP.seq (WP.mono (copyWords_ok C.scr shape.1 shape.2.1 shape.2.2.1 (.inr (.inl shape.2.2.2.1)))
    fun u ⟨Vu,Ou,Ku⟩ => ?_)
  have O1 : Outs base (powerRanges n e) s.mem u.mem := Outs.of_outside Ou (by simp [powerRanges])
  have K1 : Keeps powerClob s u := Ku.mono (by decide)
  have Cu := power_context h C O1 K1
  have Au : wordsVal u.mem base (slot n 6) n=2^(64*n)%m := by
    have Tv := T 0 (by decide) trivial
    simp only [entry,Nat.mul_zero,Nat.add_zero,tableValue,
      VG.Proof.Rsa.FixedBaseComb.exponent_zero,VG.Proof.Bignum.powMod_eq,Nat.pow_zero,
      Nat.mod_mul_mod,Nat.one_mul] at Tv
    exact Vu.trans Tv
  have Eu : val32 u.mem base (slot n 8) e=val32 s.mem base (slot n 8) e := Ou.val32 (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
  refine WP.seq (WP.mono (VG.Proof.Mont.X86.Comb.padWords_ok Cu.scr shape.2.2.2.2 (power_bounds h).2.2.2.2.2.1)
    fun v ⟨Ov,Vv,Kv⟩ => ?_)
  have O2 : Outs base (powerRanges n e) u.mem v.mem := VG.Proof.Mont.X86.Comb.widen
    (Outs.of_outside Ov (by simp : (slot n 8+4*e,4*(expWords e-e)) ∈ [(slot n 8+4*e,4*(expWords e-e))])) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨(slot n 8,4*expWords e),by simp [powerRanges],by omega,by have := shape.2.2.2.2; omega⟩)
  have Av : wordsVal v.mem base (slot n 6) n=2^(64*n)%m := by
    rw [Ov.wordsVal (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),Au]
  refine WP.seq (wp_movS rfl fun t U _ => WP.block_nil (WP.block_nil ?_))
  have O : Outs base (powerRanges n e) s.mem t.mem := U.mem ▸ O1.trans O2
  have K : Keeps powerClob s t := ((K1.trans (Kv.mono (by decide))).trans (U.keeps.mono (by decide)))
  exact ⟨power_context h C O K,power_preserves_table h C.scr T O,U.mem ▸ Av,
    U.mem ▸ Vv.trans Eu,U.gpr,O,K⟩

end VG.Proof.Dsa.X86.Comb
