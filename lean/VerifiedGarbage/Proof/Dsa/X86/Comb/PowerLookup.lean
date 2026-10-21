module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerDigits
public import VerifiedGarbage.Proof.Mont.X86.CombDigit
import VerifiedGarbage.Proof.Mont.X86.CombShift
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
public import VerifiedGarbage.Impl.Mont.X86.CombPower
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable

/-! One square and comb lookup, with public or private table selection. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt tableValue partialDigit)

theorem powerLookup_ok {n e m g E : Nat} {base : Addr} {s : State}
    (h : Supported n e) (pub : Bool) (C : Context n m base (layout n e).size s)
    (T : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem)
    (A : wordsVal s.mem base (slot n 6) n = Spec.Rsa.powMod g E m * 2^(64*n)%m) :
    WP isa (VG.Impl.Mont.X86.Comb.powerLookup n e (context n) pub) s fun t =>
      Context n m base (layout n e).size t ∧
      TableAt n (context n) m g (32*e) base (fun _ => True) t.mem ∧
      wordsVal t.mem base (slot n 6) n = Spec.Rsa.powMod g (2*E) m * 2^(64*n)%m ∧
      wordsVal t.mem base (slot n 7) n =
        tableValue n m g (32*e) (partialDigit (rows e) (val32 s.mem base (slot n 8) (expWords e)) 5) ∧
      val32 t.mem base (slot n 8) (expWords e) =
        val32 s.mem base (slot n 8) (expWords e)*2%2^(32*expWords e) ∧
      Outs base (powerRanges n e) s.mem t.mem ∧ Keeps [.eax,.ebx,.ecx,.edx,.ebp] s t := by
  unfold VG.Impl.Mont.X86.Comb.powerLookup VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine WP.seq (WP.mono (powerDigits_ok h C T A) fun w ⟨Cw,Tw,Aw,Vw,Ww,Ow,Kw⟩ => ?_)
  refine WP.seq (WP.mono (select_table_ok h pub Cw Tw (by rw [Ww]; exact VG.Proof.Mont.X86.Comb.partialDigit_lt _ _ _))
    fun t ⟨Ct,Tt,Vt,Ot,Kt⟩ => WP.block_nil ?_)
  refine ⟨Ct,Tt,?_,by rw [Vt,Ww],?_,?_,?_⟩
  · rw [wordsVal_eq_val32,Ot.val32 (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),←wordsVal_eq_val32,Aw]
  · rw [Ot.val32 (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),Vw]
  · exact Ow.trans (Ot.mono (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> simp [powerRanges]))
  · exact Kw.trans Kt

end VG.Proof.Dsa.X86.Comb
