module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
public import VerifiedGarbage.Proof.Mont.X86.CombDigit

import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerDigits
import VerifiedGarbage.Impl.Mont.X86.CombPower
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
/-! One complete comb iteration, including its public countdown. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/PowerLookup.lean`, which only this module imported.
section

/-! One square and comb lookup, with public or private table selection. -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt tableValue partialDigit)

theorem powerStep_ok {n e m g E k : Nat} {base : Addr} {s : State}
    (h : Supported n e) (pub : Bool) (C : Context n m base (layout n e).size s)
    (T : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem)
    (A : wordsVal s.mem base (slot n 6) n = Spec.Rsa.powMod g E m * 2^(64*n)%m)
    (hk : 0<k) (hk32 : k<2^32) (ESI : s.gpr .esi=BitVec.ofNat 32 k) :
    WP isa (VG.Impl.Mont.X86.Comb.powerStep n e (context n) pub) s fun t =>
      Context n m base (layout n e).size t ∧
      TableAt n (context n) m g (32*e) base (fun _ => True) t.mem ∧
      wordsVal t.mem base (slot n 6) n = Spec.Rsa.powMod g
        (2*E+Spec.Rsa.FixedBaseComb.exponent (32*e)
          (partialDigit (rows e) (val32 s.mem base (slot n 8) (expWords e)) 5)) m * 2^(64*n)%m ∧
      val32 t.mem base (slot n 8) (expWords e) =
        val32 s.mem base (slot n 8) (expWords e)*2%2^(32*expWords e) ∧
      t.gpr .esi=BitVec.ofNat 32 (k-1) ∧ t.zf=some (decide (k=1)) ∧
      Outs base (powerRanges n e) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold VG.Impl.Mont.X86.Comb.powerStep VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine WP.seq (WP.mono (powerLookup_ok h pub C T A) fun u ⟨Cu,Tu,Au,Bu,Eu,Ou,Ku⟩ => ?_)
  refine WP.seq (WP.mono (context_mul_ok Cu (o := 6) (a := 6) (b := 7)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [Bu]; exact Nat.mod_lt _ (by have := Cu.gt_one; omega))) fun v ⟨Cv,Kv,lv,Vv⟩ => ?_)
  have Av := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded Cu.coprime lv Au Bu Vv
  have Tv := Tu.op (table_layout h) Cu (by decide) Kv
  have Ev := (context_slot_val32 Cu (i := 8) (by decide) (power_bounds h).2.2.2.1
    (by decide) (by decide) (by decide) Kv).trans Eu
  have esiv : v.gpr .esi=BitVec.ofNat 32 k := by rw [Kv.gpr .esi (by decide),Ku.1 .esi (by decide),ESI]
  refine WP.seq (wp_subS rfl fun w W _ => wp_cmpS rfl fun t F Z => WP.block_nil (WP.block_nil ?_))
  have M : t.mem=v.mem := F.mem.trans W.mem
  have K : Keeps powerClob v t := (W.keeps.mono (by decide)).trans (F.keeps _)
  have Ct : Context n m base (layout n e).size t :=
    ⟨Cv.scr.of_keeps K (by decide),Cv.size_le,M ▸ Cv.modulus,Cv.gt_one,M ▸ Cv.inverse⟩
  refine ⟨Ct,M ▸ Tv,M ▸ Av,M ▸ Ev,?_,?_,?_,((Ku.mono (by decide)).trans ((OpKeep.keeps Kv).mono (by decide))).trans K⟩
  · rw [F.gpr,W.gpr,esiv]
    exact counter_sub hk32 hk
  · rw [Z,W.gpr,esiv]
    change some (BitVec.ofNat 32 k - 1 - 0 == 0) = _
    rw [counter_sub hk32 hk,counter_zero hk32 hk]
  · have ov : Outs base (powerRanges n e) u.mem v.mem := Kv.mem.mono (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> simp [powerRanges,contextMod,accLen,words] <;> omega)
    rw [M]; exact Ou.trans ov

end VG.Proof.Dsa.X86.Comb
