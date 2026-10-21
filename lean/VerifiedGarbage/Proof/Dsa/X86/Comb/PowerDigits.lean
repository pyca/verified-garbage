module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
public import VerifiedGarbage.Proof.Mont.X86.CombDigit
import VerifiedGarbage.Proof.Mont.X86.CombShift
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
public import VerifiedGarbage.Impl.Mont.X86.CombPower
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable

/-! Square the accumulator and extract the next digit before table selection. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt tableValue partialDigit)

theorem powerDigits_ok {n e m g E : Nat} {base : Addr} {s : State}
    (h : Supported n e) (C : Context n m base (layout n e).size s)
    (T : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem)
    (A : wordsVal s.mem base (slot n 6) n = Spec.Rsa.powMod g E m * 2^(64*n)%m) :
    WP isa (VG.Impl.Mont.X86.Comb.powerDigits n e) s fun t =>
      Context n m base (layout n e).size t ∧
      TableAt n (context n) m g (32*e) base (fun _ => True) t.mem ∧
      wordsVal t.mem base (slot n 6) n = Spec.Rsa.powMod g (2*E) m * 2^(64*n)%m ∧
      val32 t.mem base (slot n 8) (expWords e) =
        val32 s.mem base (slot n 8) (expWords e)*2%2^(32*expWords e) ∧
      w32 t.mem base 4=partialDigit (rows e) (val32 s.mem base (slot n 8) (expWords e)) 5 ∧
      Outs base (powerRanges n e) s.mem t.mem ∧ Keeps [.eax,.ebx,.ecx,.edx,.ebp] s t := by
  obtain ⟨dp,_,ep,ew,cover,eb,sz⟩ := power_bounds h
  unfold VG.Impl.Mont.X86.Comb.powerDigits VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine WP.seq (WP.mono (context_mul_ok C (o := 6) (a := 6) (b := 6)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [A]; exact Nat.mod_lt _ (by have := C.gt_one; omega))) fun u ⟨Cu,Ku,lu,Vu⟩ => ?_)
  have Au := VG.Proof.Rsa.FixedBaseComb.mont_square_encoded C.coprime lu A Vu
  have Eu := context_slot_val32 C (i := 8) (by decide) ew (by decide) (by decide) (by decide) Ku
  have Tu := T.op (table_layout h) C (by decide) Ku
  refine WP.seq (WP.mono (VG.Proof.Mont.X86.Comb.digit_ok Cu.scr eb dp cover sz)
    fun v ⟨Ov,Vv,Kv⟩ => ?_)
  have Cv := Cu.outside_keep Kv (by decide) (by decide) Ov (.inr (by simp [slot])) (by decide)
  have Tv := Tu.outside (table_layout h) Cu.scr Ov (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
  have Av : wordsVal v.mem base (slot n 6) n = Spec.Rsa.powMod g (2*E) m * 2^(64*n)%m := by
    rw [Ov.wordsVal (.inr (by have := slot_header n 6; omega)) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),Au]
  have Ev : val32 v.mem base (slot n 8) (expWords e) = val32 s.mem base (slot n 8) (expWords e) := by
    rw [Ov.val32 (.inr (by have := slot_header n 8; omega)) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),Eu]
  rw [Eu] at Vv
  refine WP.seq (WP.mono (shiftOne_ok Cv.scr ep eb) fun w ⟨Ow,Vw,Kw⟩ => ?_)
  have Cw := Cv.outside_keep Kw (by decide) (by decide) Ow (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
    (by have := slot_header n 8; omega)
  have Tw := Tv.outside (table_layout h) Cv.scr Ow (by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide)
  have Ww : w32 w.mem base 4 = partialDigit (rows e) (val32 s.mem base (slot n 8) (expWords e)) 5 := by
    rw [Ow.w32 (.inl (by have := slot_header n 8; omega)) (by decide),Vv]
    rfl
  have Aw : wordsVal w.mem base (slot n 6) n = Spec.Rsa.powMod g (2*E) m * 2^(64*n)%m := by
    rw [Ow.wordsVal (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide) (by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),Av]
  change val32 w.mem base (slot n 8) (expWords e) = val32 v.mem base (slot n 8) (expWords e)*2%2^(32*expWords e) at Vw
  rw [Ev] at Vw
  refine WP.block_nil ⟨Cw,Tw,Aw,Vw,Ww,?_,?_⟩
  · have ou : Outs base (powerRanges n e) s.mem u.mem := Ku.mem.mono (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> simp [powerRanges,contextMod,accLen,words] <;> omega)
    have ov := Outs.of_outside Ov (rs := powerRanges n e) (by simp [powerRanges])
    have ow := Outs.of_outside Ow (rs := powerRanges n e) (by simp [powerRanges,expWords,rows])
    exact (ou.trans ov).trans ow
  · exact (((OpKeep.keeps Ku).mono (by decide)).trans (Kv.mono (by decide))).trans Kw

end VG.Proof.Dsa.X86.Comb
