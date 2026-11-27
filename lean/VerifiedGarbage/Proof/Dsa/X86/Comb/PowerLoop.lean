module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerDigits
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
import VerifiedGarbage.Impl.Mont.X86.CombPower
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Mont.X86.WindowSelect
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! ### `Dsa.X86.Comb.PowerInit`, which the modules that import this one used -/

section

/-! Initialize the comb accumulator and zero-pad its exponent. -/

-- Formerly `VerifiedGarbage/Proof/Mont/X86/PadWords.lean`, which only this module imported.
section

/-! Zero padding retains the exponent's value at a wider public storage width. -/

section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem padWords_ok {s : State} {base : Addr} {size o used total : Nat}
    (hs : Scr s base size) (hu : used≤total) (ho : o+4*total≤size) :
    WP isa (VG.Impl.Mont.X86.Comb.padWords o used total) s fun t =>
      Outside base (o+4*used) (4*(total-used)) s.mem t.mem ∧
      val32 t.mem base o total=val32 s.mem base o used ∧ Keeps [.eax,.ebp,.edx] s t := by
  unfold VG.Impl.Mont.X86.Comb.padWords
  split
  next h =>
    refine WP.mono (zerosW_ok hs (by omega) (by omega)) fun t ⟨O,V,K⟩ => ⟨O,?_,K⟩
    have hn := hs.nowrap
    have bound : o+4*used≤2^64 := by omega
    have eq : total=used+(total-used) := by omega
    rw [eq,val32_append,O.val32 (.inl (by omega)) bound,V,Nat.mul_zero,Nat.add_zero]
  next h =>
    have eq : total=used := by omega
    subst total
    exact WP.block_nil ⟨Outside.refl _ _ _ _,rfl,Keeps.refl _ _⟩

end VG.Proof.Mont.X86.Comb
end

end

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
      exact ⟨(slot n 8,4*expWords e),by simp [powerRanges],by omega_using [],by have := shape.2.2.2.2; omega⟩)
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

end

end

/-! ### `Dsa.X86.Comb.PowerStep`, which only this module used -/

section

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
    (by rw [Bu]; exact Nat.mod_lt _ (by have := Cu.gt_one; omega_using [this]))) fun v ⟨Cv,Kv,lv,Vv⟩ => ?_)
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
      rcases hr with rfl|rfl|rfl <;> simp [powerRanges,contextMod,accLen,words] <;> omega_using [])
    rw [M]; exact Ou.trans ov

end VG.Proof.Dsa.X86.Comb

end

end


/-! The fixed-count comb scan reconstructs the full secret exponent. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt partialDigit_shifted)
open VG.Proof.Rsa.FixedBaseComb (high high_top high_step high_zero)

structure PowerLoop (n e m g x i : Nat) (base : Addr) (s t : State) : Prop where
  ctx : Context n m base (layout n e).size t
  table : TableAt n (context n) m g (32*e) base (fun _ => True) t.mem
  acc : wordsVal t.mem base (slot n 6) n = Spec.Rsa.powMod g (high (32*e) x (rows e-i)) m*2^(64*n)%m
  exp : val32 t.mem base (slot n 8) (expWords e)=x*2^i%2^(32*expWords e)
  count : t.gpr .esi=BitVec.ofNat 32 (rows e-i)
  mem : Outs base (powerRanges n e) s.mem t.mem
  keeps : Keeps powerClob s t

theorem powerLoop_step {n e m g x i : Nat} {base : Addr} {s t : State}
    (h : Supported n e) (pub : Bool) (hi : i<rows e) (I : PowerLoop n e m g x i base s t) :
    WP isa (VG.Impl.Mont.X86.Comb.powerStep n e (context n) pub) t fun u =>
      PowerLoop n e m g x (i+1) base s u ∧ u.zf=some (decide (i+1=rows e)) := by
  have hb := power_bounds h
  refine WP.mono (powerStep_ok h pub I.ctx I.table I.acc (by omega_using [hi]) (by omega_using [hb]) I.count)
    fun u ⟨Cu,Tu,Au,Eu,ESI,Z,O,K⟩ => ?_
  refine ⟨⟨Cu,Tu,?_,?_,?_,I.mem.trans O,I.keeps.trans K⟩,?_⟩
  · rw [I.exp] at Au
    have shift : rows e-1-(rows e-1-i)=i := by omega_using [hi]
    have digit := partialDigit_shifted (32*e) x (32*expWords e) (rows e-1-i) (by change rows e-1-i<rows e; omega_using [hi]) hb.2.2.2.2.1
    change VG.Proof.Mont.X86.Comb.partialDigit (rows e) ((x*2^(rows e-1-(rows e-1-i)))%2^(32*expWords e)) 5 = _ at digit
    rw [shift] at digit
    rw [digit] at Au
    have next : rows e-(i+1)=rows e-1-i := by omega_using []
    have prev : rows e-i=(rows e-1-i)+1 := by omega_using [hi]
    rw [next]
    rw [prev,←high_step (32*e) x (rows e-1-i) (by change rows e-1-i<rows e; omega_using [hi])] at Au
    exact Au
  · rw [Eu,I.exp,Nat.mod_mul_mod,Nat.pow_succ,Nat.mul_assoc]
  · simpa only [Nat.sub_sub] using ESI
  · simpa only [show (rows e-i=1) ↔ (i+1=rows e) by omega_using []] using Z

theorem powerLoop_initial {n e m g x : Nat} {base : Addr} {s : State}
    (h : Supported n e) (C : Context n m base (layout n e).size s)
    (T : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem)
    (A : wordsVal s.mem base (slot n 6) n=2^(64*n)%m)
    (X : val32 s.mem base (slot n 8) (expWords e)=x)
    (bound : x<2^(32*e)) (ESI : s.gpr .esi=BitVec.ofNat 32 (rows e)) :
    PowerLoop n e m g x 0 base s s := by
  have padded : e≤expWords e := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  have xb : x<2^(32*expWords e) := Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega_using [padded]))
  have init : PowerLoop n e m g x 0 base s s := by
    refine ⟨C,T,?_,?_,?_,Outs.refl _ _ _,Keeps.refl _ _⟩
    · rw [Nat.sub_zero,show rows e=Spec.Rsa.FixedBaseComb.rows (32*e) from rfl,high_top,VG.Proof.Bignum.powMod_eq,Nat.pow_zero,Nat.mod_mul_mod,Nat.one_mul,A]
    · rw [Nat.pow_zero,Nat.mul_one,Nat.mod_eq_of_lt xb,X]
    · simpa only [Nat.sub_zero] using ESI
  exact init

theorem powerLoop_ok {n e m g x : Nat} {base : Addr} {s : State}
    (h : Supported n e) (pub : Bool) (C : Context n m base (layout n e).size s)
    (T : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem)
    (A : wordsVal s.mem base (slot n 6) n=2^(64*n)%m)
    (X : val32 s.mem base (slot n 8) (expWords e)=x)
    (bound : x<2^(32*e)) (ESI : s.gpr .esi=BitVec.ofNat 32 (rows e)) :
    WP isa (.loop (VG.Impl.Mont.X86.Comb.powerStep n e (context n) pub) .ne) s fun t =>
      Context n m base (layout n e).size t ∧
      TableAt n (context n) m g (32*e) base (fun _ => True) t.mem ∧
      wordsVal t.mem base (slot n 6) n=Spec.Rsa.powMod g x m*2^(64*n)%m ∧
      Outs base (powerRanges n e) s.mem t.mem ∧ Keeps powerClob s t := by
  have init := powerLoop_initial h C T A X bound ESI
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop (power_bounds h).1
    (PowerLoop n e m g x · base s) (fun i t hi I => powerLoop_step h pub hi I) init)
    fun t I => ⟨I.ctx,I.table,?_,I.mem,I.keeps⟩
  simpa only [Nat.sub_self,high_zero _ _ bound] using I.acc

end VG.Proof.Dsa.X86.Comb
