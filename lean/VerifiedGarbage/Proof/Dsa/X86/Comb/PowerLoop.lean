module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerStep
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerFrame
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
import VerifiedGarbage.Proof.Mont.X86.CombTableState

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
  refine WP.mono (powerStep_ok h pub I.ctx I.table I.acc (by omega) (by omega) I.count)
    fun u ⟨Cu,Tu,Au,Eu,ESI,Z,O,K⟩ => ?_
  refine ⟨⟨Cu,Tu,?_,?_,?_,I.mem.trans O,I.keeps.trans K⟩,?_⟩
  · rw [I.exp] at Au
    have shift : rows e-1-(rows e-1-i)=i := by omega
    have digit := partialDigit_shifted (32*e) x (32*expWords e) (rows e-1-i) (by change rows e-1-i<rows e; omega) hb.2.2.2.2.1
    change VG.Proof.Mont.X86.Comb.partialDigit (rows e) ((x*2^(rows e-1-(rows e-1-i)))%2^(32*expWords e)) 5 = _ at digit
    rw [shift] at digit
    rw [digit] at Au
    have next : rows e-(i+1)=rows e-1-i := by omega
    have prev : rows e-i=(rows e-1-i)+1 := by omega
    rw [next]
    rw [prev,←high_step (32*e) x (rows e-1-i) (by change rows e-1-i<rows e; omega)] at Au
    exact Au
  · rw [Eu,I.exp,Nat.mod_mul_mod,Nat.pow_succ,Nat.mul_assoc]
  · simpa only [Nat.sub_sub] using ESI
  · simpa only [show (rows e-i=1) ↔ (i+1=rows e) by omega] using Z

theorem powerLoop_initial {n e m g x : Nat} {base : Addr} {s : State}
    (h : Supported n e) (C : Context n m base (layout n e).size s)
    (T : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem)
    (A : wordsVal s.mem base (slot n 6) n=2^(64*n)%m)
    (X : val32 s.mem base (slot n 8) (expWords e)=x)
    (bound : x<2^(32*e)) (ESI : s.gpr .esi=BitVec.ofNat 32 (rows e)) :
    PowerLoop n e m g x 0 base s s := by
  have padded : e≤expWords e := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  have xb : x<2^(32*expWords e) := Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega))
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
