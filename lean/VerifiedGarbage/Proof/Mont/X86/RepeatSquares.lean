module

public import VerifiedGarbage.Impl.Mont.X86.RepeatSquares
import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Mont.X86.Loop

/-! A shared squaring-loop proof, independent of the caller's workspace layout. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86

structure SquaresInv (P : State → Prop) (num : State → Nat) (m R E count i : Nat) (t : State) : Prop where
  state : P t
  counter : t.gpr .esi=BitVec.ofNat 32 (count-i)
  bound : num t<m
  value : num t%m=2^(2^i*E)*R%m

/-- Reuse a proved Montgomery square; only the public countdown is added. -/
theorem repeatSquaresWith_ok (square : Prog isa) (P : State → Prop) (num : State → Nat)
    {m R E count : Nat} (coprime : Nat.Coprime R m)
    (stable : ∀ s t,P s → t.mem=s.mem → Keeps [.esi] s t → P t)
    (number : ∀ s t,t.mem=s.mem → num t=num s)
    (step : ∀ s,P s → num s<m → WP isa square s fun t =>
      P t ∧ Keeps clob s t ∧ num t<m ∧ num t*R%m=num s*num s%m)
    (positive : 0<count) (small : count<2^32) {s : State}
    (initial : P s) (bound : num s<m) (value : num s%m=2^E*R%m) :
    WP isa (repeatSquaresWith square count) s fun t =>
      P t ∧ num t<m ∧ num t%m=2^(2^count*E)*R%m := by
  unfold repeatSquaresWith
  refine WP.seq (wp_movS rfl fun u su _ => WP.block_nil ?_)
  have init : SquaresInv P num m R E count 0 u := by
    refine ⟨stable s u initial su.mem su.keeps,su.gpr,?_,?_⟩
    · rw [number s u su.mem];exact bound
    · simpa only [Nat.pow_zero,Nat.one_mul,number s u su.mem] using value
  have body {i : Nat} {t : State} (I : SquaresInv P num m R E count i t) (hi : i<count) :
      WP isa (squareStepWith square) t fun w =>
        SquaresInv P num m R E count (i+1) w ∧ w.zf=some (decide (i+1=count)) := by
    unfold squareStepWith
    refine WP.seq (WP.mono (step t I.state I.bound) fun v ⟨Pv,Kv,lt,Mv⟩ => ?_)
    have val := VG.Proof.Bignum.mont_sq coprime I.value Mv
    have cnt : v.gpr .esi=BitVec.ofNat 32 (count-i) := (Kv.1 _ (by decide)).trans I.counter
    refine wp_subS rfl fun a va _ => ?_
    refine wp_cmpS rfl fun w aw zw => WP.block_nil ?_
    have mem : w.mem=v.mem := aw.mem.trans va.mem
    have keep : Keeps [.esi] v w := va.keeps.trans (aw.keeps [.esi])
    refine ⟨⟨stable v w Pv mem keep,?_,?_,?_⟩,?_⟩
    · rw [aw.gpr,va.gpr,cnt,counter_sub (by omega : count-i<2^32) (by omega)]
      congr 1
    · rw [number v w mem];exact lt
    · rw [number v w mem]
      simpa only [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using val
    · rw [zw,va.gpr,cnt,counter_sub (by omega : count-i<2^32) (by omega),counter_zero (by omega) (by omega)]
      simp only [show (count-i=1)↔i+1=count by omega]
  have loop : WP isa (.loop (squareStepWith square) .ne) u
      (SquaresInv P num m R E count count) := by
    refine WP.loop (M := isa)
      (fun k t => ∃ i,k=count-i ∧ i<count ∧ SquaresInv P num m R E count i t) ?_
      count u ⟨0,rfl,positive,init⟩
    rintro k t ⟨i,rfl,hi,I⟩
    refine WP.mono (body I hi) fun w ⟨next,zf⟩ => ?_
    by_cases done : i+1=count
    · refine .inl ⟨?_,done ▸ next⟩
      simp only [eval,zf,done,decide_true,Option.map_some,Bool.not_true]
    · refine .inr ⟨?_,count-(i+1),by omega,i+1,rfl,by omega,next⟩
      simp only [eval,zf,decide_eq_false done,Option.map_some,Bool.not_false]
  exact WP.mono loop fun t I => ⟨I.state,I.bound,I.value⟩

end VG.Proof.Mont.X86.Dynamic
