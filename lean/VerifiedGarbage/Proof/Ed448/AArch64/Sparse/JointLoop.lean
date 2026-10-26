module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.JointStep
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The descending joint loop represents the complete unreduced scalar pair. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide (digitAt residual)
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (off)
open VG.Proof.X448.AArch64.Base (pt)
open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Proof.EdwardsLaw (EPoint)
open VG.Proof.Curve448.AArch64.Fast (Mb)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem baseDigit_bound (k i:Nat) : -127≤digitAt true k i ∧ digitAt true k i≤127:=by
  have h:=WnafWide.digit_bounds true (residual true k i)
  change (-128:Int)<digitAt true k i ∧ digitAt true k i<128 at h
  omega

theorem keyDigit_bound (k i:Nat) : -15≤digitAt false k i ∧ digitAt false k i≤15:=by
  have h:=WnafWide.digit_bounds false (residual false k i)
  change (-16:Int)<digitAt false k i ∧ digitAt false k i<16 at h
  omega

structure JointInv (s₀:State) (base:Addr) (P:Spec.Ed448.Point) (S K n:Nat) (s:State) : Prop where
  bound : n≤464
  core : Core base s
  counter : s.gpr .x19=BitVec.ofNat 64 n
  tab : OddTabOk s.mem base P 8
  xb : ∀ e<8,∀ w<8,(Window.tw s.mem base e w).toNat<Mb
  baseTable : BaseTableAt s base (s.syms baseSym)
  sd : ∀ i<464,s.mem (off base (SDIG+i))=BitVec.ofInt 8 (digitAt true S i)
  kd : ∀ i<464,s.mem (off base (BITS+i))=BitVec.ofInt 8 (digitAt false K i)
  rep : ∀ a:EPoint dZ,Rep P a → Rep (pt (EV s.mem base) 3 4 5)
    ((residual true S n:Int) • baseAff+(residual false K n:Int) • a)
  chk : s.gpr .x20=s₀.gpr .x20
  rd : s.rd=s₀.rd
  wr : s.wr=s₀.wr
  mem : JointFrame base s₀.mem s.mem

theorem jointRound_ok (hA:AffineOk) {s₀ s:State} {base:Addr} {P:Spec.Ed448.Point} {S K i:Nat}
    (h:JointInv s₀ base P S K (i+1) s) :
    WP isa step s fun t => JointInv s₀ base P S K i t ∧ t.gpr .x9=BitVec.ofNat 64 i:=by
  have hi:i<464:=by have := h.bound;omega
  refine WP.mono_syms (jointStep_ok hA h.core h.tab h.xb h.baseTable hi h.counter
    (baseDigit_bound S i) (keyDigit_bound K i) (h.sd i hi) (h.kd i hi))
    fun t ⟨tc,tk,t19,t9,tp⟩ sy => ?_
  refine ⟨⟨by omega,tc,t19,tk.mem.oddTable h.tab,tk.mem.xbounds h.xb,?_,?_,?_,?_,?_,?_,?_,?_⟩,t9⟩
  · rw [sy]
    exact h.baseTable.of_frame (by rw [tk.regs.2.1,tk.regs.2.2]) tk.mem
  · intro j hj
    rw [tk.mem.baseDigit hj]
    exact h.sd j hj
  · intro j hj
    rw [tk.mem.keyDigit hj]
    exact h.kd j hj
  · intro a ha
    rw [tp]
    exact WnafWide.round_rep (h.rep a ha)
      (WnafWide.keyEntry_rep ha (WnafWide.digit_zero_or_odd false _))
  · rw [tk.regs.1 _ (by decide)]
    exact h.chk
  · rw [tk.regs.2.1]
    exact h.rd
  · rw [tk.regs.2.2]
    exact h.wr
  · exact fun x a b c => (tk.mem x a b c).trans (h.mem x a b c)

private theorem counter_zero : ∀ i<464,(BitVec.ofNat 64 i==0)=decide (i=0):=by decide +kernel

theorem jointLoop_ok (hA:AffineOk) {s₀ s:State} {base:Addr} {P:Spec.Ed448.Point} {S K n:Nat}
    (hn:0<n) (h:JointInv s₀ base P S K n s) :
    WP isa (.loop step (.nonzero .x .x9)) s (JointInv s₀ base P S K 0):=by
  refine WP.loop (M:=isa) (body:=step) (c:=.nonzero .x .x9)
    (Q:=JointInv s₀ base P S K 0)
    (fun m s => 0<m ∧ JointInv s₀ base P S K m s) ?_ n s ⟨hn,h⟩
  intro m s ⟨hm,h⟩
  obtain ⟨i,rfl⟩:∃ i,m=i+1:=⟨m-1,by omega⟩
  refine WP.mono (jointRound_ok hA h) fun t ⟨ht,t9⟩ => ?_
  have hi:i<464:=by have := h.bound;omega
  simp only [eval,State.read,BitVec.setWidth_eq,t9,bne,counter_zero i hi]
  by_cases hz:i=0
  · subst i
    exact Or.inl ⟨rfl,ht⟩
  · refine Or.inr ⟨?_,i,by omega,by omega,ht⟩
    simp only [hz,decide_false,Bool.not_false]

end VG.Proof.Ed448.AArch64.Sparse
