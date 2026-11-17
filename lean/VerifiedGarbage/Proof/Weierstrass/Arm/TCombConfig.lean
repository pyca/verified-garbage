module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombTable
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.CombDigitW
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP

/-! ### `Weierstrass.Arm.TCombLayout`, which this module and modules that import it used -/

section

/-! Workspace geometry shared by the comb setup and its addition loop. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Proof.Weierstrass.Arm.Point

/-- The accumulator and negation temporary lie below the point-call workspace. -/
structure Layout (K : TCombCfg) : Prop where
  n3 : 3≤K.L.M.n
  n6 : K.L.M.n≤6
  point : LadPt K.L
  low : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z,K.zero,K.neg],
    x+8*K.L.M.n≤Impl.Weierstrass.Point.oAt K.L.M.n
  apart : (K.L.R.x+8*K.L.M.n≤K.L.R.y ∨ K.L.R.y+8*K.L.M.n≤K.L.R.x) ∧
    (K.L.R.x+8*K.L.M.n≤K.L.R.z ∨ K.L.R.z+8*K.L.M.n≤K.L.R.x) ∧
    (K.L.R.y+8*K.L.M.n≤K.L.R.z ∨ K.L.R.z+8*K.L.M.n≤K.L.R.y)
  negApart : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z,K.zero],
    K.neg+8*K.L.M.n≤x ∨ x+8*K.L.M.n≤K.neg
  zeroApart : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z],
    K.zero+8*K.L.M.n≤x ∨ x+8*K.L.M.n≤K.zero

/-- All writes, including point-call and field-call temporaries. -/
def writes (K : TCombCfg) : List (Nat × Nat) :=
  [(K.L.R.x,8*K.L.M.n),(K.L.R.y,8*K.L.M.n),(K.L.R.z,8*K.L.M.n),
   (K.neg,8*K.L.M.n),(Impl.Weierstrass.Point.oAt K.L.M.n,
     4096-Impl.Weierstrass.Point.oAt K.L.M.n)]

/-- Iterations preserve the curve parameters between `Q` and the call workspace. -/
def loopWrites (K : TCombCfg) : List (Nat × Nat) :=
  [(K.L.R.x,8*K.L.M.n),(K.L.R.y,8*K.L.M.n),(K.L.R.z,8*K.L.M.n),
   (K.neg,8*K.L.M.n),(Impl.Weierstrass.Point.oAt K.L.M.n,72*K.L.M.n),
   (Impl.Weierstrass.Point.ownAt K.L.M.n,4096-Impl.Weierstrass.Point.ownAt K.L.M.n)]

theorem Layout.loop_cover {K : TCombCfg} (h : Layout K) :
    ∀ r ∈ loopWrites K, ∃ t ∈ writes K,t.1≤r.1 ∧ r.1+r.2≤t.1+t.2 := by
  intro r hr
  simp only [loopWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨_,List.mem_cons_self ..,Nat.le_refl _,Nat.le_refl _⟩
  · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self ..),Nat.le_refl _,Nat.le_refl _⟩
  · exact ⟨_,by simp [writes],Nat.le_refl _,Nat.le_refl _⟩
  · exact ⟨_,by simp [writes],Nat.le_refl _,Nat.le_refl _⟩
  all_goals exact ⟨(Impl.Weierstrass.Point.oAt K.L.M.n,4096-Impl.Weierstrass.Point.oAt K.L.M.n),
    by simp [writes],lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)⟩

theorem Layout.q_cover {K : TCombCfg} (h : Layout K) :
    ∀ r ∈ [(K.Q.x,24*K.L.M.n)], ∃ t ∈ loopWrites K,t.1≤r.1 ∧ r.1+r.2≤t.1+t.2 := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨(Impl.Weierstrass.Point.oAt K.L.M.n,72*K.L.M.n),by simp [loopWrites],?_⟩
  simp only [VG.Impl.Weierstrass.Arm.TCombCfg.Q,VG.Impl.Weierstrass.Arm.Point.ptAt]
  exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)

theorem Layout.sub_cover {K : TCombCfg} (h : Layout K) :
    ∀ r ∈ [(K.neg,8*K.L.M.n),(VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n,64*K.L.M.n)],
      ∃ t ∈ loopWrites K,t.1≤r.1 ∧ r.1+r.2≤t.1+t.2 := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨(K.neg,8*K.L.M.n),by simp [loopWrites],Nat.le_refl _,Nat.le_refl _⟩
  · exact ⟨(Impl.Weierstrass.Point.ownAt K.L.M.n,4096-Impl.Weierstrass.Point.ownAt K.L.M.n),
      by simp [loopWrites],lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)⟩

theorem Layout.bounded {K : TCombCfg} (h : Layout K) :
    ∀ r ∈ writes K, 0≤r.1 ∧ r.1+r.2≤4096 := by
  have hl := lay_nums h.n3 h.n6
  have low := h.low
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at low
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false]
  intro r hr
  rcases hr with rfl|rfl|rfl|rfl|rfl <;> simp only [Nat.zero_le, true_and] <;> omega_arith

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! ### `Weierstrass.Arm.TCombInputs`, which only this module used -/

section

/-! Scalar bits, curve coefficients, and ROM survive every comb iteration. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm
open VG.Proof.Weierstrass.Arm.Point

structure Inputs (K : TCombCfg) (base T : Addr) (ws : List (BitVec 64))
    (k a b : Nat) (s : State) : Prop where
  scr : Scr s base 4096
  far : Far s base 8192
  table : TableMem s T ws
  symbol : State.addr (s.syms K.tsym)=T
  zero : wordsVal s.mem base K.zero K.L.M.n=0
  bits : ∀ i<K.L.nbits,s.mem (off base (K.L.bits+i))=if k.testBit i then 1 else 0
  coeffA : wordsVal s.mem base (Impl.Weierstrass.Point.aAt K.L.M.n) K.L.M.n=a
  coeffB : wordsVal s.mem base (Impl.Weierstrass.Point.b3At K.L.M.n) K.L.M.n=b

theorem Layout.zero_apart {K : TCombCfg} (h : Layout K) :
    ∀ r ∈ loopWrites K,K.zero+8*K.L.M.n≤r.1 ∨ r.1+r.2≤K.zero := by
  have low := h.low K.zero (by simp)
  have neg := h.negApart K.zero (by simp)
  intro r hr
  simp only [loopWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  · exact h.zeroApart _ (by simp)
  · exact h.zeroApart _ (by simp)
  · exact h.zeroApart _ (by simp)
  · exact neg.symm
  · exact .inl low
  · have below : Impl.Weierstrass.Point.oAt K.L.M.n≤Impl.Weierstrass.Point.ownAt K.L.M.n := by
      exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)
    exact .inl (Nat.le_trans low below)

theorem Layout.params_apart {K : TCombCfg} (h : Layout K) :
    ∀ x ∈ [Impl.Weierstrass.Point.aAt K.L.M.n,Impl.Weierstrass.Point.b3At K.L.M.n],
      ∀ r ∈ loopWrites K,x+8*K.L.M.n≤r.1 ∨ r.1+r.2≤x := by
  have low := h.low
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at low
  intro x hx r hr
  simp only [loopWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals have geom : Impl.Weierstrass.Point.oAt K.L.M.n+72*K.L.M.n≤x ∧
      x+8*K.L.M.n≤Impl.Weierstrass.Point.ownAt K.L.M.n :=
    lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide) x hx
  all_goals simp only <;> omega_arith

theorem Inputs.keep {K : TCombCfg} {base T : Addr} {ws : List (BitVec 64)} {k a b : Nat}
    {s t : State} {rs : List Reg} (i : Inputs K base T ws k a b s)
    (h : Layout K) (hb : 4096≤K.L.bits) (hend : K.L.bits+K.L.nbits≤8192)
    (hd : Region.Disjoint ⟨T,8*ws.length⟩ ⟨base,4096⟩)
    (keep : Rest rs s t) (r12 : Reg.r12∉rs) (mem : Unch base (loopWrites K) s.mem t.mem)
    (syms : t.syms=s.syms) : Inputs K base T ws k a b t := by
  have bounded := h.bounded
  have coarse := mem.cover h.loop_cover
  have frame : Frame [⟨base,4096⟩] s.mem t.mem := outside_frame
    (coarse.outside (o := 0) (n := 4096) bounded) (Nat.le_refl _)
  have nowrap := i.scr.nowrap
  have low := h.low K.zero (by simp)
  have params : ∀ x ∈ [Impl.Weierstrass.Point.aAt K.L.M.n,Impl.Weierstrass.Point.b3At K.L.M.n],
      wordsVal t.mem base x K.L.M.n=wordsVal s.mem base x K.L.M.n := by
    intro x hx
    apply mem.wordsVal (h.params_apart x hx)
    have fit : x+8*K.L.M.n≤4096 := by
      exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide) x hx
    omega_using [fit]
  refine ⟨i.scr.of_rest keep r12,i.far.of_rest keep,
    i.table.of_frame (by rw [keep.rd,keep.wr]) frame (by simpa only [List.mem_singleton,forall_eq] using hd),
    by rw [syms]; exact i.symbol,?_,?_,?_,?_⟩
  · rw [mem.wordsVal h.zero_apart (by have hl := lay_nums h.n3 h.n6; omega_using [low, hl]),i.zero]
  · intro j hj
    rw [coarse.byte (fun w hw => .inr (by have := bounded w hw; omega_using [hb, this])) (by omega_using [hend, hj]),i.bits j hj]
  · rw [params _ (by simp),i.coeffA]
  · rw [params _ (by simp),i.coeffB]

end VG.Proof.Weierstrass.Arm.TComb

end

end


/-! Side conditions for a fixed-base comb, independent of its input scalar. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm
open Spec.Weierstrass

structure Config (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat)))
    (start : Nat × Nat) : Prop where
  layout : Layout K
  fieldK : K.F.k=K.L.M.n
  fieldM : K.F.m=C.p
  modulus : VG.Proof.Weierstrass.Arm.Mont.ModOk K.L.M.n C.p
  unit : UnitMod C.p (2^(64*K.L.M.n))
  tables : CombOkW C K.w K.J tbl start
  one_lt : K.one<C.p
  one : toM C.p (2^(64*K.L.M.n)) K.one=1
  startX : K.start.1=start.1*2^(64*K.L.M.n)%C.p
  startY : K.start.2=start.2*2^(64*K.L.M.n)%C.p
  w1 : 1≤K.w
  w9 : K.w<9
  J1 : 1≤K.J
  J32 : K.J<2^32
  startBits : K.w*(K.J-1)≤K.L.nbits
  coverBits : K.L.nbits≤K.w*K.J
  bitsLow : 4096≤K.L.bits
  bitsHigh : K.L.bits+K.L.nbits≤8192
  bitsFit : K.L.bits<8192
  windowFit : K.L.bits%4096+K.w≤4096
  encJ : encodable (BitVec.ofNat 32 K.J)=true
  encLast : encodable (BitVec.ofNat 32 (K.J-1))=true
  encRow : encodable (BitVec.ofNat 32 (16*K.L.M.n*K.H))=true
  encEntry : encodable (BitVec.ofNat 32 (16*K.L.M.n))=true
  encH : encodable (BitVec.ofNat 32 (K.H+1))=true

def tableWords (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) : List (BitVec 64) :=
  tcombWords K.L.M.n (2^(64*K.L.M.n)) C.p tbl

abbrev CurveInputs (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat)))
    (base T : Addr) (k : Nat) (s : State) : Prop :=
  Inputs K base T (tableWords K C tbl) k (C.a*2^(64*K.L.M.n)%C.p)
    ((3*C.b)*2^(64*K.L.M.n)%C.p) s

theorem Config.magnitude {K : TCombCfg} {C : Curve} {tbl : List (List (Nat × Nat))}
    {start : Nat × Nat} (h : Config K C tbl start) (k j : Nat) :
    magH K.H (combWin K.w k j)≤K.H := by
  apply magH_le
  have pow : 2^K.w=2*K.H := by
    change 2^K.w=2*2^(K.w-1)
    calc
      2^K.w=2^((K.w-1)+1) := congrArg (fun n => 2^n) (by have := h.w1; omega_using [this])
      _ = 2*2^(K.w-1) := by rw [Nat.pow_succ,Nat.mul_comm]
  rw [← pow]
  exact combWin_lt _ _ _

theorem Config.halfBound {K : TCombCfg} {C : Curve} {tbl : List (List (Nat × Nat))}
    {start : Nat × Nat} (h : Config K C tbl start) : K.H+1<2^31 := by
  have hw := h.w9
  have bound : K.H≤2^8 := Nat.pow_le_pow_right (by decide) (by omega_using [hw])
  omega_using [bound]

end VG.Proof.Weierstrass.Arm.TComb
