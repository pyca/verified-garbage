module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombLayout
public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombTable
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Framework.PlainSimp

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
  all_goals simp only <;> omega

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
    omega
  refine ⟨i.scr.of_rest keep r12,i.far.of_rest keep,
    i.table.of_frame (by rw [keep.rd,keep.wr]) frame (by simpa only [List.mem_singleton,forall_eq] using hd),
    by rw [syms]; exact i.symbol,?_,?_,?_,?_⟩
  · rw [mem.wordsVal h.zero_apart (by have hl := lay_nums h.n3 h.n6; omega),i.zero]
  · intro j hj
    rw [coarse.byte (fun w hw => .inr (by have := bounded w hw; omega)) (by omega),i.bits j hj]
  · rw [params _ (by simp),i.coeffA]
  · rw [params _ (by simp),i.coeffB]

end VG.Proof.Weierstrass.Arm.TComb
