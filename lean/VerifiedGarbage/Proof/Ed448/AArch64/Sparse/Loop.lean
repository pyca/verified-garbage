module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Step
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! The in-place public recoder preserves future input bits and completed digits. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off ofs Outside writeW8_apply writeW8_outside off_eq_iff)

structure RecInv (base : Addr) (wide : Bool) (k : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  scr : Scr s base
  x19 : s.gpr .x19=BitVec.ofNat 64 i
  carry : ∃ c≤radix wide, s.gpr .x6=BitVec.ofNat 64 c ∧ residual wide k i+half wide=k/2^i+c
  keep : Keeps recClob s₀ s
  mem : Outside base BITS 464 s₀.mem s.mem
  digits : ∀ j<i, s.mem (off base (BITS+j))=Enc wide k j
  bits : ∀ j, i≤j → j<464 → s.mem (off base (BITS+j))=BitVec.ofNat 8 (WnafWide.bit k j)

theorem RecInv.advance {base : Addr} {wide : Bool} {k i : Nat} {s₀ s u : State}
    (h:RecInv base wide k s₀ i s) (hi:i<464) (g:StepOut base wide k i s u) :
    RecInv base wide k s₀ (i+1) u := by
  refine ⟨g.scr,g.x19,g.carry,h.keep.trans g.keep,?_,?_,?_⟩
  · intro p hp
    rw [g.mem,writeW8_outside _ base _ (by simp only [BITS];omega) (by omega)]
    exact h.mem p hp
  · intro j hj
    rw [g.mem,writeW8_apply]
    simp only [off_eq_iff base (d:=BITS+j) (e:=BITS+i) (by simp only [BITS];omega) (by simp only [BITS];omega)]
    by_cases he:j=i
    · subst j
      simp only [ite_true]
    · rw [ite_eq_right (by omega)]
      exact h.digits j (by omega)
  · intro j hj hj'
    rw [g.mem,writeW8_outside _ base _ (by simp only [BITS];omega) (by
      rw [VG.Proof.X448.AArch64.ofs_off' base (by simp only [BITS];omega)]
      omega)]
    exact h.bits j (by omega) hj'

theorem recodeLoop_ok (wide : Bool) {base : Addr} {k i : Nat} {s₀ s : State}
    (hi:i<456) (h:RecInv base wide k s₀ i s) :
    WP isa (.loop (.block (recodeBody wide)) (.nonzero .x .x9)) s
      (RecInv base wide k s₀ 456) := by
  refine WP.loop (M:=isa) (body:=.block (recodeBody wide)) (c:=.nonzero .x .x9)
    (Q:=RecInv base wide k s₀ 456)
    (fun m s => ∃ i, m=456-i ∧ i<456 ∧ RecInv base wide k s₀ i s) ?_ (456-i) s ⟨i,rfl,hi,h⟩
  rintro m s ⟨i,rfl,hi,h⟩
  obtain ⟨c,hc,h6,hrel⟩:=h.carry
  refine WP.mono (recodeBody_ok wide h.scr hi hc h.x19 h6 hrel
    (fun j hj => by simpa only [Nat.add_assoc] using h.bits (i+j) (by omega) (by omega))) fun u ⟨g,gz⟩ => ?_
  have hu:=h.advance (by omega) g
  simp only [eval,State.read,BitVec.setWidth_eq,bne,gz]
  by_cases hn:i+1<456
  · refine .inr ⟨?_,456-(i+1),by omega,i+1,rfl,hn,hu⟩
    simp only [decide_eq_false (by omega : ¬i+1=456),Bool.not_false]
  · have he:i+1=456 := by omega
    rw [he] at hu
    exact .inl ⟨by simp only [he,decide_true,Bool.not_true],hu⟩

theorem recodeTail_ok (wide : Bool) {base : Addr} {k i n : Nat} {s₀ s : State}
    (hk:k<VG.Impl.Ed448.WnafWide.scalarLimit) (hi:456≤i) (hend:i+n≤464) (h:RecInv base wide k s₀ i s) :
    WP isa (recodeTail wide n) s (RecInv base wide k s₀ (i+n)) := by
  induction n generalizing i s with
  | zero =>
    simpa only [recodeTail,Nat.add_zero] using (WP.block_nil h)
  | succ n ih =>
    rw [recodeTail]
    obtain ⟨c,hc,h6,hrel⟩:=h.carry
    refine WP.seq (WP.mono (zeroStep_ok wide h.scr hk (by omega) hi hc h.x19 h6 hrel)
      fun u g => ?_)
    have hu:=h.advance (by omega) g
    have hr:=ih (i:=i+1) (by omega) (by omega) hu
    have he:i+1+n=i+(n+1) := by omega
    rw [he] at hr
    exact hr

end VG.Proof.Ed448.AArch64.Sparse
