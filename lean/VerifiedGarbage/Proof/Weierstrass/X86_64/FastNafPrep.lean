module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafState
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafOdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafChoose
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafSubtract
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Weierstrass.X86_64.FastNafStep`, which only this module used -/

section

/-! Each recoder step advances one bit for an even residual, or one window for an odd residual. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

theorem FastPrepState.of_keeps {s t : State} {base : Addr} {size n bits w k j : Nat}
    (h : FastPrepState n base size bits w k j s) {rs : List Reg} (hk : Keeps rs s t)
    (hr : ∀ r∈[Reg.rdi,.rbx,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi],r∉rs) :
    FastPrepState n base size bits w k j t := by
  refine ⟨h.scr.of_keeps hk (hr _ (by simp)),?_,?_,?_⟩
  · rw [nafValN_keep hk.1 (fun r hr' => hr r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr')))]
    exact h.value
  · exact (hk.1 .rbx (hr _ (by simp))).trans h.count
  · rw [hk.2.1]
    exact h.digits

def fastDelta (w k j : Nat) : Nat := if FastNaf.residual w k j%2=0 then 1 else w

theorem fastEvenStep_ok {s : State} {base : Addr} {size n bits w k j : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hI : FastPrepState n base size bits w k j s)
    (ho : FastNaf.residual w k j%2=0) :
    WP isa (.block (Impl.Weierstrass.X86_64.FastNaf.shiftN n 1++Impl.Weierstrass.X86_64.FastNaf.advance 1)) s fun t =>
      FastPrepState n base size bits w k (j+1) t ∧ KeepRegs (nafPrepClobN n) s t ∧
      Outside base bits (64*n+8) s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (fastShiftN_ok s hn (Or.inl rfl)) fun a ⟨va,ka⟩ => ?_
  obtain ca : a.gpr .rbx=BitVec.ofNat 64 j := (ka.1 _ (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)).trans hI.count
  refine WP.mono (fastAdvance_ok a (Or.inl rfl) ca) fun t ⟨ct,kt⟩ => ?_
  obtain mt : t.mem=s.mem := kt.2.1.trans ka.2.1
  refine ⟨⟨(hI.scr.of_keeps ka (fun h => by
    rcases List.mem_cons.mp h with h|h
    · cases h
    exact notin_sregs (by decide) h)).of_keeps kt (by decide),?_,ct,?_⟩,?_,?_⟩
  · rw [nafValN_keep kt.1 (by decide),va,hI.value,
      FastNaf.residual_succ,FastNaf.next_even w _ ho]
  · intro i hi
    rw [mt,hI.digits i hi]
    by_cases he : i=j
    · subst i
      simp only [Nat.lt_irrefl,ite_false,Nat.lt_add_one,ite_true]
      exact ((FastNaf.byte_zero_iff w k j).mpr ((FastNaf.magnitude_zero_iff w k j).mpr ho)).symm
    · have hh : (i<j)=(i<j+1) := propext (by omega_using [he])
      simp only [hh]
  · exact ((VG.Proof.Mont.X86_64.Keeps.regs ka).mono (fun r hr => mem_clobN (pre:=[.rax])
      (by decide) hr)).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kt).mono (fun r hr => mem_clobN (pre:=[.rbx])
        (by decide) (List.mem_append_left _ hr)))
  · rw [mt]
    exact Outside.refl _ _ _ _

theorem fastPrepStep_ok {s : State} {base : Addr} {size n bits w k j : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hw : FastNaf.Width w) (hI : FastPrepState n base size bits w k j s)
    (hb : bits+64*n+8≤size) (hj : j<64*n+1) (hv : FastNaf.residual w k j≤2^(64*n)) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.stepN n bits w) s fun t =>
      FastPrepState n base size bits w k (j+fastDelta w k j) t ∧
      t.cf=some (decide (j+fastDelta w k j<64*n+1)) ∧ KeepRegs (nafPrepClobN n) s t ∧
      Outside base bits (64*n+8) s.mem t.mem := by
  obtain hd : fastDelta w k j=1 ∨ fastDelta w k j=5 ∨ fastDelta w k j=7 := by
    unfold fastDelta
    split
    · exact Or.inl rfl
    · exact Or.inr hw
  rw [Impl.Weierstrass.X86_64.FastNaf.stepN]
  refine WP.seq (WP.mono (nafParity_ok s) fun a ⟨_,hz,ka⟩ => ?_)
  obtain ia := hI.of_keeps ka (by decide)
  obtain hp : s.gpr .r8 &&& 1=0 ↔ FastNaf.residual w k j%2=0 := by
    rw [nafParity]
    have h := hI.value
    rw [nafValN_r8] at h
    omega_using [h]
  apply WP.seq
  obtain branches : WP isa
      (.ite .e (.block (Impl.Weierstrass.X86_64.FastNaf.shiftN n 1++Impl.Weierstrass.X86_64.FastNaf.advance 1))
        (.seq (Impl.Weierstrass.X86_64.FastNaf.choose w)
          (.block (Naf.subtractDigitN n++[.store8 (tbl bits) .rcx]++
            Impl.Weierstrass.X86_64.FastNaf.shiftN n w++Impl.Weierstrass.X86_64.FastNaf.advance w)))) a
      (fun t => FastPrepState n base size bits w k (j+fastDelta w k j) t ∧
        KeepRegs (nafPrepClobN n) a t ∧ Outside base bits (64*n+8) a.mem t.mem) := by
    apply WP.ite (decide (s.gpr .r8 &&& 1=0)) hz
    · intro h
      obtain he := hp.mp (of_decide_eq_true h)
      simpa only [fastDelta,he,ite_true] using fastEvenStep_ok hn ia he
    · intro h
      obtain he : FastNaf.residual w k j%2≠0 := fun he => (of_decide_eq_false h) (hp.mpr he)
      simpa only [fastDelta,he,ite_false] using fastOddStep_ok hn hw ia hb hj hv he
  refine WP.mono branches fun b ⟨ib,kb,ob⟩ => ?_
  refine WP.mono (fastCompare_ok b (n:=n) (by omega_using [hn]) (by rcases hd with h|h|h <;> omega_using [hn, hj, h]) ib.count)
    fun t ⟨cf,kt⟩ => ?_
  refine ⟨ib.of_keeps kt (by simp),cf,?_,?_⟩
  · exact (((VG.Proof.Mont.X86_64.Keeps.regs ka).mono (fun r hr => mem_clobN (pre:=[.rcx])
      (by decide) (List.mem_append_left _ hr))).trans kb).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kt).mono (by simp))
  · rw [kt.2.1,ka.2.1] at *
    exact ob

/-- `fastPrepStep_ok` for the step without branches on the scalar's bits, of width five: the digit is
zero and the shift one for an even residual. -/
theorem fastPrepStepB_ok {s : State} {base : Addr} {size n bits k j : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hI : FastPrepState n base size bits 5 k j s)
    (hb : bits+64*n+8≤size) (hj : j<64*n+1) (hv : FastNaf.residual 5 k j≤2^(64*n)) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.stepB n bits) s fun t =>
      FastPrepState n base size bits 5 k (j+fastDelta 5 k j) t ∧
      t.cf=some (decide (j+fastDelta 5 k j<64*n+1)) ∧ KeepRegs (nafPrepClobN n) s t ∧
      Outside base bits (64*n+8) s.mem t.mem := by
  obtain hw : FastNaf.Width 5 := Or.inl rfl
  obtain hx : (s.gpr .r8).toNat%2^5=FastNaf.residual 5 k j%2^5 := by
    have h := hI.value
    rw [nafValN_r8] at h
    omega_using [h]
  obtain hp : (s.gpr .r8).toNat%2=FastNaf.residual 5 k j%2 := by omega_using [hx]
  obtain hδ : (if (s.gpr .r8).toNat%2=0 then 1 else 1+2^2)=fastDelta 5 k j := by
    unfold fastDelta
    rw [hp]
  obtain hsft : fastDelta 5 k j=1 ∨ fastDelta 5 k j=5 ∨ fastDelta 5 k j=7 ∨ fastDelta 5 k j=9 := by
    unfold fastDelta
    split
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  rw [Impl.Weierstrass.X86_64.FastNaf.stepB,WP.block_append_iff]
  refine WP.mono (digitB_ok s (Or.inl rfl)) fun a ⟨da,ka⟩ => ?_
  obtain sa := hI.scr.of_keeps ka (by decide)
  obtain va : nafValN n a=FastNaf.residual 5 k j :=
    (nafValN_keep ka.1 (by decide)).trans hI.value
  obtain da' := da.trans (fastSel_eq (Or.inl rfl) hx)
  rw [WP.block_append_iff]
  refine WP.mono (fastSubtractN_ok a hn 5 k j da' va hv) fun b ⟨vb,kb⟩ => ?_
  obtain nb : ∀ r,r∉[Reg.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi] → r≠.rax → r≠.rdx →
      r∉Reg.rax::Reg.rdx::Naf.sregs n := fun r h1 h2 h3 h => by
    rcases List.mem_cons.mp h with h|h
    · exact h2 h
    rcases List.mem_cons.mp h with h|h
    · exact h3 h
    exact notin_sregs h1 h
  obtain sb := sa.of_keeps kb (nb _ (by decide) (by decide) (by decide))
  obtain cb : b.gpr .rbx=BitVec.ofNat 64 j :=
    (kb.1 _ (nb _ (by decide) (by decide) (by decide))).trans ((ka.1 _ (by decide)).trans hI.count)
  obtain db : b.gpr .rcx=BitVec.ofInt 64 (FastNaf.digit 5 k j) :=
    (kb.1 _ (nb _ (by decide) (by decide) (by decide))).trans da'
  rw [WP.block_append_iff]
  refine WP.mono (fastStore_ok sb (by omega_using [hb, hj]) cb db) fun c ⟨mc,kc⟩ => ?_
  obtain sc := sb.of_keepRegs kc (by simp)
  obtain dc : c.gpr .rcx &&& 1=s.gpr .r8 &&& 1 := by
    rw [kc.gpr _ (by simp),db,←fastSel_eq (Or.inl rfl) hx,fastSel_low (Or.inl rfl)]
  rw [WP.block_append_iff]
  refine WP.mono (countB_ok c (Or.inl rfl) dc) fun e ⟨ex,ec,ke⟩ => ?_
  rw [hδ] at ex ec
  obtain se := sc.of_keeps ke (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fastShiftV_ok e hn hsft ex ec) fun d ⟨vd,kd⟩ => ?_
  obtain nd : ∀ r,r∉[Reg.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi] → r≠.rax →
      r∉Reg.rax::Naf.sregs n := fun r h1 h2 h => by
    rcases List.mem_cons.mp h with h|h
    · exact h2 h
    exact notin_sregs h1 h
  obtain sd := se.of_keeps kd (nd _ (by decide) (by decide))
  obtain cd : d.gpr .rbx=BitVec.ofNat 64 j :=
    (kd.1 _ (nd _ (by decide) (by decide))).trans ((ke.1 _ (by decide)).trans ((kc.gpr _ (by simp)).trans cb))
  obtain dd : d.gpr .rdx=BitVec.ofNat 64 (fastDelta 5 k j) := (kd.1 _ (nd _ (by decide) (by decide))).trans ex
  show WP isa (.block (([.alu .add .rbx (.reg .rdx)] : List Instr)++
    [.alu .cmp .rbx (.imm (BitVec.ofNat 32 (64*n+1)))])) d _
  rw [WP.block_append_iff]
  refine WP.mono (fastAdvanceV_ok d cd dd) fun f ⟨cf',kf⟩ => ?_
  refine WP.mono (fastCompare_ok f (n:=n) (by omega_using [hn]) (by rcases hsft with h|h|h|h <;> omega_using [hn, hj, h]) cf')
    fun t ⟨cf,kt⟩ => ?_
  obtain mt : t.mem=s.mem.writeW (off base (bits+j)) (FastNaf.byte 5 k j) := by
    rw [kt.2.1,kf.2.1,kd.2.1,ke.2.1,mc,kb.2.1,ka.2.1]
  obtain O := writeW8_outside s.mem base (FastNaf.byte 5 k j) (d:=bits+j)
    (by have := hI.scr.nowrap; omega_using [hb, hj, this])
  refine ⟨⟨(sd.of_keeps kf (by decide)).of_keeps kt (by simp),?_,(kt.1 _ (by simp)).trans cf',?_⟩,cf,?_,?_⟩
  · rw [nafValN_keep kt.1 (by simp),nafValN_keep kf.1 (by decide),vd,nafValN_keep ke.1 (by decide),
      nafValN_keep kc.gpr (by simp),vb]
    by_cases ho : FastNaf.residual 5 k j%2=0
    · simp only [fastDelta,ho,ite_true]
      omega_using []
    · simp only [fastDelta,ho,ite_false]
      rw [FastNaf.residual_succ,FastNaf.next_odd hw _ ho,FastNaf.residual_skip hw k j ho]
      omega_using []
  · intro i hi
    rw [mt]
    by_cases hij : i=j
    · subst i
      rw [writeW8_self,ite_eq_left (show j<j+fastDelta 5 k j by rcases hsft with h|h|h|h <;> omega_using [h])]
    · rw [O _ (by rw [ofs_off0 base (d:=bits+i) (by have:=hI.scr.nowrap; omega_using [hb, hi, this])]; omega_using [hij]),hI.digits i hi]
      by_cases hij' : i<j
      · simp only [hij',show i<j+fastDelta 5 k j from by omega_using [hij'],ite_true]
      · by_cases hil : i<j+fastDelta 5 k j
        · simp only [hij',hil,ite_false,ite_true]
          obtain ho : FastNaf.residual 5 k j%2≠0 := fun ho => by
            simp only [fastDelta,ho,ite_true] at hil
            omega_arith
          obtain hil' : i<j+5 := by simpa only [fastDelta,ho,ite_false] using hil
          exact (FastNaf.byte_skip_zero hw k j (i-j) ho (by omega_using [hij, hij']) (by omega_using [hil'])).symm.trans
            (by rw [Nat.add_sub_of_le (by omega_using [hij'])])
        · simp only [hij',hil,ite_false]
  · exact ((((((VG.Proof.Mont.X86_64.Keeps.regs ka).mono (fun r hr => mem_clobN (pre:=[.rax,.rcx,.rdx])
      (by decide) (List.mem_append_left _ hr))).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kb).mono (fun r hr => mem_clobN (pre:=[.rax,.rdx])
        (by decide) hr))).trans (kc.mono (by simp))).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs ke).mono (fun r hr => mem_clobN (pre:=[.rcx,.rdx])
        (by decide) (List.mem_append_left _ hr)))).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kd).mono (fun r hr => mem_clobN (pre:=[.rax])
        (by decide) hr))).trans
      (((VG.Proof.Mont.X86_64.Keeps.regs kf).mono (fun r hr => mem_clobN (pre:=[.rbx])
        (by decide) (List.mem_append_left _ hr))).trans
        ((VG.Proof.Mont.X86_64.Keeps.regs kt).mono (by simp)))
  · rw [mt]
    exact O.mono (by omega_using []) (by omega_using [hj])

end VG.Proof.Weierstrass.X86_64

end

end


/-! The sparse recoder of a scalar of `n` words terminates at index `64 n + 1` or later and
produces every required digit. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

theorem fastDelta_bounds {w : Nat} (hw : FastNaf.Width w) (k j : Nat) :
    1≤fastDelta w k j ∧ fastDelta w k j≤7 := by
  unfold fastDelta
  split
  · decide
  · rcases hw with rfl|rfl <;> decide

/-- What a step of the recoder does: `stepN`'s (`fastPrepStep_ok`) and, for width five, `stepB`'s
(`fastPrepStepB_ok`). -/
def FastStepOk (n bits w : Nat) (step : Prog isa) : Prop :=
  ∀ {s : State} {base : Addr} {size k j : Nat},FastPrepState n base size bits w k j s →
    bits+64*n+8≤size → j<64*n+1 → FastNaf.residual w k j≤2^(64*n) →
    WP isa step s fun t =>
      FastPrepState n base size bits w k (j+fastDelta w k j) t ∧
      t.cf=some (decide (j+fastDelta w k j<64*n+1)) ∧ KeepRegs (nafPrepClobN n) s t ∧
      Outside base bits (64*n+8) s.mem t.mem

/-- The recoder's loop, of any step that does what `stepN` does. -/
theorem fastPrepOf_ok {step : Prog isa} {s : State} {base : Addr} {size n src bits w : Nat}
    (hn : n=4 ∨ n=6 ∨ n=9) (hw : FastNaf.Width w) (hS : FastStepOk n bits w step)
    (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+64*n+8≤size) :
    WP isa (.seq (.block (Naf.initN n src++setConst (8*n+1) bits 0)) (.loop step .b)) s fun t =>
      (∃ j,64*n+1≤j ∧ j≤64*n+7 ∧ FastPrepState n base size bits w (wordsVal s.mem base src n) j t) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem := by
  let k := wordsVal s.mem base src n
  obtain hk : k<2^(64*n) := wordsVal_lt ..
  let I (m : Nat) (t : State) := FastPrepState n base size bits w k (64*n+1-m) t ∧
    KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem
  refine WP.seq (WP.mono (fastPrepInit_ok (w:=w) hn hs hsrc hb) fun a ⟨ia,ka,oa⟩ => ?_)
  refine WP.loop (M:=isa) (fun m t => 1≤m ∧ m≤64*n+1 ∧ I m t) (fun m t ⟨hm,hm',hi⟩ => ?_)
    (64*n+1) a ⟨by omega_using [],by omega_using [],by simpa only [Nat.sub_self] using ia,ka,oa⟩
  obtain hj : 64*n+1-m<64*n+1 := by omega_using [hm]
  obtain hv : FastNaf.residual w k (64*n+1-m)≤2^(64*n) := by
    obtain h := FastNaf.residual_boundB w (Nat.le_of_lt hk) (j:=64*n+1-m) (by omega_using [hm])
    exact Nat.le_trans h (Nat.pow_le_pow_right (by decide) (by omega_using []))
  obtain hd := fastDelta_bounds hw k (64*n+1-m)
  refine WP.mono (hS hi.1 hb hj hv) fun u ⟨iu,cf,ku,ou⟩ => ?_
  obtain ki := hi.2.1.trans ku
  obtain oi := hi.2.2.trans ou
  by_cases he : 64*n+1≤64*n+1-m+fastDelta w k (64*n+1-m)
  · refine Or.inl ⟨?_,⟨_,he,by omega_using [hm, hd],iu⟩,ki,oi⟩
    change u.cf=some false
    rw [cf]
    congr 1
    exact decide_eq_false (by omega_using [he])
  · refine Or.inr ⟨?_,m-fastDelta w k (64*n+1-m),by omega_using [hm, hd],by omega_using [he],by omega_using [hm'],?_,ki,oi⟩
    · change u.cf=some true
      rw [cf]
      congr 1
      exact decide_eq_true (by omega_using [he])
    · rw [show 64*n+1-(m-fastDelta w k (64*n+1-m))=64*n+1-m+fastDelta w k (64*n+1-m) from by omega_using [hm', he]]
      exact iu

theorem fastPrep_ok {s : State} {base : Addr} {size n src bits w : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hw : FastNaf.Width w) (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+64*n+8≤size) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.prepN n src bits w) s fun t =>
      (∃ j,64*n+1≤j ∧ j≤64*n+7 ∧ FastPrepState n base size bits w (wordsVal s.mem base src n) j t) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem :=
  fastPrepOf_ok hn hw (fun hI hb hj hv => fastPrepStep_ok hn hw hI hb hj hv) hs hsrc hb

theorem fastPrepDigitsOf_ok {step : Prog isa} {s : State} {base : Addr} {size n src bits w : Nat}
    (hn : n=4 ∨ n=6 ∨ n=9) (hw : FastNaf.Width w) (hS : FastStepOk n bits w step)
    (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+64*n+8≤size) :
    WP isa (.seq (.block (Naf.initN n src++setConst (8*n+1) bits 0)) (.loop step .b)) s fun t =>
      (∀ i<64*n+1,t.mem (off base (bits+i))=FastNaf.byte w (wordsVal s.mem base src n) i) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem := by
  refine WP.mono (fastPrepOf_ok hn hw hS hs hsrc hb) fun t ⟨⟨j,hj,_,hi⟩,kt,ot⟩ => ⟨?_,kt,ot⟩
  intro i hi'
  simpa only [show i<j from by omega_using [hj, hi'],ite_true] using hi.digits i hi'

theorem fastPrepDigits_ok {s : State} {base : Addr} {size n src bits w : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hw : FastNaf.Width w) (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+64*n+8≤size) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.prepN n src bits w) s fun t =>
      (∀ i<64*n+1,t.mem (off base (bits+i))=FastNaf.byte w (wordsVal s.mem base src n) i) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem :=
  fastPrepDigitsOf_ok hn hw (fun hI hb hj hv => fastPrepStep_ok hn hw hI hb hj hv) hs hsrc hb

/-- `fastPrepDigits_ok` for the recoder of width five without branches on the scalar's bits. -/
theorem fastPrepDigitsB_ok {s : State} {base : Addr} {size n src bits : Nat} (hn : n=4 ∨ n=6 ∨ n=9)
    (hs : Scr s base size) (hsrc : src+8*n≤size) (hb : bits+64*n+8≤size) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.prepB n src bits) s fun t =>
      (∀ i<64*n+1,t.mem (off base (bits+i))=FastNaf.byte 5 (wordsVal s.mem base src n) i) ∧
      KeepRegs (nafPrepClobN n) s t ∧ Outside base bits (64*n+8) s.mem t.mem :=
  fastPrepDigitsOf_ok hn (Or.inl rfl) (fun hI hb hj hv => fastPrepStepB_ok hn hI hb hj hv) hs hsrc hb

end VG.Proof.Weierstrass.X86_64
