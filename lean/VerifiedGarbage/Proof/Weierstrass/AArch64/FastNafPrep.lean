import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafInit

/-! ## `FastNafStep` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

def fastStepClob : List Reg := [.x1,.x2,.x3,.x5,.x6,.x7,.x8,.x9,.x19,.x20]

theorem fastKept {rs : List Reg} {s t : State} (h : Keeps rs s t)
    (hr : ∀ r∈rs,r∈fastStepClob) : KeepRegs fastStepClob s t :=
  (⟨h.gpr,h.rd,h.wr,h.sp⟩ : KeepRegs rs s t).mono hr

theorem FastPrepCore.next {s t : State} {base : Addr} {size bits w k j j' : Nat}
    (hI : FastPrepCore base size bits w k j s) (ht : KeepRegs fastStepClob s t)
    (hv : nafVal5 (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) (t.gpr .x8) (t.gpr .x9)=FastNaf.residual w k j')
    (hp : t.gpr .x20=off base (bits+j')) : FastPrepCore base size bits w k j' t :=
  ⟨hI.scr.of_keepRegs ht (by decide),hv,
   (ht.gpr _ (by decide)).trans hI.mask,(ht.gpr _ (by decide)).trans hI.sign,
   (ht.gpr _ (by decide)).trans hI.zero,(ht.gpr _ (by decide)).trans hI.one,hp⟩

theorem fast_skip_div {w : Nat} (hw : FastNaf.Width w) (k j : Nat)
    (ho : FastNaf.residual w k j%2≠0) :
    2*FastNaf.residual w k (j+1)/2^w=FastNaf.residual w k (j+w) := by
  rw [FastNaf.residual_succ,FastNaf.next_odd hw _ ho,FastNaf.residual_skip hw k j ho]
  rcases hw with rfl | rfl <;> simp only [Nat.reduceSub,Nat.reducePow] <;> omega

theorem fastOdd_ok {s : State} {base : Addr} {size bits w k j : Nat}
    (hI : FastPrepCore base size bits w k j s) (hw : FastNaf.Width w)
    (hb : bits+264≤size) (hj : j<257) (hv : FastNaf.residual w k j≤2^256)
    (ho : FastNaf.residual w k j%2≠0) :
    WP isa (.block (Impl.Weierstrass.AArch64.FastNaf.odd w)) s fun t =>
      FastPrepCore base size bits w k (j+w) t ∧ KeepRegs fastStepClob s t ∧
      t.mem=s.mem.writeW (off base (bits+j)) (FastNaf.byte w k j) := by
  rw [Impl.Weierstrass.AArch64.FastNaf.odd]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fastChoose_ok s hw k j hI.mask hI.sign hI.value ho) fun a ⟨da,ka⟩ => ?_
  have sa := hI.scr.of_keeps ka (by decide)
  have pa := (ka.gpr .x20 (by decide)).trans hI.ptr
  rw [WP.block_append_iff]
  refine WP.mono (fastStore_ok sa hb hj pa da) fun b ⟨mb,kb⟩ => ?_
  have vb : nafVal5 (b.gpr .x5) (b.gpr .x6) (b.gpr .x7) (b.gpr .x8) (b.gpr .x9)=FastNaf.residual w k j := by
    simp only [kb.gpr _ List.not_mem_nil,ka.gpr .x5 (by decide),ka.gpr .x6 (by decide),
      ka.gpr .x7 (by decide),ka.gpr .x8 (by decide),ka.gpr .x9 (by decide),hI.value]
  rw [WP.block_append_iff]
  refine WP.mono (fastSubtract_ok b w k j
    (by rw [kb.gpr _ List.not_mem_nil,ka.gpr _ (by decide),hI.zero])
    (by rw [kb.gpr _ List.not_mem_nil]; exact da) vb hv) fun c ⟨vc,kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fastShift_ok c w (Or.inr hw)) fun d ⟨vd,kd⟩ => ?_
  have pd : d.gpr .x20=off base (bits+j) := by
    rw [kd.gpr _ (by decide),kc.gpr _ (by decide),kb.gpr _ List.not_mem_nil,pa]
  refine WP.mono (fastAdvance_ok d (by rcases hw with rfl | rfl <;> decide) pd) fun t ⟨pt,kt⟩ => ?_
  have keep := (fastKept ka (by decide)).trans ((kb.mono (by simp)).trans
    ((fastKept kc (by decide)).trans ((fastKept kd (by decide)).trans (fastKept kt (by decide)))))
  refine ⟨hI.next keep ?_ pt,keep,?_⟩
  · simp only [kt.gpr .x5 (by decide),kt.gpr .x6 (by decide),kt.gpr .x7 (by decide),
      kt.gpr .x8 (by decide),kt.gpr .x9 (by decide),vd,vc,fast_skip_div hw k j ho]
  · rw [kt.mem,kd.mem,kc.mem,mb,ka.mem]

theorem fastEven_ok {s : State} {base : Addr} {size bits w k j : Nat}
    (hI : FastPrepCore base size bits w k j s) (he : FastNaf.residual w k j%2=0) :
    WP isa (.block Impl.Weierstrass.AArch64.FastNaf.even) s fun t =>
      FastPrepCore base size bits w k (j+1) t ∧ KeepRegs fastStepClob s t ∧ t.mem=s.mem := by
  rw [Impl.Weierstrass.AArch64.FastNaf.even,WP.block_append_iff]
  refine WP.mono (fastShift_ok s 1 (Or.inl rfl)) fun a ⟨va,ka⟩ => ?_
  have pa := (ka.gpr .x20 (by decide)).trans hI.ptr
  refine WP.mono (fastAdvance_ok a (d:=1) (by decide) pa) fun t ⟨pt,kt⟩ => ?_
  have keep := (fastKept ka (by decide)).trans (fastKept kt (by decide))
  refine ⟨hI.next keep ?_ pt,keep,kt.mem.trans ka.mem⟩
  simp only [kt.gpr .x5 (by decide),kt.gpr .x6 (by decide),kt.gpr .x7 (by decide),
    kt.gpr .x8 (by decide),kt.gpr .x9 (by decide),va,hI.value]
  rw [FastNaf.residual_succ,FastNaf.next_even _ _ he]

end VG.Proof.Weierstrass.AArch64

end

/-! ## `FastNafDigits` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

theorem FastPrepState.of_keeps {s t : State} {base : Addr} {size bits w k j : Nat}
    (hI : FastPrepState base size bits w k j s) {rs : List Reg}
    (ht : Keeps rs s t) (hr : ∀ r∈rs,r∈[Reg.x1,.x2,.x3,.x19]) :
    FastPrepState base size bits w k j t := by
  have kt := ht.mono hr
  refine ⟨hI.toFastPrepCore.next (fastKept kt (by decide)) ?_ ?_,?_⟩
  · simp only [kt.gpr .x5 (by decide),kt.gpr .x6 (by decide),kt.gpr .x7 (by decide),
      kt.gpr .x8 (by decide),kt.gpr .x9 (by decide),hI.value]
  · exact (kt.gpr _ (by decide)).trans hI.ptr
  · rw [kt.mem]; exact hI.digits

theorem fastSetup_ok (K : WinCfg) {w : Nat} (hw : FastNaf.Width w)
    {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hsrc8 : src%8=0)
    (hbits : K.bits<4096) (hbits8 : K.bits%8=0) (hb : K.bits+264≤size) :
    WP isa (.block (Impl.Weierstrass.AArch64.FastNaf.init K src w ++
      Impl.Weierstrass.AArch64.FastNaf.clear K)) s fun t =>
      FastPrepState base size K.bits w (wordsVal s.mem base src 4) 0 t ∧
      KeepRegs nafPrepClob s t ∧ Outside base K.bits 264 s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (fastInit_ok K hw hs hsrc hsrc8 hbits) fun a ⟨ia,ka,ma⟩ => ?_
  refine WP.mono (fastClear_ok K ia.scr ia.zero hbits8 hb) fun t ⟨zt,kt,ot⟩ => ?_
  refine ⟨⟨ia.next (kt.mono (by simp)) ?_ ?_,?_⟩,ka.trans (kt.mono (by simp)),?_⟩
  · simp only [kt.gpr _ List.not_mem_nil,ia.value]
  · exact (kt.gpr _ List.not_mem_nil).trans ia.ptr
  · intro i hi
    simpa only [Nat.not_lt_zero,ite_false] using zt i (by omega)
  · rw [←ma]; exact ot

theorem fastOddState_ok {s : State} {base : Addr} {size bits w k j : Nat}
    (hI : FastPrepState base size bits w k j s) (hw : FastNaf.Width w)
    (hb : bits+264≤size) (hj : j<257) (hv : FastNaf.residual w k j≤2^256)
    (ho : FastNaf.residual w k j%2≠0) :
    WP isa (.block (Impl.Weierstrass.AArch64.FastNaf.odd w)) s fun t =>
      FastPrepState base size bits w k (j+w) t ∧ KeepRegs fastStepClob s t ∧
      Outside base bits 264 s.mem t.mem := by
  refine WP.mono (fastOdd_ok hI.toFastPrepCore hw hb hj hv ho) fun t ⟨it,kt,mt⟩ => ?_
  have O := writeW8_outside s.mem base (FastNaf.byte w k j) (d:=bits+j) (by have:=hI.scr.nowrap; omega)
  refine ⟨⟨it,?_⟩,kt,?_⟩
  · intro i hi
    rw [mt]
    by_cases hij : i=j
    · subst i
      rw [writeW8_self,ite_eq_left (by rcases hw with rfl | rfl <;> omega)]
    · rw [O _ (by
        have hoff : ofs base (off base (bits+i))=bits+i := by
          simpa only [BitVec.add_zero,Nat.add_zero] using (ofs_off base (d:=bits+i) (i:=0) (by have:=hI.scr.nowrap; omega))
        rw [hoff]; omega),hI.digits i hi]
      by_cases hlt : i<j
      · simp only [hlt,ite_true,show i<j+w from by omega]
      · simp only [hlt,ite_false]
        split
        · have hz := FastNaf.byte_skip_zero hw k j (i-j) ho (by omega) (by omega)
          rw [show j+(i-j)=i from by omega] at hz
          exact hz.symm
        · rfl
  · rw [mt]; exact O.mono (by omega) (by omega)

theorem fastEvenState_ok {s : State} {base : Addr} {size bits w k j : Nat}
    (hI : FastPrepState base size bits w k j s) (he : FastNaf.residual w k j%2=0) :
    WP isa (.block Impl.Weierstrass.AArch64.FastNaf.even) s fun t =>
      FastPrepState base size bits w k (j+1) t ∧ KeepRegs fastStepClob s t ∧
      Outside base bits 264 s.mem t.mem := by
  refine WP.mono (fastEven_ok hI.toFastPrepCore he) fun t ⟨it,kt,mt⟩ => ?_
  refine ⟨⟨it,?_⟩,kt,?_⟩
  · intro i hi
    rw [mt,hI.digits i hi]
    by_cases hij : i=j
    · subst i
      have hz : FastNaf.byte w k j=0 := by rw [FastNaf.byte_zero_iff,FastNaf.magnitude_zero_iff]; exact he
      simp only [Nat.lt_irrefl,ite_false,Nat.lt_succ_self,ite_true,hz]
    · by_cases hlt : i<j
      · simp only [hlt,ite_true,show i<j+1 from by omega]
      · simp only [hlt,ite_false,show ¬i<j+1 from by omega]
  · rw [mt]; exact Outside.refl _ _ _ _

end VG.Proof.Weierstrass.AArch64

end

/-! ## `FastNafLoop` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

def fastNextIndex (w k j : Nat) : Nat := j+if FastNaf.residual w k j%2=0 then 1 else w

theorem fastNextIndex_gt {w : Nat} (hw : FastNaf.Width w) (k j : Nat) : j<fastNextIndex w k j := by
  unfold fastNextIndex
  split <;> rcases hw with rfl | rfl <;> omega

theorem fastTest_ok (s : State) (h13 : s.gpr .x13=1) :
    WP isa (.block [.logic .and .x .x1 .x5 .x13]) s fun t =>
      t.gpr .x1=s.gpr .x5 &&& 1 ∧ Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    BitVec.setWidth_eq,ite_true,h13,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,?_,rfl,rfl,rfl,rfl⟩
  intro r hr
  have h : r≠.x1 := by simpa using hr
  simp only [RegUpd.gpr_write,h,ite_false]

theorem fastLow_even {s : State} {w k j : Nat}
    (hv : nafVal5 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9)=FastNaf.residual w k j) :
    s.gpr .x5 &&& 1=0 ↔ FastNaf.residual w k j%2=0 := by
  rw [←BitVec.toNat_inj]
  change (s.gpr .x5).toNat &&& 1=0 ↔ _
  rw [Nat.and_one_is_mod]
  dsimp only [nafVal5] at hv
  omega

theorem fastStep_ok {s : State} {base : Addr} {size bits w k j : Nat}
    (hI : FastPrepState base size bits w k j s) (hw : FastNaf.Width w)
    (hb : bits+264≤size) (hj : j<257) (hv : FastNaf.residual w k j≤2^256) :
    WP isa (Impl.Weierstrass.AArch64.FastNaf.step w) s fun t =>
      FastPrepState base size bits w k (fastNextIndex w k j) t ∧
      KeepRegs fastStepClob s t ∧ Outside base bits 264 s.mem t.mem ∧
      (t.gpr .x19=0 ↔ FastNaf.residual w k (fastNextIndex w k j)=0) := by
  rw [Impl.Weierstrass.AArch64.FastNaf.step]
  refine WP.seq (WP.mono (fastTest_ok s hI.one) fun a ⟨ea,ka⟩ => ?_)
  have ia := hI.of_keeps ka (by decide)
  have eb : a.gpr .x1=0 ↔ FastNaf.residual w k j%2=0 := by rw [ea]; exact fastLow_even hI.value
  have branches : WP isa (.ite (.nonzero .x .x1) (.block (Impl.Weierstrass.AArch64.FastNaf.odd w))
      (.block Impl.Weierstrass.AArch64.FastNaf.even)) a fun b =>
      FastPrepState base size bits w k (fastNextIndex w k j) b ∧ KeepRegs fastStepClob a b ∧
      Outside base bits 264 a.mem b.mem := by
    by_cases he : FastNaf.residual w k j%2=0
    · refine WP.ite false ?_ (by intro h; cases h) (fun _ => ?_)
      · simp only [eval,read_x,Size.bits,show a.gpr .x1=0 from eb.mpr he]
        rfl
      · simpa only [fastNextIndex,he,ite_true] using fastEvenState_ok ia he
    · refine WP.ite true ?_ (fun _ => ?_) (by intro h; cases h)
      · simp only [eval,read_x,Size.bits,Option.some.injEq,bne_iff_ne]
        exact fun h => he (eb.mp h)
      · simpa only [fastNextIndex,he,ite_false] using fastOddState_ok ia hw hb hj hv he
  refine WP.seq (WP.mono branches fun b ⟨ib,kb,ob⟩ => ?_)
  refine WP.mono (fastRemain_ok b) fun t ⟨et,kt⟩ => ?_
  refine ⟨ib.of_keeps kt (by decide),
    (fastKept ka (by decide)).trans (kb.trans (fastKept kt (by decide))),?_,?_⟩
  · rw [kt.mem,←ka.mem]; exact ob
  · rw [et,ib.value]

structure FastPrepPost (base : Addr) (size bits w k : Nat) (s : State) : Prop where
  scr : Scr s base size
  digits : ∀ i<257,s.mem (off base (bits+i))=FastNaf.byte w k i

theorem fastPrepPost_of_zero {s : State} {base : Addr} {size bits w k j : Nat}
    (hI : FastPrepState base size bits w k j s) (hz : FastNaf.residual w k j=0) :
    FastPrepPost base size bits w k s := by
  refine ⟨hI.scr,?_⟩
  intro i hi
  rw [hI.digits i hi]
  split
  · rfl
  · have hv := FastNaf.residual_of_zero w k j hz (i-j)
    rw [show j+(i-j)=i from by omega] at hv
    exact (FastNaf.byte_of_zero w k i hv).symm

theorem fastLoop_ok {s : State} {base : Addr} {size bits w k j : Nat}
    (hI : FastPrepState base size bits w k j s) (hw : FastNaf.Width w)
    (hk : k<2^256) (hb : bits+264≤size) (hj : j<257) :
    WP isa (.loop (Impl.Weierstrass.AArch64.FastNaf.step w) (.nonzero .x .x19)) s fun t =>
      FastPrepPost base size bits w k t ∧ KeepRegs fastStepClob s t ∧ Outside base bits 264 s.mem t.mem := by
  let I (n : Nat) (t : State) := ∃ i, i<257 ∧ n=257-i ∧ FastPrepState base size bits w k i t ∧
    KeepRegs fastStepClob s t ∧ Outside base bits 264 s.mem t.mem
  apply WP.loop I (n:=257-j)
  · intro n a ⟨i,hi,hn,ia,ka,oa⟩
    have hv : FastNaf.residual w k i≤2^256 :=
      Nat.le_trans (FastNaf.residual_bound w (Nat.le_of_lt hk) (j:=i) (by omega))
        (Nat.pow_le_pow_right (by decide) (by omega))
    refine WP.mono (fastStep_ok ia hw hb hi hv) fun t ⟨it,kt,ot,et⟩ => ?_
    by_cases hz : FastNaf.residual w k (fastNextIndex w k i)=0
    · refine Or.inl ⟨?_,fastPrepPost_of_zero it hz,ka.trans kt,oa.trans ot⟩
      simp only [eval,read_x,Size.bits,et.mpr hz]
      rfl
    · have hj' : fastNextIndex w k i<257 := by
        by_contra h
        exact hz (FastNaf.residual_zero_ge hk (by omega))
      refine Or.inr ⟨?_,257-fastNextIndex w k i,?_,fastNextIndex w k i,hj',rfl,it,ka.trans kt,oa.trans ot⟩
      · simp only [eval,read_x,Size.bits,Option.some.injEq,bne_iff_ne]
        exact fun h => hz (et.mp h)
      · have := fastNextIndex_gt hw k i; omega
  · exact ⟨j,hj,rfl,hI,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩

end VG.Proof.Weierstrass.AArch64

end

/-! ## `FastNafPrep` -/

section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont

/-- Both measured public widths produce all257 signed digits, touching only their264-byte buffer. -/
theorem fastPrep_ok (K : WinCfg) {w : Nat} (hw : FastNaf.Width w)
    {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hsrc8 : src%8=0)
    (hbits : K.bits<4096) (hbits8 : K.bits%8=0) (hb : K.bits+264≤size) :
    WP isa (Impl.Weierstrass.AArch64.FastNaf.prep K src w) s fun t =>
      FastPrepPost base size K.bits w (wordsVal s.mem base src 4) t ∧
      KeepRegs nafPrepClob s t ∧ Outside base K.bits 264 s.mem t.mem := by
  rw [Impl.Weierstrass.AArch64.FastNaf.prep]
  refine WP.seq (WP.mono (fastSetup_ok K hw hs hsrc hsrc8 hbits hbits8 hb) fun a ⟨ia,ka,oa⟩ => ?_)
  refine WP.mono (fastLoop_ok ia hw (wordsVal_lt ..) hb (by decide)) fun t ⟨it,kt,ot⟩ => ?_
  exact ⟨it,ka.trans (kt.mono (by decide)),oa.trans ot⟩

end VG.Proof.Weierstrass.AArch64

end
