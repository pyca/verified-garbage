import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafDigits

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
