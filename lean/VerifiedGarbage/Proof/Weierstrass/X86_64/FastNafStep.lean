import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafOdd

/-! Each recoder step advances one bit for an even residual, or one window for an odd residual. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

theorem FastPrepState.of_keeps {s t : State} {base : Addr} {size bits w k j : Nat}
    (h : FastPrepState base size bits w k j s) {rs : List Reg} (hk : Keeps rs s t)
    (hr : ∀ r∈[Reg.rdi,.rbx,.r8,.r9,.r10,.r11,.r12],r∉rs) :
    FastPrepState base size bits w k j t := by
  refine ⟨h.scr.of_keeps hk (hr _ (by simp)),?_,?_,?_⟩
  · rw [hk.1 .r8 (hr _ (by simp)),hk.1 .r9 (hr _ (by simp)),hk.1 .r10 (hr _ (by simp)),
      hk.1 .r11 (hr _ (by simp)),hk.1 .r12 (hr _ (by simp))]
    exact h.value
  · exact (hk.1 .rbx (hr _ (by simp))).trans h.count
  · rw [hk.2.1]
    exact h.digits

def fastDelta (w k j : Nat) : Nat := if FastNaf.residual w k j%2=0 then 1 else w

theorem fastEvenStep_ok {s : State} {base : Addr} {size bits w k j : Nat}
    (hI : FastPrepState base size bits w k j s)
    (ho : FastNaf.residual w k j%2=0) :
    WP isa (.block (Impl.Weierstrass.X86_64.FastNaf.shift 1++Impl.Weierstrass.X86_64.FastNaf.advance 1)) s fun t =>
      FastPrepState base size bits w k (j+1) t ∧ KeepRegs nafPrepClob s t ∧
      Outside base bits 264 s.mem t.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (fastShift_ok s (Or.inl rfl)) fun a ⟨va,ka⟩ => ?_
  have ca : a.gpr .rbx=BitVec.ofNat 64 j := (ka.1 _ (by decide)).trans hI.count
  refine WP.mono (fastAdvance_ok a (Or.inl rfl) ca) fun t ⟨ct,kt⟩ => ?_
  have mt : t.mem=s.mem := kt.2.1.trans ka.2.1
  refine ⟨⟨(hI.scr.of_keeps ka (by decide)).of_keeps kt (by decide),?_,ct,?_⟩,?_,?_⟩
  · rw [kt.1 .r8 (by decide),kt.1 .r9 (by decide),kt.1 .r10 (by decide),
      kt.1 .r11 (by decide),kt.1 .r12 (by decide),va,hI.value,
      FastNaf.residual_succ,FastNaf.next_even w _ ho]
  · intro i hi
    rw [mt,hI.digits i hi]
    by_cases he : i=j
    · subst i
      simp only [Nat.lt_irrefl,ite_false,Nat.lt_add_one,ite_true]
      exact ((FastNaf.byte_zero_iff w k j).mpr ((FastNaf.magnitude_zero_iff w k j).mpr ho)).symm
    · have hh : (i<j)=(i<j+1) := propext (by omega)
      simp only [hh]
  · exact ((VG.Proof.Mont.X86_64.Keeps.regs ka).mono (by decide)).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kt).mono (by decide))
  · rw [mt]
    exact Outside.refl _ _ _ _

theorem fastPrepStep_ok {s : State} {base : Addr} {size bits w k j : Nat}
    (hw : FastNaf.Width w) (hI : FastPrepState base size bits w k j s)
    (hb : bits+264≤size) (hj : j<257) (hv : FastNaf.residual w k j≤2^256) :
    WP isa (Impl.Weierstrass.X86_64.FastNaf.step bits w) s fun t =>
      FastPrepState base size bits w k (j+fastDelta w k j) t ∧
      t.cf=some (decide (j+fastDelta w k j<257)) ∧ KeepRegs nafPrepClob s t ∧
      Outside base bits 264 s.mem t.mem := by
  have hd : fastDelta w k j=1 ∨ fastDelta w k j=5 ∨ fastDelta w k j=7 := by
    unfold fastDelta
    split
    · exact Or.inl rfl
    · exact Or.inr hw
  rw [Impl.Weierstrass.X86_64.FastNaf.step]
  refine WP.seq (WP.mono (nafParity_ok s) fun a ⟨_,hz,ka⟩ => ?_)
  have ia := hI.of_keeps ka (by decide)
  have hp : s.gpr .r8 &&& 1=0 ↔ FastNaf.residual w k j%2=0 := by
    rw [nafParity]
    have h := hI.value
    dsimp only [nafVal5] at h
    omega
  apply WP.seq
  have branches : WP isa
      (.ite .e (.block (Impl.Weierstrass.X86_64.FastNaf.shift 1++Impl.Weierstrass.X86_64.FastNaf.advance 1))
        (.seq (Impl.Weierstrass.X86_64.FastNaf.choose w)
          (.block (Naf.subtractDigit++[.store8 (tbl bits) .rcx]++Impl.Weierstrass.X86_64.FastNaf.shift w++Impl.Weierstrass.X86_64.FastNaf.advance w)))) a
      (fun t => FastPrepState base size bits w k (j+fastDelta w k j) t ∧
        KeepRegs nafPrepClob a t ∧ Outside base bits 264 a.mem t.mem) := by
    apply WP.ite (decide (s.gpr .r8 &&& 1=0)) hz
    · intro h
      have he := hp.mp (of_decide_eq_true h)
      simpa only [fastDelta,he,ite_true] using fastEvenStep_ok ia he
    · intro h
      have he : FastNaf.residual w k j%2≠0 := fun he => (of_decide_eq_false h) (hp.mpr he)
      simpa only [fastDelta,he,ite_false] using fastOddStep_ok hw ia hb hj hv he
  refine WP.mono branches fun b ⟨ib,kb,ob⟩ => ?_
  refine WP.mono (fastCompare_ok b (by rcases hd with h|h|h <;> omega) ib.count) fun t ⟨cf,kt⟩ => ?_
  refine ⟨ib.of_keeps kt (by simp),cf,?_,?_⟩
  · exact (((VG.Proof.Mont.X86_64.Keeps.regs ka).mono (by decide)).trans kb).trans
      ((VG.Proof.Mont.X86_64.Keeps.regs kt).mono (by simp))
  · rw [kt.2.1,ka.2.1] at *
    exact ob

end VG.Proof.Weierstrass.X86_64
