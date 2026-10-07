import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafInit

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
