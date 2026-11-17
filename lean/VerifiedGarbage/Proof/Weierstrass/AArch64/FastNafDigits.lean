module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafInit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafExec

/-! ### `Weierstrass.AArch64.FastNafStep`, which this module and modules that import it used -/

section

@[expose] public section

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
  rcases hw with rfl | rfl <;> simp only [Nat.reduceSub,Nat.reducePow] <;> omega_using []

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
  refine WP.mono (fastShift_ok c w (Or.inr hw.wide)) fun d ⟨vd,kd⟩ => ?_
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

end

@[expose] public section

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
  refine WP.mono (fastInit_ok K hw.wide hs hsrc hsrc8 hbits) fun a ⟨ia,ka,ma⟩ => ?_
  refine WP.mono (fastClear_ok K ia.scr ia.zero hbits8 hb) fun t ⟨zt,kt,ot⟩ => ?_
  refine ⟨⟨ia.next (kt.mono (by simp)) ?_ ?_,?_⟩,ka.trans (kt.mono (by simp)),?_⟩
  · simp only [kt.gpr _ List.not_mem_nil,ia.value]
  · exact (kt.gpr _ List.not_mem_nil).trans ia.ptr
  · intro i hi
    simpa only [Nat.not_lt_zero,ite_false] using zt i (by omega_using [hi])
  · rw [←ma]; exact ot

theorem fastOddState_ok {s : State} {base : Addr} {size bits w k j : Nat}
    (hI : FastPrepState base size bits w k j s) (hw : FastNaf.Width w)
    (hb : bits+264≤size) (hj : j<257) (hv : FastNaf.residual w k j≤2^256)
    (ho : FastNaf.residual w k j%2≠0) :
    WP isa (.block (Impl.Weierstrass.AArch64.FastNaf.odd w)) s fun t =>
      FastPrepState base size bits w k (j+w) t ∧ KeepRegs fastStepClob s t ∧
      Outside base bits 264 s.mem t.mem := by
  refine WP.mono (fastOdd_ok hI.toFastPrepCore hw hb hj hv ho) fun t ⟨it,kt,mt⟩ => ?_
  have O := writeW8_outside s.mem base (FastNaf.byte w k j) (d:=bits+j) (by have:=hI.scr.nowrap; omega_using [hb, hj, this])
  refine ⟨⟨it,?_⟩,kt,?_⟩
  · intro i hi
    rw [mt]
    by_cases hij : i=j
    · subst i
      rw [writeW8_self,ite_eq_left (by rcases hw with rfl | rfl <;> omega_using [])]
    · rw [O _ (by
        have hoff : ofs base (off base (bits+i))=bits+i := by
          simpa only [BitVec.add_zero,Nat.add_zero] using (ofs_off base (d:=bits+i) (i:=0) (by have:=hI.scr.nowrap; omega_using [hb, hi, this]))
        rw [hoff]; omega_using [hij]),hI.digits i hi]
      by_cases hlt : i<j
      · simp only [hlt,ite_true,show i<j+w from by omega_using [hlt]]
      · simp only [hlt,ite_false]
        split
        · have hz := FastNaf.byte_skip_zero hw k j (i-j) ho (by omega_using [hij, hlt]) (by omega_arith)
          rw [show j+(i-j)=i from by omega_using [hlt]] at hz
          exact hz.symm
        · rfl
  · rw [mt]; exact O.mono (by omega_using []) (by omega_using [hj])

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
      · simp only [hlt,ite_true,show i<j+1 from by omega_using [hlt]]
      · simp only [hlt,ite_false,show ¬i<j+1 from by omega_using [hij, hlt]]
  · rw [mt]; exact Outside.refl _ _ _ _

end VG.Proof.Weierstrass.AArch64
