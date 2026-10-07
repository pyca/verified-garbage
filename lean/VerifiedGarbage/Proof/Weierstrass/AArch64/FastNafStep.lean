import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafState

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
