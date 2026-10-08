import VerifiedGarbage.Proof.P256.EcdhJac.Counter
import VerifiedGarbage.Proof.Weierstrass.AArch64.CopyKeep

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)
open Spec.Weierstrass

def digitMagnitude (k j : Nat) := magH 16 (Window5.nib (k+offset) j)
def maskCode : List Instr := nzMask 4 K.R.z++selPt 4 K.D K.E K.D++tc.digit++
  [zero7,.movz .x .x5 1 0,.subs .x .x16 .x2 .x5,.sbc .x .x3 .x7 .x7]++selPt 4 K.R K.D K.R

private theorem infinityMask_ok {base : Addr} {s : State} (hs : Scr s base 8192) :
    WP isa (.block (nzMask 4 K.R.z++selPt 4 K.D K.E K.D)) s fun b =>
      AllocatedFrame allocatedRegs base work s b ∧
      (∀ i<3,wordsVal b.mem base (512+32*i) 4=wordsVal s.mem base (512+32*i) 4) ∧
      (∀ i<3,wordsVal b.mem base (608+32*i) 4=
        if wordsVal s.mem base 576 4=0 then wordsVal s.mem base (704+32*i) 4
        else wordsVal s.mem base (608+32*i) 4) := by
  rw [WP.block_append_iff]
  refine WP.mono (nzMask_ok hs (by decide) (by decide : 576+8*4≤8192) (by decide))
    fun a ⟨a3,ka⟩ => ?_
  change a.gpr .x3=mask (wordsVal s.mem base 576 4≠0) at a3
  refine WP.mono (selPtKeep_ok (hs.of_keeps ka (by decide))
    (decide (wordsVal s.mem base 576 4≠0)) (by simpa only [mask,decide_eq_true_eq] using a3)
    (n:=4) (o:=K.D) (a:=K.E) (by decide) (by decide) (by decide)) fun b ⟨bx,by',bz,kb,ub⟩ => ?_
  have ud : Unch base [(608,32),(640,32),(672,32)] a.mem b.mem := fun x hx =>
    ub x (hx (608,32) (by decide)) (hx (640,32) (by decide)) (hx (672,32) (by decide))
  have fb : AllocatedFrame allocatedRegs base work s b := ⟨
    (Keeps.regs ka).mono (by decide) |>.trans (kb.mono (by decide)),by
      simpa only [ka.mem] using ud.cover (by decide : ∀ w∈[(608,32),(640,32),(672,32)],
        ∃ r∈work,r.1≤w.1 ∧ w.1+w.2≤r.1+r.2)⟩
  have sameR : ∀ i<3,wordsVal b.mem base (512+32*i) 4=wordsVal s.mem base (512+32*i) 4 := by
    intro i hi
    rw [ud.wordsVal (by
      have hh : ∀ i<3,∀ w∈[(608,32),(640,32),(672,32)],512+32*i+32≤w.1 ∨ w.1+w.2≤512+32*i := by decide
      exact hh i hi) (by omega),ka.mem]
  have sameD : ∀ i<3,wordsVal b.mem base (608+32*i) 4=
      if wordsVal s.mem base 576 4=0 then wordsVal s.mem base (704+32*i) 4
      else wordsVal s.mem base (608+32*i) 4 := by
    simp only [ka.mem,decide_eq_true_eq] at bx by' bz
    intro i hi
    rcases (by omega : i=0 ∨ i=1 ∨ i=2) with rfl|rfl|rfl
    all_goals simp only [Nat.mul_zero,Nat.add_zero,Nat.reduceMul,Nat.reduceAdd]
    · change wordsVal b.mem base 608 4=(if _ then wordsVal s.mem base 608 4 else wordsVal s.mem base 704 4) at bx
      simpa only [ne_eq,ite_not] using bx
    · change wordsVal b.mem base 640 4=(if _ then wordsVal s.mem base 640 4 else wordsVal s.mem base 736 4) at by'
      simpa only [ne_eq,ite_not] using by'
    · change wordsVal b.mem base 672 4=(if _ then wordsVal s.mem base 672 4 else wordsVal s.mem base 768 4) at bz
      simpa only [ne_eq,ite_not] using bz
  exact ⟨fb,sameR,sameD⟩

def digitMaskCode : List Instr := tc.digit++
  [zero7,.movz .x .x5 1 0,.subs .x .x16 .x2 .x5,.sbc .x .x3 .x7 .x7]++selPt 4 K.R K.D K.R

private theorem magnitude_zero (a : Nat) (ha : a≤16) :
    BitVec.ofNat 64 a=0 ↔ a=0 := by
  constructor
  · intro h
    have hh := congrArg BitVec.toNat h
    change a%2^64=0 at hh
    omega
  · intro h; rw [h]; rfl

private theorem zeroSelect_ok {base : Addr} {c : State} {a : Nat}
    (hs : Scr c base 8192) (ha : a≤16) (h2 : c.gpr .x2=BitVec.ofNat 64 a) :
    WP isa (.block (([zero7,.movz .x .x5 1 0,.subs .x .x16 .x2 .x5,.sbc .x .x3 .x7 .x7] : List Instr)++selPt 4 K.R K.D K.R)) c
      fun t => AllocatedFrame allocatedRegs base work c t ∧
        ∀ i<3,wordsVal t.mem base (512+32*i) 4=
          if a=0 then wordsVal c.mem base (512+32*i) 4 else wordsVal c.mem base (608+32*i) 4 := by
  rw [WP.block_append_iff]
  have ce : c.gpr .x2=0 ↔ a=0 := h2 ▸ magnitude_zero a ha
  refine WP.mono (booth_eqMask_ok c) fun d ⟨d3,kd⟩ => ?_
  refine WP.mono (selPtKeep_ok (hs.of_keeps kd (by decide))
    (decide (a=0)) (by simpa only [mask,decide_eq_true_eq,ce] using d3)
    (n:=4) (o:=K.R) (a:=K.D) (by decide) (by decide) (by decide)) fun t ⟨tx,ty,tz,kt,ut⟩ => ?_
  have ur : Unch base [(512,32),(544,32),(576,32)] d.mem t.mem := fun x hx =>
    ut x (hx (512,32) (by decide)) (hx (544,32) (by decide)) (hx (576,32) (by decide))
  have fd : AllocatedFrame allocatedRegs base work c d := (AllocatedFrame.of_keeps kd).widenRegs (by decide)
  have ft : AllocatedFrame allocatedRegs base work d t := ⟨kt.mono (by decide),ur.cover (by decide)⟩
  refine ⟨fd.trans ft,?_⟩
  simp only [kd.mem,decide_eq_true_eq] at tx ty tz
  intro i hi
  have e : wordsVal t.mem base (512+32*i) 4=
      if a=0 then wordsVal c.mem base (512+32*i) 4 else wordsVal c.mem base (608+32*i) 4 := by
    rcases (by omega : i=0 ∨ i=1 ∨ i=2) with rfl|rfl|rfl
    · exact tx
    · exact ty
    · exact tz
  exact e


private theorem digitMask_ok {base : Addr} {P : Point C} {k j : Nat} {b : State}
    (fxb : Fixed base P k b) (hj : j<52) (h19 : b.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block digitMaskCode) b fun t => AllocatedFrame allocatedRegs base work b t ∧
      ∀ i<3,wordsVal t.mem base (512+32*i) 4=
        if digitMagnitude k j=0 then wordsVal b.mem base (512+32*i) 4
        else wordsVal b.mem base (608+32*i) 4 := by
  rw [digitMaskCode,List.append_assoc,WP.block_append_iff]
  refine WP.mono (digitW_ok tc fxb.field.scr (k:=k+offset) (j:=j) (N:=260)
    (by decide) (by decide) (by change 5*j+5≤260; omega) (by decide) (by decide) h19 fxb.bits)
    fun c ⟨c2,kc⟩ => ?_
  have c2' : c.gpr .x2=BitVec.ofNat 64 (digitMagnitude k j) := by
    change c.gpr .x2=BitVec.ofNat 64 (magH 16 (combWin 5 (k+offset) j)) at c2
    simpa only [Window5.combWin_five,digitMagnitude] using c2
  refine WP.mono (zeroSelect_ok (fxb.field.scr.of_keeps kc (by decide))
    (magH_le (Window5.nib_lt (k+offset) j)) c2') fun t ⟨ft,hv⟩ => ?_
  refine ⟨((AllocatedFrame.of_keeps kc).widenRegs (by decide)).trans ft,?_⟩
  intro i hi
  have hh := hv i hi
  rw [kc.mem] at hh
  exact hh

theorem masks_ok {base : Addr} {P : Point C} {k j : Nat} {s : State}
    (hf : Fixed base P k s) (hj : j<52) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block maskCode) s fun t => AllocatedFrame allocatedRegs base work s t ∧
      ∀ i<3,wordsVal t.mem base (512+32*i) 4=
        if digitMagnitude k j=0 then wordsVal s.mem base (512+32*i) 4
        else if wordsVal s.mem base 576 4=0 then wordsVal s.mem base (704+32*i) 4
        else wordsVal s.mem base (608+32*i) 4 := by
  rw [show maskCode=(nzMask 4 K.R.z++selPt 4 K.D K.E K.D)++digitMaskCode by
    simp only [maskCode,digitMaskCode,List.append_assoc],WP.block_append_iff]
  refine WP.mono (infinityMask_ok hf.field.scr) fun b ⟨fb,sameR,sameD⟩ => ?_
  refine WP.mono (digitMask_ok (hf.keep (frame_build (fb.widenRegs allocated_regs))) hj
    ((fb.regs.gpr _ allocatedRegs_x19).trans h19)) fun t ⟨ft,hv⟩ => ?_
  refine ⟨fb.trans ft,?_⟩
  intro i hi
  rw [hv i hi,sameR i hi,sameD i hi]

end VG.Proof.P256.EcdhJac
