import VerifiedGarbage.Proof.P256.EcdhJac.Frame
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
import VerifiedGarbage.Proof.Framework.AArch64.Spill

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Impl.P256.EcdhJac (extra)
open VG.Proof.Weierstrass.AArch64
open VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open Spec.Weierstrass
def saveExtra : List Instr := extra.map fun (r,d) => VG.Impl.Mont.AArch64.st r d
def restoreExtra : List Instr := extra.map fun (r,d) => VG.Impl.Mont.AArch64.ld r d
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- The additional ABI registers and live output pointer. -/
def extraRegs : List Reg := extra.map Prod.fst

theorem saveExtra_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hsize : 7840≤size) : WP isa (.block saveExtra) s fun t =>
      KeepRegs [] s t ∧ Outside base 7800 40 s.mem t.mem ∧ Spill.Saved base s.gpr extra t.mem := by
  refine WP.mono (Spill.save_wp (b:=.x0) (l:=extra) (by decide) (fun p hp => hs.st (by
    have h : ∀ p∈extra,p.2+8≤7840 := by decide
    exact Nat.le_trans (h p hp) hsize))) fun t h => ⟨⟨?_,h.rd,h.wr,h.sp⟩,?_,?_⟩
  · intro r _; exact congrFun h.gpr r
  · rw [h.mem,hs.x0]
    intro x hx
    change ((((s.mem.writeW (off base 7800) (s.gpr .x26)).writeW (off base 7808) (s.gpr .x27)).writeW
      (off base 7816) (s.gpr .x28)).writeW (off base 7824) (s.gpr .x30)).writeW (off base 7832) (s.gpr .x20) x=s.mem x
    rw [(writeW_outside _ base (d:=7832) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7824) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7816) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7808) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7800) _ (by decide)) x (by omega)]
  · rw [h.mem,hs.x0]; exact Spill.saveMem_saved (by decide) _ _ _

/-- A body's write frame preserves the saved extra registers. -/
theorem savedExtra_keep {base : Addr} {g : Reg → BitVec 64} {s t : State}
    {W : List (Nat × Nat)} (h : Spill.Saved base g extra s.mem)
    (hu : Unch base W s.mem t.mem)
    (hw : ∀ w∈W,w.1+w.2≤7800 ∨ 7840≤w.1) : Spill.Saved base g extra t.mem := by
  intro p hp
  have hb : ∀ p∈extra,7800≤p.2 ∧ p.2+8≤7840 := by decide
  change word t.mem base p.2=_
  rw [hu.word (fun w hm => by have := hw w hm; have := hb p hp; omega) (by have := hb p hp; omega)]
  exact h p hp

 theorem restoreExtra_ok {s : State} {base : Addr} {size : Nat} {g : Reg → BitVec 64}
    (hs : Scr s base size) (hsize : 7840≤size) (hsv : Spill.Saved base g extra s.mem) :
    WP isa (.block restoreExtra) s fun t =>
      VG.Proof.Ed25519.AArch64.Keeps extraRegs s t ∧ ∀ r∈extraRegs,t.gpr r=g r := by
  refine WP.mono (Spill.restore_wp hs.x0 (l:=extra) (by decide) (by decide)
    (fun p hp => by
      rw [←hs.x0]
      apply hs.ld
      have hh : ∀ p∈extra,p.2+8≤7840 := by decide
      exact Nat.le_trans (hh p hp) hsize) hsv) fun t h => ⟨⟨h.other,h.mem,h.rd,h.wr,h.sp⟩,?_⟩
  intro r hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  exact h.gpr p hp

/-- Restoring the saved registers removes them from the enclosing register frame. -/
theorem restoreExtra_frame {s a b t : State} {rs : List Reg}
    (hs : KeepRegs [] s a) (hb : KeepRegs rs a b)
    (ht : Keeps extraRegs b t) (hv : ∀ r∈extraRegs,t.gpr r=s.gpr r) :
    KeepRegs (rs.filter fun r => r∉extraRegs) s t := by
  refine ⟨?_,ht.rd.trans (hb.rd.trans hs.rd),ht.wr.trans (hb.wr.trans hs.wr),ht.sp.trans (hb.sp.trans hs.sp)⟩
  intro r hr
  by_cases he : r∈extraRegs
  · exact hv r he
  · have hnot : r∉rs := by simpa only [List.mem_filter,decide_eq_true_eq,he,not_false_eq_true,and_true] using hr
    rw [ht.gpr r he,hb.gpr r hnot,hs.gpr r (by simp)]

theorem Fixed.keep_save {base : Addr} {P : Point C} {k : Nat} {s t : State}
    (h : Fixed base P k s) (hk : AllocatedFrame [] base [(7800,40)] s t) : Fixed base P k t := by
  have hw : ∀ x∈ro,wordsVal t.mem base x 4=wordsVal s.mem base x 4 := by
    intro x hx
    exact hk.unch.wordsVal (by
      have hh : ∀ x∈ro,∀ w∈[(7800,40)],x+32≤w.1 ∨ w.1+w.2≤x := by decide +kernel
      exact hh x hx) (by
      have hh : ∀ x∈ro,x+32≤2^64 := by decide +kernel
      exact hh x hx)
  have hf : ∀ x∈ro,tmv C 4 base t x=tmv C 4 base s x := fun x hx => by unfold tmv; rw [hw x hx]
  refine ⟨⟨hk.scr (by decide) h.field.scr,h.field.mod.unch hk.unch (by decide +kernel) h.field.scr.nowrap,
    h.field.sl,fun x hx => by change wordsVal t.mem base x 4<C.p; rw [hw x hx]; exact h.field.lt x hx,fun _ _ => rfl⟩,?_,?_,?_,?_⟩
  · rw [hw _ (by decide)]; exact h.zero
  · rw [hf _ (by decide),hf _ (by decide),hf _ (by decide)]; exact h.peer
  · rw [hf _ (by decide)]; exact h.one
  · intro i hi
    rw [hk.unch.byte (by
      intro w hw
      have hh : ∀ w∈[(7800,40)],K.bits+260≤w.1 ∨ w.1+w.2≤K.bits := by decide +kernel
      have := hh w hw; omega) (by change 1824+i+1≤2^64; omega)]
    exact h.bits i hi

end VG.Proof.P256.EcdhJac
