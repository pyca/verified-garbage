import VerifiedGarbage.Impl.P256.EcdhInverse
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
import VerifiedGarbage.Proof.Framework.AArch64.Spill

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Impl.P256.EcdhInverse (saveExtra restoreExtra)
open VG.Proof.Weierstrass.AArch64

def extraSlots : List (Reg × Nat) :=
  [(.x21,7800),(.x22,7808),(.x23,7816),(.x24,7824),(.x25,7832),
   (.x26,7840),(.x27,7848),(.x28,7856),(.x30,7864)]
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- The additional callee-saved registers used by allocated arithmetic. -/
def extraRegs : List Reg := extraSlots.map Prod.fst

theorem saveExtra_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hsize : 7872≤size) : WP isa (.block saveExtra) s fun t =>
      KeepRegs [] s t ∧ Outside base 7800 72 s.mem t.mem ∧ Spill.Saved base s.gpr extraSlots t.mem := by
  refine WP.mono (Spill.save_wp (b:=.x0) (l:=extraSlots) (by decide) (fun p hp => hs.st (by
    have h : ∀ p∈extraSlots,p.2+8≤7872 := by decide
    exact Nat.le_trans (h p hp) hsize))) fun t h => ⟨⟨?_,h.rd,h.wr,h.sp⟩,?_,?_⟩
  · intro r _; exact congrFun h.gpr r
  · rw [h.mem,hs.x0]
    intro x hx
    change (((((((((s.mem.writeW (off base 7800) (s.gpr .x21)).writeW (off base 7808) (s.gpr .x22)).writeW (off base 7816) (s.gpr .x23)).writeW (off base 7824) (s.gpr .x24)).writeW (off base 7832) (s.gpr .x25)).writeW (off base 7840) (s.gpr .x26)).writeW (off base 7848) (s.gpr .x27)).writeW (off base 7856) (s.gpr .x28)).writeW (off base 7864) (s.gpr .x30)) x=s.mem x
    rw [(writeW_outside _ base (d:=7864) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7856) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7848) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7840) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7832) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7824) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7816) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7808) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7800) _ (by decide)) x (by omega)]
  · rw [h.mem,hs.x0]; exact Spill.saveMem_saved (by decide) _ _ _

/-- A body's write frame preserves the saved extra registers. -/
theorem savedExtra_keep {base : Addr} {g : Reg → BitVec 64} {s t : State}
    {W : List (Nat × Nat)} (h : Spill.Saved base g extraSlots s.mem)
    (hu : Unch base W s.mem t.mem)
    (hw : ∀ w∈W,w.1+w.2≤7800 ∨ 7872≤w.1) : Spill.Saved base g extraSlots t.mem := by
  intro p hp
  have hb : ∀ p∈extraSlots,7800≤p.2 ∧ p.2+8≤7872 := by decide
  change word t.mem base p.2=_
  rw [hu.word (fun w hm => by have := hw w hm; have := hb p hp; omega) (by have := hb p hp; omega)]
  exact h p hp

 theorem restoreExtra_ok {s : State} {base : Addr} {size : Nat} {g : Reg → BitVec 64}
    (hs : Scr s base size) (hsize : 7872≤size) (hsv : Spill.Saved base g extraSlots s.mem) :
    WP isa (.block restoreExtra) s fun t =>
      VG.Proof.Ed25519.AArch64.Keeps extraRegs s t ∧ ∀ r∈extraRegs,t.gpr r=g r := by
  refine WP.mono (Spill.restore_wp hs.x0 (l:=extraSlots) (by decide) (by decide)
    (fun p hp => by
      rw [←hs.x0]
      apply hs.ld
      have hh : ∀ p∈extraSlots,p.2+8≤7872 := by decide
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

end VG.Proof.P256.EcdhInverse
