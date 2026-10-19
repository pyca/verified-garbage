module

public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
meta import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.Unch
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Spec.Weierstrass.Mul
meta import VerifiedGarbage.Impl.Ecdh.P256.AArch64
meta import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
meta import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Spec.Weierstrass.Mul

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64.P256Allocated (extra saveExtra restoreExtra)
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- The four additional callee-saved registers used by allocated arithmetic. -/
def allocatedExtraRegs : List Reg := extra.map Prod.fst

theorem allocatedSave_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hsize : 7832≤size) : WP isa (.block saveExtra) s fun t =>
      KeepRegs [] s t ∧ Outside base 7800 32 s.mem t.mem ∧ Spill.Saved base s.gpr extra t.mem := by
  refine WP.mono (Spill.save_wp (b:=.x0) (l:=extra) (by decide) (fun p hp => hs.st (by
    have h : ∀ p∈extra,p.2+8≤7832 := by decide
    exact Nat.le_trans (h p hp) hsize))) fun t h => ⟨⟨?_,h.rd,h.wr,h.sp⟩,?_,?_⟩
  · intro r _; exact congrFun h.gpr r
  · rw [h.mem,hs.x0]
    intro x hx
    change (((s.mem.writeW (off base 7800) (s.gpr .x26)).writeW (off base 7808) (s.gpr .x27)).writeW
      (off base 7816) (s.gpr .x28)).writeW (off base 7824) (s.gpr .x30) x=s.mem x
    rw [(writeW_outside _ base (d:=7824) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7816) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7808) _ (by decide)) x (by omega),
      (writeW_outside _ base (d:=7800) _ (by decide)) x (by omega)]
  · rw [h.mem,hs.x0]; exact Spill.saveMem_saved (by decide) _ _ _

/-- A body's write frame preserves the saved extra registers. -/
theorem allocatedSaved_keep {base : Addr} {g : Reg → BitVec 64} {s t : State}
    {W : List (Nat × Nat)} (h : Spill.Saved base g extra s.mem)
    (hu : Unch base W s.mem t.mem)
    (hw : ∀ w∈W,w.1+w.2≤7800 ∨ 7832≤w.1) : Spill.Saved base g extra t.mem := by
  intro p hp
  have hb : ∀ p∈extra,7800≤p.2 ∧ p.2+8≤7832 := by decide
  change word t.mem base p.2=_
  rw [hu.word (fun w hm => by have := hw w hm; have := hb p hp; omega) (by have := hb p hp; omega)]
  exact h p hp

 theorem allocatedRestore_ok {s : State} {base : Addr} {size : Nat} {g : Reg → BitVec 64}
    (hs : Scr s base size) (hsize : 7832≤size) (hsv : Spill.Saved base g extra s.mem) :
    WP isa (.block restoreExtra) s fun t =>
      VG.Proof.Ed25519.AArch64.Keeps allocatedExtraRegs s t ∧ ∀ r∈allocatedExtraRegs,t.gpr r=g r := by
  refine WP.mono (Spill.restore_wp hs.x0 (l:=extra) (by decide) (by decide)
    (fun p hp => by
      rw [←hs.x0]
      apply hs.ld
      have hh : ∀ p∈extra,p.2+8≤7832 := by decide
      exact Nat.le_trans (hh p hp) hsize) hsv) fun t h => ⟨⟨h.other,h.mem,h.rd,h.wr,h.sp⟩,?_⟩
  intro r hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  exact h.gpr p hp

/-- Restoring the saved registers removes them from the enclosing register frame. -/
theorem allocatedRestore_frame {s a b t : State} {rs : List Reg}
    (hs : KeepRegs [] s a) (hb : KeepRegs rs a b)
    (ht : Keeps allocatedExtraRegs b t) (hv : ∀ r∈allocatedExtraRegs,t.gpr r=s.gpr r) :
    KeepRegs (rs.filter fun r => r∉allocatedExtraRegs) s t := by
  refine ⟨?_,ht.rd.trans (hb.rd.trans hs.rd),ht.wr.trans (hb.wr.trans hs.wr),ht.sp.trans (hb.sp.trans hs.sp)⟩
  intro r hr
  by_cases he : r∈allocatedExtraRegs
  · exact hv r he
  · have hnot : r∉rs := by simpa only [List.mem_filter,decide_eq_true_eq,he,not_false_eq_true,and_true] using hr
    rw [ht.gpr r he,hb.gpr r hnot,hs.gpr r (by simp)]

 theorem invAllocated_save_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block saveExtra) := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

 theorem invAllocated_restore_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block restoreExtra) := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)


end VG.Proof.Weierstrass.AArch64
