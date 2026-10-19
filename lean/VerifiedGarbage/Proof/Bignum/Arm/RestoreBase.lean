module
public import Batteries.Logic
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Mont.Words

/-! # Recover the workspace pointer saved by the outer RSA frame -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem saved_base_kept {s t : State} {base : BitVec 32} {size : Nat}
    (frame : Frame [⟨State.addr base, size⟩] s.mem t.mem)
    (sep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, size⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) (sp : t.sp = s.sp) :
    t.mem.readW (State.addr t.sp) 32 = base := by
  rw [sp]
  have e := frame.read (r := ⟨State.addr s.sp, 4⟩) (a := State.addr s.sp) (n := 4)
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep)
    (by decide)
  change (t.mem.read (State.addr s.sp) 4).setWidth 32 = base
  rw [e]
  exact saved

theorem restoreBase_ok (s : State) {base : BitVec 32}
    (read : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa (.block [.ldrSp .r0 0]) s fun t =>
      t.gpr .r0 = base ∧ t.mem = s.mem ∧ Rest [.r0] s t := by
  refine wp_loadStack (a := State.addr s.sp) (by decide) (by simp) read fun t h => WP.block_nil ?_
  exact ⟨h.gpr.trans saved, h.mem, h.rest (by simp)⟩

end VG.Proof.Bignum.Arm
