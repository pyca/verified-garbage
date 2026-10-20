module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtWorkspaceCall
public import Batteries.Logic
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Workspace selection writes only the saved base pointer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

theorem crt_saveMain_ok (s : State) (fit : s.sp.toNat + 12 ≤ 2 ^ 32)
    (write : InRegions s.wr (off (State.addr s.sp) 8) 4) :
    WP isa (.block saveMain) s fun t =>
      t.mem = s.mem.writeW (off (State.addr s.sp) 8) (s.gpr .r0) ∧
      Frame [⟨off (State.addr s.sp) 8, 4⟩] s.mem t.mem ∧ Rest [.r12] s t := by
  unfold saveMain
  refine wp_stackAddr (by decide) fun u a => ?_
  refine wp_str (a := off (State.addr s.sp) 8) (by decide)
    (by rw [a.gpr, BitVec.add_zero]; exact addr_add (by omega))
    (by rw [a.wr]; exact write) fun t b => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off (State.addr s.sp) 8) (s.gpr .r0) := by
    rw [b.mem, a.mem, a.other .r0 (by decide)]
  refine ⟨mem, ?_, (a.rest (by simp)).trans (b.rest _)⟩
  rw [mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem crt_selectChild_ok (s : State) {base child : BitVec 32} {size slot : Nat}
    (ws : Workspace s base size) (fit : slot + 4 ≤ size) (hs : slot < 4096)
    (ptr : s.gpr .r0 = base)
    (link : s.mem.readW (off (State.addr base) slot) 32 = child)
    (write : InRegions s.wr (State.addr s.sp) 4) :
    WP isa (selectChild slot) s fun t => t.gpr .r0 = child ∧
      t.mem = s.mem.writeW (State.addr s.sp) child ∧
      Frame [⟨State.addr s.sp, 4⟩] s.mem t.mem ∧ Rest [.r0, .r12] s t := by
  rw [selectChild, WP.seq_iff]
  refine wp_ldr (a := off (State.addr base) slot) hs
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read fit) fun u a => WP.block_nil ?_
  refine WP.mono (activateWorkspace_ok u (by rw [a.wr, a.sp]; exact write)) ?_
  rintro t ⟨mem, frame, rest⟩
  rw [a.mem, a.sp, a.gpr, link] at mem
  rw [a.mem, a.sp] at frame
  exact ⟨(rest.gpr .r0 (by simp)).trans (a.gpr.trans link), mem, frame,
    (a.rest (by simp)).trans (rest.mono (by simp))⟩

theorem crt_selectMain_ok (s : State) {base : BitVec 32}
    (fit : s.sp.toNat + 12 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 8) 4)
    (saved : s.mem.readW (off (State.addr s.sp) 8) 32 = base)
    (write : InRegions s.wr (State.addr s.sp) 4) :
    WP isa selectMain s fun t => t.gpr .r0 = base ∧
      t.mem = s.mem.writeW (State.addr s.sp) base ∧
      Frame [⟨State.addr s.sp, 4⟩] s.mem t.mem ∧ Rest [.r0, .r12] s t := by
  rw [selectMain, WP.seq_iff]
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
    (addr_add (by omega)) read fun u a => WP.block_nil ?_
  refine WP.mono (activateWorkspace_ok u (by rw [a.wr, a.sp]; exact write)) ?_
  rintro t ⟨mem, frame, rest⟩
  rw [a.mem, a.sp, a.gpr, saved] at mem
  rw [a.mem, a.sp] at frame
  exact ⟨(rest.gpr .r0 (by simp)).trans (a.gpr.trans saved), mem, frame,
    (a.rest (by simp)).trans (rest.mono (by simp))⟩

end VG.Proof.Bignum.Arm
