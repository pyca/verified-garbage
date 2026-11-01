module

public import VerifiedGarbage.Impl.Bignum.Arm.ActivateWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT

/-! # Switching workspaces refreshes the saved base without touching their contents -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem activateWorkspace_ok (s : State) (write : InRegions s.wr (State.addr s.sp) 4) :
    WP isa (.block activateWorkspace) s fun t =>
      t.mem = s.mem.writeW (State.addr s.sp) (s.gpr .r0) ∧
      Frame [⟨State.addr s.sp, 4⟩] s.mem t.mem ∧ Rest [.r12] s t := by
  unfold activateWorkspace
  refine wp_stackAddr (by decide) fun u a => ?_
  have ptr : u.gpr .r12 = s.sp := by simpa only [BitVec.add_zero] using a.gpr
  refine wp_str (a := State.addr s.sp) (by decide)
    (by rw [ptr, BitVec.add_zero]) (by rw [a.wr]; exact write) fun t b => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (State.addr s.sp) (s.gpr .r0) := by
    rw [b.mem, a.mem, a.other .r0 (by decide)]
  refine ⟨mem, ?_, (a.rest (by simp)).trans (b.rest _)⟩
  rw [mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem activateWorkspace_ready (s : State) {base : BitVec 32} {len w : Nat}
    (h : SelectArrayReady base len w s) (write : InRegions s.wr (State.addr s.sp) 4)
    (sep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩) :
    WP isa (.block activateWorkspace) s fun t => LayoutFrameReady base len w t ∧
      WorkspaceEq (State.addr base) (8 * len) s.mem t.mem ∧
      Frame [⟨State.addr s.sp, 4⟩] s.mem t.mem ∧ Rest [.r12] s t := by
  refine WP.mono (activateWorkspace_ok s write) ?_
  rintro t ⟨mem, frame, rest⟩
  have eq := WorkspaceEq.of_frame (by have := h.workspace.nowrap; omega : 8 * len < 2 ^ 64) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep.symm)
  have size : 56 ≤ 8 * len := by
    have := h.layout.2.2.1
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  refine ⟨⟨⟨h.workspace.congr rest.wr, eq.layout h.layout, (eq.width size).trans h.width,
    (rest.gpr .r0 (by simp)).trans h.ptr⟩, ?_, ?_, ?_⟩, eq, frame, rest⟩
  · rw [rest.rd, rest.wr, rest.sp]
    obtain ⟨R, hr, sub⟩ := write
    exact ⟨R, List.mem_append_right _ hr, sub⟩
  · rw [rest.sp]; exact sep
  · rw [rest.sp, mem, Mem.readW_writeW_self32, h.ptr]

end VG.Proof.Bignum.Arm
