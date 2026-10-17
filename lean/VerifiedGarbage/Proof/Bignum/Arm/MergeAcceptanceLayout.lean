module

public import VerifiedGarbage.Impl.Bignum.Arm.SaveAcceptance
public import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutExternal
public import VerifiedGarbage.Proof.Bignum.Arm.MergeAcceptance
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Saving acceptance leaves the RSA workspace and saved base unchanged -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem mergeAcceptanceLayout_ready (s : State) {base : BitVec 32} {len w : Nat}
    (h : LayoutFrameReady base len w s) (fit : s.sp.toNat + 52 ≤ 2 ^ 32)
    (write : InRegions s.wr (off (State.addr s.sp) 48) 4)
    (separate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨off (State.addr s.sp) 48, 4⟩) :
    WP isa (.block mergeAcceptance) s fun t => LayoutFrameReady base len w t ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.gpr .r11 &&& s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      WorkspaceEq (State.addr base) (8 * len) s.mem t.mem ∧
      Frame [⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem ∧ Rest [.r1, .r11, .r12] s t ∧
      t.mem = s.mem.writeW (off (State.addr s.sp) 48) (s.gpr .r11 &&& s.mem.readW (off (State.addr s.sp) 48) 32) := by
  refine WP.mono (mergeAcceptance_ok s fit write) ?_
  rintro t ⟨_, mem, frame, rest⟩
  obtain ⟨ready, eq⟩ := h.after_external frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact separate)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact (Offset.disjoint_base (State.addr s.sp) (d := 48) (n := 4) (k := 4) (by decide) (by decide)).symm)
    rest ((rest.gpr .r0 (by simp)).trans h.ptr)
  exact ⟨ready, by rw [rest.sp, mem, Mem.readW_writeW_self32], eq, frame, rest, mem⟩

end VG.Proof.Bignum.Arm
