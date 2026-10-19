module

public import VerifiedGarbage.Impl.Bignum.Arm.SaveAcceptance
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Saving acceptance leaves the RSA workspace and saved base unchanged -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem saveAcceptance_ok (s : State) (fit : s.sp.toNat + 52 ≤ 2 ^ 32)
    (write : InRegions s.wr (off (State.addr s.sp) 48) 4) :
    WP isa (.block saveAcceptance) s fun t =>
      t.mem = s.mem.writeW (off (State.addr s.sp) 48) (s.gpr .r11) ∧
      Frame [⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem ∧ Rest [.r12] s t := by
  unfold saveAcceptance
  refine wp_stackAddr (by decide) fun u a => ?_
  refine wp_str (a := off (State.addr s.sp) 48) (by decide)
    (by rw [a.gpr]; simp only [BitVec.add_zero]; exact addr_add (by omega))
    (by rw [a.wr]; exact write) fun t b => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off (State.addr s.sp) 48) (s.gpr .r11) := by
    rw [b.mem, a.mem, a.other .r11 (by decide)]
  refine ⟨mem, ?_, (a.rest (by simp)).trans (b.rest _)⟩
  rw [mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem saveAcceptance_ready (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) (fit : s.sp.toNat + 52 ≤ 2 ^ 32)
    (write : InRegions s.wr (off (State.addr s.sp) 48) 4)
    (separate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨off (State.addr s.sp) 48, 4⟩) :
    WP isa (.block saveAcceptance) s fun t => ArithmeticReady base len w t ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.gpr .r11 ∧
      WorkspaceEq (State.addr base) (8 * len) s.mem t.mem ∧
      Frame [⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem ∧ Rest [.r12] s t ∧
      t.mem = s.mem.writeW (off (State.addr s.sp) 48) (s.gpr .r11) := by
  refine WP.mono (saveAcceptance_ok s fit write) ?_
  rintro t ⟨mem, frame, rest⟩
  obtain ⟨ready, eq⟩ := h.after_external frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact separate)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact (Offset.disjoint_base (State.addr s.sp) (d := 48) (n := 4) (k := 4) (by decide) (by decide)).symm)
    rest ((rest.gpr .r0 (by simp)).trans h.ptr)
  exact ⟨ready, by rw [rest.sp, mem, Mem.readW_writeW_self32], eq, frame, rest, mem⟩

end VG.Proof.Bignum.Arm
