module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.Words32

/-! # Search status updates preserve every other persistent frame word -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem frameStatus_ok {s : State} {base : Addr} {words : Nat → BitVec 32}
    (F : SearchFrame s base) (R : FrameWords s.mem base words) (status : Nat) :
    WP isa (.block (frameStatus status)) s fun t => SearchFrame t base ∧
      FrameWords t.mem base (frameUpdate words 19 (BitVec.ofNat 32 status)) ∧
      Outside base 76 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold frameStatus
  refine wp_movS rfl fun a sa _ => ?_
  have Fa := F.keeps sa.keeps (by decide)
  refine wp_storeS (Fa.ea (by decide : 19 < 37)) (Fa.writable (by decide : 19 < 37)) fun t at' => WP.block_nil ?_
  have K := sa.keeps.trans (at'.keeps [.eax])
  have mem : t.mem = s.mem.writeW (off base 76) (BitVec.ofNat 32 status) := by
    rw [at'.mem, sa.gpr, sa.mem]
  exact ⟨F.keeps K (by decide), by rw [mem]; exact R.write (by decide : 19 < 37) _,
    by rw [mem]; exact writeW32_outside _ _ _ (by decide), K⟩

theorem frameStatusAx_ok {s : State} {base : Addr} {words : Nat → BitVec 32}
    (F : SearchFrame s base) (R : FrameWords s.mem base words) :
    WP isa (.block [.store (frameSlot 19) .eax]) s fun t => SearchFrame t base ∧
      FrameWords t.mem base (frameUpdate words 19 (s.gpr .eax)) ∧
      Outside base 76 4 s.mem t.mem ∧ Keeps [] s t := by
  refine wp_storeS (F.ea (by decide : 19 < 37)) (F.writable (by decide : 19 < 37)) fun t st => WP.block_nil ?_
  exact ⟨F.keeps (st.keeps []) (by decide), by rw [st.mem]; exact R.write (by decide : 19 < 37) _,
    by rw [st.mem]; exact writeW32_outside _ _ _ (by decide), st.keeps []⟩

theorem frameUpdate_same {words : Nat → BitVec 32} {i : Nat} {value : BitVec 32} (same : words i = value) :
    frameUpdate words i value = words := by
  funext j
  by_cases eq : j = i
  · subst j; simp only [frameUpdate, ite_true, same]
  · simp only [frameUpdate, ite_eq_right eq]
end VG.Proof.Dsa.X86.Generation
