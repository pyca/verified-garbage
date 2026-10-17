module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivStackWord
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # All fourteen CRT stack arguments are copied without changing retained slots -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem copyArgs_prefix_ok (n : Nat) (hn : n ≤ 14) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) (ptr : s.gpr .r12 = g.stack) :
    WP isa (.block ((List.range n).flatMap copyArg)) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      (∀ j < n, t.mem.readW (off (State.addr g.stack) (4 * j)) 32 = g.argument (j + 2)) ∧
      Frame [⟨State.addr g.stack, 56⟩] s.mem t.mem ∧ Rest [.r0] s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨h, slots, by intro j hj; omega, Frame.refl _ _, Rest.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h slots ptr) ?_
    rintro u ⟨hu, slotsU, copied, frameU, restU⟩
    refine WP.mono (copyArg_context u hu slotsU (by omega : n < 14)
      ((restU.gpr .r12 (by simp)).trans ptr)) ?_
    rintro t ⟨ht, slotsT, mem, restT⟩
    refine ⟨ht, slotsT, ?_, ?_, restU.trans restT⟩
    · intro j hj
      by_cases same : j = n
      · subst j; rw [mem, Mem.readW_writeW_self32]
      · have outside := writeW32_outside u.mem (State.addr g.stack) (d := 4 * n) (g.argument (n + 2)) (by omega)
        rw [mem, outside_read32 outside (d := 4 * j) (by omega) (by omega)]
        exact copied j (by omega)
    · apply frameU.trans
      rw [mem]
      exact outgoing_frame (by omega)

theorem copyArgs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) (ptr : s.gpr .r12 = g.stack) :
    WP isa (.block copyArgs) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      (∀ j < 14, t.mem.readW (off (State.addr g.stack) (4 * j)) 32 = g.argument (j + 2)) ∧
      Frame [⟨State.addr g.stack, 56⟩] s.mem t.mem ∧ Rest [.r0] s t :=
  copyArgs_prefix_ok 14 (by decide) s h slots ptr
end VG.Proof.Rsa.Arm
