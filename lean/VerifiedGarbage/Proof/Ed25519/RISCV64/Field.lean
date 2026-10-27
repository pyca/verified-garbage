module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Field
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed25519 on RISCV64: slots, and constants and copies in them

The slots' offsets and separation, the field area `FA` (bytes 64–1023: the
slots, `ACC` and the freeze's temporaries), and the fills of a slot with a
constant (`constField_op`) or another slot (`copyField_op`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Impl.Words.RISCV64 (li32)
open VG.Proof.X25519 (val32 val32_succ pow32_succ val32_congr)


/-- The field area `[64, 1024)` of the working space. -/
abbrev FA (b : Addr) : Region := ⟨b + BitVec.ofNat 64 64, 960⟩

theorem slot_range (o : Slot) : 64 ≤ offset o ∧ offset o + 32 ≤ 768 := by
  simp only [offset]
  omega

theorem slot_sep (o a : Slot) :
    offset o = offset a ∨ offset o + 32 ≤ offset a ∨ offset a + 32 ≤ offset o := by
  simp only [offset]
  omega

/-- A prefix of eight independent limb stores. -/
structure FillInv (b : Addr) (o : Nat) (s0 : State) (f : Nat → Nat) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, limb s.mem b o j = f j

theorem fill_ok {b : Addr} {o : Nat} {src : Nat → List Instr} {s0 : State}
    {f : Nat → Nat} (hc : Ctx b s0) (ho : o + 32 ≤ 2048) (ho4 : o % 4 = 0)
    (hsrc : ∀ k < 8, ∀ s, FillInv b o s0 f k s →
      WP isa (.block (src k)) s fun t =>
        (t.gpr .a4).toNat % 2 ^ 32 = f k ∧ Rest [.a4] s t ∧ t.mem = s.mem) :
    WP isa (.block ((List.range 8).flatMap fun k =>
      src k ++ ([.store .w .a4 .a3 (o + 4 * k)] : List Instr))) s0 (FillInv b o s0 f 8) := by
  refine wp_range_flatMap (M := isa) (FillInv b o s0 f) (fun k s hk h => ?_)
    8 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  refine WP.append (hsrc k hk s h) fun t ⟨hv, hr, hm⟩ => ?_
  refine sw0_ok ((hc.of_rest h.rest (by decide)).of_rest hr (by decide))
    (by omega) (by omega) fun u hu => WP.block_nil ?_
  have em : u.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 4 * k)) ((t.gpr .a4).setWidth 32) := by
    rw [hu.mem, hm]
  refine ⟨h.rest.trans (hr.trans (hu.rest _)), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _)
        (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [limb, em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.outs j hj
    · rw [wd_write_self, toNat_lo32, hv]

theorem val32_digits (v n : Nat) :
    val32 (fun k => v / 2 ^ (32 * k) % 2 ^ 32) n = v % 2 ^ (32 * n) := by
  induction n with
  | zero => simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | succ n ih =>
    rw [val32_succ, ih, pow32_succ, Nat.mod_mul]

theorem constField_op {b : Addr} {s : State} (hc : Ctx b s) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Rest [.a4] s t ∧ Frame [⟨b + BitVec.ofNat 64 (offset o), 32⟩] s.mem t.mem ∧
      FS t.mem b (offset o) = v := by
  have ho := slot_range o
  refine WP.mono (fill_ok (src := fun k => li32 .a4 (BitVec.ofNat 32 (v.val / 2 ^ (32 * k))))
    (f := fun k => v.val / 2 ^ (32 * k) % 2 ^ 32) hc (by omega) (by simp only [offset]; omega)
    (fun k _ t _ => WP.mono (ByteLoad.li32_ok _) fun u hu => ⟨?_,
      by rw [hu]; exact ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩,
      by rw [hu]; rfl⟩))
    fun t ht => ⟨ht.rest, ht.frame, ?_⟩
  · rw [hu, RegUpd.gpr_write_self, sext32_lo, BitVec.toNat_ofNat]
  · rw [FS, V, val32_congr ht.outs, val32_digits, Nat.mod_eq_of_lt]
    · exact VG.Proof.X25519.toFe_self v
    · have := v.isLt
      simp only [Spec.X25519.P] at this
      omega

theorem copyField_op {b : Addr} {s : State} (hc : Ctx b s) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      Rest [.a4] s t ∧ Frame [⟨b + BitVec.ofNat 64 (offset o), 32⟩] s.mem t.mem ∧
      FS t.mem b (offset o) = FS s.mem b (offset a) := by
  have ho := slot_range o
  have ha := slot_range a
  have hsep := slot_sep o a
  refine WP.mono (fill_ok (src := fun k => [.load .w .a4 .a3 (offset a + 4 * k)])
    (f := limb s.mem b (offset a)) hc (by omega) (by simp only [offset]; omega)
    (fun k hk t ht => lw0_ok (hc.of_rest ht.rest (by decide)) (by omega) (by simp only [offset]; omega)
      fun u hu => WP.block_nil ⟨?_, hu.rest (by decide), hu.mem⟩))
    fun t ht => ⟨ht.rest, ht.frame, ?_⟩
  · rw [hu.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
    exact wd_frame ht.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · exact congrArg VG.Proof.X25519.toFe (val32_congr ht.outs)

end VG.Proof.Ed25519.RISCV64
