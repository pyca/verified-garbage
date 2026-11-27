module

public import VerifiedGarbage.Impl.Ffdh.Arm.VettedCap
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import Mathlib.Tactic.NormNum
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.ScalarWidth

/-! ### `Ffdh.Arm.VettedCapPolicy`, which the modules that import this one used -/

section

/-! ### `Ffdh.VettedBounds`, which only this module used -/

section

/-! Exact vetted groups have scalar bounds exceeding their recommended widths. -/

@[expose] public section
namespace VG.Proof.Ffdh.VettedPolicy
open VG

private theorem recognized_properties {a : Spec.Ffdh.Parameters} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits a = some bits) :
    bits ≤ 400 ∧ 2 ^ 400 < a.p := by
  have pow400 : (2 : Nat) ^ 400 = 2 ^ 200 * 2 ^ 200 := by
    rw [show (400 : Nat) = 200 + 200 from rfl, Nat.pow_add]
  rw [pow400]
  unfold Spec.Ffdh.vettedExponentBits at recognized
  split at recognized
  · cases recognized
  split at recognized
  · rename_i choice
    cases recognized
    have choices : a.p = Spec.Ffdh.modp2048Prime ∨ a.p = Spec.Ffdh.ffdhe2048Prime := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using choice
    rcases choices with prime | prime <;> rw [prime] <;>
      norm_num [Spec.Ffdh.modp2048Prime, Spec.Ffdh.ffdhe2048Prime]
  split at recognized
  · rename_i choice
    cases recognized
    have choices : a.p = Spec.Ffdh.modp3072Prime ∨ a.p = Spec.Ffdh.ffdhe3072Prime := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using choice
    rcases choices with prime | prime <;> rw [prime] <;>
      norm_num [Spec.Ffdh.modp3072Prime, Spec.Ffdh.ffdhe3072Prime]
  split at recognized
  · rename_i choice
    cases recognized
    have choices : a.p = Spec.Ffdh.modp4096Prime ∨ a.p = Spec.Ffdh.ffdhe4096Prime := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using choice
    rcases choices with prime | prime <;> rw [prime] <;>
      norm_num [Spec.Ffdh.modp4096Prime, Spec.Ffdh.ffdhe4096Prime]
  split at recognized
  · rename_i choice
    cases recognized
    have choices : a.p = Spec.Ffdh.modp6144Prime ∨ a.p = Spec.Ffdh.ffdhe6144Prime := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using choice
    rcases choices with prime | prime <;> rw [prime] <;>
      norm_num [Spec.Ffdh.modp6144Prime, Spec.Ffdh.ffdhe6144Prime]
  split at recognized
  · rename_i choice
    cases recognized
    have choices : a.p = Spec.Ffdh.modp8192Prime ∨ a.p = Spec.Ffdh.ffdhe8192Prime := by
      simpa only [Bool.or_eq_true, beq_iff_eq] using choice
    rcases choices with prime | prime <;> rw [prime] <;>
      norm_num [Spec.Ffdh.modp8192Prime, Spec.Ffdh.ffdhe8192Prime]
  cases recognized

theorem recognized_q {a : Spec.Ffdh.Parameters} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits a = some bits) :
    a.q = none ∨ a.q = some ((a.p - 1) / 2) := by
  unfold Spec.Ffdh.vettedExponentBits at recognized
  split at recognized
  · cases recognized
  rename_i guard
  cases qeq : a.q with
  | none => exact Or.inl rfl
  | some q =>
    right
    simp only [qeq, Option.isSome_some, Bool.true_and, Bool.or_eq_true, bne_iff_ne] at guard
    by_contra different
    exact guard (Or.inr different)

private theorem half_bound {p n : Nat} (hp : 2 * n < p) : n ≤ p - 1 ∧ n ≤ (p - 1) / 2 := by
  omega_using [hp]

private theorem lower_bitLength {n x : Nat} (lower : 2 ^ n ≤ x) : n < Spec.RsaKeyGen.bitLength x := by
  have nonzero : x ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _) lower)
  have upper := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds nonzero).2
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt lower upper)

theorem recognized_le_bound {a : Spec.Ffdh.Parameters} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits a = some bits) :
    bits ≤ Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound a) := by
  have properties := recognized_properties recognized
  have power : (2 : Nat) ^ 400 = 2 * 2 ^ 399 := by
    rw [show (400 : Nat) = 200 + 200 from rfl, Nat.pow_add,
      show (399 : Nat) = 200 + 199 from rfl, Nat.pow_add,
      show (200 : Nat) = 199 + 1 from rfl, Nat.pow_succ]
  have halves := half_bound (by rw [← power]; exact properties.2)
  have bound : 2 ^ 399 ≤ Spec.Ffdh.scalarBound a := by
    rcases recognized_q recognized with absent | present
    · simpa only [Spec.Ffdh.scalarBound, absent, Option.getD_none] using halves.1
    · simpa only [Spec.Ffdh.scalarBound, present, Option.getD_some] using halves.2
  have large := lower_bitLength bound
  exact Nat.le_trans properties.1 (Nat.succ_le_of_lt large)

theorem bits_of_recognized_uncapped {a : Spec.Ffdh.Parameters} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits a = some bits) :
    Spec.Ffdh.generationScalarBits a = bits := by
  simp only [Spec.Ffdh.generationScalarBits, recognized, Nat.min_eq_left (recognized_le_bound recognized)]

end VG.Proof.Ffdh.VettedPolicy

end

end


/-! Exact public caps select the reviewed byte widths and masks. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

theorem vetted_caps {a : Spec.Ffdh.Parameters} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits a = some bits) :
    bits = 225 ∨ bits = 275 ∨ bits = 325 ∨ bits = 375 ∨ bits = 400 := by
  unfold Spec.Ffdh.vettedExponentBits at recognized
  repeat' split at recognized
  all_goals cases recognized
  all_goals simp

theorem vetted_cap_result {a : Spec.Ffdh.Parameters} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits a = some bits) (old : BitVec 32 × BitVec 32) :
    VG.Impl.Ffdh.Arm.VettedCap.result VG.Impl.Ffdh.Arm.VettedCap.choices (BitVec.ofNat 32 bits) old =
      (BitVec.ofNat 32 (VG.Proof.Ffdh.ScalarWidth.width bits),
       (VG.Proof.Ffdh.ScalarWidth.mask bits).setWidth 32) := by
  rcases vetted_caps recognized with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem vetted_layout_width {p : Inputs} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf p.k p.dom) = some bits) :
    (ScalarLayout.vetted p).width = VG.Proof.Ffdh.ScalarWidth.width bits := by
  have uncapped := VG.Proof.Ffdh.VettedPolicy.bits_of_recognized_uncapped recognized
  have fit := VG.Proof.Ffdh.ScalarWidth.width_le (by have := p.minLength; omega_using [this])
    (Nat.le_trans (VG.Proof.Ffdh.VettedPolicy.recognized_le_bound recognized) p.scalarBound_bits_fit)
  simp only [ScalarLayout.width, ScalarLayout.vetted, uncapped]
  omega_using [fit]

theorem vetted_layout_mask {p : Inputs} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf p.k p.dom) = some bits) :
    (ScalarLayout.vetted p).mask = (VG.Proof.Ffdh.ScalarWidth.mask bits).setWidth 32 := by
  simp only [ScalarLayout.vetted, VG.Proof.Ffdh.VettedPolicy.bits_of_recognized_uncapped recognized]

theorem vetted_cap_layout {p : Inputs} {bits : Nat}
    (recognized : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf p.k p.dom) = some bits)
    (old : BitVec 32 × BitVec 32) :
    VG.Impl.Ffdh.Arm.VettedCap.result VG.Impl.Ffdh.Arm.VettedCap.choices (BitVec.ofNat 32 bits) old =
      (BitVec.ofNat 32 (ScalarLayout.vetted p).width, (ScalarLayout.vetted p).mask) := by
  rw [vetted_cap_result recognized, vetted_layout_width recognized, vetted_layout_mask recognized]

end VG.Proof.Ffdh.Arm

end

end

/-! Store any selected width and mask while preserving the common saved arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedCap
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem load_ok (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s) :
    WP isa (.block VG.Impl.Ffdh.Arm.VettedCap.load) s fun t =>
      (t.gpr .r6 = s.mem.readW (off (State.addr s.sp) 20) 32 ∧
        t.gpr .r3 = s.mem.readW (off (State.addr s.sp) 68) 32 ∧ t.mem = s.mem) ∧
      Rest [.r3, .r6] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) : State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega_using [hd, this])
  have r20 := h.locals.read (d := 20) (by decide)
  have r68 := h.locals.read (d := 68) (by decide)
  refine withRest_all [.r3, .r6] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.VettedCap.load
  ffrun [addr 20 (by decide), addr 68 (by decide), r20, r68]

theorem save_store (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr s.sp) 20) (s.gpr .r6)).writeW
        (off (State.addr s.sp) 68) (s.gpr .r3) ∧ Rest [.r12] s t := by
  have addr (d : Nat) (hd : d + 4 ≤ 72) : State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega_using [hd, this])
  have w20 := h.locals.space.write (off := 20) (by decide)
  have w68 := h.locals.space.write (off := 68) (by decide)
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave VG.Impl.Ffdh.Arm.Domain.st
  ffrun [addr 20 (by decide), addr 68 (by decide), w20, w68, BitVec.add_zero, off]

theorem save_ok (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s)
    (common : sampleSlots slots) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.boundSave) s fun t =>
      Context p slots t ∧ t.mem.readW (off (State.addr t.sp) 20) 32 = s.gpr .r6 ∧
      t.mem.readW (off (State.addr t.sp) 68) 32 = s.gpr .r3 ∧
      Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem ∧ Rest [.r12] s t := by
  refine WP.mono (save_store s h) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem := by
    rw [mem]
    exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
      (by simp) _ (Region.contains_self _ _)
  have ctx : Context p slots t := by
    refine h.after_frame frame rest ((rest.gpr .r0 (by simp)).trans h.ptr) ?_ ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.domainStack.sub_right (Offset.sub_base _ (by decide : 20 + 4 ≤ 72))
      · exact h.domainStack.sub_right (Offset.sub_base _ (by decide : 68 + 4 ≤ 72))
    · intro d hd r hr
      have bounds := common d hd
      have nowrap := h.locals.space.nowrap
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_using [bounds]) (by omega_using [bounds]) (by omega_using [])
      · exact Offset.disjoint _ (by omega_using [bounds]) (by omega_using [bounds]) (by omega_using [])
  refine ⟨ctx, ?_, ?_, frame, rest⟩
  · rw [rest.sp, mem, Mem.readW_writeW_sep (Offset.sep (State.addr s.sp) (d := 20) (n := 4) (e := 68) (k := 4) (by decide)
      (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  · rw [rest.sp, mem, Mem.readW_writeW_self32]

end VG.Proof.Ffdh.Arm.VettedCap
