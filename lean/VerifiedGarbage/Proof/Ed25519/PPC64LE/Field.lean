module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Field
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed25519 on PPC64LE: slots, and constants and copies in them

The slots' offsets and separation, the field area `FA` (bytes 64–1023: the
slots, `ACC` and the freeze's temporaries), and the fills of a slot with a
constant (`constField_op`) or another slot (`copyField_op`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE

theorem ACC_eq : ACC = 864 := rfl

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
  rest : Rest [.r7] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, limb s.mem b o j = f j

theorem fill_ok {b : Addr} {o : Nat} {src : Nat → List Instr} {s0 : State}
    {f : Nat → Nat} (hc : Ctx b s0) (ho : o + 32 ≤ 4096)
    (hsrc : ∀ k < 8, ∀ s, FillInv b o s0 f k s →
      WP isa (.block (src k)) s fun t =>
        (t.gpr .r7).toNat % 2 ^ 32 = f k ∧ Rest [.r7] s t ∧ t.mem = s.mem) :
    WP isa (.block ((List.range 8).flatMap fun k =>
      src k ++ ([.store .w .r7 .r6 (o + 4 * k)] : List Instr))) s0 (FillInv b o s0 f 8) := by
  refine wp_range_flatMap (M := isa) (FillInv b o s0 f) (fun k s hk h => ?_)
    8 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  refine WP.append (hsrc k hk s h) fun t ⟨hv, hr, hm⟩ => ?_
  refine sw0_ok ((hc.of_rest h.rest (by decide)).of_rest hr (by decide))
    (by omega) fun u hu => WP.block_nil ?_
  have em : u.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 4 * k)) ((t.gpr .r7).setWidth 32) := by
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

/-- `lis` of the high half of a word and `ori` of its low half: the word in
the low 32 bits. -/
theorem lis_ori_word (w : Nat) :
    (((BitVec.ofNat 16 (w / 2 ^ 16) ++ (0 : BitVec 16)).signExtend 64 |||
      (BitVec.ofNat 16 w).setWidth 64)).toNat % 2 ^ 32 = w % 2 ^ 32 := by
  have h := lis_ori (BitVec.ofNat 32 w)
  have e1 : (BitVec.ofNat 32 w).extractLsb' 16 16 = BitVec.ofNat 16 (w / 2 ^ 16) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [show (2 : Nat) ^ 32 = 2 ^ 16 * 2 ^ 16 from rfl, Nat.mod_mul_right_div_self, Nat.mod_mod]
  have e2 : (BitVec.ofNat 32 w).extractLsb' 0 16 = BitVec.ofNat 16 w := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    exact Nat.mod_mod_of_dvd _ (by decide)
  rw [e1, e2] at h
  rw [← toNat_lo32, h, BitVec.toNat_ofNat]

theorem constField_op {b : Addr} {s : State} (hc : Ctx b s) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Rest [.r7] s t ∧ Frame [⟨b + BitVec.ofNat 64 (offset o), 32⟩] s.mem t.mem ∧
      FS t.mem b (offset o) = v := by
  have ho := slot_range o
  refine WP.mono (fill_ok (src := fun k => [.lis .r7 (BitVec.ofNat 16 (v.val / 2 ^ (32 * k + 16))),
      .ori .r7 .r7 (BitVec.ofNat 16 (v.val / 2 ^ (32 * k)))])
    (f := fun k => v.val / 2 ^ (32 * k) % 2 ^ 32) hc (by omega)
    (fun k _ t _ => wp_lis fun u hu => wp_ori fun w hw => WP.block_nil ⟨?_,
      (hu.rest (by decide)).trans (hw.rest (by decide)), by rw [hw.mem, hu.mem]⟩))
    fun t ht => ⟨ht.rest, ht.frame, ?_⟩
  · rw [hw.gpr, hu.gpr, show v.val / 2 ^ (32 * k + 16) = v.val / 2 ^ (32 * k) / 2 ^ 16 by
      rw [Nat.pow_add, Nat.div_div_eq_div_mul], lis_ori_word]
  · rw [FS, V, val32_congr ht.outs, val32_digits, Nat.mod_eq_of_lt]
    · exact VG.Proof.X25519.toFe_self v
    · have := v.isLt
      simp only [Spec.X25519.P] at this
      omega

theorem copyField_op {b : Addr} {s : State} (hc : Ctx b s) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      Rest [.r7] s t ∧ Frame [⟨b + BitVec.ofNat 64 (offset o), 32⟩] s.mem t.mem ∧
      FS t.mem b (offset o) = FS s.mem b (offset a) := by
  have ho := slot_range o
  have ha := slot_range a
  have hsep := slot_sep o a
  refine WP.mono (fill_ok (src := fun k => [.load .w .r7 .r6 (offset a + 4 * k)])
    (f := limb s.mem b (offset a)) hc (by omega)
    (fun k hk t ht => lw0_ok (hc.of_rest ht.rest (by decide)) (by omega)
      fun u hu => WP.block_nil ⟨?_, hu.rest (by decide), hu.mem⟩))
    fun t ht => ⟨ht.rest, ht.frame, ?_⟩
  · rw [hu.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
    exact wd_frame ht.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · exact congrArg VG.Proof.X25519.toFe (val32_congr ht.outs)

end VG.Proof.Ed25519.PPC64LE
