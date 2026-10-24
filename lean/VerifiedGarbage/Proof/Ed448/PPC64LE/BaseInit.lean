module

public import VerifiedGarbage.Impl.Ed448.PPC64LE.ScalarBase
public import VerifiedGarbage.Proof.X448.PPC64LE.Field
import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarBit
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass

/-!
# Ed448 on PPC64LE: constants in slots

`constField o v` stores the fourteen words of `v` in the slot at `o`
(`constField_ok`), and `initSlots` the starting values of the base-point
multiplication: `R = (0 : 1 : 1)`, the base point `Q` and `d`
(`initSlots_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Spec.X448 (Fe P)

theorem val32_digits (v n : Nat) :
    val32 (fun k => v / 2 ^ (32 * k) % 2 ^ 32) n = v % 2 ^ (32 * n) := by
  induction n with
  | zero => simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | succ n ih =>
    rw [val32_succ, ih, pow32_succ, Nat.mod_mul]

section
variable {b : Addr}

/-- A prefix of fourteen independent limb stores. -/
structure FillInv (b : Addr) (o : Nat) (s0 : State) (f : Nat → Nat) (k : Nat) (s : State) : Prop where
  rest : Rest [.r7] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, limb s.mem b o j = f j

theorem fill_ok {o : Nat} {src : Nat → List Instr} {s0 : State} {f : Nat → Nat} (hc : Ctx b s0)
    (ho : o + 56 ≤ 4096)
    (hsrc : ∀ k < 14, ∀ s, FillInv b o s0 f k s →
      WP isa (.block (src k)) s fun t =>
        (t.gpr .r7).toNat % 2 ^ 32 = f k ∧ Rest [.r7] s t ∧ t.mem = s.mem) :
    WP isa (.block ((List.range 14).flatMap fun k =>
      src k ++ ([.store .w .r7 .r6 (o + 4 * k)] : List Instr))) s0 (FillInv b o s0 f 14) := by
  refine wp_range_flatMap (M := isa) (FillInv b o s0 f) (fun k s hk h => ?_)
    14 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
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

/-- The number `v < 2⁴⁴⁸` into the slot at `o`. -/
theorem constField_ok {s : State} (hc : Ctx b s) {o : Nat} (ho : o + 56 ≤ 4096) {v : Nat}
    (hv : v < 2 ^ 224 * 2 ^ 224) :
    WP isa (.block (constField o v)) s fun t =>
      Rest [.r7] s t ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem t.mem ∧ V t.mem b o = v := by
  refine WP.mono (fill_ok (src := fun k => [.lis .r7 (BitVec.ofNat 16 (v / 2 ^ (32 * k + 16))),
      .ori .r7 .r7 (BitVec.ofNat 16 (v / 2 ^ (32 * k)))])
    (f := fun k => v / 2 ^ (32 * k) % 2 ^ 32) hc ho
    (fun k _ t _ => wp_lis fun u hu => wp_ori fun w hw => WP.block_nil ⟨?_,
      (hu.rest (by decide)).trans (hw.rest (by decide)), by rw [hw.mem, hu.mem]⟩))
    fun t ht => ⟨ht.rest, ht.frame, ?_⟩
  · rw [hw.gpr, hu.gpr, show v / 2 ^ (32 * k + 16) = v / 2 ^ (32 * k) / 2 ^ 16 by
      rw [Nat.pow_add, Nat.div_div_eq_div_mul], lis_ori_word]
  · rw [V, val32_congr ht.outs, val32_digits, Nat.mod_eq_of_lt (by rw [pow448]; exact hv)]

theorem fe_lt (x : Fe) : x.val < 2 ^ 224 * 2 ^ 224 := by
  have := x.isLt
  have := P_eq
  omega

/-- A slot apart from the one `constField` writes keeps its element. -/
theorem slot_keep {m m' : Mem} {o q : Nat} (hf : Frame [⟨b + BitVec.ofNat 64 o, 56⟩] m m')
    (hoq : o + 56 ≤ q ∨ q + 56 ≤ o) (ho : o + 56 ≤ 4096) (hq : q + 56 ≤ 4096) : V m' b q = V m b q := by
  unfold V
  exact val32_congr (limb_frame hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega))

/-- The slots `initSlots` writes. -/
def initQ : List Nat := [RX, RY, RZ, QX, QY, QZ, DK]

/-- The starting value of each of them. -/
def initVal (q : Nat) : Nat :=
  if q = RX then Spec.Ed448.identity.X.val else if q = RY then Spec.Ed448.identity.Y.val
  else if q = RZ then Spec.Ed448.identity.Z.val else if q = QX then Spec.Ed448.basePoint.X.val
  else if q = QY then Spec.Ed448.basePoint.Y.val else if q = QZ then Spec.Ed448.basePoint.Z.val
  else Spec.Ed448.d.val

/-- After the first `n` of the stores of `initSlots`. -/
structure InitInv (b : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  rest : Rest [.r7] s0 s
  frame : Frame (initQ.map fun q => ⟨b + BitVec.ofNat 64 q, 56⟩) s0.mem s.mem
  vals : ∀ i < n, V s.mem b (initQ.getD i 0) = initVal (initQ.getD i 0)

theorem initQ_sep : ∀ i < 7, ∀ j < 7, i ≠ j →
    initQ.getD i 0 + 56 ≤ initQ.getD j 0 ∨ initQ.getD j 0 + 56 ≤ initQ.getD i 0 := by decide

theorem initQ_mem : ∀ i < 7, initQ.getD i 0 ∈ initQ := by decide

theorem initQ_fits : ∀ i < 7, initQ.getD i 0 + 56 ≤ 4096 := by decide

theorem initSlots_eq : initSlots = (List.range 7).flatMap fun i =>
    constField (initQ.getD i 0) (initVal (initQ.getD i 0)) := by
  simp only [initSlots, List.range_succ, List.range_zero, List.flatMap_append, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

theorem initSlots_ok {s : State} (hc : Ctx b s) :
    WP isa (.block initSlots) s fun t => Rest [.r7] s t ∧
      Frame (initQ.map fun q => ⟨b + BitVec.ofNat 64 q, 56⟩) s.mem t.mem ∧
      ∀ q ∈ initQ, V t.mem b q = initVal q := by
  rw [initSlots_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (InitInv b s) (fun i t hi h => ?_) 7 (Nat.le_refl _) s
    ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩) fun t h => ⟨h.rest, h.frame, fun q hq => ?_⟩
  · have hi' := initQ_fits i hi
    have hv : initVal (initQ.getD i 0) < 2 ^ 224 * 2 ^ 224 := by
      simp only [initVal]; repeat' split
      all_goals exact fe_lt _
    refine WP.mono (constField_ok (hc.of_rest h.rest (by decide)) hi' hv) fun u ⟨ru, fu, vu⟩ =>
      ⟨h.rest.trans ru, h.frame.trans (fu.sub fun r hr => ⟨r, ?_, fun x hx => hx⟩), fun j hj => ?_⟩
    · rw [List.mem_singleton.mp hr]
      exact List.mem_map.mpr ⟨_, initQ_mem i hi, rfl⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [slot_keep fu (initQ_sep i hi j (by omega) (by omega)) hi' (initQ_fits j (by omega))]
        exact h.vals j hj
      · exact vu
  · have : ∃ i < 7, initQ.getD i 0 = q := by
      simp only [initQ, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩,
        ⟨4, by decide, rfl⟩, ⟨5, by decide, rfl⟩, ⟨6, by decide, rfl⟩]
    obtain ⟨i, hi, rfl⟩ := this
    exact h.vals i hi

end

end VG.Proof.Ed448.PPC64LE
