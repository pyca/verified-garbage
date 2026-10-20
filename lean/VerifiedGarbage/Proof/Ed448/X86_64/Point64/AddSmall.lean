module

public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
import VerifiedGarbage.Proof.Framework.Block

/-! Specializing the affine addition's fixed curve constant, without changing its contract. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Point64

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Point64 VG.Proof.Ed448
open VG.Proof.X448.X86_64 (Scr Index Env E Keep clob ofs Outside E_update slot_lt)
open VG.Impl.X448.X86_64 (slot ACC)

set_option exponentiation.threshold 1024
private theorem small_neg (x : Spec.X448.Fe) :
    Spec.X448.a24 * (0 - x) = Spec.Ed448.d * x := by
  apply Fin.ext
  change (39081 * ((Spec.X448.P - x.val) % Spec.X448.P)) % Spec.X448.P =
    ((Spec.X448.P - 39081) * x.val) % Spec.X448.P
  have h : 39081 * (Spec.X448.P - x.val) + Spec.X448.P * x.val =
      (Spec.X448.P - 39081) * x.val + 39081 * Spec.X448.P := by
    have hx := x.isLt
    unfold Spec.X448.P at *
    omega
  have hm := congrArg (fun n => n % Spec.X448.P) h
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.mul_zero,
    Nat.add_zero, Nat.zero_mod, Nat.mod_mod] using hm

/-- The field operation's exact value and memory frame are unchanged when slot 11 holds `d`. -/
theorem mulD_ok {s : State} {base : Addr} (hs : Scr s base)
    (hd : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (.block mulD) s fun t =>
      Keep base s t ∧ E t.mem base = evalOp (.mul 16 11 14) (E s.mem base) ∧
      ∀ x, OutOf base x (.mul 16 11 14) → (ofs base x < ACC ∨ ACC + 112 ≤ ofs base x) →
        t.mem x = s.mem x := by
  rw [mulD, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fop_frame Proof.X448.X86_64.baseline_ok hs (.sub 16 14 14) (by decide))
    fun s₁ ⟨k₁, e₁, f₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fop_frame Proof.X448.X86_64.baseline_ok (k₁.scr hs) (.sub 16 16 14) (by decide))
    fun s₂ ⟨k₂, e₂, f₂⟩ => ?_
  refine WP.mono (Proof.X448.X86_64.baseline_ok.a24 (k₂.scr (k₁.scr hs))
    (slot_lt (16 : Index)) (slot_lt (16 : Index))) fun t ⟨kt, et⟩ => ?_
  refine ⟨(k₁.trans k₂).trans (Proof.X448.X86_64.Op.keep (o := 16) kt), ?_, fun x hx ha => ?_⟩
  · rw [E_update (o := 16) kt.mem]
    change Function.update (E s₂.mem base) 16 (Proof.X448.X86_64.F t.mem base (slot 16)) = _
    rw [et]
    change Function.update (E s₂.mem base) 16 (Spec.X448.a24 * E s₂.mem base 16) = _
    rw [e₂, e₁]
    simp only [evalOp, show idx 16 = (16 : Index) from rfl,
      show idx 14 = (14 : Index) from rfl, show idx 11 = (11 : Index) from rfl]
    simp only [Function.update_self, Function.update_of_ne (by decide : (14 : Index) ≠ 16),
      Fin.sub_self, Function.update_idem, hd]
    rw [small_neg]
  · rw [kt.mem x hx ha, f₂ x hx ha, f₁ x hx ha]

/-- Specializing `d` preserves every field slot, including the intermediates. -/
theorem addCodeWith_ok {F : Impl.X448.X86_64.Field} (hf : Proof.X448.X86_64.FieldOk F) {s : State} {base : Addr} (hs : Scr s base)
    (hd : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (.block (addCodeWith F)) s fun t =>
      Keep base s t ∧ E t.mem base = evalOps addAffineOps (E s.mem base) ∧
      ∀ x, (∀ op ∈ addAffineOps, OutOf base x op) →
        (ofs base x < ACC ∨ ACC + 112 ≤ ofs base x) → t.mem x = s.mem x := by
  rw [addCodeWith, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_frame hf (addAffineOps.take 3)
    (by decide) hs) fun s₁ ⟨k₁, e₁, f₁⟩ => ?_
  have hd₁ : E s₁.mem base 11 = Spec.Ed448.d := by rw [e₁]; exact hd
  rw [WP.block_append_iff]
  refine WP.mono (mulD_ok (k₁.scr hs) hd₁) fun s₂ ⟨k₂, e₂, f₂⟩ => ?_
  refine WP.mono (fieldCode_frame hf (addAffineOps.drop 4)
    (by decide) (k₂.scr (k₁.scr hs))) fun t ⟨kt, et, ft⟩ => ?_
  refine ⟨(k₁.trans k₂).trans kt, ?_, fun x hx ha => ?_⟩
  · rw [et, e₂, e₁]
    conv => rhs; rw [show addAffineOps = addAffineOps.take 3 ++ [.mul 16 11 14] ++
      addAffineOps.drop 4 from rfl]
    simp only [evalOps, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · rw [ft x (fun op hop => hx op (List.mem_of_mem_drop hop)) ha,
      f₂ x (hx _ (by decide)) ha,
      f₁ x (fun op hop => hx op (List.mem_of_mem_take hop)) ha]

theorem addCode_ok {s : State} {base : Addr} (hs : Scr s base)
    (hd : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (.block addCode) s fun t =>
      Keep base s t ∧ E t.mem base = evalOps addAffineOps (E s.mem base) ∧
      ∀ x, (∀ op ∈ addAffineOps, OutOf base x op) →
        (ofs base x < ACC ∨ ACC + 112 ≤ ofs base x) → t.mem x = s.mem x :=
  addCodeWith_ok Proof.X448.X86_64.baseline_ok hs hd

/-- The specialized addition between the same register saves and restores. -/
theorem addFnWith_ok {F : Impl.X448.X86_64.Field} (hf : Proof.X448.X86_64.FieldOk F) {s : State} {base : Addr} (hs : Scr s base)
    (hd : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (addFnWith F) s fun t =>
      Keep base s t ∧ E t.mem base = evalOps addAffineOps (E s.mem base) ∧
      ∀ x, (∀ op ∈ addAffineOps, OutOf base x op) →
        (ofs base x < ACC ∨ ACC + 112 ≤ ofs base x) → t.mem x = s.mem x := by
  simp only [addFnWith, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (saves_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (addCodeWith_ok hf hs₁ (by rw [m₁]; exact hd)) fun s₂ ⟨k₂, e₂, f₂⟩ => ?_
  refine WP.mono (restores_ok s₂) fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [rd₃, k₂.rd, rd₁], by rw [wr₃, k₂.wr, wr₁], ?_⟩,
    by rw [m₃, e₂, m₁], fun x hx ha => by rw [m₃, f₂ x hx ha, m₁]⟩
  · have hk : r ∉ keptRegs := fun h => hr (by
      revert h; simp only [keptRegs, kept, clob, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl | rfl) <;> simp)
    rw [g₃ r hk, k₂.gpr r hr, g₁]
  · intro x hx
    rw [m₃, k₂.mem x hx, m₁]

theorem addFn_ok {s : State} {base : Addr} (hs : Scr s base)
    (hd : E s.mem base 11 = Spec.Ed448.d) :
    WP isa addFn s fun t =>
      Keep base s t ∧ E t.mem base = evalOps addAffineOps (E s.mem base) ∧
      ∀ x, (∀ op ∈ addAffineOps, OutOf base x op) →
        (ofs base x < ACC ∨ ACC + 112 ≤ ofs base x) → t.mem x = s.mem x :=
  addFnWith_ok Proof.X448.X86_64.baseline_ok hs hd

/-- The functions' code, as the calls run it. The addition uses its existing `d` precondition. -/
theorem bodies_ok : PointOk bodies where
  dbl hs := WP.mono (fn_ok doubleOps doubleOps_valid hs) fun _ ⟨k, e, _⟩ => ⟨k, e⟩
  add hs hd := WP.mono (addFn_ok hs hd) fun _ ⟨k, e, _⟩ => ⟨k, e⟩

end VG.Proof.Ed448.X86_64.Point64
