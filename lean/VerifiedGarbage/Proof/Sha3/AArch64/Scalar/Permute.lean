module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Boundary
import VerifiedGarbage.Proof.Framework.Offset

/-! # Keccak-f[1600] on AArch64, in general registers: the permutation and absorbing blocks -/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar

open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Proof.Sha3.AArch64
open VG.Spec.Sha3 (keccakF stateAt)

/-- Loading the state at the pointer in `x16`, and the pointer to the working space, then the 24 rounds. -/
theorem run_ok {o s : State} (hc : Ctx o s) {stride off : Nat} (hd : stride % 8 = 0) (ho : off % 8 = 0)
    (hs : stride ≤ 16) (hoff : off < 16) {w : Addr} (hw : vdword (s.v .v30) 0 = w)
    (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (stride * i + off)) 8)
    (hsp : ∀ k < 3, InRegions s.wr (w + BitVec.ofNat 64 (8 * k)) 8) {Q : State → Prop}
    (hQ : ∀ t, Ctx o t → Lanes t (keccakF (stateFrom s.mem (s.gpr .x16) stride off)) →
      (∀ r ∈ argVec, t.v r = s.v r) → Env s t → Frame [⟨w, 24⟩] s.mem t.mem → Q t) :
    WP isa (.block (load .x16 stride off ++ ([.umov .x .x28 .v30 0] : List Instr))) s fun t => WP isa callCore t Q := by
  rw [WP.block_append_iff]
  refine WP.mono (load_ok (A := stateFrom s.mem (s.gpr .x16) stride off) b16 hd ho hs hoff hin
    fun i hi => (stateFrom_get _ _ _ _ hi).symm) fun t ⟨hl, h⟩ => wp_umov fun u d => wp_nil ?_
  have h28 : u.gpr .x28 = w := by rw [d.gpr, h.v, hw]
  have hlu := lanes_upd hl d
  refine callCore_ok hlu (fun k hk => by rw [h28, d.wr, h.env.wr]; exact hsp k hk) fun v hv k => ?_
  refine hQ v (((hc.ofV h.v h.env).upd d).core k) hv (fun r hr => ?_) ((h.env.trans (.upd d)).trans ⟨k.rd, k.wr, k.sp⟩) ?_
  · have : r ≠ .v27 ∧ r ≠ .v28 := by revert r; decide
    rw [k.v r this.1 this.2, d.vec, h.v]
  · have := k.frame
    rw [h28, d.mem, h.mem] at this
    exact this

theorem permute_ok (s : State) (hp : Proof.Sha3.permuteAArch64.pre s) :
    WP isa permute s fun t => abiPreserved s t ∧ Proof.Sha3.permuteAArch64.post s t := by
  obtain ⟨hrd, hwr, hdis⟩ := hp
  have inS : ∀ i < 25, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 (8 * i + 0)) 8 := fun i hi =>
    ⟨⟨s.gpr .x0, 200⟩, by simp [hwr], Offset.contains_base _ (by omega) (by omega)⟩
  have inW : ∀ k < 3, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8 := fun k hk =>
    ⟨⟨s.gpr .x1, 512⟩, by simp [hwr], Offset.contains_base _ (by omega) (by omega)⟩
  unfold permute
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (enter_ok s) fun t₁ ⟨c₁, g₁, m₁⟩ => ?_
  refine wp_dup fun t₂ d₂ => wp_dup fun t₃ d₃ => wp_umov fun t₄ d₄ => ?_
  have c₄ : Ctx s t₄ := ((c₁.dup (by decide) d₂).dup (by decide) d₃).upd d₄
  have v29 : vdword (t₄.v .v29) 0 = s.gpr .x0 := by rw [d₄.vec, d₃.other _ (by decide), d₂.v, g₁]
  have v30 : vdword (t₄.v .v30) 0 = s.gpr .x1 := by rw [d₄.vec, d₃.v, d₂.gpr, g₁]
  have x16 : t₄.gpr .x16 = s.gpr .x0 := by rw [d₄.gpr, d₃.other _ (by decide), d₂.v, g₁]
  have m₄ : t₄.mem = s.mem := by rw [d₄.mem, d₃.mem, d₂.mem, m₁]
  have inr : ∀ a, InRegions s.wr a 8 → InRegions (t₄.rd ++ t₄.wr) a 8 := fun a ⟨R, hR, hc⟩ =>
    ⟨R, List.mem_append_right _ (by rw [c₄.env.wr]; exact hR), hc⟩
  refine WP.mono (run_ok c₄ (by decide) (by decide) (by decide) (by decide) v30
    (fun i hi => by rw [x16]; exact inr _ (inS i hi)) (fun k hk => by rw [c₄.env.wr]; exact inW k hk)
    fun t₅ c₅ l₅ a₅ e₅ f₅ => ?_) fun _ h => WP.seq h
  · rw [x16, m₄, stateFrom_stateAt] at l₅
    rw [m₄] at f₅
    simp only [List.cons_append, List.nil_append]
    refine wp_umov fun t₆ d₆ => ?_
    rw [WP.block_append_iff]
    have x16' : t₆.gpr .x16 = s.gpr .x0 := by rw [d₆.gpr, a₅ _ (by decide), v29]
    have c₆ := c₅.upd d₆
    have hlt := lanes_upd l₅ d₆
    have hin : ∀ i < 25, InRegions t₆.wr (t₆.gpr .x16 + BitVec.ofNat 64 (8 * i + 0)) 8 := fun i hi => by
      rw [x16', c₆.env.wr]; exact inS i hi
    have st := store_ok (s := t₆) b16 (stride := 8) (off := 0) rfl rfl (by decide) (by decide) (by decide) hlt hin
    refine WP.mono st fun t₇ ⟨r₇, f₇, g₇, v₇, e₇⟩ => ?_
    have hA : stateAt t₇.mem (s.gpr .x0) = keccakF (stateAt s.mem (s.gpr .x0)) := by
      rw [← stateFrom_stateAt]
      rw [x16'] at r₇
      exact eq_stateFrom r₇
    refine WP.mono (exit_ok (c₆.ofV v₇ e₇)) fun t₈ h => ⟨h.1, ?_⟩
    simp only [Proof.Sha3.permuteAArch64]
    rw [h.2.1, hA]

end VG.Proof.Sha3.AArch64.Scalar
