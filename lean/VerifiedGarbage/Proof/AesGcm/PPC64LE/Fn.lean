module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.J0
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash

/-!
# AES-GCM on PPC64LE: the functions' entry and exit

Untrusted: everything here is checked by Lean. Every function saves our
caller's `r18`–`r31` and its return address in `W` on entry (`save_ok`,
`Spill.save_ok`) and restores them on exit (`restore_ok`), which with the
other nonvolatile registers (`r2`, `r14`–`r17`, which the pieces keep:
`Env`) gives `abiPreserved`. Also here: the layout from the disjointness of
the buffers (`Lay.of`), and that the pieces never write the saved slots.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)

/-- Where `save` puts our caller's registers and return address. -/
def SavedAt (m : Mem) (w : Addr) (s₀ : State) : Prop :=
  Spill.Saved w s₀.gpr saved m ∧ m.readW (w + BitVec.ofNat 64 lrO) 64 = s₀.lr

/-- The saved registers' and return address's slots. -/
abbrev savedR (w : Addr) : Region := ⟨w + BitVec.ofNat 64 128, 120⟩

theorem saved_bound : ∀ p ∈ saved, 128 ≤ p.2 ∧ p.2 + 8 ≤ 240 := by decide

theorem saved_fits : Spill.Fits saved := by decide

theorem save_eq (b : Reg) :
    save b = Spill.saveCode b saved ++ ([.mflr .r0, .store .d .r0 b lrO, mov .r31 b] : List Instr) := rfl

theorem restore_eq :
    restore = ([mov .r12 .r31, .load .d .r0 .r12 lrO, .mtlr .r0] : List Instr) ++
      Spill.restoreCode .r12 saved := rfl

/-- Saving the registers and the return address in `W`, at `b`. -/
theorem save_ok {s : State} {b : Reg} (hb0 : b ≠ .r0) (hw : Covers [⟨s.gpr b, 2560⟩] s.wr) :
    WP isa (.block (save b)) s fun s' =>
      (∀ r, r ≠ .r0 → r ≠ .r31 → s'.gpr r = s.gpr r) ∧ s'.gpr .r31 = s.gpr b ∧
      Keeps' s s' ∧ SavedAt s'.mem (s.gpr b) s ∧ Frame [savedR (s.gpr b)] s.mem s'.mem := by
  rw [save_eq]
  refine Spill.save_ok hb0 (fun p hp => by have := saved_bound p hp; revert p; decide)
    (fun p hp => in_off hw (by have := saved_bound p hp; omega) (by decide)) ?_
  generalize hM : Spill.saveMem s.mem (s.gpr b) s.gpr saved = M
  have hl := in_off hw (show lrO + 8 ≤ 2560 by decide) (by decide)
  have hb0' : (b = .r0) = False := eq_false hb0
  simp only [lrO] at hl
  crun [lrO, hb0', hl, mov, BitVec.or_self, write_8]
  refine ⟨fun r a c => by simp [a, c], ⟨rfl, rfl, rfl, rfl⟩, ⟨?_, ?_⟩, ?_⟩
  · have hS := Spill.saveMem_saved saved_fits s.mem (s.gpr b) s.gpr
    rw [hM] at hS
    refine hS.frame (rs := [⟨s.gpr b + BitVec.ofNat 64 240, 8⟩])
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun p hp r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have := saved_bound p hp
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  · simp only [lrO]; exact Mem.readW_writeW_self64 _ _ _
  · rw [← hM]
    exact (Spill.saveMem_frame (lo := 128) (n := 120) (fun p hp => by have := saved_bound p hp; omega)
      (by decide) _ _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide)
        (by decide))

/-- The saved slots stay as they are, outside a frame. -/
theorem SavedAt.frame {m m' : Mem} {w : Addr} {s₀ : State} (h : SavedAt m w s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savedR w).Disjoint r) : SavedAt m' w s₀ := by
  refine ⟨h.1.frame hf fun p hp r hr => (hd r hr).sub_left ?_, ?_⟩
  · have := saved_bound p hp
    exact Offset.sub _ (by omega) (by omega)
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide)
      (by decide))) (by decide)]
    exact h.2

/-- The end of every function: our caller's registers and return address
restored, from `W` in `r31`. -/
theorem restore_ok {s s₀ : State} {w : Addr} (h31 : s.gpr .r31 = w)
    (hr : Covers [⟨w, 2560⟩] (s.rd ++ s.wr)) (hs : SavedAt s.mem w s₀) (hsp : s.sp = s₀.sp)
    (hk : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s.gpr r = s₀.gpr r) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [restore_eq]
  have hl := in_off hr (show lrO + 8 ≤ 2560 by decide) (by decide)
  have h₁ : WP isa (.block [mov .r12 .r31, .load .d .r0 .r12 lrO, .mtlr .r0]) s fun s₁ =>
      s₁.gpr .r12 = w ∧ s₁.lr = s₀.lr ∧ (∀ r, r ≠ .r0 → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
    have hl' := hs.2
    simp only [lrO] at hl hl'
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, mov, State.write, addr,
      State.load, Size.bytes, BitVec.setWidth_eq, h31, hl, BitVec.or_self, Proof.Gcm.PPC64LE.read_8,
      hl', Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq, ne_eq,
      not_false_eq_true, Nat.reduceLT, Nat.reducePow, Nat.reduceMod, ↓reduceIte, and_self, implies_true,
      lrO, true_and, and_true]
    exact fun r a b => by simp [a, b]
  refine WP.block_append (WP.mono h₁ fun s₁ ⟨h12, hlr, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ => ?_)
  refine WP.mono (Spill.restore_wp (by decide) h12 (fun p hp => by have := saved_bound p hp; revert p; decide)
    (by decide) (fun p hp => by
      rw [hrd₁, hwr₁]; exact in_off hr (by have := saved_bound p hp; omega) (by decide))
    (hm₁ ▸ hs.1)) fun s' h => ?_
  refine ⟨⟨fun r hr => h.gpr_of ?_, by rw [h.sp, hsp₁, hsp], by rw [h.lr, hlr]⟩,
    by rw [h.mem, hm₁], ?_, by rw [h.rd, hrd₁], by rw [h.wr, hwr₁]⟩
  · by_cases hm : r ∈ saved.map Prod.fst
    · exact .inl hm
    · right
      have hr' : r ∈ [Reg.r2, .r14, .r15, .r16, .r17] := by revert hm hr; revert r; decide
      rw [hg₁ r (by revert hr'; revert r; decide) (by revert hr'; revert r; decide), hk r hr']
  · rw [h.other _ (by decide), hg₁ _ (by decide) (by decide)]

/-- The layout, from the disjointness of the context, the state and `W`. -/
theorem Lay.of {c st w : Addr} (cw : c.toNat + 256 ≤ 2 ^ 64) (sw : st.toNat + 80 ≤ 2 ^ 64)
    (ww : w.toNat + 2560 ≤ 2 ^ 64) (cs : (⟨c, 256⟩ : Region).Disjoint ⟨st, 80⟩)
    (cW : (⟨c, 256⟩ : Region).Disjoint ⟨w, 2560⟩) (sW : (⟨st, 80⟩ : Region).Disjoint ⟨w, 2560⟩) :
    Lay c st w :=
  ⟨cw, sw, ww, cs, cW, sW.sub_right (Region.sub_prefix (by decide)),
    sW.sub_right (Offset.sub_base _ (by decide))⟩

/-- A run that satisfies `R`, and for each `i` with `P i`, `Q i`. -/
theorem WP.forall_det {c : Prog isa} {s : State} {ι : Sort _} {P : ι → Prop} {Q : ι → State → Prop}
    {R : State → Prop} (h₀ : WP isa c s R) (h : ∀ i, P i → WP isa c s (Q i)) :
    WP isa c s fun s' => R s' ∧ ∀ i, P i → Q i s' := by
  obtain ⟨t, s', e, r⟩ := h₀
  refine ⟨t, s', e, r, fun i hi => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h i hi
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

theorem toNat_mod16 (n : Nat) : (BitVec.ofNat 64 n).toNat % 16 = n % 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

theorem ctxH_eq (m : Mem) (p : Addr) : Spec.Gcm.ctxH m p = Spec.Gcm.blockAt m (p + BitVec.ofNat 64 240) :=
  rfl

section
variable {c st w : Addr} (L : Lay c st w)
include L

omit L in
theorem saved_w {d k : Nat} (hd : d + k ≤ 2560) (ho : d + k ≤ 128 ∨ 248 ≤ d) :
    (savedR w).Disjoint ⟨w + BitVec.ofNat 64 d, k⟩ :=
  Lay.w_w (by omega) (by decide) hd

theorem Lay.saved_st {d k : Nat} (hd : d + k ≤ 80) : (savedR w).Disjoint ⟨st + BitVec.ofNat 64 d, k⟩ :=
  (L.st_w hd (.inr ⟨by decide, by decide⟩)).symm

theorem Lay.saved_ctx {d k : Nat} (hd : d + k ≤ 256) : (savedR w).Disjoint ⟨c + BitVec.ofNat 64 d, k⟩ :=
  (L.ctx_w hd (by decide)).symm

theorem saved_absFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) :
    ∀ r ∈ absFrame st w yo, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.saved_st (by omega)
  · exact L.saved_st (by decide)
  · exact saved_w (by decide) (.inr (by decide))

theorem saved_tFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) :
    ∀ r ∈ tFrame st w yo, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.saved_st (by omega)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by decide) (.inr (by decide))

theorem saved_j0Frame : ∀ r ∈ j0Frame st w, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 80) (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by decide) (.inr (by decide))

end

end VG.Proof.AesGcm.PPC64LE
