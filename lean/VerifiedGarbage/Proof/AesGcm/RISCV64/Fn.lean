module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
public import VerifiedGarbage.Proof.AesGcm.RISCV64.J0
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISCV64: the functions' entry and exit

Untrusted: everything here is checked by Lean. Every function saves our
caller's `s0`–`s11` and its return address `ra` in `W` on entry (`save_ok`,
`Spill.save_ok`) and restores them on exit (`restore_ok`), which gives
`abiPreserved`. Also here: the layout from the disjointness of
the buffers (`Lay.of`), and that the pieces never write the saved slots.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)

/-- Where `save` puts our caller's registers and return address. -/
def SavedAt (m : Mem) (w : Addr) (s₀ : State) : Prop :=
  Spill.Saved w s₀.gpr saved m

/-- The saved registers' and return address's slots. -/
abbrev savedR (w : Addr) : Region := ⟨w + BitVec.ofNat 64 128, 104⟩

theorem saved_bound : ∀ p ∈ saved, 128 ≤ p.2 ∧ p.2 + 8 ≤ 232 := by decide

theorem saved_fits : Spill.Fits saved := by decide

theorem saved_ok : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem save_eq (b : Reg) : save b = Spill.saveCode b saved ++ ([mov .s0 b] : List Instr) := rfl

theorem restore_eq : restore = ([mov .t1 .s0] : List Instr) ++ Spill.restoreCode .t1 saved := rfl

/-- Saving the registers and the return address in `W`, at `b`. -/
theorem save_ok {s : State} {b : Reg} (hw : Covers [⟨s.gpr b, 2560⟩] s.wr) (hal : (s.gpr b).toNat % 8 = 0) :
    WP isa (.block (save b)) s fun s' =>
      (∀ r, r ≠ .s0 → s'.gpr r = s.gpr r) ∧ s'.gpr .s0 = s.gpr b ∧
      Keeps' s s' ∧ SavedAt s'.mem (s.gpr b) s ∧ Frame [savedR (s.gpr b)] s.mem s'.mem := by
  rw [save_eq]
  refine Spill.save_ok hal saved_ok
    (fun p hp => in_off hw (by have := saved_bound p hp; omega) (by decide)) ?_
  refine Steps.wp_mv fun s' u => WP.block_nil ?_
  refine ⟨fun r hr => u.other r hr, u.gpr, ⟨u.rd, u.wr, u.sp⟩, ?_, ?_⟩
  · rw [SavedAt, u.mem]
    exact Spill.saveMem_saved saved_fits s.mem (s.gpr b) s.gpr
  · rw [u.mem]
    exact Spill.saveMem_frame (lo := 128) (n := 104) (fun p hp => by have := saved_bound p hp; omega)
      (by decide) _ _ _

/-- The saved slots stay as they are, outside a frame. -/
theorem SavedAt.frame {m m' : Mem} {w : Addr} {s₀ : State} (h : SavedAt m w s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savedR w).Disjoint r) : SavedAt m' w s₀ :=
  Spill.Saved.frame h hf fun p hp r hr => (hd r hr).sub_left (by
    have := saved_bound p hp
    exact Offset.sub _ (by omega) (by omega))

/-- The end of every function: our caller's registers and return address
restored, from `W` in `s0`. -/
theorem restore_ok {s s₀ : State} {w : Addr} (h31 : s.gpr .s0 = w) (hal : w.toNat % 8 = 0)
    (hr : Covers [⟨w, 2560⟩] (s.rd ++ s.wr)) (hs : SavedAt s.mem w s₀) (hsp : s.sp = s₀.sp) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧
      s'.gpr .a0 = s.gpr .a0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [restore_eq]
  refine Steps.wp_mv fun s₁ u₁ => ?_
  refine WP.mono (Spill.restore_wp hal (by rw [u₁.gpr, h31]) saved_ok (by decide) (fun p hp => by
      rw [u₁.rd, u₁.wr]; exact in_off hr (by have := saved_bound p hp; omega) (by decide))
    (u₁.mem ▸ hs)) fun s' h => ?_
  refine ⟨⟨fun r hr => h.gpr_of (.inl (by revert hr; revert r; decide)), by rw [h.sp, u₁.sp, hsp],
    h.gpr_of (.inl (by decide))⟩, by rw [h.mem, u₁.mem], ?_, by rw [h.rd, u₁.rd], by rw [h.wr, u₁.wr]⟩
  rw [h.other _ (by decide), u₁.other _ (by decide)]

/-- The layout, from the disjointness of the context, the state and `W`. -/
theorem Lay.of {c st w : Addr} (cw : c.toNat + 256 ≤ 2 ^ 64) (sw : st.toNat + 80 ≤ 2 ^ 64)
    (ww : w.toNat + 2560 ≤ 2 ^ 64) (cs : (⟨c, 256⟩ : Region).Disjoint ⟨st, 80⟩)
    (cW : (⟨c, 256⟩ : Region).Disjoint ⟨w, 2560⟩) (sW : (⟨st, 80⟩ : Region).Disjoint ⟨w, 2560⟩)
    (ca : c.toNat % 8 = 0) (sal : st.toNat % 8 = 0) (wal : w.toNat % 8 = 0) :
    Lay c st w :=
  ⟨cw, sw, ww, cs, cW, sW.sub_right (Region.sub_prefix (by decide)),
    sW.sub_right (Offset.sub_base _ (by decide)), ca, sal, wal⟩

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
theorem saved_w {d k : Nat} (hd : d + k ≤ 2560) (ho : d + k ≤ 128 ∨ 232 ≤ d) :
    (savedR w).Disjoint ⟨w + BitVec.ofNat 64 d, k⟩ :=
  Lay.w_w (by omega) (by decide) hd

omit L in
theorem saved_below {sp : Addr} (hk : StkOk c st w sp) : (savedR w).Disjoint (below sp 2048) :=
  hk.w.sub_left (Lay.wSub (by decide))

theorem Lay.saved_st {d k : Nat} (hd : d + k ≤ 80) : (savedR w).Disjoint ⟨st + BitVec.ofNat 64 d, k⟩ :=
  (L.st_w hd (.inr ⟨by decide, by decide⟩)).symm

theorem Lay.saved_ctx {d k : Nat} (hd : d + k ≤ 256) : (savedR w).Disjoint ⟨c + BitVec.ofNat 64 d, k⟩ :=
  (L.ctx_w hd (by decide)).symm

theorem saved_absFrame {yo : Nat} {sp : Addr} (hyo : yo = 0 ∨ yo = 16) (hk : StkOk c st w sp) :
    ∀ r ∈ absFrame st w yo sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.saved_st (by omega)
  · exact L.saved_st (by decide)
  · exact saved_w (by decide) (.inr (by decide))
  · exact saved_below hk

theorem saved_tFrame {yo : Nat} {sp : Addr} (hyo : yo = 0 ∨ yo = 16) (hk : StkOk c st w sp) :
    ∀ r ∈ tFrame st w yo sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.saved_st (by omega)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by decide) (.inr (by decide))
  · exact saved_below hk

theorem saved_j0Frame {sp : Addr} (hk : StkOk c st w sp) : ∀ r ∈ j0Frame st w sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.saved_st (d := 0) (k := 80) (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by decide) (.inr (by decide))
  · exact saved_below hk

end

end VG.Proof.AesGcm.RISCV64
