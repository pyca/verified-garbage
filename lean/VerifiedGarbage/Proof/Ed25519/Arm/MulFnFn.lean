import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFinal
import VerifiedGarbage.Proof.Framework.Arm.Spill

/-!
# `vg_gf25519_r16_mul` on ARMv7: the function

Untrusted: everything here is checked by Lean. `mulFn_ok`: `mulBody_ok`
between saving the callee-saved registers the body changes (`r4`–`r11`) at
`SAVE` and restoring them (`Spill`): the function changes no register but
`r1`–`r3` and no memory but the result's and its own working space (`ACC`
and `SAVE`).
-/

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.X25519 (P)

theorem SAVE_eq : SAVE = 1600 := rfl

theorem mulSaved_ok : Spill.Slots SAVE (SAVE + 32) mulSaved := by decide

theorem mulSaved_restorable : Spill.Restorable .r0 mulSaved := by decide

/-- The registers `vg_gf25519_r16_mul` changes. -/
abbrev mulFnClob : List Reg := [.r1, .r2, .r3]

theorem mulClob_split : ∀ r, r ∉ mulFnClob → r ∉ mulSaved.map Prod.fst → r ∉ mulClob := by
  intro r; cases r <;> decide

/-- **`vg_gf25519_r16_mul`**: the product of `[x]` and `[y]` into `[o]`, the offsets in
`r1`–`r3`, saving and restoring the registers its body changes. -/
theorem mulFn_ok {e : Nat} {b : BitVec 32} {o x y : Nat} (ho : o + 64 ≤ ACC) (hx : x + 64 ≤ ACC)
    (hy : y + 64 ≤ ACC) {s : State} (hc : CtxN e b s) (h1 : s.gpr .r1 = BitVec.ofNat 32 o)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 x) (h3 : s.gpr .r3 = BitVec.ofNat 32 y)
    (hlx : Lim s.mem (State.addr b) x) (hly : Lim s.mem (State.addr b) y) :
    WP isa mulFn s fun t =>
      Rest mulFnClob s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o % P = (V s.mem (State.addr b) x * V s.mem (State.addr b) y) % P := by
  have hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := hc.fit; omega
  have hS := SAVE_eq
  have hA := ACC_eq
  have hB : State.addr (s.gpr .r0) = State.addr b := by rw [hc.r0]
  rw [mulFn, WP.seq_iff]
  rw [← List.append_nil (List.map _ mulSaved)]
  refine Spill.save_slots_ok mulSaved_ok (by rw [hc.r0, hS]; omega)
    (fun d hd hd' => by rw [hB]; exact hc.inW (by rw [hS] at hd'; omega)) (WP.block_nil ?_)
  rw [hB]
  have hf1 : Frame [⟨State.addr b + BitVec.ofNat 64 SAVE, SAVE + 32 - SAVE⟩] s.mem
      (Spill.saveMem s.mem (State.addr b) s.gpr mulSaved) :=
    Spill.saveMem_frame_slots mulSaved_ok s.mem (State.addr b) s.gpr
  have hsv1 : Spill.Saved (Spill.saveMem s.mem (State.addr b) s.gpr mulSaved) (State.addr b) s.gpr
      mulSaved :=
    Spill.saveMem_saved (State.addr b) s.gpr s.mem mulSaved mulSaved_ok
  generalize Spill.saveMem s.mem (State.addr b) s.gpr mulSaved = M1 at hf1 hsv1 ⊢
  have hlimb : ∀ z : Nat, z + 64 ≤ ACC → ∀ k < 16, limb M1 (State.addr b) z k = limb s.mem (State.addr b) z k :=
    fun z hz => limb_frame hf1 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by rw [hS]; omega)) (by omega) (by omega)
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : State, s₁ = { s with mem := M1 } := ⟨_, rfl⟩
  rw [← hs₁]
  have hm₁ : s₁.mem = M1 := by rw [hs₁]
  have hg₁ : s₁.gpr = s.gpr := by rw [hs₁]
  have hc₁ : CtxN e b s₁ := by rw [hs₁]; exact ⟨hc.r0, hc.fit, hc.wr⟩
  have hlx₁ : Lim s₁.mem (State.addr b) x := fun k hk => by rw [hm₁, hlimb x hx k hk]; exact hlx k hk
  have hly₁ : Lim s₁.mem (State.addr b) y := fun k hk => by rw [hm₁, hlimb y hy k hk]; exact hly k hk
  have hV : ∀ z : Nat, z + 64 ≤ ACC → V s₁.mem (State.addr b) z = V s.mem (State.addr b) z :=
    fun z hz => by rw [hm₁]; exact val16_congr (hlimb z hz)
  refine WP.seq (WP.mono (mulBody_ok ho hx hy hc₁ (by rw [hg₁, h1]) (by rw [hg₁, h2])
    (by rw [hg₁, h3]) hlx₁ hly₁) fun t ⟨hrt, hf, hlt, hvt⟩ => ?_)
  rw [hm₁] at hf
  have hct : CtxN e b t := hc₁.of_rest hrt (by decide)
  have hsv : Spill.Saved t.mem (State.addr (t.gpr .r0)) s.gpr mulSaved := by
    rw [hct.r0]
    refine hsv1.frame mulSaved_ok hf fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inr (by rw [hS]; omega)) (by omega) (by omega)
    · exact Offset.disjoint _ (.inr (by rw [hS]; omega)) (by omega) (by omega)
  refine WP.mono (Spill.restore_block_ok mulSaved_ok mulSaved_restorable
    (by rw [hct.r0, hS]; omega) (fun d _ hd' => by rw [hct.r0]; exact hct.inR (by rw [hS] at hd'; omega)) hsv)
    fun u ⟨hres, hoth, hmu, hrd, hwr, hsp⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [hrd, hrt.rd, hs₁], by rw [hwr, hrt.wr, hs₁], by rw [hsp, hrt.sp, hs₁]⟩,
    ?_, by rw [hmu]; exact hlt, ?_⟩
  · by_cases hm : r ∈ mulSaved.map Prod.fst
    · exact Spill.restored_reg hres hm
    · rw [hoth r hm, hrt.gpr r (mulClob_split r hr hm), hg₁]
  · rw [hmu]
    refine (hf1.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩).trans
      (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by rw [hS]; omega) (by rw [hS]; omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · rw [hmu, hvt, hV x hx, hV y hy]

end VG.Proof.Ed25519.Arm
