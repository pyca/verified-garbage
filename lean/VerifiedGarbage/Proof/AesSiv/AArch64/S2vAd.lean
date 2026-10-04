import VerifiedGarbage.Proof.AesSiv.AArch64.CmacOf

/-!
# AES-SIV on AArch64: a step of S2V over the associated data

After the CMAC of a component into the working space (`cmacOf_wp`), the code
doubles `D` (at `W + 2560`) in place and XORs the CMAC into it, so `D` is
then `dbl(D) ⊕ CMAC(S)` (`Spec.Siv.s2vStep`); then it moves to the next
descriptor and counts one fewer left (`adStep_wp`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Proof.CmacAes.AArch64 (k0 dblMem dbl_ok dblMem_bytes dblMem_frame xor2_ok)

variable {D W : Addr}

/-- `adStep`: `dbl(D)` in place with the CMAC state XORed into it, then the
descriptor pointer advanced by 16 and the count decremented. -/
theorem adStep_wp {s : State} (h19 : s.gpr .x19 = W) (hD : D = W + BitVec.ofNat 64 dOff)
    (hDw : (⟨D, 16⟩ : Region) ∈ s.wr) (hWw : (⟨W, 2560⟩ : Region) ∈ s.wr)
    (hDW : (⟨D, 16⟩ : Region).Disjoint ⟨W, 2560⟩) (wD : D.toNat + 16 ≤ 2 ^ 64) (_wW : W.toNat + 2560 ≤ 2 ^ 64) :
    WP isa (.block adStep) s fun s' =>
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x24 → r ≠ .x25 → s'.gpr r = s.gpr r) ∧
      s'.gpr .x24 = s.gpr .x24 + BitVec.ofNat 64 16 ∧ s'.gpr .x25 = s.gpr .x25 - BitVec.ofNat 64 1 ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Spec.Aes.bytesAt s'.mem D 16 =
        Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16))
          (Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 128) 16) ∧
      Frame [⟨D, 16⟩] s.mem s'.mem := by
  subst hD
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (W + BitVec.ofNat 64 dOff + BitVec.ofNat 64 d) 8 :=
    ⟨_, hDw, Offset.contains_base _ hd (by omega)⟩
  have inD' (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (W + BitVec.ofNat 64 (dOff + d)) 8 := by
    rw [← Offset.add_add]; exact inD d hd
  have inW (d : Nat) (hd : d + 8 ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) 8 :=
    ⟨_, hWw, Offset.contains_base W hd (by omega)⟩
  have rr {a : Addr} (h : InRegions s.wr a 8) : InRegions (s.rd ++ s.wr) a 8 :=
    let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩
  rw [adStep, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := dbl_ok s h19 (src := dOff) (dst := dOff) (by decide) (by decide)
    (rr (inD' 0 (by decide))) (rr (inD' 8 (by decide))) (inD' 0 (by decide)) (inD' 8 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have h19₁ : s₁.gpr .x19 = W := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h19]
  obtain ⟨s₂, run₂, m₂, g₂, sp₂, rd₂, wr₂⟩ := xor2_ok s₁ .x19 .x19 .x19 dOff stOff dOff
    (P := W + BitVec.ofNat 64 dOff) (Q := W + BitVec.ofNat 64 stOff) (C := W + BitVec.ofNat 64 dOff)
    (by decide) (by decide) (by decide) (by rw [h19₁]) (by rw [h19₁, Offset.add_add])
    (by rw [h19₁]) (by rw [h19₁, Offset.add_add]) (by rw [h19₁]) (by rw [h19₁, Offset.add_add])
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [rd₁, wr₁]; exact rr (inD' 0 (by decide))) (by rw [rd₁, wr₁, Offset.add_add]; exact rr (inD' 8 (by decide)))
    (by rw [rd₁, wr₁]; exact rr (inW 128 (by decide)))
    (by rw [rd₁, wr₁, Offset.add_add]; exact rr (inW 136 (by decide)))
    (by rw [wr₁]; exact inD' 0 (by decide)) (by rw [wr₁, Offset.add_add]; exact inD' 8 (by decide))
  refine WP.of_runBlock ⟨s₂, by rw [← xor2_eq] at run₂; exact run₂, ?_⟩
  refine WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  have dW {d n : Nat} (hd : d + n ≤ 2560) (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 dOff, 16⟩ : Region)]) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact hDW.symm.sub_left (Offset.sub_base W hd)
  refine ⟨fun r a b c d e f => by
      simp only [gpr_write, e, f, ite_false]
      rw [g₂ r a b, g₁ r a b c d], by simp [gpr_write, g₂ .x24 (by decide) (by decide),
      g₁ .x24 (by decide) (by decide) (by decide) (by decide)],
    by simp [gpr_write, g₂ .x25 (by decide) (by decide), g₁ .x25 (by decide) (by decide) (by decide) (by decide)],
    by simp only [sp_write, sp₂, sp₁], by simp only [rd_write, rd₂, rd₁], by simp only [wr_write, wr₂, wr₁], ?_, ?_⟩
  · have s₁ : (⟨W + BitVec.ofNat 64 dOff, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 dOff + BitVec.ofNat 64 8, 8⟩ := by
      rw [Offset.add_add]
      exact Offset.disjoint W (d := dOff) (n := 8) (e := dOff + 8) (k := 8) (by decide) (by decide) (by decide)
    have s₂ : (⟨W + BitVec.ofNat 64 dOff, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 136, 8⟩ :=
      (dW (d := 136) (n := 8) (by decide) _ (List.mem_singleton_self _)).symm.sub_left
      (Region.sub_prefix (by decide))
    simp only [mem_write]
    rw [m₂, Proof.Cmac.xor2Mem_bytes _ s₁ (by rw [Offset.add_add]; exact s₂),
      m₁, dblMem_bytes, Proof.Cmac.bytesAt_frame (dblMem_frame _ _ _ _) (dW (d := stOff) (n := 16) (by decide))
        (by decide), Spec.Siv.dbl, Siv.xor_eq]
    all_goals rfl
  · simp only [mem_write]
    rw [m₂]
    exact (m₁ ▸ dblMem_frame s.mem W dOff dOff).trans (Proof.Cmac.xor2Mem_frame _ _ _ _)

end VG.Proof.AesSiv.AArch64
