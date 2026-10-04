import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Finish

/-!
# Argon2 H′ on ARMv7: correctness

`setup_ok` saves the caller's registers in `scratch`, keeps the input, the
output pointer and the bytes left in registers and the length prefix in
`scratch`; `correct` composes it with `first_ok`, `finish_ok` and the
restore of the registers.
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (setup restore first finishOutput saved baseSlot pfxOff)
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_str wp_ldrSp op2_reg)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem arg_in : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 0)) 4 := by
  refine ⟨argR s₀, by simp [hp.rd], ?_⟩
  simp [stackArgAddr, Region.Contains]

theorem scr_w {d : Nat} (hd : d + 4 ≤ 16384) : InRegions s₀.wr (P s₀ + BitVec.ofNat 64 d) 4 :=
  ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ hd (by omega)⟩

/-- The state after `setup`. -/
theorem setup_ok : WP isa (.block setup) s₀ fun t => Body s₀ t ∧ Out s₀ t [] ∧
    Frame [scrR s₀] s₀.mem t.mem := by
  have hs := hp.scr_fits
  unfold setup
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp (by decide) rfl (arg_in hp) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .r12 = scr s₀ := by rw [u₁.gpr]; rfl
  refine Spill.save_slots_ok (b := .r12) saveList_slots (by rw [e₁]; omega)
    (fun d h₁ h₂ => by rw [e₁, u₁.wr]; exact scr_w hp (by omega)) ?_
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  have r4₆ : s₆.gpr .r4 = scr s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    exact e₁
  have w₆ : InRegions s₆.wr (State.addr (scr s₀) + BitVec.ofNat 64 pfxOff) 4 := by
    rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
    exact scr_w hp (by decide)
  refine wp_str (by decide) (by rw [r4₆]; exact scr_addr hp (by decide)) w₆ fun t u => WP.block_nil ?_
  -- Values.
  have g₆ : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → s₆.gpr r = s₁.gpr r := fun r h4 h5 h6 h7 h8 => by
    rw [u₆.other _ h8, u₅.other _ h7, u₄.other _ h6, u₃.other _ h5, u₂.other _ h4]
  have m₆ : s₆.mem = Spill.saveMem s₁.mem (P s₀) s₁.gpr saveList := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, e₁]
  have gl : ∀ p ∈ saveList, s₁.gpr p.1 = s₀.gpr p.1 := fun p hpm => u₁.other _ (by
    simp only [saveList, saved, baseSlot, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hv : (s₆.gpr .r3) = s₀.gpr .r3 := by rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide),
    u₁.other _ (by decide)]
  have mt : t.mem = (Spill.saveMem s₀.mem (P s₀) s₀.gpr saveList).writeW (P s₀ + BitVec.ofNat 64 pfxOff)
      (s₀.gpr .r3) := by
    rw [u.mem, m₆, hv, u₁.mem, Spill.saveMem_congr _ _ _ gl]
  have Ft : Frame [scrR s₀] s₀.mem t.mem := by
    rw [mt]
    exact (Spill.saveMem_frame_of _ _ (List.mem_singleton_self (scrR s₀)) _ _ fun p hpm => by
      have := saveList_slots.bound hpm
      exact Offset.contains_base _ (by omega) (by omega)).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by decide) (by decide))
  have gt : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r12 → t.gpr r = s₀.gpr r :=
    fun r h4 h5 h6 h7 h8 h12 => by rw [u.gpr, g₆ r h4 h5 h6 h7 h8, u₁.other _ h12]
  refine ⟨⟨by rw [u.gpr, r4₆], ?_, ?_, ?_, ?_, ?_, Ft.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩,
      fun q hq => ?_, ?_⟩, ⟨?_, ?_, rfl, Nat.zero_le _⟩, Ft⟩
  · rw [u.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · have hb := saveList_slots.bound hq
    rw [mt, Mem.readW_writeW_sep (Offset.sep _ (by simp only [pfxOff]; omega) (by omega) (by decide)) (by decide)]
    exact Spill.saveMem_saved _ _ _ _ saveList_slots q hq
  · rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (.inl rfl), mt,
      show P s₀ + 832 = P s₀ + BitVec.ofNat 64 pfxOff from rfl, Mem.readW_writeW_self32, Spec.Argon2.le32,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [u.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]; simp
  · rw [u.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]; simp [ol]

theorem correct : WP isa Impl.Argon2.Arm.HPrime.code s₀ fun t =>
    (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧ t.sp = s₀.sp ∧ hPrimeArm.post s₀ t := by
  have hif := hp.in_fits
  have hs := hp.scr_fits
  unfold Impl.Argon2.Arm.HPrime.code
  refine WP.seq ((setup_ok hp).mono fun s₁ ⟨b₁, o₁, F₁⟩ => ?_)
  have hin : bytesAt s₁.mem (State.addr (inp s₀)) (inl s₀) = bytesAt s₀.mem (State.addr (inp s₀)) (inl s₀) :=
    Proof.Blake2.bytesAt_congr fun i hi => F₁.bytes (R := inR s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega) hi
  refine WP.seq ((first_ok hp ⟨b₁, o₁, hin⟩).mono fun s₂ ⟨⟨b₂, o₂, _⟩, d₂⟩ => ?_)
  refine WP.seq ((finish_ok hp b₂ o₂ d₂).mono fun s₃ ⟨b₃, _, h₃⟩ => ?_)
  unfold restore
  rw [← List.append_nil (List.map _ _)]
  have sv : Spill.Saved s₃.mem (State.addr (s₃.gpr .r4)) s₀.gpr (saved ++ [(.r4, baseSlot)]) := by
    rw [b₃.r4]
    intro p hpm
    exact b₃.saved p (by
      simp only [List.mem_append, List.mem_singleton] at hpm
      rcases hpm with hpm | rfl
      · exact List.mem_cons_of_mem _ hpm
      · exact List.mem_cons_self)
  refine Spill.restoreBase_slots_ok (lo := 840) (hi := 876) (by decide) (by decide) (g := s₀.gpr)
    (by rw [b₃.r4]; omega)
    (fun d h₁ h₂ => by rw [b₃.r4, b₃.rd, b₃.wr]; exact VG.Proof.Sha512.Arm.mem_rd (scr_w hp (by omega))) sv
    fun t ht ho hm hrd hwr hsp => WP.block_nil ⟨fun r hr => ?_, hsp.trans b₃.sp, ?_⟩
  · exact Spill.restored_of ht (by decide) r hr
  · show bytesAt t.mem _ _ = _
    rw [hm]; exact h₃

end

end VG.Proof.Argon2.Arm.HPrime
