import VerifiedGarbage.Proof.AesOcb.Arm.Pass

/-!
# AES-OCB on ARMv7: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs the
first pass (each block XORed with its offset, `pre`), `f` on all the blocks
(`ENCIPHER` or `DECIPHER`), and the second pass from `Offset_0` again
(`post`), each pass also updating the checksum (`whole_ok`): block `k`
becomes `Offset_{k+1} ⊕ g(X_k ⊕ Offset_{k+1})`, as on AArch64
(`Proof.AesOcb.AArch64.whole_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.Arm (below)

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, the
working space of the functions called, the data and the stack below `SP`. -/
abbrev wholeR (p : Prm) (m : Nat) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 16, 32⟩, ⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 512, 2048⟩, ⟨State.addr p.D, 16 * m⟩, below p.SP]

theorem wholeR_mut {p : Prm} (L : Lay p) {m : Nat} (hm : 16 * m ≤ p.n) {M M' : Mem} (h : Frame (wholeR p m) M M') :
    Frame (mutR p) M M' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact w_mut L (.inl (by decide))
  · exact w_mut L (.inl (by decide))
  · exact w_mut L (.inr ⟨by decide, by decide⟩)
  · simpa using data_mut L (a := 0) (l := 16 * m) (by omega)
  · exact below_mut L

/-- The registers `whole` writes. -/
abbrev wholeRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r12, .lr]

/-- What `whole` leaves. -/
structure WholePost (p : Prm) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame (wholeR p m) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ck
  gpr : Others wholeRegs t t'

/-- The start of a pass: `r4 ← D`, `r5 ← m`, `r6 ← 1`. -/
theorem passStart_run {p : Prm} {t : State} (h8 : t.gpr .r8 = p.D) {m : Nat} (h7 : t.gpr .r7 = BitVec.ofNat 32 m) :
    ∃ t', runBlock isa passStart t = some t' ∧
      t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * 0) ∧ t'.gpr .r5 = BitVec.ofNat 32 (m - 0) ∧
      t'.gpr .r6 = BitVec.ofNat 32 (0 + 1) ∧ Ran [.r4, .r5, .r6] t.mem t t' := by
  refine ⟨_, by orun [passStart], ?_, ?_, ?_, by rfl, by others_tac, by rfl, by rfl, by rfl⟩
  · simp [gpr_setReg, h8]
  · simp [gpr_setReg, h7]
  · simp [gpr_setReg]

theorem passR_mut {p : Prm} (L : Lay p) {m : Nat} (hm : 16 * m ≤ p.n) {M M' : Mem} (h : Frame (passR p m) M M') :
    Frame (mutR p) M M' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact w_mut L (.inl (by decide))
  · exact w_mut L (.inl (by decide))
  · exact w_mut L (.inl (by decide))
  · simpa using data_mut L (a := 0) (l := 16 * m) (by omega)

theorem whole_ok (F : BlkFn) {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block}
    {ckF1 ckF2 : Nat → Block} {p : Prm} (L : Lay p)
    (hB1 : BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk p post (fun b o => b ^^^ o) fC2)
    {t : State} (E : Env p t) {m : Nat} (hmn : 16 * m ≤ p.n) (hm0 : 0 < m) {O0 l : Block}
    (h8 : t.gpr .r8 = p.D) (h7 : t.gpr .r7 = BitVec.ofNat 32 m)
    (hofs : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) =
      fC1 (ckF1 i) (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 m)
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (F.ciph p.R (sched p t.mem) (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (whole (blkFrame F) pre post) t (WholePost p m O0 l
      (fun k => F.ciph p.R (sched p t.mem)
        (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 m) t) := by
  have fw := L.ww
  have fd := L.dw
  have n32 := L.n_lt
  -- the first pass
  obtain ⟨s₁, run₁, r4₁, r5₁, r6₁, R₁⟩ := passStart_run h8 h7
  have E₁ : Env p s₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have P₀ : PassInv p m O0 l (fun k => blockAtMem s₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, r4 := r4₁, r6 := r6₁, r5 := r5₁
      ofs := by rw [R₁.mem, hofs]; rfl
      ck := by rw [R₁.mem, hck]
      blk := fun k _ => by simp
      l0 := by rw [R₁.mem, hl0]
      gpr := fun _ _ => rfl }
  unfold whole
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (pass_ok L hB1 (fun i _ => by rw [hckF1, R₁.mem]) hmn hm0 P₀) fun s₂ P₂ => ?_)
  have E₂ := P₂.env
  have r8₂ : s₂.gpr .r8 = p.D := by rw [P₂.gpr _ (by decide), R₁.gpr _ (by decide), h8]
  have r7₂ : s₂.gpr .r7 = BitVec.ofNat 32 m := by rw [P₂.gpr _ (by decide), R₁.gpr _ (by decide), h7]
  -- the call
  refine WP.seq (WP.of_runBlock ⟨_, by orun [callArgs, E₂.r9, E₂.r10, E₂.r11, r8₂, r7₂], ?_⟩)
  have hB := blkFrame_ok F L (t := ((((((s₂.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12
    (p.W + BitVec.ofNat 32 scrO)).setReg .r2 p.D).setReg .r3 (BitVec.ofNat 32 m))))
    (D := p.D) (n := m) (E₂.of_others (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac)
      (by rfl) (by rfl) (by rfl)) (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by omega)
      (Proof.AesGcm.Arm.covers_prefix E₂.perm.d hmn) (L.k_d.sub_right (Region.sub_prefix hmn))
      ((L.d_w' (d := scrO) (k := 2048) (by decide)).sub_left (Region.sub_prefix hmn))
      (L.bd.sub_right (Region.sub_prefix hmn))
  refine WP.seq (WP.mono hB fun s₃ C₃ => ?_)
  have g₃ : ∀ r ∈ keptRegs, s₃.gpr r = s₂.gpr r := fun r hr => by
    rw [C₃.saved r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  have E₃ : Env p s₃ := E₂.keep (fun r hr => g₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))
    (by rw [C₃.sp]; rfl) (by rw [C₃.rd]; rfl) (by rw [C₃.wr]; rfl)
  have kC : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.D, 16 * m⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩ →
      (⟨Q, 16⟩ : Region).Disjoint (below p.SP) → blockAtMem s₃.mem Q = blockAtMem s₂.mem Q :=
    fun h₁ h₂ h₃ => blockAtMem_frame C₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h₁, h₂, h₃]
  have dW : ∀ {d : Nat}, d + 16 ≤ 512 → (⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint
      ⟨State.addr p.D, 16 * m⟩ := fun hd =>
    ((L.d_w' (k := 16) (by omega)).sub_left (Region.sub_prefix hmn)).symm
  have kWP : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 512)) →
      blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd => by
      rw [kC (dW (by omega)) (L.w_w (.inl (by simp only [scrO]; omega)) (by omega) (by decide))
          (L.bw' (by omega)).symm,
        blockAtMem_frame P₂.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact L.w_w (a := _) (d := 96) (k := 16) (by omega) (by omega) (by decide)
          · exact L.w_w (a := _) (d := 16) (k := 16) (by omega) (by omega) (by decide)
          · exact L.w_w (a := _) (d := 32) (k := 16) (by omega) (by omega) (by decide)
          · exact dW (by omega))]
  have o0₃ : blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0 := by
    rw [kWP (by decide), R₁.mem, ho0]
  -- `Offset_0` again
  refine WP.seq (WP.block_append (WP.mono (copy16_wp (t := s₃) (W := State.addr p.W) (sO := o0O) (dO := ofsO)
    (by rw [E₃.r11]) (by decide) (by decide) (by rw [E₃.r11]; omega) (by decide) (by decide)
    (E₃.perm.wCR (by decide)) (E₃.perm.wC (by decide))) fun s₄a R₄ => ?_))
  have E₄a : Env p s₄a := E₃.of_others R₄.gpr R₄.sp R₄.rd R₄.wr
  have r8₄ : s₄a.gpr .r8 = p.D := by rw [R₄.gpr _ (by decide), g₃ _ (by decide), r8₂]
  have r7₄ : s₄a.gpr .r7 = BitVec.ofNat 32 m := by rw [R₄.gpr _ (by decide), g₃ _ (by decide), r7₂]
  obtain ⟨s₄, run₄, r4₄, r5₄, r6₄, R₄'⟩ := passStart_run r8₄ r7₄
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have E₄ : Env p s₄ := E₄a.of_others R₄'.gpr R₄'.sp R₄'.rd R₄'.wr
  have m₄ : s₄.mem = copyMem s₃.mem (State.addr p.W + BitVec.ofNat 64 o0O) (State.addr p.W + BitVec.ofNat 64 ofsO) := by
    rw [R₄'.mem, R₄.mem]
  have kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ →
      blockAtMem s₄.mem Q = blockAtMem s₃.mem Q := fun hQ => by
    rw [m₄]; exact blockAtMem_frame (copyMem_frame _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hQ
  have hsched : sched p s₂.mem = sched p t.mem := by
    rw [sched_mut L (passR_mut L hmn P₂.frame), R₁.mem]
  have X₄ : ∀ k < m, blockAtMem s₄.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) =
      F.ciph p.R (sched p t.mem)
        (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) := fun k hk => by
    rw [kB₄ (bO L (by omega)), C₃.out k hk]
    simp only [mem_setReg]
    rw [hsched, P₂.blk k hk]
    simp only [hk, ↓reduceIte, R₁.mem]
  have ck₃ : blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [kC (dW (by decide)) (L.w_w (.inl (by decide)) (by decide) (by decide)) (L.bw' (by decide)).symm,
      P₂.ck, hckF2₀]
  have P₀' : PassInv p m O0 l (fun k => blockAtMem s₄.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF2 s₄ s₄ 0 :=
    { env := E₄, frame := Frame.refl _ _, rd := rfl, wr := rfl, r4 := r4₄, r6 := r6₄, r5 := r5₄
      ofs := by rw [m₄, blockAtMem_copy, o0₃]; rfl
      ck := by rw [kB₄ (L.w_w (.inr (by decide)) (by decide) (by decide)), ck₃]
      blk := fun k _ => by simp
      l0 := by rw [kB₄ (L.w_w (.inr (by decide)) (by decide) (by decide)), kWP (by decide), R₁.mem, hl0]
      gpr := fun _ _ => rfl }
  refine WP.mono (pass_ok L hB2 (fun i hi => by rw [hckF2, X₄ i hi]) hmn hm0 P₀') fun s₅ P₅ => ?_
  have subW : ∀ r ∈ passR p m, ∃ r' ∈ wholeR p m, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨⟨State.addr p.D, 16 * m⟩, by simp, fun _ h => h⟩
  refine ⟨P₅.env, ?_, by rw [P₅.rd, R₄'.rd, R₄.rd, C₃.rd]; simp only [rd_setReg]; rw [P₂.rd, R₁.rd],
    by rw [P₅.wr, R₄'.wr, R₄.wr, C₃.wr]; simp only [wr_setReg]; rw [P₂.wr, R₁.wr], fun k hk => ?_, P₅.ofs, P₅.ck, fun r hr => ?_⟩
  · rw [← R₁.mem]
    refine (P₂.frame.sub subW).trans ((C₃.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨State.addr p.D, 16 * m⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp [scrO], fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · have F₅ := P₅.frame
      rw [m₄] at F₅
      exact ((copyMem_frame _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide)
          (by decide)⟩).trans (F₅.sub subW)
  · rw [P₅.blk k hk]
    simp only [hk, ↓reduceIte]
    rw [X₄ k hk]
  · simp only [wholeRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    have hk : r ∈ keptRegs := by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false]
      cases r <;> simp_all
    rw [P₅.gpr r (by simp [passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      R₄'.gpr r (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      R₄.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), g₃ r hk,
      P₂.gpr r (by simp [passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      R₁.gpr r (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1])]

end VG.Proof.AesOcb.Arm
