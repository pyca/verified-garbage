import VerifiedGarbage.Proof.AesOcb.Arm.HashChunk
import VerifiedGarbage.Proof.AesOcb.Arm.PadTo

/-!
# AES-OCB on ARMv7: `HASH` (`hash`)

Untrusted: everything here is checked by Lean. `hash` zeroes the sum and the
offset, takes the whole blocks of the associated data in chunks
(`hashChunk_ok`), then the rest, padded, XORed with the offset `⊕ L_*`,
enciphered and added to the sum (`hashRest`): `HASH(K, A)` at `W + sumO`
(`hash_ok`, `Proof.Ocb.hash_eq`), as on AArch64
(`Proof.AesOcb.AArch64.hash_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz pad)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.AesGcm.Arm (eval_eq' eval_ne' z_subFlags z_cmp0 and15 mem_store gpr_store rd_store wr_store
  sp_store)

/-- What `hash` leaves, from `t`. -/
structure HashOut (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame (hashR p) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sum : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ciphOf p t.mem) (lstarOf p t.mem) (aadOf p t.mem)

/-- The whole blocks of the associated data. -/
theorem hashWhole_ok {p : Prm} (L : Lay p) {t₀ t : State} (H : HInv p t₀ t 0)
    (hz : t.z = decide (p.al / 16 = 0)) :
    WP isa (.ite .eq (.block []) (.loop hashChunk .ne)) t fun t' => HInv p t₀ t' (p.al / 16) := by
  refine WP.ite (decide (p.al / 16 = 0)) (eval_eq' hz) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : p.al / 16 = 0 := of_decide_eq_true hb
    rw [h0]; exact H
  · have hm : p.al / 16 ≠ 0 := by simpa using hb
    refine WP.loop (M := isa) (fun k t' => ∃ j, k = p.al / 16 - j ∧ j < p.al / 16 ∧ HInv p t₀ t' j) ?_
      (p.al / 16 - 0) t ⟨0, rfl, by omega, H⟩
    rintro k t' ⟨j, rfl, hj, Hj⟩
    refine WP.mono (hashChunk_ok L Hj hj) fun t'' ⟨H', z⟩ => ?_
    by_cases h : p.al / 16 - (j + min 16 (p.al / 16 - j)) = 0
    · left
      refine ⟨(eval_ne' z).trans (by simp [h]), ?_⟩
      have e : j + min 16 (p.al / 16 - j) = p.al / 16 := by omega
      rw [e] at H'; exact H'
    · right
      exact ⟨(eval_ne' z).trans (by simp [h]), p.al / 16 - (j + min 16 (p.al / 16 - j)), by omega,
        j + min 16 (p.al / 16 - j), rfl, by omega, H'⟩

/-- The rest of the associated data, `n` bytes after the `m` whole blocks. -/
theorem hashRest_ok {p : Prm} (L : Lay p) {t₀ t : State} (H : HInv p t₀ t (p.al / 16))
    (h5 : t.gpr .r5 = BitVec.ofNat 32 (p.al % 16)) (hn : p.al % 16 ≠ 0) :
    WP isa hashRest t fun t' => Env p t' ∧ Frame (hashR p) t₀.mem t'.mem ∧ t'.rd = t₀.rd ∧ t'.wr = t₀.wr ∧
      blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
        hsum (ciphOf p t₀.mem) (lstarOf p t₀.mem) (aadOf p t₀.mem) (p.al / 16) ^^^
          ciphOf p t₀.mem (pad ((aadOf p t₀.mem).drop (16 * (p.al / 16))) ^^^
            (offAt 0 (lstarOf p t₀.mem) (p.al / 16) ^^^ lstarOf p t₀.mem)) := by
  have fw := L.ww
  have fk := L.kw
  have al32 := L.al_lt
  have E := H.env
  have eK : State.addr (p.K + BitVec.ofNat 32 0) = State.addr p.K := by rw [BitVec.add_zero]
  unfold hashRest
  -- the offset `⊕ L_*`
  refine WP.seq (WP.mono (xorB_wp (s := t) (pb := .r11) (qb := .r10) (cb := .r11) (pd := ohO) (qd := 240)
    (cd := ohO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [E.r11]; simp only [ohO]; omega) (by rw [E.r10]; omega)
    (by rw [E.r11]; simp only [ohO]; omega) (by rw [E.r11]; exact E.perm.wCR (by decide))
    (by rw [E.r10]; exact E.perm.kC (by decide)) (by rw [E.r11]; exact E.perm.wC (by decide))) fun t₁ R₁ => ?_)
  rw [E.r11, E.r10] at R₁
  have E₁ : Env p t₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have fr₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have lK : blockAtMem t.mem (State.addr p.K + BitVec.ofNat 64 240) = lstarOf p t₀.mem := by
    show Spec.Ocb.ctxLstar t.mem (State.addr p.K) = _
    exact lstar_mut L (hashR_mut L H.frame)
  have oh₁ : blockAtMem t₁.mem (State.addr p.W + BitVec.ofNat 64 ohO) =
      offAt 0 (lstarOf p t₀.mem) (p.al / 16) ^^^ lstarOf p t₀.mem := by
    rw [R₁.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint
      ((L.k_w' (d := ohO) (k := 16) (by decide)).symm.sub_right (Offset.sub_base _ (by decide)))), H.oh, lK]
  -- `pad(A_*)` at `W + bufO`
  have hm : 16 * (p.al / 16) + p.al % 16 = p.al := by omega
  have eA : State.addr (p.A + BitVec.ofNat 32 (16 * (p.al / 16))) =
      State.addr p.A + BitVec.ofNat 64 (16 * (p.al / 16)) := addr_add (by have := L.aw; omega)
  have hSA : (⟨State.addr p.A + BitVec.ofNat 64 (16 * (p.al / 16)), p.al % 16⟩ : Region).Sub ⟨State.addr p.A, p.al⟩ :=
    Offset.sub_base _ (by omega)
  refine WP.seq (WP.mono (padTo_ok L E₁ (S := p.A + BitVec.ofNat 32 (16 * (p.al / 16))) (n := p.al % 16)
    (d := bufO) (by omega) (by omega) (by decide) (by decide) (by rw [R₁.gpr _ (by decide), H.r4])
    (by rw [R₁.gpr _ (by decide), h5])
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (p.al / 16)) (by omega),
      Nat.mod_eq_of_lt (by have := L.aw; omega)]; have := L.aw; omega)
    (by rw [eA]; exact Proof.AesGcm.Arm.covers_off E₁.perm.aad (by omega) (by omega))
    (by rw [eA]; exact (L.a_w' (by decide)).sub_left hSA)) fun t₂ ⟨fr₂, pad₂, g₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : Env p t₂ := E₁.of_others g₂ sp₂ rd₂ wr₂
  have hrest : bytesAt t₁.mem (State.addr (p.A + BitVec.ofNat 32 (16 * (p.al / 16)))) (p.al % 16) =
      (aadOf p t₀.mem).drop (16 * (p.al / 16)) := by
    rw [eA, Proof.Ocb.bytesAt_drop _ _ (by omega), show p.al - 16 * (p.al / 16) = p.al % 16 by omega]
    rw [R₁.mem]
    exact Proof.Cmac.bytesAt_frame ((hashR_mut L H.frame).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).sub
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact w_mut L (.inr ⟨by decide, by decide⟩)))
      (fun r hr => (disj_mut L L.a_w L.ba L.a_d r hr).sub_left hSA) (by omega)
  rw [hrest] at pad₂
  have oh₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 ohO) =
      offAt 0 (lstarOf p t₀.mem) (p.al / 16) ^^^ lstarOf p t₀.mem := by
    rw [blockAtMem_frame fr₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)), oh₁]
  -- the XOR with the offset
  refine WP.seq (WP.mono (xorB_wp (s := t₂) (pb := .r11) (qb := .r11) (cb := .r11) (pd := bufO) (qd := ohO)
    (cd := bufO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [E₂.r11]; simp only [bufO]; omega) (by rw [E₂.r11]; simp only [ohO]; omega)
    (by rw [E₂.r11]; simp only [bufO]; omega) (by rw [E₂.r11]; exact E₂.perm.wCR (by decide))
    (by rw [E₂.r11]; exact E₂.perm.wCR (by decide)) (by rw [E₂.r11]; exact E₂.perm.wC (by decide))) fun t₃ R₃ => ?_)
  rw [E₂.r11] at R₃
  have E₃ : Env p t₃ := E₂.of_others R₃.gpr R₃.sp R₃.rd R₃.wr
  have fr₃' : Frame [⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 bufO, 16⟩]
      t.mem t₃.mem := ((fr₁.mono (by simp)).trans (fr₂.mono (by simp))).trans
        ((by rw [R₃.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _ : Frame [⟨State.addr p.W + BitVec.ofNat 64 bufO, 16⟩]
          t₂.mem t₃.mem).mono (by simp))
  have fr₃ : Frame (hashR p) t₀.mem t₃.mem := H.frame.trans (fr₃'.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact w_hash (b := 192) (k := 24) (by simp) ⟨by decide, by decide⟩ (by decide)
    · exact w_hash (b := 256) (k := 2304) (by simp) ⟨by decide, by decide⟩ (by decide))
  have b₃ : blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 bufO) =
      pad ((aadOf p t₀.mem).drop (16 * (p.al / 16))) ^^^
        (offAt 0 (lstarOf p t₀.mem) (p.al / 16) ^^^ lstarOf p t₀.mem) := by
    rw [R₃.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inr (by decide)) (by decide) (by decide))), pad₂, oh₂]
  -- enciphered
  refine WP.seq (WP.mono (encOne_ok L E₃ (d := bufO) (by decide) (by decide)) fun t₄ C₄ => ?_)
  have E₄ := C₄.env E₃
  have b₄ : blockAtMem t₄.mem (State.addr p.W + BitVec.ofNat 64 bufO) =
      ciphOf p t₀.mem (pad ((aadOf p t₀.mem).drop (16 * (p.al / 16))) ^^^
        (offAt 0 (lstarOf p t₀.mem) (p.al / 16) ^^^ lstarOf p t₀.mem)) := by
    have := C₄.out 0 (by decide)
    simp only [Nat.mul_zero, BitVec.add_zero] at this
    rw [this, encF_ciph, b₃, sched_mut L (hashR_mut L fr₃)]
  have fr₄ : Frame (hashR p) t₀.mem t₄.mem := fr₃.trans (C₄.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact w_hash (b := 256) (k := 2304) (by simp) ⟨by decide, by decide⟩ (by decide)
    · exact w_hash (b := 256) (k := 2304) (by simp) ⟨by decide, by decide⟩ (by decide)
    · exact ⟨_, by simp, fun _ h => h⟩)
  have sum₄ : blockAtMem t₄.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
      hsum (ciphOf p t₀.mem) (lstarOf p t₀.mem) (aadOf p t₀.mem) (p.al / 16) := by
    rw [blockAtMem_frame C₄.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm),
      blockAtMem_frame fr₃' (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)), H.sum]
  -- added to the sum
  refine WP.mono (xorB_wp (s := t₄) (pb := .r11) (qb := .r11) (cb := .r11) (pd := sumO) (qd := bufO)
    (cd := sumO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [E₄.r11]; simp only [sumO]; omega) (by rw [E₄.r11]; simp only [bufO]; omega)
    (by rw [E₄.r11]; simp only [sumO]; omega) (by rw [E₄.r11]; exact E₄.perm.wCR (by decide))
    (by rw [E₄.r11]; exact E₄.perm.wCR (by decide)) (by rw [E₄.r11]; exact E₄.perm.wC (by decide))) fun t₅ R₅ => ?_
  rw [E₄.r11] at R₅
  refine ⟨E₄.of_others R₅.gpr R₅.sp R₅.rd R₅.wr, ?_, by rw [R₅.rd, C₄.rd, R₃.rd, rd₂, R₁.rd, H.rd],
    by rw [R₅.wr, C₄.wr, R₃.wr, wr₂, R₁.wr, H.wr], ?_⟩
  · rw [R₅.mem]
    exact fr₄.trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact w_hash (b := 48) (k := 16) (by simp) (by decide) (by decide))
  · rw [R₅.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inl (by decide)) (by decide) (by decide))), sum₄, b₄]

/-- The start of `hash`: the sum and the offset zeroed, the associated data
in `r4`, its whole blocks in `r7` and `i = 1` in `r6`. -/
theorem hashHead_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem)
    (hl0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p t.mem) 0) :
    WP isa (.block (Impl.AesGcm.Arm.zero16 sumO ++ Impl.AesGcm.Arm.zero16 ohO ++
      ([.ldrSp .r4 0, .ldrSp .r7 4, .mov .r7 (.shifted .r7 .lsr 4), .mov .r6 (Impl.AesGcm.Arm.imm 1),
        .cmp .r7 (Impl.AesGcm.Arm.imm 0)] : List Instr))) t
      fun t₂ => HInv p t t₂ 0 ∧ t₂.z = decide (p.al / 16 = 0) := by
  have fw := L.ww
  have al32 := L.al_lt
  refine WP.block_append (WP.block_append (WP.mono (zero16_wp (s := t) (o := sumO) (by decide)
    (by rw [E.r11]; simp only [sumO]; omega) (by rw [E.r11]; exact E.perm.wC (by decide))) fun t₁ R₁ => ?_))
  rw [E.r11] at R₁
  have E₁ : Env p t₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  refine WP.mono (zero16_wp (s := t₁) (o := ohO) (by decide) (by rw [E₁.r11]; simp only [ohO]; omega)
    (by rw [E₁.r11]; exact E₁.perm.wC (by decide))) fun t₂ R₂ => ?_
  rw [E₁.r11] at R₂
  have E₂ : Env p t₂ := E₁.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  have fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩]
      t.mem t₂.mem := by
    rw [R₂.mem]
    exact ((by rw [R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _ :
      Frame [⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩] t.mem t₁.mem).mono (by simp)).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp))
  have A₂ : Args p t₂.mem := A.frame L fr₂ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact L.args_w' (by decide))
  have a₀ := E₂.perm.argR' L (k := 0) (by decide)
  have a₄ := E₂.perm.argR' L (k := 4) (by decide)
  refine WP.of_runBlock ⟨_, by orun [E₂.sp, a₀, a₄, A₂.a0, A₂.a4], ?_⟩
  have fsub : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩],
      ∃ r' ∈ hashR p, Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact w_hash (b := 48) (k := 16) (by simp) ⟨by decide, by decide⟩ (by decide)
    · exact w_hash (b := 192) (k := 24) (by simp) ⟨by decide, by decide⟩ (by decide)
  have kblk : ∀ {d : Nat}, d + 16 ≤ 2560 → (d + 16 ≤ sumO ∨ sumO + 16 ≤ d) → (d + 16 ≤ ohO ∨ ohO + 16 ≤ d) →
      blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd h₁ h₂ => blockAtMem_frame fr₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w h₁ hd (by decide)
      · exact L.w_w h₂ hd (by decide)
  refine ⟨?_, ?_⟩
  · refine ⟨E₂.of_others (rs := [.r4, .r6, .r7]) (by others_tac) (by rfl) (by rfl) (by rfl),
        fr₂.sub fsub, by simp [rd_setReg, R₂.rd, R₁.rd], by simp [wr_setReg, R₂.wr, R₁.wr], Nat.zero_le _, ?_, ?_,
        by simp [gpr_setReg], by simp [gpr_setReg], ?_, ?_⟩
    · simp only [Proof.AesGcm.Arm.mem_subFlags, mem_setReg]
      have fz : Frame [⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩] t₁.mem
          (Proof.Cmac.zero4 t₁.mem (State.addr p.W + BitVec.ofNat 64 ohO)) := Proof.Cmac.frame_store4 _ _ _ _ _
      rw [R₂.mem, blockAtMem_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := sumO) (n := 16) (d := ohO) (k := 16) (.inl (by decide)) (by decide) (by decide)),
        R₁.mem, blockAtMem_zero4]; rfl
    · simp only [Proof.AesGcm.Arm.mem_subFlags, mem_setReg]
      rw [R₂.mem, blockAtMem_zero4]; rfl
    · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, ofNat_lsr32 al32]
      rfl
    · simp only [Proof.AesGcm.Arm.mem_subFlags, mem_setReg]
      rw [kblk (by decide) (.inr (by decide)) (.inl (by decide)), hl0]
  · simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, BitVec.sub_zero, ofNat_lsr32 al32,
      z_cmp0 (show p.al / 2 ^ 4 < 2 ^ 32 by omega)]

/-- After the whole blocks of the associated data: the rest's length in `r5`. -/
theorem hashMid_ok {p : Prm} (L : Lay p) {t₀ t : State} (H : HInv p t₀ t (p.al / 16)) (A : Args p t.mem) :
    WP isa (.block [.ldrSp .r5 4, .dp .and .r5 .r5 (Impl.AesGcm.Arm.imm 15), .cmp .r5 (Impl.AesGcm.Arm.imm 0)]) t
      fun t' => HInv p t₀ t' (p.al / 16) ∧ t'.gpr .r5 = BitVec.ofNat 32 (p.al % 16) ∧
        t'.z = decide (p.al % 16 = 0) := by
  have E₃ := H.env
  have a₄' := E₃.perm.argR' L (k := 4) (by decide)
  refine WP.of_runBlock ⟨_, by orun [E₃.sp, a₄', A.a4], ?_, ?_, ?_⟩
  · exact ⟨E₃.of_others (rs := [.r5]) (by others_tac) (by rfl) (by rfl) (by rfl), H.frame, H.rd, H.wr, H.le,
      H.sum, H.oh, H.r4, H.r6, H.r7, H.l0⟩
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, and15, toNat_ofNat32 L.al_lt]
  · simp only [z_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, and15, toNat_ofNat32 L.al_lt,
      z_cmp0 (show p.al % 16 < 2 ^ 32 by omega)]

theorem hash_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem)
    (hl0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p t.mem) 0) :
    WP isa Impl.AesOcb.Arm.hash t (HashOut p t) := by
  have al32 := L.al_lt
  unfold Impl.AesOcb.Arm.hash
  refine WP.seq (WP.mono (hashHead_ok L E A hl0) fun t₂ ⟨H₂, hz₂⟩ => ?_)
  refine WP.seq (WP.mono (hashWhole_ok L H₂ hz₂) fun t₃ H₃ => ?_)
  have A₃ : Args p t₃.mem := A.mut L (hashR_mut L H₃.frame)
  refine WP.seq (WP.mono (hashMid_ok L H₃ A₃) fun t₄ ⟨H₄, h5₄, hz₄⟩ => ?_)
  have hlen : (aadOf p t.mem).length = p.al := Proof.Ocb.length_bytesAt _ _ _
  have hdrop : ((aadOf p t.mem).drop (16 * ((aadOf p t.mem).length / 16))).length = p.al % 16 := by
    rw [List.length_drop, hlen]; omega
  have heq := Proof.Ocb.hash_eq (ciphOf p t.mem) (lstarOf p t.mem) (aadOf p t.mem)
  rw [hdrop, hlen] at heq
  refine WP.ite (decide (p.al % 16 = 0)) (eval_eq' hz₄) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : p.al % 16 = 0 := of_decide_eq_true hb
    refine ⟨H₄.env, H₄.frame, H₄.rd, H₄.wr, ?_⟩
    rw [H₄.sum, heq]; simp only [show ¬ p.al % 16 > 0 by omega, ↓reduceIte]
  · have h0 : p.al % 16 ≠ 0 := by simpa using hb
    refine WP.mono (hashRest_ok L H₄ h5₄ h0) fun t' ⟨E', fr', rd', wr', sum'⟩ => ⟨E', fr', rd', wr', ?_⟩
    rw [sum', heq]; simp only [show p.al % 16 > 0 by omega, ↓reduceIte, hlen]

end VG.Proof.AesOcb.Arm
