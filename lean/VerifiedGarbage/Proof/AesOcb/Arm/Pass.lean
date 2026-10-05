import VerifiedGarbage.Proof.AesOcb.Arm.Hash

/-!
# AES-OCB on ARMv7: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. `pass body` goes over the
`m` whole blocks of the data at `D`: for block `i` it computes
`Offset_{i+1}` (`lNtz_ok`, `xorB_wp`), then runs `body` on the block, which
replaces it with `fB` of it and the offset, and the checksum with `fC` of
them (`BodyOk`: `xorOfs`, `addCk ++ xorOfs`, `xorOfs ++ addCk`); `pass_ok`
gives the blocks and the checksum after all `m`, as on AArch64
(`Proof.AesOcb.AArch64.pass_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.Arm (eval_ne' z_subFlags dec32 z_dec)

/-- The data block at offset `k` of the data, as a 64-bit address. -/
theorem dA {p : Prm} (L : Lay p) {k : Nat} (h : k + 16 ≤ p.n) :
    State.addr (p.D + BitVec.ofNat 32 k) = State.addr p.D + BitVec.ofNat 64 k :=
  addr_add (by have := L.dw; omega)

/-- What a body does to the block at `B` (in `r4`) and the checksum, with the
offset at `W + ofsO`. -/
def BodyOk (p : Prm) (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) : Prop :=
  ∀ (t : State) (k : Nat), Env p t → t.gpr .r4 = p.D + BitVec.ofNat 32 k → k + 16 ≤ p.n →
    WP isa (.block body) t fun t' =>
      blockAtMem t'.mem (State.addr p.D + BitVec.ofNat 64 k) =
        fB (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 k))
          (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO)) ∧
      blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) = fC (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO))
        (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 k)) (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO)) ∧
      Frame [⟨State.addr p.D + BitVec.ofNat 64 k, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩] t.mem t'.mem ∧
      Others [.r0, .r1] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr

section
variable {p : Prm} (L : Lay p)
include L

theorem bW {k : Nat} (h : k + 16 ≤ p.n) :
    (⟨State.addr p.D + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩ :=
  (L.d_w' (by decide)).sub_left (Offset.sub_base _ h)

theorem bO {k : Nat} (h : k + 16 ≤ p.n) :
    (⟨State.addr p.D + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ :=
  (L.d_w' (by decide)).sub_left (Offset.sub_base _ h)

/-- `(r4) ⊕= W + ofsO`. -/
theorem xorOfs_wp {t : State} (E : Env p t) {k : Nat} (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 k)
    (hk : k + 16 ≤ p.n) :
    WP isa (.block xorOfs) t (Ran [.r0, .r1] (Proof.Cmac.xor4Mem t.mem (State.addr p.D + BitVec.ofNat 64 k)
      (State.addr p.D + BitVec.ofNat 64 k) (State.addr p.W + BitVec.ofNat 64 ofsO)) t) := by
  have fw := L.ww
  have fd := L.dw
  have e := dA L hk
  have := xorB_wp (s := t) (pb := .r4) (qb := .r11) (cb := .r4) (pd := 0) (qd := ofsO) (cd := 0) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [h4, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega) (by rw [E.r11]; simp only [ofsO]; omega)
    (by rw [h4, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega)
    (by rw [h4, e, BitVec.add_zero]; exact Proof.AesGcm.Arm.covers_left (Proof.AesGcm.Arm.covers_off E.perm.d hk (by omega)))
    (by rw [E.r11]; exact E.perm.wCR (by decide))
    (by rw [h4, e, BitVec.add_zero]; exact Proof.AesGcm.Arm.covers_off E.perm.d hk (by omega))
  rw [h4, E.r11, e, BitVec.add_zero] at this
  exact this

/-- `W + ckO ⊕= (r4)`. -/
theorem addCk_wp {t : State} (E : Env p t) {k : Nat} (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 k)
    (hk : k + 16 ≤ p.n) :
    WP isa (.block addCk) t (Ran [.r0, .r1] (Proof.Cmac.xor4Mem t.mem (State.addr p.W + BitVec.ofNat 64 ckO)
      (State.addr p.W + BitVec.ofNat 64 ckO) (State.addr p.D + BitVec.ofNat 64 k)) t) := by
  have fw := L.ww
  have fd := L.dw
  have e := dA L hk
  have := xorB_wp (s := t) (pb := .r11) (qb := .r4) (cb := .r11) (pd := ckO) (qd := 0) (cd := ckO) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [E.r11]; simp only [ckO]; omega)
    (by rw [h4, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega) (by rw [E.r11]; simp only [ckO]; omega)
    (by rw [E.r11]; exact E.perm.wCR (by decide))
    (by rw [h4, e, BitVec.add_zero]; exact Proof.AesGcm.Arm.covers_left (Proof.AesGcm.Arm.covers_off E.perm.d hk (by omega)))
    (by rw [E.r11]; exact E.perm.wC (by decide))
  rw [h4, E.r11, e, BitVec.add_zero] at this
  exact this

theorem xorOfs_ok : BodyOk p xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t k E h4 hk
  refine WP.mono (xorOfs_wp L E h4 hk) fun t' R => ⟨?_, ?_, ?_, R.gpr, R.sp, R.rd, R.wr⟩
  · rw [R.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (bO L hk))]
  · rw [R.mem, blockAtMem_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (bW L hk).symm)]
  · rw [R.mem]; exact (Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp)

theorem sealPre_ok : BodyOk p (addCk ++ xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := by
  intro t k E h4 hk
  refine WP.block_append (WP.mono (addCk_wp L E h4 hk) fun t₁ R₁ => ?_)
  have E₁ : Env p t₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have fr₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩] t.mem t₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  refine WP.mono (xorOfs_wp L E₁ (by rw [R₁.gpr _ (by decide), h4]) hk) fun t₂ R₂ =>
    ⟨?_, ?_, ?_, fun r hr => by rw [R₂.gpr r hr, R₁.gpr r hr], by rw [R₂.sp, R₁.sp], by rw [R₂.rd, R₁.rd],
      by rw [R₂.wr, R₁.wr]⟩
  · rw [R₂.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (bO L hk)),
      blockAtMem_frame fr₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact bW L hk),
      blockAtMem_frame fr₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))]
  · rw [R₂.mem, blockAtMem_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (bW L hk).symm), R₁.mem,
      blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (bW L hk).symm)]
  · rw [R₂.mem]
    exact (fr₁.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))

theorem openPost_ok : BodyOk p (xorOfs ++ addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := by
  intro t k E h4 hk
  refine WP.block_append (WP.mono (xorOfs_wp L E h4 hk) fun t₁ R₁ => ?_)
  have E₁ : Env p t₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have fr₁ : Frame [⟨State.addr p.D + BitVec.ofNat 64 k, 16⟩] t.mem t₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have b₁ : blockAtMem t₁.mem (State.addr p.D + BitVec.ofNat 64 k) =
      blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 k) ^^^ blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) := by
    rw [R₁.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (bO L hk))]
  refine WP.mono (addCk_wp L E₁ (by rw [R₁.gpr _ (by decide), h4]) hk) fun t₂ R₂ =>
    ⟨?_, ?_, ?_, fun r hr => by rw [R₂.gpr r hr, R₁.gpr r hr], by rw [R₂.sp, R₁.sp], by rw [R₂.rd, R₁.rd],
      by rw [R₂.wr, R₁.wr]⟩
  · rw [R₂.mem, blockAtMem_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact bW L hk), b₁]
  · rw [R₂.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (bW L hk).symm), b₁,
      blockAtMem_frame fr₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (bW L hk).symm)]
  · rw [R₂.mem]
    exact (fr₁.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))

end

/-- The registers a pass writes. -/
abbrev passRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r12, .lr]

/-- What a pass writes, over `m` blocks. -/
abbrev passR (p : Prm) (m : Nat) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨State.addr p.D, 16 * m⟩]

/-- A pass over the `m` whole blocks of the data (`X k` at its start, `t₀`),
after `i` of them. -/
structure PassInv (p : Prm) (m : Nat) (O0 l : Block) (X : Nat → Block) (fB : Block → Block → Block)
    (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env p t
  frame : Frame (passR p m) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  r4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * i)
  r6 : t.gpr .r6 = BitVec.ofNat 32 (i + 1)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (m - i)
  ofs : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : Others passRegs t₀ t

theorem pass_step {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk p body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    (hm : 16 * m ≤ p.n) {t₀ t : State} {i : Nat} (hi : i < m) (P : PassInv p m O0 l X fB ckF t₀ t i) :
    WP isa (.seq nextOffset (.block (body ++ nextBlock))) t fun t' =>
      PassInv p m O0 l X fB ckF t₀ t' (i + 1) ∧ t'.z = decide (i + 1 = m) := by
  have fw := L.ww
  have n32 := L.n_lt
  have E := P.env
  unfold nextOffset
  refine WP.seq (WP.seq (WP.mono (lNtz_ok L E (i := i + 1) (by omega) (by omega) P.r6 P.l0) fun t₁ P₁ => ?_))
  have E₁ : Env p t₁ := E.of_others P₁.gpr P₁.sp P₁.rd P₁.wr
  refine WP.mono (xorB_wp (s := t₁) (pb := .r11) (qb := .r11) (cb := .r11) (pd := ofsO) (qd := lO) (cd := ofsO)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [E₁.r11]; simp only [ofsO]; omega) (by rw [E₁.r11]; simp only [lO]; omega)
    (by rw [E₁.r11]; simp only [ofsO]; omega) (by rw [E₁.r11]; exact E₁.perm.wCR (by decide))
    (by rw [E₁.r11]; exact E₁.perm.wCR (by decide)) (by rw [E₁.r11]; exact E₁.perm.wC (by decide))) fun t₂ R₂ => ?_
  rw [E₁.r11] at R₂
  have E₂ : Env p t₂ := E₁.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  have g₂ : ∀ r, r ∉ ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    have h' : r ∉ [Reg.r0, .r1] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h <;> simp [h])
    rw [R₂.gpr r h', P₁.gpr r hr]
  have fW₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩]
      t.mem t₂.mem := by
    rw [R₂.mem]; exact (P₁.frame.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
  have kD₂ : ∀ {k : Nat}, k + 16 ≤ p.n → blockAtMem t₂.mem (State.addr p.D + BitVec.ofNat 64 k) =
      blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 k) := fun hk =>
    blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (L.d_w' (by decide)).sub_left (Offset.sub_base _ hk)
  have ofs₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [R₂.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inl (by decide)) (by decide) (by decide))),
      blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      P.ofs, P₁.val]
    rfl
  have ck₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF i := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.ck]
  have Bi₂ : blockAtMem t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) = X i := by
    rw [kD₂ (by omega), P.blk i hi]; simp
  -- the body
  refine WP.block_append (WP.mono (hB t₂ (16 * i) E₂ (by rw [g₂ _ (by decide), P.r4]) (by omega))
    fun t₃ ⟨blk₃, ck₃, fr₃, g₃, sp₃, rd₃, wr₃⟩ => ?_)
  have g₃' : ∀ r, r ∉ ntzRegs → t₃.gpr r = t.gpr r := fun r hr => by
    have h' : r ∉ [Reg.r0, .r1] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h <;> simp [h])
    rw [g₃ r h', g₂ r hr]
  have r4₃ : t₃.gpr .r4 = p.D + BitVec.ofNat 32 (16 * i) := by rw [g₃' _ (by decide), P.r4]
  have r5₃ : t₃.gpr .r5 = BitVec.ofNat 32 (m - i) := by rw [g₃' _ (by decide), P.r5]
  have r6₃ : t₃.gpr .r6 = BitVec.ofNat 32 (i + 1) := by rw [g₃' _ (by decide), P.r6]
  refine WP.of_runBlock ⟨_, by orun [nextBlock, r4₃, r5₃, r6₃], ?_⟩
  have kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.D + BitVec.ofNat 64 (16 * i), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩ →
      blockAtMem t₃.mem Q = blockAtMem t₂.mem Q := fun h₁ h₂ =>
    blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂)
  refine ⟨⟨E₂.of_others (rs := [.r0, .r1, .r4, .r5, .r6]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ↓reduceIte]
      exact g₃ r (by simp [hr.1, hr.2.1])) (by simp [sp_setReg, Proof.AesGcm.Arm.sp_subFlags, sp₃])
      (by simp [rd_setReg, Proof.AesGcm.Arm.rd_subFlags, rd₃]) (by simp [wr_setReg, Proof.AesGcm.Arm.wr_subFlags, wr₃]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, fun r hr => ?_⟩, ?_⟩
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    exact P.frame.trans ((fW₂.mono (by simp)).trans (fr₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr p.D, 16 * m⟩, by simp, Offset.sub_base _ (by omega)⟩
      · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩, by simp, fun _ h => h⟩))
  · simp [rd_setReg, Proof.AesGcm.Arm.rd_subFlags, rd₃, R₂.rd, P₁.rd, P.rd]
  · simp [wr_setReg, Proof.AesGcm.Arm.wr_subFlags, wr₃, R₂.wr, P₁.wr, P.wr]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc,
      ← BitVec.ofNat_add]
    rw [show 16 * i + 16 = 16 * (i + 1) by omega]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, ← BitVec.ofNat_add]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, dec32 hi (by omega)]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [kB₃ (bO L (by omega)).symm (L.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [ck₃, ck₂, Bi₂, ofs₂, hckF i hi]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    by_cases hki : k = i
    · subst hki
      rw [blk₃, Bi₂, ofs₂]; simp
    · rw [kB₃ (Offset.disjoint _ (by omega) (by omega) (by have := L.dw; omega)) (bW L (by omega)),
        kD₂ (by omega), P.blk k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    have l0D : (⟨State.addr p.W + BitVec.ofNat 64 l0O, 16⟩ : Region).Disjoint
        ⟨State.addr p.D + BitVec.ofNat 64 (16 * i), 16⟩ :=
      ((L.d_w' (d := l0O) (k := 16) (by decide)).sub_left (Offset.sub_base _ (by omega))).symm
    rw [kB₃ l0D (L.w_w (.inr (by decide)) (by decide) (by decide)), blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.l0]
  · simp only [passRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, ite_false]
    rw [g₃' r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      P.gpr r (by simp [passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
  · simp only [z_setReg, z_subFlags, dec32 hi (by omega), z_dec hi (by omega)]

theorem pass_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk p body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    (hm : 16 * m ≤ p.n) (hm0 : 0 < m) {t₀ t : State} (P : PassInv p m O0 l X fB ckF t₀ t 0) :
    WP isa (pass body) t (fun t' => PassInv p m O0 l X fB ckF t₀ t' m) := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ PassInv p m O0 l X fB ckF t₀ u i) ?_
    (m - 0) _ ⟨0, rfl, hm0, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (pass_step L hB hckF hm hi P) fun u' ⟨P', z⟩ => ?_
  by_cases he : i + 1 = m
  · left
    exact ⟨(eval_ne' z).trans (by simp [he]), he ▸ P'⟩
  · right
    exact ⟨(eval_ne' z).trans (by simp [he]), m - (i + 1), by omega, i + 1, rfl, by omega, P'⟩

end VG.Proof.AesOcb.Arm
