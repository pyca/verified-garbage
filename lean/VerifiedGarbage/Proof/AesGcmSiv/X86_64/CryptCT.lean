import VerifiedGarbage.Proof.AesGcmSiv.X86_64.CTBase

/-!
# AES-GCM-SIV on x86-64: the tag and counter mode are constant time

Untrusted: everything here is checked by Lean. The code around each call of
`vg_aes_ctr32` passes the taint analysis from the public slots and the
registers both runs agree on (`rel_taintC`); each call has the same
arguments in both runs, by correctness.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr xorLoop)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl CtrCall ctr_rel ctr_call)

/-! ## The tag -/

theorem tagCall_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    {t : State} (O : One K W SP R N A D al n t) {o : Nat} (ho : o = 0 ∨ o = 128 ∨ o = 144) :
    WP isa (.block (copy16 cmO ccO ++ zero16 o ++ ptr .rdi .r15 skO ++ ctrArgs ++ ptr .rcx .r15 o)) t fun t₁ =>
      CtrCall t₁ (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 o)
        (W + BitVec.ofNat 64 2048) R 1 ∧ t₁.gpr .rsp = SP := by
  obtain ⟨t₁, run₁, -, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ := tagArgs_ok L O.env O.sl ho
  have E₁ : Env K W SP t₁ := O.env.of_saved hg₁ hrd₁ hwr₁
  have dO : (⟨W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 112, 16⟩ :=
    L.w_w (by omega) (by omega) (by decide)
  exact WP.of_runBlock ⟨t₁, run₁, cargs L E₁ hR (keyS L E₁.perm) (c := 112) (by decide)
    (srcW L E₁.perm (t := o) (k := 16 * 1) (by omega)) dO (L.w_w (.inr (by omega)) (by decide) (by omega))
    (E₁.perm.wC (by omega)) rdi rsi rdx rcx r8 r9, E₁.rsp⟩

theorem tagArgs_check {o : Nat} (ho : o = 0 ∨ o = 128 ∨ o = 144) :
    ∃ hc, (taint.check (sivT []) (.block (copy16 cmO ccO ++ zero16 o ++ ptr .rdi .r15 skO ++ ctrArgs ++
      ptr .rcx .r15 o)) hc).isSome = true := by
  rcases ho with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `tag o`, in two runs with the same public arguments. -/
theorem tag_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) (hn : n ≤ 2 ^ 64) {o : Nat}
    (ho : o = 0 ∨ o = 128 ∨ o = 144) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → Both K W SP R N A D al n [] t₁ t₂) :
    RelCT isa P (tag v.callees o) fun _ _ => True := by
  have a := (rel_taintC [] hDW hn hP (tagArgs_check ho)).wp
    (F₁ := fun (t₁ : State) => CtrCall t₁ (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 o)
        (W + BitVec.ofNat 64 2048) R 1 ∧ t₁.gpr .rsp = SP)
    (F₂ := fun (t₁ : State) => CtrCall t₁ (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 o)
        (W + BitVec.ofNat 64 2048) R 1 ∧ t₁.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨tagCall_wp L hR (hP _ _ h).o₁ ho, tagCall_wp L hR (hP _ _ h).o₂ ho⟩
  exact RelCT.seq a (ctr_rel v.ctr fun t₁ t₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)

/-! ## Counter mode's whole blocks -/

/-- The end of a block: the counter incremented, the pointer and the count. -/
theorem blkEnd_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {D : Addr} {b j : Nat} (hj : j < b)
    (hb : b < 2 ^ 60) (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j)) (hbx : t.gpr .rbx = BitVec.ofNat 64 (b - j)) :
    ∃ t' : State, runBlock isa [.mov32 .rax (.mem (at_ .r15 cmO)), .alu32 .add .rax (imm 1), .store32 (at_ .r15 cmO) .rax,
        .alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)] t = some t' ∧
      Frame [⟨W + BitVec.ofNat 64 96, 4⟩] t.mem t'.mem ∧ t'.gpr .r12 = D + BitVec.ofNat 64 (16 * (j + 1)) ∧
      t'.gpr .rbx = BitVec.ofNat 64 (b - (j + 1)) ∧ t'.zf = some (decide (b - (j + 1) = 0)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbp], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have c₀ := E.perm.wR (show 96 + 4 ≤ 4096 by decide)
  have c₁ := E.perm.wW (show 96 + 4 ≤ 4096 by decide)
  refine ⟨_, by srun [h15, c₀, c₁, h12, hbx], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [gpr_arithFlags, gpr_setReg, mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg,
    wr_arithFlags, wr_setReg, zf_arithFlags, zf_setReg, ite_true, ite_false, reduceCtorEq]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [add_ofNat_assoc, show 16 * j + 16 = 16 * (j + 1) by omega]
  · rw [Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega), Nat.sub_sub]
  · rw [Proof.AesGcm.X86_64.sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp

/-- A run of counter mode before block `j`. -/
structure CInv (K W SP : Addr) (R : Nat) (N A D : Addr) (al n b : Nat) (j : Nat) (t : State) : Prop where
  one : One K W SP R N A D al n t
  buf : Buf K W SP t D n
  r12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j)
  rbx : t.gpr .rbx = BitVec.ofNat 64 (b - j)
  rbp : t.gpr .rbp = BitVec.ofNat 64 (n % 16)

theorem CInv.agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n b : Nat} {j : Nat} {t₁ t₂ : State}
    (h₁ : CInv K W SP R N A D al n b j t₁) (h₂ : CInv K W SP R N A D al n b j t₂) :
    Both K W SP R N A D al n [.r12, .rbx, .rbp] t₁ t₂ :=
  ⟨h₁.one, h₂.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r12, h₂.r12]
    · rw [h₁.rbx, h₂.rbx]
    · rw [h₁.rbp, h₂.rbp]⟩

/-- A block, after its arguments: the call's, and the run's. -/
def BlkArgs (K W SP : Addr) (R : Nat) (N A D : Addr) (al n b : Nat) (j : Nat) (t : State) : Prop :=
  CtrCall t (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 112) (D + BitVec.ofNat 64 (16 * j))
    (W + BitVec.ofNat 64 2048) R 1 ∧ t.gpr .rsp = SP ∧ CInv K W SP R N A D al n b j t

theorem blkArgs_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n b : Nat}
    (hb : 16 * b ≤ n) {j : Nat} (hj : j < b) {t : State} (I : CInv K W SP R N A D al n b j t) :
    WP isa (.block (copy16 cmO ccO ++ ptr .rdi .r15 skO ++ ctrArgs ++ ([.mov .rcx (.reg .r12)] : List Instr))) t
      (BlkArgs K W SP R N A D al n b j) := by
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ := blkArgs_ok L I.one.env I.one.sl I.r12
  have E₁ : Env K W SP t₁ := I.one.env.of_saved hg₁ hrd₁ hwr₁
  have hn := I.buf.lt
  have hD₁ := I.buf.of_eq hrd₁ hwr₁
  have hQ : Buf K W SP t₁ (D + BitVec.ofNat 64 (16 * j)) (16 * 1) := hD₁.slice (by omega)
  have hDw : Covers [⟨D, n⟩] t₁.wr := by rw [hwr₁, I.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp)
  refine WP.of_runBlock ⟨t₁, run₁, cargs L E₁ hR (keyS L E₁.perm) (c := 112) (by decide) (srcBuf hQ)
    (hQ.w.sub_right (Lay.wSub (by decide))) (hQ.w.sub_right (Lay.wSub (show 512 + 240 ≤ 4096 by decide))).symm
    (Proof.AesGcm.X86_64.covers_off hDw (by omega) hn) rdi rsi rdx rcx r8 r9, E₁.rsp,
    ⟨⟨E₁, by rw [hm₁]; exact I.one.sl.of_frame (Proof.Cmac.frame_store2 _ _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      hwr₁.trans I.one.wr⟩, hD₁, by rw [hg₁ _ (by decide), I.r12], by rw [hg₁ _ (by decide), I.rbx],
      by rw [hg₁ _ (by decide), I.rbp]⟩⟩

theorem blkCalled_wp (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n b : Nat}
    (hb : 16 * b ≤ n) {j : Nat} (hj : j < b) {t : State} (h : BlkArgs K W SP R N A D al n b j t) :
    WP isa (.call v.ctr.callee.name v.ctr.callee.code) t (CInv K W SP R N A D al n b j) := by
  obtain ⟨cc, hsp, I⟩ := h
  refine WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_
  have fc := P.frame
  rw [hsp] at fc
  refine ⟨⟨I.one.env.of_saved P.saved P.rd P.wr, I.one.sl.of_frame fc (fun q hq => ?_), P.wr.trans I.one.wr⟩,
    I.buf.of_eq P.rd P.wr, by rw [P.saved _ (by decide), I.r12], by rw [P.saved _ (by decide), I.rbx],
    by rw [P.saved _ (by decide), I.rbp]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact ((I.buf.w.sub_left (Offset.sub_base D (show 16 * j + 16 * 1 ≤ n by omega))).sub_right
      (Lay.wSub (by decide))).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

theorem blkEnd_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n b : Nat} (hb : 16 * b ≤ n)
    {j : Nat} (hj : j < b) {t : State} (I : CInv K W SP R N A D al n b j t) :
    WP isa (.block [.mov32 .rax (.mem (at_ .r15 cmO)), .alu32 .add .rax (imm 1), .store32 (at_ .r15 cmO) .rax,
        .alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)]) t fun t' =>
      CInv K W SP R N A D al n b (j + 1) t' ∧ t'.zf = some (decide (b - (j + 1) = 0)) := by
  have hn := I.buf.lt
  obtain ⟨t', run', f', r12', rbx', zf', hg', hrd', hwr'⟩ := blkEnd_ok I.one.env hj (by omega) I.r12 I.rbx
  exact WP.of_runBlock ⟨t', run', ⟨⟨I.one.env.keep (fun r hr => hg' r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd' hwr',
    I.one.sl.of_frame f' (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
    hwr'.trans I.one.wr⟩, I.buf.of_eq hrd' hwr', r12', rbx', by rw [hg' _ (by simp), I.rbp]⟩, zf'⟩

theorem blkArgs_check : ∃ hc, (taint.check (sivT [.r12, .rbx, .rbp])
    (.block (copy16 cmO ccO ++ ptr .rdi .r15 skO ++ ctrArgs ++ ([.mov .rcx (.reg .r12)] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem blkEnd_check : ∃ hc, (taint.check (sivT [.r12, .rbx, .rbp])
    (.block [.mov32 .rax (.mem (at_ .r15 cmO)), .alu32 .add .rax (imm 1), .store32 (at_ .r15 cmO) .rax,
      .alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)]) hc).isSome = true := ⟨_, by taint_decide⟩

/-- A block of counter mode, in two runs before the same block. -/
theorem blk_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n b : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) (hn : n ≤ 2 ^ 64) (hb : 16 * b ≤ n) {j : Nat}
    (hj : j < b) :
    RelCT isa (fun t₁ t₂ => CInv K W SP R N A D al n b j t₁ ∧ CInv K W SP R N A D al n b j t₂) (cryptBlock v.callees)
      fun t₁ t₂ => (CInv K W SP R N A D al n b (j + 1) t₁ ∧ t₁.zf = some (decide (b - (j + 1) = 0))) ∧
        (CInv K W SP R N A D al n b (j + 1) t₂ ∧ t₂.zf = some (decide (b - (j + 1) = 0))) := by
  have r₁ := (rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ => CInv K W SP R N A D al n b j t₁ ∧
      CInv K W SP R N A D al n b j t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2) blkArgs_check).wp
    (F₁ := BlkArgs K W SP R N A D al n b j) (F₂ := BlkArgs K W SP R N A D al n b j)
    fun t₁ t₂ h => ⟨blkArgs_wp L hR hb hj h.1, blkArgs_wp L hR hb hj h.2⟩
  have r₂ := (ctr_rel v.ctr (P := fun t₁ t₂ => True ∧ BlkArgs K W SP R N A D al n b j t₁ ∧
      BlkArgs K W SP R N A D al n b j t₂)
    fun t₁ t₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1]⟩).wp
    (F₁ := CInv K W SP R N A D al n b j) (F₂ := CInv K W SP R N A D al n b j)
    fun t₁ t₂ h => ⟨blkCalled_wp v L hb hj h.2.1, blkCalled_wp v L hb hj h.2.2⟩
  have r₃ := (rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ => True ∧ CInv K W SP R N A D al n b j t₁ ∧
      CInv K W SP R N A D al n b j t₂) hDW hn (fun t₁ t₂ h => h.2.1.agree h.2.2) blkEnd_check).wp
    (F₁ := fun (t' : State) => CInv K W SP R N A D al n b (j + 1) t' ∧ t'.zf = some (decide (b - (j + 1) = 0)))
    (F₂ := fun (t' : State) => CInv K W SP R N A D al n b (j + 1) t' ∧ t'.zf = some (decide (b - (j + 1) = 0)))
    fun t₁ t₂ h => ⟨blkEnd_wp L hb hj h.2.1, blkEnd_wp L hb hj h.2.2⟩
  exact (RelCT.seq r₁ (RelCT.seq r₂ r₃)).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

/-- The whole blocks of counter mode, in two runs. -/
theorem blks_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n b : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) (hn : n ≤ 2 ^ 64) (hb : 16 * b ≤ n) (hb1 : 1 ≤ b) :
    RelCT isa (fun t₁ t₂ => CInv K W SP R N A D al n b 0 t₁ ∧ CInv K W SP R N A D al n b 0 t₂)
      (.loop (cryptBlock v.callees) .ne)
      fun t₁ t₂ => CInv K W SP R N A D al n b b t₁ ∧ CInv K W SP R N A D al n b b t₂ := by
  refine (RelCT.loop (fun m t₁ t₂ => ∃ j, m = b - j ∧ j < b ∧ CInv K W SP R N A D al n b j t₁ ∧
      CInv K W SP R N A D al n b j t₂) (fun m => ?_) (b - 0)).mono (fun t₁ t₂ h => ⟨0, rfl, hb1, h⟩) fun _ _ h => h
  refine RelCT.exists_ fun j => ?_
  by_cases hj : j < b
  · by_cases hm : m = b - j
    · subst hm
      refine (blk_rel v L hR hDW hn hb hj).mono (fun t₁ t₂ h => ⟨h.2.2.1, h.2.2.2⟩)
        fun t₁ t₂ ⟨⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ => ⟨by rw [eval_ne z₁, eval_ne z₂], fun hc => ?_, fun hc => ?_⟩
      · rw [eval_ne z₁] at hc
        have he : j + 1 = b := by simp at hc; omega
        rw [he] at I₁ I₂
        exact ⟨I₁, I₂⟩
      · rw [eval_ne z₁] at hc
        have he : b - (j + 1) ≠ 0 := by simpa using hc
        exact ⟨b - (j + 1), by omega, j + 1, rfl, by omega, I₁, I₂⟩
    · exact RelCT.of_false fun _ _ h => hm h.1
  · exact RelCT.of_false fun _ _ h => hj h.2.1

end VG.Proof.AesGcmSiv.X86_64
