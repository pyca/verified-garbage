import VerifiedGarbage.Proof.AesGcmSiv.X86_64.CryptCT

/-!
# AES-GCM-SIV on x86-64: the keys are constant time

Untrusted: everything here is checked by Lean. Both runs derive the same
number of blocks (`rounds / 2 − 1`), from a slot; the code around the calls
passes the taint analysis, and each call has the same arguments in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl CtrCall ctr_rel ctr_call KeyCall key_rel key_call)

/-- A run of `derive` before block `i`. -/
structure DCInv (K W SP : Addr) (R : Nat) (N A D : Addr) (al n i : Nat) (t : State) : Prop where
  one : One K W SP R N A D al n t
  nonce : Buf K W SP t N 12
  rbx : t.gpr .rbx = BitVec.ofNat 64 i
  rbp : t.gpr .rbp = BitVec.ofNat 64 (R / 2 - 1)
  r12 : t.gpr .r12 = W + BitVec.ofNat 64 (16 + 8 * i)

theorem DCInv.agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n i : Nat} {t₁ t₂ : State}
    (h₁ : DCInv K W SP R N A D al n i t₁) (h₂ : DCInv K W SP R N A D al n i t₂) :
    Both K W SP R N A D al n [.rbx, .rbp, .r12] t₁ t₂ :=
  ⟨h₁.one, h₂.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.rbx, h₂.rbx]
    · rw [h₁.rbp, h₂.rbp]
    · rw [h₁.r12, h₂.r12]⟩

/-- A step of `derive`, after its arguments. -/
def DArgs (K W SP : Addr) (R : Nat) (N A D : Addr) (al n i : Nat) (t : State) : Prop :=
  CtrCall t K (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 128) (W + BitVec.ofNat 64 2048) R 1 ∧
    t.gpr .rsp = SP ∧ DCInv K W SP R N A D al n i t

theorem dArgs_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n i : Nat}
    {t : State} (I : DCInv K W SP R N A D al n i t) :
    WP isa (.block (deriveBlock ++ ([.mov .rdi (.reg .r13)] : List Instr) ++ ctrArgs ++ ptr .rcx .r15 bO)) t
      (DArgs K W SP R N A D al n i) := by
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, rcx, r8, r9, hg₁, hrd₁, hwr₁⟩ :=
    derArgs_ok I.one.env I.one.sl I.nonce I.rbx
  have E₁ : Env K W SP t₁ := I.one.env.keep (fun r hr => hg₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
    hrd₁ hwr₁
  have f₁ : Frame [⟨W + BitVec.ofNat 64 112, 32⟩] t.mem t₁.mem := by
    rw [hm₁]
    exact ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 128) (n := 8) (e := 112) (k := 32) (by decide)
        (by decide) (by have := L.ww; omega)) |>.writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 136) (n := 8) (e := 112) (k := 32) (by decide)
        (by decide) (by have := L.ww; omega))
  exact WP.of_runBlock ⟨t₁, run₁, cargs L E₁ hR (keyK L E₁.perm) (c := 112) (by decide)
    (srcW L E₁.perm (t := 128) (k := 16 * 1) (by decide)) (L.w_w (.inr (by decide)) (by decide) (by decide))
    (L.k_w' (by decide)) (E₁.perm.wC (by decide)) rdi rsi rdx rcx r8 r9, E₁.rsp,
    ⟨E₁, I.one.sl.of_frame f₁ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      hwr₁.trans I.one.wr⟩, I.nonce.of_eq hrd₁ hwr₁, by rw [hg₁ _ (by simp), I.rbx], by rw [hg₁ _ (by simp), I.rbp],
    by rw [hg₁ _ (by simp), I.r12]⟩

theorem dCalled_wp (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n i : Nat}
    {t : State} (h : DArgs K W SP R N A D al n i t) :
    WP isa (.call v.ctr.callee.name v.ctr.callee.code) t (DCInv K W SP R N A D al n i) := by
  obtain ⟨cc, hsp, I⟩ := h
  refine WP.mono (ctr_call v.ctr cc) fun t₂ P => ?_
  have fc := P.frame
  rw [hsp] at fc
  refine ⟨⟨I.one.env.of_saved P.saved P.rd P.wr, I.one.sl.of_frame fc (fun q hq => ?_), P.wr.trans I.one.wr⟩,
    I.nonce.of_eq P.rd P.wr, by rw [P.saved _ (by decide), I.rbx], by rw [P.saved _ (by decide), I.rbp],
    by rw [P.saved _ (by decide), I.r12]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

theorem dPost_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n i : Nat}
    (hi : i < R / 2 - 1) {t : State} (I : DCInv K W SP R N A D al n i t) :
    WP isa (.block derPost) t fun t' =>
      DCInv K W SP R N A D al n (i + 1) t' ∧ t'.zf = some (decide (i + 1 = R / 2 - 1)) := by
  obtain ⟨t', run', hm', bx', bp', r12', zf', hg', hrd', hwr'⟩ :=
    derPost_ok I.one.env hi (by omega) I.rbx I.rbp I.r12
  have f' : Frame [⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩] t.mem t'.mem := by
    rw [hm']; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact WP.of_runBlock ⟨t', run', ⟨⟨I.one.env.keep hg' hrd' hwr', I.one.sl.of_frame f' (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by omega)) (by decide) (by omega)),
    hwr'.trans I.one.wr⟩, I.nonce.of_eq hrd' hwr', bx', bp', r12'⟩, zf'⟩

theorem dArgs_check : ∃ hc, (taint.check (sivT [.rbx, .rbp, .r12])
    (.block (deriveBlock ++ ([.mov .rdi (.reg .r13)] : List Instr) ++ ctrArgs ++ ptr .rcx .r15 bO)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dPost_check : ∃ hc, (taint.check (sivT [.rbx, .rbp, .r12]) (.block derPost) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A step of `derive`, in two runs before the same block. -/
theorem dStep_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) (hn : n ≤ 2 ^ 64) {i : Nat} (hi : i < R / 2 - 1) :
    RelCT isa (fun t₁ t₂ => DCInv K W SP R N A D al n i t₁ ∧ DCInv K W SP R N A D al n i t₂)
      (.seq (.block (deriveBlock ++ ([.mov .rdi (.reg .r13)] : List Instr) ++ ctrArgs ++ ptr .rcx .r15 bO))
        (.seq (callCtr v.callees) (.block derPost)))
      fun t₁ t₂ => (DCInv K W SP R N A D al n (i + 1) t₁ ∧ t₁.zf = some (decide (i + 1 = R / 2 - 1))) ∧
        (DCInv K W SP R N A D al n (i + 1) t₂ ∧ t₂.zf = some (decide (i + 1 = R / 2 - 1))) := by
  have r₁ := (rel_taintC [.rbx, .rbp, .r12] (P := fun t₁ t₂ => DCInv K W SP R N A D al n i t₁ ∧
      DCInv K W SP R N A D al n i t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2) dArgs_check).wp
    (F₁ := DArgs K W SP R N A D al n i) (F₂ := DArgs K W SP R N A D al n i)
    fun t₁ t₂ h => ⟨dArgs_wp L hR h.1, dArgs_wp L hR h.2⟩
  have r₂ := (ctr_rel v.ctr (P := fun t₁ t₂ => True ∧ DArgs K W SP R N A D al n i t₁ ∧
      DArgs K W SP R N A D al n i t₂)
    fun t₁ t₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1]⟩).wp
    (F₁ := DCInv K W SP R N A D al n i) (F₂ := DCInv K W SP R N A D al n i)
    fun t₁ t₂ h => ⟨dCalled_wp v L h.2.1, dCalled_wp v L h.2.2⟩
  have r₃ := (rel_taintC [.rbx, .rbp, .r12] (P := fun t₁ t₂ => True ∧ DCInv K W SP R N A D al n i t₁ ∧
      DCInv K W SP R N A D al n i t₂) hDW hn (fun t₁ t₂ h => h.2.1.agree h.2.2) dPost_check).wp
    (F₁ := fun (t' : State) => DCInv K W SP R N A D al n (i + 1) t' ∧ t'.zf = some (decide (i + 1 = R / 2 - 1)))
    (F₂ := fun (t' : State) => DCInv K W SP R N A D al n (i + 1) t' ∧ t'.zf = some (decide (i + 1 = R / 2 - 1)))
    fun t₁ t₂ h => ⟨dPost_wp L hR hi h.2.1, dPost_wp L hR hi h.2.2⟩
  exact (RelCT.seq r₁ (RelCT.seq r₂ r₃)).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

theorem dInit_check : ∃ hc, (taint.check (sivT []) (.block (([.mov32 .rbx (imm 0)] : List Instr) ++ ptr .r12 .r15 akO ++
    ([.mov .rbp (.mem (at_ .r15 roundsO)), .shift .shr .rbp 1, .alu .sub .rbp (imm 1)] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem slots_derR {K W SP : Addr} (L : Lay K W SP) : ∀ q ∈ derR W SP, (⟨W + BitVec.ofNat 64 272, 48⟩ : Region).Disjoint q := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

theorem dInit_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    {σ : State} (O : One K W SP R N A D al n σ) (hN : Buf K W SP σ N 12) :
    WP isa (.block (([.mov32 .rbx (imm 0)] : List Instr) ++ ptr .r12 .r15 akO ++
      ([.mov .rbp (.mem (at_ .r15 roundsO)), .shift .shr .rbp 1, .alu .sub .rbp (imm 1)] : List Instr))) σ
      (DCInv K W SP R N A D al n 0) :=
  WP.mono (derInit_ok O.env hR O.sl) fun t I =>
    ⟨⟨I.env, O.sl.of_frame I.frame (slots_derR L), I.wr.trans O.wr⟩, hN.of_eq I.rd I.wr, I.rbx, I.rbp,
      by rw [I.r12]⟩

/-- `derive`, in two runs with the same public arguments. -/
theorem derive_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) (hn : n ≤ 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → (One K W SP R N A D al n t₁ ∧ Buf K W SP t₁ N 12) ∧
      (One K W SP R N A D al n t₂ ∧ Buf K W SP t₂ N 12)) :
    RelCT isa P (derive v.callees) fun t₁ t₂ =>
      DCInv K W SP R N A D al n (R / 2 - 1) t₁ ∧ DCInv K W SP R N A D al n (R / 2 - 1) t₂ := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.1, (hP _ _ h).2.1, fun _ h => nomatch h⟩)
    dInit_check).wp (F₁ := DCInv K W SP R N A D al n 0) (F₂ := DCInv K W SP R N A D al n 0)
    fun t₁ t₂ h => ⟨dInit_wp L hR (hP _ _ h).1.1 (hP _ _ h).1.2, dInit_wp L hR (hP _ _ h).2.1 (hP _ _ h).2.2⟩
  refine RelCT.seq r₁ ?_
  refine (RelCT.loop (fun m t₁ t₂ => ∃ i, m = (R / 2 - 1) - i ∧ i < R / 2 - 1 ∧ DCInv K W SP R N A D al n i t₁ ∧
      DCInv K W SP R N A D al n i t₂) (fun m => ?_) ((R / 2 - 1) - 0)).mono
    (fun t₁ t₂ h => ⟨0, rfl, by omega, h.2.1, h.2.2⟩) fun _ _ h => h
  refine RelCT.exists_ fun i => ?_
  by_cases hi : i < R / 2 - 1
  · by_cases hm : m = (R / 2 - 1) - i
    · subst hm
      refine (dStep_rel v L hR hDW hn hi).mono (fun t₁ t₂ h => ⟨h.2.2.1, h.2.2.2⟩)
        fun t₁ t₂ ⟨⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ => ⟨by rw [eval_ne z₁, eval_ne z₂], fun hc => ?_, fun hc => ?_⟩
      · rw [eval_ne z₁] at hc
        have he : i + 1 = R / 2 - 1 := by simpa using hc
        rw [he] at I₁ I₂
        exact ⟨I₁, I₂⟩
      · rw [eval_ne z₁] at hc
        have he : i + 1 ≠ R / 2 - 1 := by simpa using hc
        exact ⟨(R / 2 - 1) - (i + 1), by omega, i + 1, rfl, by omega, I₁, I₂⟩
    · exact RelCT.of_false fun _ _ h => hm h.1
  · exact RelCT.of_false fun _ _ h => hi h.2.1

theorem expArgs_check : ∃ hc, (taint.check (sivT []) (.block (ptr .rdi .r15 ekO ++
    ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6), .alu .add .rsi (.reg .rsi),
      .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO ++ ptr .rcx .r15 scrO)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem hkey_check : ∃ hc, (taint.check (sivT []) (.block hkey) hc).isSome = true := ⟨_, by taint_decide⟩

theorem expArgs_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    {t : State} (O : One K W SP R N A D al n t) :
    WP isa (.block (ptr .rdi .r15 ekO ++ ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6),
      .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO ++
      ptr .rcx .r15 scrO)) t fun t₁ =>
      KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 2048)
        (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP := by
  obtain ⟨t₁, run₁, -, rdi, rsi, rdx, rcx, hg₁, hrd₁, hwr₁⟩ := expArgs_ok hR O.env O.sl
  have E₁ : Env K W SP t₁ := O.env.of_saved hg₁ hrd₁ hwr₁
  have hl : Spec.GcmSiv.keyLen R = 16 ∨ Spec.GcmSiv.keyLen R = 32 := by unfold Spec.GcmSiv.keyLen; omega
  exact WP.of_runBlock ⟨t₁, run₁, kargs L E₁ hl rdi rsi rdx rcx, E₁.rsp⟩

/-- `keys`, in two runs with the same public arguments. -/
theorem keys_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 4096⟩) (hn : n ≤ 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → (One K W SP R N A D al n t₁ ∧ Buf K W SP t₁ N 12) ∧
      (One K W SP R N A D al n t₂ ∧ Buf K W SP t₂ N 12)) :
    RelCT isa P (keys v.callees) fun _ _ => True := by
  refine RelCT.seq (derive_rel v L hR hDW hn hP) ?_
  have one_exp : ∀ {t : State}, One K W SP R N A D al n t → WP isa (.seq (.block (ptr .rdi .r15 ekO ++
      ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6), .alu .add .rsi (.reg .rsi),
        .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO ++ ptr .rcx .r15 scrO))
      (.call v.key.fn.name v.key.fn.code)) t (One K W SP R N A D al n) :=
    fun O => WP.mono (expand_ok v L hR O.env O.sl) fun t' X => ⟨X.env, O.sl.of_frame X.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm), X.wr.trans O.wr⟩
  have r₁ := (rel_taintC [] (P := fun t₁ t₂ => DCInv K W SP R N A D al n (R / 2 - 1) t₁ ∧
      DCInv K W SP R N A D al n (R / 2 - 1) t₂) hDW hn (fun t₁ t₂ h => ⟨h.1.one, h.2.one, fun _ h => nomatch h⟩)
    expArgs_check).wp
    (F₁ := fun (t₁ : State) => KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 512)
      (W + BitVec.ofNat 64 2048) (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP)
    (F₂ := fun (t₁ : State) => KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 512)
      (W + BitVec.ofNat 64 2048) (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨expArgs_wp L hR h.1.one, expArgs_wp L hR h.2.one⟩
  have r₂ := (RelCT.seq r₁ (key_rel v.key fun t₁ t₂ h =>
    ⟨_, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)).wp
    (F₁ := One K W SP R N A D al n) (F₂ := One K W SP R N A D al n)
    fun t₁ t₂ h => ⟨one_exp h.1.one, one_exp h.2.one⟩
  exact RelCT.seq r₂ (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨h.2.1, h.2.2, fun _ h => nomatch h⟩) hkey_check)

end VG.Proof.AesGcmSiv.X86_64
