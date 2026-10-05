import VerifiedGarbage.Proof.AesGcmSiv.X86_64.CryptCT

/-!
# AES-GCM-SIV on x86-64: the keys and POLYVAL are constant time

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
  CtrCall t K (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 128) (W + BitVec.ofNat 64 1768) R 1 ∧
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
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {i : Nat} (hi : i < R / 2 - 1) :
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

theorem slots_derR {K W SP : Addr} (L : Lay K W SP) : ∀ q ∈ derR W SP, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint q := by
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
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {P : State → State → Prop}
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
      KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 1768)
        (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP := by
  obtain ⟨t₁, run₁, -, rdi, rsi, rdx, rcx, hg₁, hrd₁, hwr₁⟩ := expArgs_ok hR O.env O.sl
  have E₁ : Env K W SP t₁ := O.env.of_saved hg₁ hrd₁ hwr₁
  have hl : Spec.GcmSiv.keyLen R = 16 ∨ Spec.GcmSiv.keyLen R = 32 := by unfold Spec.GcmSiv.keyLen; omega
  exact WP.of_runBlock ⟨t₁, run₁, kargs L E₁ hl rdi rsi rdx rcx, E₁.rsp⟩

/-- `keys`, in two runs with the same public arguments. -/
theorem keys_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {P : State → State → Prop}
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
    (F₁ := fun (t₁ : State) => KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248)
      (W + BitVec.ofNat 64 1768) (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP)
    (F₂ := fun (t₁ : State) => KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248)
      (W + BitVec.ofNat 64 1768) (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨expArgs_wp L hR h.1.one, expArgs_wp L hR h.2.one⟩
  have r₂ := (RelCT.seq r₁ (key_rel v.key fun t₁ t₂ h =>
    ⟨_, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)).wp
    (F₁ := One K W SP R N A D al n) (F₂ := One K W SP R N A D al n)
    fun t₁ t₂ h => ⟨one_exp h.1.one, one_exp h.2.one⟩
  exact RelCT.seq r₂ (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨h.2.1, h.2.2, fun _ h => nomatch h⟩) hkey_check)

end VG.Proof.AesGcmSiv.X86_64

/-!
## POLYVAL is constant time

Untrusted: everything here is checked by Lean. Both runs absorb the same
chunks of blocks: their number depends only on the lengths, which are
public; the code around each call of `vg_ghash` passes the taint analysis,
and each call has the same arguments in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl GhCall gh_rel gh_call toNat_ofNat_of_lt)

/-- `(a; (b; c)); d`, related as `a; (b; (c; d))`. -/
theorem rel_assoc3 {P Q : State → State → Prop} {a b c d : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b c)) d) Q) : RelCT isa P (.seq a (.seq b (.seq c d))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ d₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ d₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ c₁)) d₁) (.seq (.seq a₂ (.seq b₂ c₂)) d₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- `(a; (b; (c; (d; e)))); g`, related as `a; (b; (c; (d; (e; g))))`. -/
theorem rel_assoc5 {P Q : State → State → Prop} {a b c d e g : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c (.seq d e)))) g) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d (.seq e g))))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
  | seq d₁ e₁ => cases e₁ with | seq e₁' g₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
  | seq d₂ e₂ => cases e₂ with | seq e₂' g₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ e₁')))) g₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ e₂')))) g₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-! ## The chunks -/

/-- A run of the chunks of `b` blocks at `Q`, after `d` of them, with
`nr` bytes left after them. -/
structure AInv (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (Q : Addr) (b nr d : Nat) (t : State) :
    Prop where
  one : One K W SP R N A D al n t
  buf : Buf K W SP t Q (16 * b)
  res : Buf K W SP t (Q + BitVec.ofNat 64 (16 * b)) nr
  r12 : t.gpr .r12 = Q + BitVec.ofNat 64 (16 * d)
  rbx : t.gpr .rbx = BitVec.ofNat 64 (b - d)
  rbp : t.gpr .rbp = BitVec.ofNat 64 nr

theorem AInv.agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d : Nat} {t₁ t₂ : State}
    (h₁ : AInv K W SP R N A D al n Q b nr d t₁) (h₂ : AInv K W SP R N A D al n Q b nr d t₂) :
    Both K W SP R N A D al n [.r12, .rbx, .rbp] t₁ t₂ :=
  ⟨h₁.one, h₂.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r12, h₂.r12]
    · rw [h₁.rbx, h₂.rbx]
    · rw [h₁.rbp, h₂.rbp]⟩

/-- A chunk after its call, or up to it: the run, `k`, and the call's arguments. -/
structure AMid (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (Q : Addr) (b nr d k : Nat) (t : State) :
    Prop where
  inv : AInv K W SP R N A D al n Q b nr d t
  r14 : t.gpr .r14 = BitVec.ofNat 64 k

theorem AMid.agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d k : Nat} {t₁ t₂ : State}
    (h₁ : AMid K W SP R N A D al n Q b nr d k t₁) (h₂ : AMid K W SP R N A D al n Q b nr d k t₂) :
    Both K W SP R N A D al n [.r12, .rbx, .rbp, .r14] t₁ t₂ :=
  ⟨h₁.inv.one, h₂.inv.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.inv.r12, h₂.inv.r12]
    · rw [h₁.inv.rbx, h₂.inv.rbx]
    · rw [h₁.inv.rbp, h₂.inv.rbp]
    · rw [h₁.r14, h₂.r14]⟩

theorem chunkPre_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d : Nat}
    (hd : d < b) {t : State} (I : AInv K W SP R N A D al n Q b nr d t) :
    WP isa (.seq (.block [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)])
      (.seq (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block []))
      (.seq (.block (([.mov .rsi (.reg .r12)] : List Instr) ++ ptr .rdi .r15 revO))
      (.seq revLoop (.block (ghArgs ++ ptr .rdx .r15 revO ++ ([.mov .rcx (.reg .r14)] : List Instr))))))) t
      fun t₅ => GhCall t₅ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₅.gpr .rsp = SP ∧
        AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₅ := by
  have hQ : Buf K W SP t (Q + BitVec.ofNat 64 (16 * d)) (16 * (b - d)) := I.buf.slice (by omega)
  refine WP.mono (chunkPre_ok L I.one.env (by omega) hQ I.r12 I.rbx) fun t₅ Pr => ⟨Pr.call, Pr.env.rsp, ?_, Pr.r14⟩
  refine ⟨⟨Pr.env, I.one.sl.of_frame Pr.frame (fun q hq => ?_), Pr.wr.trans I.one.wr⟩, I.buf.of_eq Pr.rd Pr.wr,
    I.res.of_eq Pr.rd Pr.wr, by rw [Pr.regs _ (by simp), I.r12], by rw [Pr.regs _ (by simp), I.rbx], by rw [Pr.regs _ (by simp), I.rbp]⟩
  simp only [List.mem_singleton] at hq; subst hq
  exact L.w_w (.inl (by decide)) (by decide) (by omega)

theorem chunkCalled_wp (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    {Q : Addr} {b nr d k : Nat} {t : State} (h : GhCall t (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80)
      (W + BitVec.ofNat 64 488) (W + BitVec.ofNat 64 1512) k ∧ t.gpr .rsp = SP ∧
      AMid K W SP R N A D al n Q b nr d k t) :
    WP isa (.call v.gh.fn.name v.gh.fn.code) t (AMid K W SP R N A D al n Q b nr d k) := by
  obtain ⟨gc, hsp, M⟩ := h
  refine WP.mono (gh_call v.gh gc) fun t₆ P => ?_
  have fc := P.frame
  rw [hsp] at fc
  refine ⟨⟨⟨M.inv.one.env.of_saved P.saved P.rd P.wr, M.inv.one.sl.of_frame fc (fun q hq => ?_),
    P.wr.trans M.inv.one.wr⟩, M.inv.buf.of_eq P.rd P.wr, M.inv.res.of_eq P.rd P.wr, by rw [P.saved _ (by decide), M.inv.r12],
    by rw [P.saved _ (by decide), M.inv.rbx], by rw [P.saved _ (by decide), M.inv.rbp]⟩,
    by rw [P.saved _ (by decide), M.r14]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- The end of a chunk: the pointer and the count past it. -/
theorem chunkEnd_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d : Nat} (hd : d < b)
    {t : State} (M : AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t) :
    WP isa (.block [.mov .rax (.reg .r14), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .r12 (.reg .rax), .alu .sub .rbx (.reg .r14)]) t
      fun t' => AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t' ∧
        t'.zf = some (decide (b - (d + min (b - d) 64) = 0)) := by
  have hbl : b < 2 ^ 60 := by have := M.inv.buf.lt; omega
  refine WP.of_runBlock ⟨_, by srun [], ?_, ?_⟩
  · refine ⟨⟨M.inv.one.env.keep (fun r hr => ?_) rfl rfl, M.inv.one.sl, M.inv.one.wr⟩, M.inv.buf.of_eq rfl rfl,
      M.inv.res.of_eq rfl rfl, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, M.inv.r12, M.r14,
        Proof.AesGcm.X86_64.times16_val, add_ofNat_assoc, Nat.mul_add]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, M.inv.rbx, M.r14]
      rw [Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega), Nat.sub_sub]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, M.inv.rbp]
  · simp only [zf_setReg, zf_arithFlags, gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, M.inv.rbx,
      M.r14, Proof.AesGcm.X86_64.sub_beq (show b - d < 2 ^ 64 by omega) (show min (b - d) 64 < 2 ^ 64 by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

theorem chunkPre_check : ∃ hc, (taint.check (sivT [.r12, .rbx, .rbp])
    (.seq (.block [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)])
      (.seq (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block []))
      (.seq (.block (([.mov .rsi (.reg .r12)] : List Instr) ++ ptr .rdi .r15 revO))
      (.seq revLoop (.block (ghArgs ++ ptr .rdx .r15 revO ++ ([.mov .rcx (.reg .r14)] : List Instr))))))) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem chunkEnd_check : ∃ hc, (taint.check (sivT [.r12, .rbx, .rbp, .r14])
    (.block [.mov .rax (.reg .r14), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .r12 (.reg .rax), .alu .sub .rbx (.reg .r14)])
    hc).isSome = true := ⟨_, by taint_decide⟩

/-- A chunk, in two runs after the same blocks. -/
theorem chunk_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {Q : Addr} {b nr d : Nat} (hd : d < b) :
    RelCT isa (fun t₁ t₂ => AInv K W SP R N A D al n Q b nr d t₁ ∧ AInv K W SP R N A D al n Q b nr d t₂)
      (absorbChunk v.callees)
      fun t₁ t₂ => (AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t₁ ∧
          t₁.zf = some (decide (b - (d + min (b - d) 64) = 0))) ∧
        (AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t₂ ∧
          t₂.zf = some (decide (b - (d + min (b - d) 64) = 0))) := by
  refine rel_assoc5 ?_
  have r₁ := (rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ => AInv K W SP R N A D al n Q b nr d t₁ ∧
      AInv K W SP R N A D al n Q b nr d t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2) chunkPre_check).wp
    (F₁ := fun (t₅ : State) => GhCall t₅ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₅.gpr .rsp = SP ∧
        AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₅)
    (F₂ := fun (t₅ : State) => GhCall t₅ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₅.gpr .rsp = SP ∧
        AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₅)
    fun t₁ t₂ h => ⟨chunkPre_wp L hd h.1, chunkPre_wp L hd h.2⟩
  have r₂ := (gh_rel v.gh (P := fun t₁ t₂ => True ∧ (GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80)
        (W + BitVec.ofNat 64 488) (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₁.gpr .rsp = SP ∧
        AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₁) ∧
      (GhCall t₂ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₂.gpr .rsp = SP ∧
        AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₂))
    fun t₁ t₂ h => ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1]⟩).wp
    (F₁ := AMid K W SP R N A D al n Q b nr d (min (b - d) 64))
    (F₂ := AMid K W SP R N A D al n Q b nr d (min (b - d) 64))
    fun t₁ t₂ h => ⟨chunkCalled_wp v L h.2.1, chunkCalled_wp v L h.2.2⟩
  have r₃ := (rel_taintC [.r12, .rbx, .rbp, .r14] (P := fun t₁ t₂ => True ∧
      AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₁ ∧ AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₂)
      hDW hn (fun t₁ t₂ h => h.2.1.agree h.2.2) chunkEnd_check).wp
    (F₁ := fun (t' : State) => AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t' ∧
      t'.zf = some (decide (b - (d + min (b - d) 64) = 0)))
    (F₂ := fun (t' : State) => AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t' ∧
      t'.zf = some (decide (b - (d + min (b - d) 64) = 0)))
    fun t₁ t₂ h => ⟨chunkEnd_wp hd h.2.1, chunkEnd_wp hd h.2.2⟩
  exact (RelCT.seq r₁ (RelCT.seq r₂ r₃)).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

/-- The chunks, in two runs. -/
theorem chunks_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {Q : Addr} {b nr : Nat} (hb : 1 ≤ b) :
    RelCT isa (fun t₁ t₂ => AInv K W SP R N A D al n Q b nr 0 t₁ ∧ AInv K W SP R N A D al n Q b nr 0 t₂)
      (.loop (absorbChunk v.callees) .ne)
      fun t₁ t₂ => AInv K W SP R N A D al n Q b nr b t₁ ∧ AInv K W SP R N A D al n Q b nr b t₂ := by
  refine (RelCT.loop (fun m t₁ t₂ => ∃ d, m = b - d ∧ d < b ∧ AInv K W SP R N A D al n Q b nr d t₁ ∧
      AInv K W SP R N A D al n Q b nr d t₂) (fun m => ?_) (b - 0)).mono
    (fun t₁ t₂ h => ⟨0, rfl, hb, h⟩) fun _ _ h => h
  refine RelCT.exists_ fun d => ?_
  by_cases hd : d < b
  · by_cases hm : m = b - d
    · subst hm
      refine (chunk_rel v L hDW hn hd).mono (fun t₁ t₂ h => ⟨h.2.2.1, h.2.2.2⟩)
        fun t₁ t₂ ⟨⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ => ⟨by rw [eval_ne z₁, eval_ne z₂], fun hc => ?_, fun hc => ?_⟩
      · rw [eval_ne z₁] at hc
        have he : d + min (b - d) 64 = b := by simp at hc; omega
        rw [he] at I₁ I₂
        exact ⟨I₁, I₂⟩
      · rw [eval_ne z₁] at hc
        have he : b - (d + min (b - d) 64) ≠ 0 := by simpa using hc
        exact ⟨b - (d + min (b - d) 64), by omega, d + min (b - d) 64, rfl, by omega, I₁, I₂⟩
    · exact RelCT.of_false fun _ _ h => hm h.1
  · exact RelCT.of_false fun _ _ h => hd h.2.1

/-! ## The last bytes and `absorb` -/

theorem tailPre_check : ∃ hc, (taint.check (sivT [.r12, .rbx, .rbp])
    (.seq (.block (zero16 bO ++ ptr .rdi .r15 bO ++ ([.mov .rsi (.reg .r12), .mov .rcx (.reg .rbp)] : List Instr)))
      (.seq copyLoop (.block (([.mov .rax (.mem (at_ .r15 bO)), .mov .rdx (.mem (at_ .r15 (bO + 8))), .bswap .rax,
        .bswap .rdx, .store (at_ .r15 revO) .rdx, .store (at_ .r15 (revO + 8)) .rax] : List Instr) ++ ghArgs ++
        ptr .rdx .r15 revO ++ ([.mov32 .rcx (imm 1)] : List Instr))))) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The last bytes, in two runs. -/
theorem absTail_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {Q : Addr} {b nr : Nat} (hr1 : 1 ≤ nr)
    (hr : nr < 16) :
    RelCT isa (fun t₁ t₂ => AInv K W SP R N A D al n Q b nr b t₁ ∧ AInv K W SP R N A D al n Q b nr b t₂)
      (absorbTail v.callees) fun _ _ => True := by
  have pre : ∀ {t : State}, AInv K W SP R N A D al n Q b nr b t → WP isa _ t fun t₃ =>
      GhCall t₃ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₃.gpr .rsp = SP := fun I =>
    WP.mono (tailPre_ok L I.one.env hr1 hr I.res I.r12 I.rbp) fun _ Tp => ⟨Tp.call, Tp.env.rsp⟩
  refine rel_assoc3 (RelCT.seq ((rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ =>
      AInv K W SP R N A D al n Q b nr b t₁ ∧ AInv K W SP R N A D al n Q b nr b t₂) hDW hn
      (fun t₁ t₂ h => h.1.agree h.2) tailPre_check).wp
    (F₁ := fun (t₃ : State) => GhCall t₃ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₃.gpr .rsp = SP)
    (F₂ := fun (t₃ : State) => GhCall t₃ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₃.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨pre h.1, pre h.2⟩) ?_)
  exact gh_rel v.gh fun t₁ t₂ h => ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩

/-- What `absorb` is given: `nb` bytes at `Q`. -/
structure AbsIn (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (Q : Addr) (nb : Nat) (t : State) : Prop where
  one : One K W SP R N A D al n t
  buf : Buf K W SP t Q nb
  r12 : t.gpr .r12 = Q
  rbp : t.gpr .rbp = BitVec.ofNat 64 nb

theorem absHead_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {nb : Nat} {t : State}
    (h : AbsIn K W SP R N A D al n Q nb t) :
    WP isa (.block [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)]) t
      fun t₁ => AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₁ ∧ t₁.zf = some (decide (nb / 16 = 0)) := by
  have hn := h.buf.lt
  have hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 nb)
  rw [toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  refine WP.of_runBlock ⟨_, by srun [], ?_, ?_⟩
  · refine ⟨⟨h.one.env.keep (fun r hr => ?_) rfl rfl, h.one.sl, h.one.wr⟩, (h.buf.take (by omega)).of_eq rfl rfl,
      (h.buf.slice (by omega)).of_eq rfl rfl, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h.r12, Nat.mul_zero,
        BitVec.add_zero]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h.rbp,
        Proof.AesGcm.X86_64.shr4 _ hn, Nat.sub_zero]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h.rbp, hand]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
      reduceCtorEq, h.rbp, Proof.AesGcm.X86_64.shr4 _ hn]
    rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]

theorem absHead_check : ∃ hc, (taint.check (sivT [.r12, .rbp])
    (.block [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem absTest_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d : Nat} (hnr : nr < 16)
    {t : State} (I : AInv K W SP R N A D al n Q b nr d t) :
    WP isa (.block [.alu .test .rbp (.reg .rbp)]) t fun t' =>
      AInv K W SP R N A D al n Q b nr d t' ∧ t'.zf = some (decide (nr = 0)) := by
  refine WP.of_runBlock ⟨_, by srun [], ?_, ?_⟩
  · exact ⟨⟨I.one.env.keep (fun _ _ => by simp only [gpr_arithFlags]) rfl rfl, I.one.sl, I.one.wr⟩,
      I.buf.of_eq rfl rfl, I.res.of_eq rfl rfl, by simp only [gpr_arithFlags, I.r12], by simp only [gpr_arithFlags, I.rbx],
      by simp only [gpr_arithFlags, I.rbp]⟩
  · simp only [zf_arithFlags, I.rbp]
    rw [Proof.AesGcm.X86_64.and_self_beq (by omega)]

/-- `absorb`, in two runs with the same public arguments. -/
theorem absorb_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {Q : Addr} {nb : Nat} {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → AbsIn K W SP R N A D al n Q nb t₁ ∧ AbsIn K W SP R N A D al n Q nb t₂) :
    RelCT isa P (absorb v.callees) fun _ _ => True := by
  have r₁ := (rel_taintC [.r12, .rbp] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.one, (hP _ _ h).2.one, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [(hP _ _ h).1.r12, (hP _ _ h).2.r12]
      · rw [(hP _ _ h).1.rbp, (hP _ _ h).2.rbp]⟩) absHead_check).wp
    (F₁ := fun (t₁ : State) => AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₁ ∧ t₁.zf = some (decide (nb / 16 = 0)))
    (F₂ := fun (t₁ : State) => AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₁ ∧ t₁.zf = some (decide (nb / 16 = 0)))
    fun t₁ t₂ h => ⟨absHead_wp (hP _ _ h).1, absHead_wp (hP _ _ h).2⟩
  have r₂ : RelCT isa (fun t₁ t₂ => True ∧ (AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₁ ∧
        t₁.zf = some (decide (nb / 16 = 0))) ∧ (AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₂ ∧
        t₂.zf = some (decide (nb / 16 = 0))))
      (.ite .e (.block []) (.loop (absorbChunk v.callees) .ne))
      fun t₁ t₂ => AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₁ ∧
        AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₂ := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [eval_e h.2.1.2, eval_e h.2.2.2]) ?_ ?_
    · refine RelCT.block_nil fun t₁ t₂ h => ?_
      have h0 : nb / 16 = 0 := by have := h.2; rw [eval_e h.1.2.1.2] at this; simpa using this
      have a := h.1.2.1.1
      have b := h.1.2.2.1
      rw [h0] at a b ⊢
      exact ⟨a, b⟩
    · by_cases h0 : nb / 16 = 0
      · refine RelCT.of_false fun t₁ t₂ h => ?_
        have := h.2
        rw [eval_e h.1.2.1.2] at this
        simp [h0] at this
      · exact (chunks_rel v L hDW hn (b := nb / 16) (by omega)).mono (fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩)
          fun _ _ h => h
  have r₃ := (rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ =>
      AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₁ ∧
      AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2)
      test_check).wp
    (F₁ := fun (t : State) => AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t ∧
      t.zf = some (decide (nb % 16 = 0)))
    (F₂ := fun (t : State) => AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t ∧
      t.zf = some (decide (nb % 16 = 0)))
    fun t₁ t₂ h => ⟨absTest_wp (by omega) h.1, absTest_wp (by omega) h.2⟩
  have r₄ : RelCT isa (fun t₁ t₂ => True ∧ (AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₁ ∧
        t₁.zf = some (decide (nb % 16 = 0))) ∧ (AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₂ ∧
        t₂.zf = some (decide (nb % 16 = 0))))
      (.ite .e (.block []) (absorbTail v.callees)) fun _ _ => True := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [eval_e h.2.1.2, eval_e h.2.2.2]) (RelCT.block_nil fun _ _ _ => trivial) ?_
    by_cases h0 : nb % 16 = 0
    · refine RelCT.of_false fun t₁ t₂ h => ?_
      have := h.2
      rw [eval_e h.1.2.1.2] at this
      simp [h0] at this
    · exact (absTail_rel v L hDW hn (by omega) (by omega)).mono (fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩)
        fun _ _ _ => trivial
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ r₄))

/-! ## The lengths, and `polyval` -/

theorem lensArgs_check : ∃ hc, (taint.check (sivT []) (.block (([.mov .rax (.mem (at_ .r15 lenO)),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax,
    .store (at_ .r15 bO) .rax, .mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 (bO + 8)) .rax] :
      List Instr) ++ ghArgs ++ ptr .rdx .r15 bO ++ ([.mov32 .rcx (imm 1)] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `lens`, in two runs with the same public arguments. -/
theorem lens_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → One K W SP R N A D al n t₁ ∧ One K W SP R N A D al n t₂) :
    RelCT isa P (lens v.callees) fun _ _ => True := by
  have pre : ∀ {t : State}, One K W SP R N A D al n t → WP isa (.block (([.mov .rax (.mem (at_ .r15 lenO)),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax,
      .store (at_ .r15 bO) .rax, .mov .rax (.mem (at_ .r15 alenO)), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax, .store (at_ .r15 (bO + 8)) .rax] :
        List Instr) ++ ghArgs ++ ptr .rdx .r15 bO ++ ([.mov32 .rcx (imm 1)] : List Instr))) t fun t₁ =>
      GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 128)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₁.gpr .rsp = SP := fun O => by
    obtain ⟨t₁, run₁, -, rdi₁, rsi₁, r8₁, rdx₁, rcx₁, hg₁, hrd₁, hwr₁⟩ := lensArgs_ok O.env O.sl.alen O.sl.len hal hn'
    have E₁ : Env K W SP t₁ := O.env.of_saved hg₁ hrd₁ hwr₁
    exact WP.of_runBlock ⟨t₁, run₁, gargs L E₁ (d := 128) (n := 1) (by decide) (by decide) rdi₁ rsi₁ rdx₁ rcx₁ r8₁,
      E₁.rsp⟩
  refine RelCT.seq ((rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1, (hP _ _ h).2, fun _ h => nomatch h⟩)
    lensArgs_check).wp
    (F₁ := fun (t₁ : State) => GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 128)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₁.gpr .rsp = SP)
    (F₂ := fun (t₁ : State) => GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 128)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₁.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨pre (hP _ _ h).1, pre (hP _ _ h).2⟩) ?_
  exact gh_rel v.gh fun t₁ t₂ h => ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩

theorem tagIn_check : ∃ hc, (taint.check (sivT []) (.block tagIn) hc).isSome = true := ⟨_, by taint_decide⟩

theorem polyA_check : ∃ hc, (taint.check (sivT [])
    (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem polyD_check : ∃ hc, (taint.check (sivT [])
    (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A run with the public arguments and the buffers of the additional data
and the data. -/
structure Bufs (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (t : State) : Prop where
  one : One K W SP R N A D al n t
  aad : Buf K W SP t A al
  data : Buf K W SP t D n

theorem Bufs.of_eq {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t t' : State}
    (h : Bufs K W SP R N A D al n t) (E : Env K W SP t') (hf : Frame (absR W SP) t.mem t'.mem) (L : Lay K W SP)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) : Bufs K W SP R N A D al n t' :=
  ⟨⟨E, Slots.absR L h.one.sl hf, hwr.trans h.one.wr⟩, h.aad.of_eq hrd hwr, h.data.of_eq hrd hwr⟩

theorem polyBlk_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (h : Bufs K W SP R N A D al n t) {o₁ o₂ : Nat} {Q : Addr} {nb : Nat} (hQ : Buf K W SP t Q nb)
    (h₁ : t.mem.readW (W + BitVec.ofNat 64 o₁) 64 = Q) (h₂ : t.mem.readW (W + BitVec.ofNat 64 o₂) 64 = BitVec.ofNat 64 nb)
    (ho₁ : o₁ + 8 ≤ 3816) (ho₂ : o₂ + 8 ≤ 3816) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 o₁)), .mov .rbp (.mem (at_ .r15 o₂))]) t
      fun t' => AbsIn K W SP R N A D al n Q nb t' ∧ Bufs K W SP R N A D al n t' := by
  have h15 := h.one.env.r15
  have r₁ := h.one.env.perm.wR ho₁
  have r₂ := h.one.env.perm.wR ho₂
  refine WP.of_runBlock ⟨_, by srun [h15, r₁, r₂], ?_⟩
  have E' : Env K W SP ((t.setReg .r12 (t.mem.readW (W + BitVec.ofNat 64 o₁) 64)).setReg .rbp
      (t.mem.readW (W + BitVec.ofNat 64 o₂) 64)) :=
    h.one.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]) rfl rfl
  exact ⟨⟨⟨E', h.one.sl, h.one.wr⟩, hQ.of_eq rfl rfl, by simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h₁],
    by simp only [gpr_setReg, ite_true, h₂]⟩, ⟨E', h.one.sl, h.one.wr⟩, h.aad.of_eq rfl rfl, h.data.of_eq rfl rfl⟩

theorem absorb_bufs (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    {Q : Addr} {nb : Nat} {t : State} (h : AbsIn K W SP R N A D al n Q nb t ∧ Bufs K W SP R N A D al n t) :
    WP isa (absorb v.callees) t (Bufs K W SP R N A D al n) :=
  WP.mono (absorb_ok v L h.1.one.env h.1.buf h.1.r12 h.1.rbp) fun _ P => h.2.of_eq P.env P.frame L P.rd P.wr

/-- `polyval`, in two runs with the same public arguments. -/
theorem polyval_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂) :
    RelCT isa P (polyval v.callees) fun _ _ => True := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.one, (hP _ _ h).2.one, fun _ h => nomatch h⟩)
    polyA_check).wp
    (F₁ := fun (t : State) => AbsIn K W SP R N A D al n A al t ∧ Bufs K W SP R N A D al n t)
    (F₂ := fun (t : State) => AbsIn K W SP R N A D al n A al t ∧ Bufs K W SP R N A D al n t)
    fun t₁ t₂ h => ⟨polyBlk_wp (o₁ := aadO) (o₂ := alenO) (hP _ _ h).1 (hP _ _ h).1.aad (hP _ _ h).1.one.sl.aad
        (hP _ _ h).1.one.sl.alen (by decide) (by decide),
      polyBlk_wp (o₁ := aadO) (o₂ := alenO) (hP _ _ h).2 (hP _ _ h).2.aad (hP _ _ h).2.one.sl.aad
        (hP _ _ h).2.one.sl.alen (by decide) (by decide)⟩
  have r₂ := (absorb_rel v L hDW hn (Q := A) (nb := al) (P := fun t₁ t₂ => True ∧
      (AbsIn K W SP R N A D al n A al t₁ ∧ Bufs K W SP R N A D al n t₁) ∧
      (AbsIn K W SP R N A D al n A al t₂ ∧ Bufs K W SP R N A D al n t₂))
    fun t₁ t₂ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨absorb_bufs v L h.2.1, absorb_bufs v L h.2.2⟩
  have r₃ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) polyD_check).wp
    (F₁ := fun (t : State) => AbsIn K W SP R N A D al n D n t ∧ Bufs K W SP R N A D al n t)
    (F₂ := fun (t : State) => AbsIn K W SP R N A D al n D n t ∧ Bufs K W SP R N A D al n t)
    fun t₁ t₂ h => ⟨polyBlk_wp (o₁ := dataO) (o₂ := lenO) h.2.1 h.2.1.data h.2.1.one.sl.data h.2.1.one.sl.len
        (by decide) (by decide),
      polyBlk_wp (o₁ := dataO) (o₂ := lenO) h.2.2 h.2.2.data h.2.2.one.sl.data h.2.2.one.sl.len (by decide)
        (by decide)⟩
  have r₄ := (absorb_rel v L hDW hn (Q := D) (nb := n) (P := fun t₁ t₂ => True ∧
      (AbsIn K W SP R N A D al n D n t₁ ∧ Bufs K W SP R N A D al n t₁) ∧
      (AbsIn K W SP R N A D al n D n t₂ ∧ Bufs K W SP R N A D al n t₂))
    fun t₁ t₂ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨absorb_bufs v L h.2.1, absorb_bufs v L h.2.2⟩
  have lens_bufs : ∀ {t : State}, Bufs K W SP R N A D al n t → WP isa (lens v.callees) t (Bufs K W SP R N A D al n) :=
    fun h => WP.mono (lens_ok v L h.one.env h.one.sl.alen h.one.sl.len hal hn') fun _ P =>
      h.of_eq P.env P.frame L P.rd P.wr
  have r₅ := (lens_rel v L hDW hn hal hn' (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧
      Bufs K W SP R N A D al n t₂) fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨lens_bufs h.2.1, lens_bufs h.2.2⟩
  have r₆ := rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) tagIn_check
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (RelCT.seq r₅ r₆))))

end VG.Proof.AesGcmSiv.X86_64
