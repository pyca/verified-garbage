import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5ParseCT

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (sample4K relInv taintRel relStart Rel2 ofNat64_pred ofNat64_beq_zero RelCT.postDep)
open VG.Proof.MlKem.X86_64.S4 (R4 Pre aP at' pre_of pub_scr pub_aP pub_B env_rbx start_ct)
open VG.Proof.MlDsa.X86_64.Sample (nil_regs WP.all')
open VG.Proof.MlDsa.X86_64.Sample.RejNttCT (BPre BRel body_ct)
open VG.Spec.MlKem (poly4)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (batch flags fallback finish)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem batch2_ct : RelCT isa (R4 fun σ s => Batch σ 2 0 112 0 s)
    (batch 0 112) (R4 fun σ s => Batch σ 2 0 112 4 s) := by
  refine RelCT.seq (segment_ct (K := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment_ct (K := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment_ct (K := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  exact (segment_ct (K := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide))

theorem batch3_ct : RelCT isa (R4 fun σ s => Batch σ 3 112 56 0 s)
    (batch 112 56) (R4 fun σ s => Batch σ 3 112 56 4 s) := by
  refine RelCT.seq (segment_ct (K := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment_ct (K := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (segment_ct (K := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)) ?_
  exact (segment_ct (K := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide))

structure Checked (σ s : State) : Prop where
  prior : ∃ start, Batch σ 2 0 112 4 start ∧ s.mem = start.mem ∧ Keep [.rax, .r14] start s
  r14 : s.gpr .r14 = if allFull σ 280 then 1 else 0
  zf : s.zf = some (!allFull σ 280)

theorem Checked.env {σ s : State} (h : Checked σ s) : VG.Proof.MlKem.X86_64.S4.Env σ s := by
  obtain ⟨_, hb, hm, hk⟩ := h.prior
  exact hb.sq.env.keep hm hk (by simp)

theorem check_ok {σ s : State} (hp : Pre σ) (h : Batch σ 2 0 112 4 s) :
    WP isa (.block (flags ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr))) s (Checked σ) := by
  have hj : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 280).length :=
    fun k hk => by simpa only [ite_eq_left hk] using h.j k hk
  apply WP.block_append
  refine WP.mono (flags_ok hp h.sq.env hj) fun s₁ ⟨⟨hr, hm⟩, hk⟩ => ?_
  refine WP.mono (WP.keep [.r14] (Q := fun s₂ => s₂.mem = s₁.mem ∧ s₂.gpr .r14 = s₁.gpr .r14 ∧
    s₂.zf = some ((s₁.gpr .r14).setWidth 32 == 0)) (by xrun; simp) (by decide))
    fun s₂ ⟨⟨hm', hr', hz⟩, hk'⟩ => ?_
  refine ⟨⟨s, h, hm'.trans hm, (hk.trans hk').mono (by simp)⟩, hr'.trans hr, ?_⟩
  rw [hz, hr]; cases allFull σ 280 <;> rfl

theorem check_ct : RelCT isa (R4 fun σ s => Batch σ 2 0 112 4 s)
    (.block (flags ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr))) (R4 Checked) :=
  relInv (fun σ s hp h => check_ok (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))

theorem reset_ok {σ s : State} (h : Checked σ s) :
    WP isa (.block [.mov32 .r14 (.imm 1)]) s (Batch σ 2 0 112 4) := by
  refine WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = 1)
    (by xrun) (by decide)) fun s' ⟨⟨hm, hr⟩, hk⟩ => ?_
  obtain ⟨_, hb, hm₀, hk₀⟩ := h.prior
  exact hb.restore (hm.trans hm₀) ((hk₀.trans hk).mono (by simp)) hr

theorem fallback_ct : RelCT isa (R4 Checked) fallback (R4 Done) := by
  refine RelCT.seq (relInv (fun σ s _ h => reset_ok h) (taintRel [] nil_regs (by taint_decide))) ?_
  obtain ⟨_, c⟩ := sqTaint2
  refine RelCT.seq (relInv (fun σ s hp h => squeeze_last_ok (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) c)) ?_
  refine RelCT.seq batch3_ct ?_
  exact relInv (fun σ s hp h => last_flags_ok (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) (by taint_decide))

theorem pub_allFull {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) (n : Nat) :
    allFull σ₁ n = allFull σ₂ n := by
  simp only [allFull, List.range_succ, List.range_zero, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.true_and]
  rw [pub_Lt4 hq (K := 0) (by decide), pub_Lt4 hq (K := 1) (by decide),
    pub_Lt4 hq (K := 2) (by decide), pub_Lt4 hq (K := 3) (by decide)]


theorem branch_ct : RelCT isa (R4 Checked) (.ite .e fallback (.block [])) (R4 Done) := by
  refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
    show x.zf = y.zf; rw [h₁.zf, h₂.zf, pub_allFull hq])
    (RelCT.mono fallback_ct (fun _ _ h => h.1) (fun _ _ h => h)) ?_
  have empty : RelCT isa (R4 fun σ s => Checked σ s ∧ allFull σ 280 = true) (.block []) (R4 Done) :=
    relInv (fun σ s _ ⟨h, hf⟩ => by
      obtain ⟨_, hb, hm, hk⟩ := h.prior
      exact WP.block_nil (early_done hb hm hk (by rw [h.r14, hf]; rfl) hf))
      (taintRel [] nil_regs (by taint_decide))
  refine RelCT.mono empty (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hb⟩ => ?_) (fun _ _ h => h)
  have hz : x.zf = some false := hb
  have hf : allFull σ₁ 280 = true := by rw [h₁.zf] at hz; simpa using hz
  exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, hf⟩, ⟨h₂, by rw [← pub_allFull hq]; exact hf⟩⟩

theorem finish_ct : RelCT isa (R4 fun σ s => Batch σ 2 0 112 4 s) finish (fun _ _ => True) :=
  RelCT.seq check_ct (RelCT.seq branch_ct
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)))

theorem ct : ConstantTime isa r4K.pre r4K.pub VG.Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq start_ct (RelCT.seq (RelCT.mono (sqT_ct (t := 0) (by decide) sqTaint0)
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, sqT_of h₁, sqT_of h₂⟩) fun _ _ h => h)
    (RelCT.seq (sqT_ct (by decide) sqTaint1) (RelCT.seq (sqT_ct (by decide) sqTaint2) ?_))))
  refine RelCT.seq (relInv (fun σ s hp h => zeroJ_ok (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide))) ?_
  refine RelCT.seq (first_ct (K := 0) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (first_ct (K := 1) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (first_ct (K := 2) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (first_ct (K := 3) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (RelCT.mono (sqM_ct (by decide) sqTaint0)
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, m2_of h₁, m2_of h₂⟩) fun _ _ h => h)
    (RelCT.seq (sqM_ct (by decide) sqTaint1) ?_)
  exact RelCT.seq (RelCT.mono batch2_ct
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hq, batch_of_m2 h₁, batch_of_m2 h₂⟩) (fun _ _ h => h)) finish_ct

end VG.Proof.MlDsa.X86_64.Rej4.Segment
