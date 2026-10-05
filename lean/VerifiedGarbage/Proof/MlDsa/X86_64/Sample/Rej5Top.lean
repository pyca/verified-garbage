import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej5Flags

namespace VG.Proof.MlDsa.X86_64.Rej4.Segment

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (Keep ea_at add_ofNat_zero pR WP.keep ofNat64_pred sample4K)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold Stored stored_nil stored_frame stored_polyIs toPoly G_length)
open VG.Spec.MlKem (poly4 seed4)
open VG.Spec.MlDsa (Zq G PolyIs)
open VG.Proof.MlKem (xofByte)

open VG.Impl.MlDsa.X86_64.Sample.Rej5 (flags fallback finish)

structure Done (σ s : State) : Prop where
  env : EnvK σ s
  r14 : s.gpr .r14 = BitVec.ofNat 64 (okN σ 4)
  st : ∀ k < 4, Stored s.mem (poly4 (aP σ) k) (Lt σ k 336)

theorem Batch.restore {σ s s' : State} {n off count K : Nat} (h : Batch σ n off count K s)
    (hm : s'.mem = s.mem) (hk : Keep [.rax, .r14] s s') (hr : s'.gpr .r14 = 1) : Batch σ n off count K s' :=
  ⟨⟨h.sq.env.keep hm hk (by simp), hr, by rw [hm]; exact h.sq.rc,
    by rw [hm]; exact h.sq.lanes, by rw [hm]; exact h.sq.buf⟩,
    by rw [hm]; exact h.j, by rw [hm]; exact h.st⟩

section
variable {σ : State} (hp : Pre σ)
include hp

/-- The return value, and the callee-saved registers restored. -/
theorem end_ok {s : State} (h : Done σ s) :
    WP isa (.block epi) s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega)
  rw [epi_eq]
  refine WP.mono (WP.keep [.rax, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      (s'.gpr .rax).setWidth 32 = (s.gpr .r14).setWidth 32 ∧
      s'.gpr .r14 = s.mem.readW (at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, hax, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  refine ⟨⟨?_, fun k hk e => ?_⟩, fun r hr => ?_, ?_⟩
  · rw [hax, h.r14, okN]
    simp only [Lt_336]
    split <;> rfl
  · rw [hm]
    have := h.st k hk
    rw [Lt_336] at this
    exact stored_polyIs this e
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega)⟩)
      (by decide)


/-- Clear upper vector lanes before restoring the caller's registers. -/
theorem end_vec_ok {s : State} (h : Done σ s) :
    WP isa (.block (([.vop .vzeroupper] : List Instr) ++ epi)) s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  apply WP.block_append
  refine WP.mono (WP.keep [] (Q := fun s' => s'.mem = s.mem) (by xrun; rfl) rfl) fun s' ⟨hm, hk⟩ => ?_
  exact end_ok hp ⟨h.env.keep hm hk (by simp), by rw [hk.gpr (by simp)]; exact h.r14,
    by rw [hm]; exact h.st⟩

theorem last_flags_ok {s : State} (h : Batch σ 3 112 56 4 s) : WP isa (.block flags) s (Done σ) := by
  have hj : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 336).length :=
    fun k hk => by simpa only [ite_eq_left hk] using h.j k hk
  refine WP.mono (flags_ok hp h.sq.env hj) fun s' ⟨⟨hr, hm⟩, hk⟩ =>
    ⟨h.sq.env.keep hm hk (by simp), ?_, fun k hk' => ?_⟩
  · rw [hr]; unfold allFull okN; split <;> rfl
  · rw [hm]; simpa only [ite_eq_left hk'] using h.st k hk'

theorem fallback_ok {s s₀ : State} (h : Batch σ 2 0 112 4 s₀)
    (hm : s.mem = s₀.mem) (hk : Keep [.rax, .r14] s₀ s) : WP isa fallback s (Done σ) := by
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .r14 = 1)
    (by xrun) (by decide)) fun s' ⟨⟨hm', hr⟩, hk'⟩ => ?_)
  have hb := h.restore (hm'.trans hm) ((hk.trans hk').mono (by simp)) hr
  exact WP.seq (WP.mono (squeeze_last_ok hp hb) fun _ h₁ =>
    WP.seq (WP.mono (batch_ok hp (by decide) (by decide) (by decide) (by decide) h₁)
      fun _ h₂ => last_flags_ok hp h₂))

omit hp in
theorem early_done {s s₀ : State} (h : Batch σ 2 0 112 4 s₀)
    (hm : s.mem = s₀.mem) (hk : Keep [.rax, .r14] s₀ s)
    (hr : s.gpr .r14 = 1) (hf : allFull σ 280 = true) : Done σ s := by
  have hfull : ∀ k < 4, (Lt σ k 280).length = 256 := by
    simpa only [allFull, List.all_eq_true, List.mem_range, beq_iff_eq] using hf
  have he : ∀ k < 4, Lt σ k 336 = Lt σ k 280 := fun k hk => full_after_five σ k (hfull k hk)
  refine ⟨h.sq.env.keep hm hk (by simp), ?_, fun k hk' => ?_⟩
  · have hf' : (List.range 4).all (fun k => (Lt σ k 336).length == 256) = true := by
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
      intro k hk; rw [he k hk]; exact hfull k hk
    rw [hr, okN, hf']; rfl
  · rw [hm, he k hk']; simpa only [ite_eq_left hk'] using h.st k hk'

theorem finish_ok {s : State} (h : Batch σ 2 0 112 4 s) :
    WP isa finish s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  have hj : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 280).length :=
    fun k hk => by simpa only [ite_eq_left hk] using h.j k hk
  apply WP.seq
  apply WP.block_append
  refine WP.mono (flags_ok hp h.sq.env hj) fun s₁ ⟨⟨hr, hm⟩, hk⟩ => ?_
  refine WP.mono (WP.keep [.r14] (Q := fun s₂ => s₂.mem = s₁.mem ∧ s₂.gpr .r14 = s₁.gpr .r14 ∧
    s₂.zf = some ((s₁.gpr .r14).setWidth 32 == 0)) (by xrun; simp) (by decide))
    fun s₂ ⟨⟨hm', hr', hz⟩, hk'⟩ => ?_
  apply WP.seq
  apply WP.mono (Q := Done σ) ?_ (fun _ hd => end_vec_ok hp hd)
  have hkeep : Keep [.rax, .r14] s s₂ := (hk.trans hk').mono (by simp)
  cases hf : allFull σ 280 with
  | false =>
    have hz' : s₂.zf = some true := by rw [hz, hr, hf]; rfl
    exact WP.ite true hz' (fun _ => fallback_ok hp h (hm'.trans hm) hkeep)
      (fun hb => absurd hb (by decide))
  | true =>
    have hz' : s₂.zf = some false := by rw [hz, hr, hf]; rfl
    refine WP.ite false hz' (fun hb => absurd hb (by decide)) (fun _ => WP.block_nil ?_)
    exact early_done h (hm'.trans hm) hkeep (by rw [hr', hr, hf]; rfl) hf

/-- Everything after the prologue, the round constants and the padded seeds. -/
theorem body_ok {s : State} (h : SqInv σ 0 s) :
    WP isa (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (squeeze4 2) (.seq (.block zeroJ)
      (.seq (first 0) (.seq (first 1) (.seq (first 2) (.seq (first 3)
        (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (VG.Impl.MlDsa.X86_64.Sample.Rej5.batch 0 112) finish))))))))))) s
      fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  refine WP.seq (WP.mono (sqT_ok hp (by decide) (sqT_of h)) fun s₁ ⟨q₁, _⟩ => WP.seq (WP.mono
    (sqT_ok hp (by decide) q₁) fun s₂ ⟨q₂, _⟩ => WP.seq (WP.mono (sqT_ok hp (by decide) q₂) fun s₃ ⟨q₃, _⟩ =>
      WP.seq (WP.mono (zeroJ_ok hp q₃) fun s₄ p₀ => ?_))))
  refine WP.seq (WP.mono (first_ok hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (first_ok hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (first_ok hp (by decide) p₂) fun _ p₃ =>
      WP.seq (WP.mono (first_ok hp (by decide) p₃) fun _ p₄ => ?_))))
  exact WP.seq (WP.mono (sqM_ok hp (by decide) (m2_of p₄)) fun _ m₁ =>
    WP.seq (WP.mono (sqM_ok hp (by decide) m₁) fun _ m₂ =>
      WP.seq (WP.mono (batch_ok hp (by decide) (by decide) (by decide) (by decide) (batch_of_m2 m₂))
        fun _ b => finish_ok hp b)))

end
theorem correct (σ : State) (hs : r4K.pre σ) :
    ∃ t s', Exec isa VG.Impl.MlDsa.X86_64.Sample.Rej5.rejNTT4Avx2 σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s' := by
  have hp := pre_of (by dsimp only [r4K] at hs; exact hs)
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (start_ok hp) fun _ h => body_ok hp h)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Rej4.Segment
