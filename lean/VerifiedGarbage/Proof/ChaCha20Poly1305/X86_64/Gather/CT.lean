module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Fn
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Fn
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments,
stack pointer and descriptors agree (`gatherPub`) leak the same trace,
related piece by piece from given states (`Eq2`, `Gather/LoopCT.lean`): the
frames are pushed and popped at `rsp`, the same in both runs
(`RelCT.frame`); the entry and the call's arguments are read at `rsp`
(the taint analysis from `rsp` and `r8`); the step past the first slice and
the load of its descriptor branch on `src_count` and read the descriptors
(from `r9`, `r11` and `r8`); the gathering is constant time by
`gather_rel`; and the call is constant time by its callee's contract, whose
public arguments agree, the first slice included, as the descriptors do
(`sealGather_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width entry skipFirst gather callArgs firstArgs sealGather)

/-- A frame, from two runs of its body from the states its push leaves. -/
theorem rel_frame {rs : List Reg} {r : Reg} {k : Nat} {body : Prog isa} {σ₁ σ₂ : State}
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hb : RelCT isa (Eq2 (pushed rs σ₁) (pushed rs σ₂)) body TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.frame (.push rs) body (.pop r k)) TT :=
  RelCT.frame (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact hsp)
    (hb.mono (fun _ _ ⟨s₁, s₂, ⟨e₁, e₂⟩, hx, hy⟩ => by subst e₁ e₂; exact ⟨hx, hy⟩) fun _ _ h => h)

/-- The call, in two runs ready for it with the same public arguments. -/
theorem call_rel (F : SealSplitFn) {σ₁ σ₂ c₁ c₂ : State} (h₁ : Lay σ₁) (h₂ : Lay σ₂) (hc₁ : Ready σ₁ c₁)
    (hc₂ : Ready σ₂ c₂) (hrd : rdC σ₂ = rdC σ₁) (hwr : wrC σ₂ = wrC σ₁) (hB : Bs σ₁ = Bs σ₂)
    (hk : K σ₁ = K σ₂) (hn : Nn σ₁ = Nn σ₂) (ha : Ad σ₁ = Ad σ₂) (hal : σ₁.gpr .rcx = σ₂.gpr .rcx)
    (hs : S0 σ₁ = S0 σ₂) (hsl : L0 σ₁ = L0 σ₂)
    (hd : Dst σ₁ = Dst σ₂) (hl : stackArg σ₁ 1 = stackArg σ₂ 1) (ht : Tg σ₁ = Tg σ₂) :
    RelCT isa (Eq2 c₁ c₂) (.frame (.push [.rax, .r10, .r11]) (.call F.name F.code) (.pop .rax 3)) TT := by
  refine rel_frame (by rw [hc₁.rsp, hc₂.rsp, hB]) ?_
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.call h₂
  have hx₂ : xS σ₂ c₂ = (qS c₂).callEntry.withRegions (rdC σ₁) (wrC σ₁) := by rw [← hrd, ← hwr]
  rw [hx₂] at cp₂
  rw [hrd, hwr] at cv₂
  rw [hwr] at cw₂
  have g₁ (r : Reg) (hr : r ≠ .rsp) : (xS σ₁ c₁).gpr r = c₁.gpr r := xgpr_eq hr
  have g₂ (r : Reg) (hr : r ≠ .rsp) : ((qS c₂).callEntry.withRegions (rdC σ₁) (wrC σ₁)).gpr r = c₂.gpr r :=
    xgpr_eq (s := σ₁) hr
  have t₀ : stackArg ((qS c₂).callEntry.withRegions (rdC σ₁) (wrC σ₁)) 0 = Dst σ₂ := by
    rw [← hx₂]; exact hc₂.xa0 h₂
  have t₁ : stackArg ((qS c₂).callEntry.withRegions (rdC σ₁) (wrC σ₁)) 1 = stackArg σ₂ 1 := by
    rw [← hx₂]; exact hc₂.xa1 h₂
  have t₂ : stackArg ((qS c₂).callEntry.withRegions (rdC σ₁) (wrC σ₁)) 2 = Tg σ₂ := by
    rw [← hx₂]; exact hc₂.xa2 h₂
  refine (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun x y ⟨e₁, e₂⟩ => ?_).mono
    (fun a b h => h) fun _ _ h => h
  subst e₁ e₂
  refine ⟨sealSplitSpec_pre cp₁, sealSplitSpec_pre cp₂,
    sealSplitSpec_pub ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, cv₁, cw₁, cv₂, cw₂,
    by rw [hc₁.qsp, hc₂.qsp, hB]⟩
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.rdi, hc₂.rdi, hk]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.rsi, hc₂.rsi, hn]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.rdx, hc₂.rdx, ha]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.rcx, hc₂.rcx, hal]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.r8, hc₂.r8, hs]
  · rw [g₁ _ (by decide), g₂ _ (by decide)]
    exact BitVec.eq_of_toNat_eq (by rw [hc₁.r9, hc₂.r9, hsl])
  · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, hc₁.qsp,
      hc₂.qsp, hB]
  · rw [hc₁.xa0 h₁, t₀, hd]
  · rw [hc₁.xa1 h₁, t₁, hl]
  · rw [hc₁.xa2 h₁, t₂, ht]

theorem sealGather_ct (w : Width) (F : SealSplitFn) :
    ConstantTime isa gatherPre gatherPub (sealGather w F.name F.code) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨qdi, qsi, qdx, qcx, q8, q9, qsp, a0, a1, a2, hdesc⟩ := hq
  have hB : Bs σ₁ = Bs σ₂ := by simp only [Bs, qsp]
  have hS : Src σ₂ = Src σ₁ := q8.symm
  have hC : Cnt σ₂ = Cnt σ₁ := congrArg BitVec.toNat q9.symm
  have hD : Dst σ₂ = Dst σ₁ := a0.symm
  have hL : L σ₂ = L σ₁ := congrArg BitVec.toNat a1.symm
  -- The descriptors agree after the push.
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds₁, -, -, -, -, -, -, ods₁, -⟩ := p₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds₂, -⟩ := p₂
  have hdE : ∀ j < Cnt σ₁ * 16,
      eM σ₁ (Src σ₁ + BitVec.ofNat 64 j) = eM σ₂ (Src σ₁ + BitVec.ofNat 64 j) := by
    intro j hj
    have hx : (dsR σ₁).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by omega)
    have hx₂ : (dsR σ₂).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← q8, ← q9]; exact hx
    rw [h₁.keepE bds₁.symm hx, h₂.keepE bds₂.symm hx₂]
    exact hdesc j hj
  have hk : k1 σ₂ = k1 σ₁ := by simp only [k1, hC]
  have hRs : Rs σ₂ = Rs σ₁ := by simp only [Rs, hk, hS]
  have hRc : Rc σ₂ = Rc σ₁ := by simp only [Rc, hk, hC]
  have hL0 : L0 σ₂ = L0 σ₁ := by
    simp only [L0, hC]
    split
    · rfl
    · rename_i h0
      rw [hS]; exact (sl_agree hdE (by omega)).symm
  have hS0 : S0 σ₂ = S0 σ₁ := by
    simp only [S0, hC]
    split
    · exact hS
    · rename_i h0
      rw [hS]; exact (sb_agree hdE (by omega)).symm
  refine rel_frame qsp ?_
  -- The entry.
  refine rel_seq (rel_regs [.rsp, .r8] (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [hP, hP, hB], by rw [pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide), q8]⟩)
      ⟨_, by taint_decide⟩) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- Past the first slice.
  refine rel_seq (rel_regs [.r9, .r11] (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [he₁.gpr _ (by decide) (by decide) (by decide), he₂.gpr _ (by decide) (by decide) (by decide), q9],
        by rw [he₁.r11, he₂.r11, hS]⟩)
      ⟨_, by taint_decide⟩) (skipped_wp h₁ he₁) (skipped_wp h₂ he₂) fun f₁ f₂ hf₁ hf₂ => ?_
  -- The gathering.
  have gp₁ := gatherPre_of h₁ hf₁
  have gp₂ : GatherPre f₂ (Rs σ₁) (Dst σ₁ + BitVec.ofNat 64 (L0 σ₁)) (Rc σ₁) (L σ₁ - L0 σ₁) := by
    have := gatherPre_of h₂ hf₂
    rwa [hRs, hD, hL0, hRc, hL] at this
  have hd : ∀ j < Rc σ₁ * 16,
      f₁.mem (Rs σ₁ + BitVec.ofNat 64 j) = f₂.mem (Rs σ₁ + BitVec.ofNat 64 j) := by
    intro j hj
    have hk1 : k1 σ₁ ≤ Cnt σ₁ := by simp only [k1]; split <;> omega
    have e : Rs σ₁ + BitVec.ofNat 64 j = Src σ₁ + BitVec.ofNat 64 (16 * k1 σ₁ + j) := by
      simp only [Rs, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [hf₁.mem, hf₂.mem, e]
    exact hdE _ (by simp only [Rc] at hj; rw [Nat.sub_mul] at hj; omega)
  refine rel_seq (gather_rel w hd gp₁ gp₂) (gathered_wp w h₁ hf₁) (gathered_wp w h₂ hf₂)
    fun g₁ g₂ hg₁ hg₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_regs [.rsp] (by simp [hg₁.rsp, hg₂.rsp, hB]) ⟨_, by taint_decide⟩)
    (args_wp h₁ hg₁) (args_wp h₂ hg₂) fun a₁ a₂ ha₁ ha₂ => ?_
  -- The first slice.
  refine rel_seq (rel_regs [.r8, .r9] (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [ha₁.r8, ha₂.r8, hS], by rw [ha₁.r9, ha₂.r9, q9]⟩)
      ⟨_, by taint_decide⟩) (ready_wp h₁ ha₁) (ready_wp h₂ ha₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by
    simp only [rdC, kR, nR, aR, sR, K, Nn, Ad, AL, Bs, qdi, qsi, qdx, qcx, qsp, hS0, hL0]
  have hwr : wrC σ₂ = wrC σ₁ := by
    simp only [wrC, dR, tgR, Dst, L, Tg, a0, a1, a2]
  exact call_rel F h₁ h₂ hc₁ hc₂ hrd hwr hB qdi qsi qdx qcx hS0.symm hL0.symm a0 a1 a2

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
