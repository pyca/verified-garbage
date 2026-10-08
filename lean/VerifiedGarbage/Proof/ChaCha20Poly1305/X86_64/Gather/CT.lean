import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Fn

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments,
stack pointer and descriptors agree (`gatherPub`) leak the same trace,
related piece by piece from given states (`Eq2`, `Gather/LoopCT.lean`): the
frames are pushed and popped at `rsp`, the same in both runs
(`RelCT.frame`); the entry and the call's arguments are read at `rsp`
(the taint analysis from `rsp` and `r8`); the gathering is constant time by
`gather_rel`; and the call is constant time by its callee's contract, whose
public arguments agree (`sealGather_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width entry gather callArgs sealGather)

/-- A frame, from two runs of its body from the states its push leaves. -/
theorem rel_frame {rs : List Reg} {r : Reg} {k : Nat} {body : Prog isa} {σ₁ σ₂ : State}
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hb : RelCT isa (Eq2 (pushed rs σ₁) (pushed rs σ₂)) body TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.frame (.push rs) body (.pop r k)) TT :=
  RelCT.frame (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact hsp)
    (hb.mono (fun _ _ ⟨s₁, s₂, ⟨e₁, e₂⟩, hx, hy⟩ => by subst e₁ e₂; exact ⟨hx, hy⟩) fun _ _ h => h)

/-- The call, in two runs ready for it with the same public arguments. -/
theorem call_rel (F : SealFn) {σ₁ σ₂ c₁ c₂ : State} (h₁ : Lay σ₁) (h₂ : Lay σ₂) (hc₁ : Ready σ₁ c₁)
    (hc₂ : Ready σ₂ c₂) (hrd : rdC σ₂ = rdC σ₁) (hwr : wrC σ₂ = wrC σ₁) (hB : Bs σ₁ = Bs σ₂)
    (hk : K σ₁ = K σ₂) (hn : Nn σ₁ = Nn σ₂) (ha : Ad σ₁ = Ad σ₂) (hal : σ₁.gpr .rcx = σ₂.gpr .rcx)
    (hd : Dst σ₁ = Dst σ₂) (hl : stackArg σ₁ 1 = stackArg σ₂ 1) (ht : Tg σ₁ = Tg σ₂) :
    RelCT isa (Eq2 c₁ c₂) (.frame (.push [.rax]) (.call F.name F.code) (.pop .rax 1)) TT := by
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
  have t₂ : stackArg ((qS c₂).callEntry.withRegions (rdC σ₁) (wrC σ₁)) 0 = Tg σ₂ := by
    rw [← hx₂]; exact hc₂.xtag h₂
  refine (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun x y ⟨e₁, e₂⟩ => ?_).mono
    (fun a b h => h) fun _ _ h => h
  subst e₁ e₂
  refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, sealSpec_pub ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, cv₁, cw₁, cv₂, cw₂,
    by rw [hc₁.qsp, hc₂.qsp, hB]⟩
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.rdi, hc₂.rdi, hk]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.rsi, hc₂.rsi, hn]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.rdx, hc₂.rdx, ha]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.rcx, hc₂.rcx, hal]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.r8, hc₂.r8, hd]
  · rw [g₁ _ (by decide), g₂ _ (by decide), hc₁.r9, hc₂.r9, hl]
  · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, hc₁.qsp,
      hc₂.qsp, hB]
  · rw [hc₁.xtag h₁, t₂, ht]

theorem sealGather_ct (w : Width) (F : SealFn) :
    ConstantTime isa gatherPre gatherPub (sealGather w F.name F.code) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨qdi, qsi, qdx, qcx, q8, q9, qsp, a0, a1, a2, hdesc⟩ := hq
  have hB : Bs σ₁ = Bs σ₂ := by simp only [Bs, qsp]
  refine rel_frame qsp ?_
  -- The entry.
  refine rel_seq (rel_regs [.rsp, .r8] (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [hP, hP, hB], by rw [pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide), q8]⟩)
      ⟨_, by taint_decide⟩) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The gathering.
  have gp₁ := gatherPre_of h₁ he₁
  have gp₂ : GatherPre e₂ (Src σ₁) (Dst σ₁) (Cnt σ₁) (L σ₁) := by
    have := gatherPre_of h₂ he₂
    rwa [show Src σ₂ = Src σ₁ from q8.symm, show Dst σ₂ = Dst σ₁ from a0.symm,
      show Cnt σ₂ = Cnt σ₁ from congrArg BitVec.toNat q9.symm, show L σ₂ = L σ₁ from congrArg BitVec.toNat a1.symm]
      at this
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds₁, -, -, -, -, -, -, ods₁, -⟩ := p₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds₂, -⟩ := p₂
  have hd : ∀ j < Cnt σ₁ * 16,
      e₁.mem (Src σ₁ + BitVec.ofNat 64 j) = e₂.mem (Src σ₁ + BitVec.ofNat 64 j) := by
    intro j hj
    have hx : (dsR σ₁).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by omega)
    have hx₂ : (dsR σ₂).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← q8, ← q9]; exact hx
    rw [he₁.mem, he₂.mem, h₁.keepE bds₁.symm hx, h₂.keepE bds₂.symm hx₂]
    exact hdesc j hj
  refine rel_seq (gather_rel w hd gp₁ gp₂) (gathered_wp w h₁ he₁) (gathered_wp w h₂ he₂)
    fun g₁ g₂ hg₁ hg₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_regs [.rsp] (by simp [hg₁.rsp, hg₂.rsp, hB]) ⟨_, by taint_decide⟩)
    (ready_wp h₁ hg₁) (ready_wp h₂ hg₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by
    simp only [rdC, kR, nR, aR, K, Nn, Ad, AL, Bs, qdi, qsi, qdx, qcx, qsp]
  have hwr : wrC σ₂ = wrC σ₁ := by
    simp only [wrC, dR, tgR, Dst, L, Tg, a0, a1, a2]
  exact call_rel F h₁ h₂ hc₁ hc₂ hrd hwr hB qdi qsi qdx qcx a0 a1 a2

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
