module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Fn
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.CT
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.CT
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Fn
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.CT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.CT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit


/-!
# ChaCha20-Poly1305 with the data's first bytes from `src`, x86-64: the function in constant time

Two runs of `sealSplitFor` whose arguments, stack pointer and stack
arguments agree (`splitPub`) leak the same trace, related piece by piece from
given states (`Gather.Eq2`): each block of `head` by the taint analysis, from
the registers the correctness proof pins to the same values in both runs
(`work`'s address in `rax`, loaded by a block of its own, and the copy's
arguments); the frame is pushed and popped at `rsp`, the same in both runs;
and `seal`'s body, inline, by its own constant-time proof (`relCT_inline`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Split

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealSplit
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width copyBytes)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT rel_seq rel_regs ct_of rel_frame)

/-- What two runs agree on: the arguments, the stack pointer and the stack
arguments. -/
def splitPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3

theorem sealSplitBody_ct (v : Proof.ChaCha20.X86_64.XorImpl) (b : Impl.Poly1305.X86_64.Blocks)
    (hvb : v.poly = b) (hb : b = .avx512 ∨ b = .ifma) :
    ConstantTime isa SPre PubS (sealSplitBody v.callee b) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (sealSplitBody_rel h₁ h₂ hq v b hvb hb _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem sealFor_ct (v : Proof.ChaCha20.X86_64.XorImpl) :
    ConstantTime isa sealX86_64.pre sealX86_64.pub (Stitch.sealFor v.callee v.poly) := by
  cases hb : v.poly with
  | avx2 => have h₂ := Proof.ChaCha20Poly1305.X86_64.Stitch.sealSC_ct v hb; rw [hb] at h₂; exact h₂
  | avx512 =>
    have h₁ := seal_ct v; rw [hb] at h₁
    have := Proof.ChaCha20Poly1305.X86_64.Stitch.sealSmall_ct v.small v.small_poly h₁
    rwa [Proof.ChaCha20.X86_64.XorImpl.small_callee] at this
  | _ => have h₁ := seal_ct v; rw [hb] at h₁; exact h₁

section
variable {σ₁ σ₂ : State} (p₁ : FPre σ₁) (p₂ : FPre σ₂) (hq : splitPub σ₁ σ₂)
include p₁ p₂ hq

/-- `head`, in two runs. -/
theorem head_rel (whole : Bool) (w : Width) : RelCT isa (Eq2 σ₁ σ₂) (head whole w) TT := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, qsp, a₀, a₁, a₂, a₃⟩ := hq
  have hc : cntOf σ₁ whole = cntOf σ₂ whole := by simp only [cntOf, eSN, eLn, q₆, a₁]
  refine rel_seq (rel_regs [.rsp] (by simp [qsp]) ⟨_, by taint_decide⟩) (loaded_ok p₁) (loaded_ok p₂)
    fun x₁ x₂ hx₁ hx₂ => ?_
  refine rel_seq (rel_regs [.rax, .rsp] (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [hx₁.1, hx₂.1, eW, eW, a₃], by rw [hx₁.2.1 _ (by decide), hx₂.2.1 _ (by decide), qsp]⟩)
      (by cases whole <;> exact ⟨_, by taint_decide⟩)) (ready_ok whole p₁ hx₁) (ready_ok whole p₂ hx₂)
    fun b₁ b₂ hb₁ hb₂ => ?_
  refine rel_seq (rel_regs [.rsi, .rdi, .rcx] (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rw [hb₁.2.1, hb₂.2.1, eSrc, eSrc, q₅], by rw [hb₁.2.2.1, hb₂.2.2.1, eDst, eDst, a₀],
        by rw [hb₁.2.2.2.1, hb₂.2.2.2.1, hc]⟩)
      (by cases w <;> exact ⟨_, by taint_decide⟩)) (copied_ok whole w p₁ hb₁) (copied_ok whole w p₂ hb₂)
    fun c₁ c₂ hc₁ hc₂ => ?_
  have sp₁ : c₁.gpr .rsp = σ₁.gpr .rsp :=
    hc₁.2.1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have sp₂ : c₂.gpr .rsp = σ₂.gpr .rsp :=
    hc₂.2.1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine rel_seq (rel_regs [.rsp] (by simp [sp₁, sp₂, qsp]) ⟨_, by taint_decide⟩) (loaded2_ok whole p₁ hc₁)
    (loaded2_ok whole p₂ hc₂) fun d₁ d₂ hd₁ hd₂ => ?_
  refine rel_regs [.rax, .rsp] ?_ ⟨_, by taint_decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by rw [hd₁.1, hd₂.1, eW, eW, a₃],
    by rw [hd₁.2.2.1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hd₂.2.2.1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), qsp]⟩

omit p₁ p₂ in
/-- The public data of `seal`'s entry state in the frame, in two runs. -/
theorem body_pub {whole : Bool} {u₁ u₂ : State} (hu₁ : Body whole σ₁ u₁) (hu₂ : Body whole σ₂ u₂) :
    PubS u₁ u₂ := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, qsp, a₀, a₁, a₂, a₃⟩ := hq
  have hB : fB σ₁ = fB σ₂ := by simp only [fB, qsp]
  exact ⟨⟨by rw [hu₁.rdi, hu₂.rdi, q₁], by rw [hu₁.rsi, hu₂.rsi, q₂], by rw [hu₁.rdx, hu₂.rdx, q₃],
    by rw [hu₁.rcx, hu₂.rcx, q₄], by rw [hu₁.r8, hu₂.r8, eDst, eDst, a₀], by rw [hu₁.r9, hu₂.r9, a₁],
    by rw [hu₁.rsp, hu₂.rsp, hB], by rw [hu₁.arg0, hu₂.arg0, eTg, eTg, a₂],
    by rw [hu₁.arg1, hu₂.arg1, eW, eW, a₃]⟩, by rw [hu₁.arg2, hu₂.arg2, eSrc, eSrc, q₅],
    by rw [hu₁.arg3, hu₂.arg3, q₆]⟩

/-- The frame around a body that is constant time from `seal`'s entry state,
narrowed. -/
theorem framed_rel {whole : Bool} {c : Prog isa} {Pre : State → Prop} {Post : State → State → Prop}
    {Pub : State → State → Prop}
    (hv : ∀ s, Pre s → ∃ t s', Exec isa c s t s' ∧ Post s s') (hct : ConstantTime isa Pre Pub c)
    (more : State → List Region)
    (hpre : ∀ σ u, FPre σ → Body whole σ u → Pre (u.withRegions (rdB u ++ more u) (wrB u)))
    (hmore : ∀ σ u, FPre σ → Body whole σ u → Covers (more u) (u.rd ++ u.wr))
    (hpub : ∀ {u₁ u₂}, Body whole σ₁ u₁ → Body whole σ₂ u₂ →
      Pub (u₁.withRegions (rdB u₁ ++ more u₁) (wrB u₁)) (u₂.withRegions (rdB u₂ ++ more u₂) (wrB u₂)))
    {h₁ h₂ : State} (hh₁ : Headed whole σ₁ h₁) (hh₂ : Headed whole σ₂ h₂) :
    RelCT isa (Eq2 h₁ h₂) (framed c) TT := by
  have qsp := hq.2.2.2.2.2.2.1
  have hsp : ∀ {σ h}, Headed whole σ h → h.gpr .rsp = σ.gpr .rsp := fun hh =>
    hh.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine rel_frame (by rw [hsp hh₁, hsp hh₂, qsp]) ?_
  refine rel_seq (rel_regs [.rsp] (by simp [pushed_rsp' (hsp hh₁), pushed_rsp' (hsp hh₂), fB, qsp])
    ⟨_, by taint_decide⟩) (body_ok p₁ hh₁) (body_ok p₂ hh₂) fun u₁ u₂ hu₁ hu₂ => ?_
  refine (regionModel.relCT_inline (c := c) (Pre := Pre) (Pub := Pub) hv hct (P := Eq2 u₁ u₂)
    fun x₁ x₂ ⟨e₁, e₂⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
  subst e₁ e₂
  exact ⟨_, _, _, _, hpre _ _ p₁ hu₁, hpre _ _ p₂ hu₂, hpub hu₁ hu₂,
    Covers.append_left (Covers.append_left (hu₁.rdB_cov p₁) (hmore _ _ p₁ hu₁)) (hu₁.wrB_cov p₁).right,
    hu₁.wrB_cov p₁,
    Covers.append_left (Covers.append_left (hu₂.rdB_cov p₂) (hmore _ _ p₂ hu₂)) (hu₂.wrB_cov p₂).right,
    hu₂.wrB_cov p₂⟩

end

/-- `vg_chacha20_poly1305_seal_split` of the instance calling the
implementation `v` of `vg_chacha20_xor`. -/
theorem sealSplit_ct (v : Proof.ChaCha20.X86_64.XorImpl) :
    ConstantTime isa FPre splitPub (sealSplitFor v.callee v.poly) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have split : ∀ b, v.poly = b → (hb : b = .avx512 ∨ b = .ifma) →
      RelCT isa (Eq2 σ₁ σ₂) (.seq (head false .z64) (framed (sealSplitBody v.callee b))) TT := fun b hvb hb =>
    rel_seq (head_rel p₁ p₂ hq false .z64) (head_ok false .z64 p₁) (head_ok false .z64 p₂)
      fun h₁ h₂ hh₁ hh₂ => framed_rel p₁ p₂ hq (Pre := SPre) (Pub := PubS)
        (fun s hs => let ⟨t, s', e, _, p⟩ := split_hv v b hvb hb s hs; ⟨t, s', e, p⟩) (sealSplitBody_ct v b hvb hb)
        (fun u => [arg2R u, spR u]) (fun _ _ hs hu => hu.spre hs) (fun _ _ hs hu => hu.more_cov hs)
        (fun hu₁ hu₂ => by have := body_pub hq hu₁ hu₂; exact this) hh₁ hh₂
  have whole : ∀ (x : Impl.ChaCha20.X86_64.Callee) (b : Impl.Poly1305.X86_64.Blocks),
      (∀ s, sealX86_64.pre s → ∃ t s', Exec isa (Stitch.sealFor x b) s t s' ∧ abiPreserved s s' ∧
        sealX86_64.post s s') →
      ConstantTime isa sealX86_64.pre sealX86_64.pub (Stitch.sealFor x b) →
      RelCT isa (Eq2 σ₁ σ₂) (.seq (head true (Width.ofBlocks b)) (framed (Stitch.sealFor x b))) TT :=
    fun x b hv hct =>
    rel_seq (head_rel p₁ p₂ hq true _) (head_ok true _ p₁) (head_ok true _ p₂)
      fun h₁ h₂ hh₁ hh₂ => framed_rel p₁ p₂ hq (Pre := sealX86_64.pre) (Pub := sealX86_64.pub)
        (fun s hs => let ⟨t, s', e, _, p⟩ := hv s hs; ⟨t, s', e, p⟩) hct
        (fun _ => []) (fun _ _ hs hu => by rw [List.append_nil]; exact hu.pre hs) (fun _ _ _ _ => Covers.nil)
        (fun hu₁ hu₂ => by rw [List.append_nil, List.append_nil]; have := (body_pub hq hu₁ hu₂).1; exact this) hh₁ hh₂
  have hv := sealFor_hv v
  have hct := sealFor_ct v
  cases hp : v.poly with
  | avx512 => exact split .avx512 hp (.inl rfl)
  | ifma => exact split .ifma hp (.inr rfl)
  | scalar => rw [hp] at hv hct; exact whole _ _ hv hct
  | avx2 => rw [hp] at hv hct; exact whole _ _ hv hct

end VG.Proof.ChaCha20Poly1305.X86_64.Split
