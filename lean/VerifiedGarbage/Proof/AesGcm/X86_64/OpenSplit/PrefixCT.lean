module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Prefix
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Prefix
meta import VerifiedGarbage.Impl.AesGcm.X86_64.OpenSplit
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM `open_split` on x86-64: `prefix` in constant time

Untrusted: everything here is checked by Lean. `OpenSplit.prefix`, as
`Split.prefix_ct` for `seal_split`'s, with the call of
`vg_aes_gcm_decrypt_blocks_to` and no copy (`prefixD_ct`): the same blocks,
checked by the taint analysis, and the same branch on the public length,
with `Mid2D` in place of `Mid2` after the call, which gets the same public
arguments in both runs (`callD_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenSplit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64.Split
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (step skip_rel)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {σ : State} (h : PP M Ctx W SP D S R n sl σ)
include h

omit h in
theorem mid2D_zero {s : State} (g : G₁ Ctx W SP sl σ s) (h0 : sl / 16 = 0) : Mid2D Ctx W SP D S R sl σ s := by
  obtain ⟨he, -, -, m, rd, wr⟩ := g
  refine ⟨he, rd, wr, by rw [m]; exact Frame.refl _ _, ?_, ?_, ?_⟩
  · rw [h0, m]; rfl
  · rw [h0, m]; rfl
  · rw [h0, m]; rfl

theorem mid2D_call_wp (T : BlkToDecFn M) {s : State} (g : G₂ Ctx W SP D S R sl σ s) :
    WP isa (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3)) s
      (Mid2D Ctx W SP D S R sl σ) := by
  obtain ⟨he, di, si, dx, cx, r8, r9, r10, r11, ax, m, rd, wr⟩ := g
  refine WP.mono (preCallToDec_ok h T (q := sl / 16) (by omega_arith) he.rsp rd wr m di si dx cx r8 r9 r10 r11 ax)
    fun s₃ ⟨cs₃, rd₃, wr₃, fr₃, bl₃, ct₃, y₃⟩ => ⟨he.keep (fun r hr => cs₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) rd₃ wr₃,
      rd₃.trans rd, wr₃.trans wr, by rw [m] at fr₃; exact fr₃, bl₃, ct₃, y₃⟩

end

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {σ σ' : State}
  (h : PP M Ctx W SP D S R n sl σ) (h' : PP M Ctx W SP D S R n sl σ')
include h h'

/-- The call of `vg_aes_gcm_decrypt_blocks_to`, in two runs: the same public
arguments. -/
theorem callD_rel (T : BlkToDecFn M) :
    RelCT isa (fun s₁ s₂ => G₂ Ctx W SP D S R sl σ s₁ ∧ G₂ Ctx W SP D S R sl σ' s₂)
      (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3)) fun _ _ => True := by
  have hq : 16 * (sl / 16) ≤ sl := Nat.mul_div_le _ _
  refine RelCT.frame (fun _ _ g => by rw [g.1.1.rsp, g.2.1.rsp])
    (RelCT.callEx (k := Proof.AesGcm.decryptBlocksToX86_64M M) T.ok T.ct fun _ _ hab => ?_)
  obtain ⟨s₁, s₂, ⟨g₁, g₂⟩, rfl, rfl⟩ := hab
  obtain ⟨he₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, r10₁, r11₁, ax₁, m₁, rd₁, wr₁⟩ := g₁
  obtain ⟨he₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂, r11₂, ax₂, m₂, rd₂, wr₂⟩ := g₂
  obtain ⟨p₁, cr₁, cw₁, gU₁, hU₁, a0₁, a1₁, a2₁⟩ :=
    callIn h hq he₁.rsp rd₁ wr₁ m₁ di₁ si₁ dx₁ cx₁ r8₁ r9₁ r10₁ r11₁ ax₁
  obtain ⟨p₂, cr₂, cw₂, gU₂, hU₂, a0₂, a1₂, a2₂⟩ :=
    callIn h' hq he₂.rsp rd₂ wr₂ m₂ di₂ si₂ dx₂ cx₂ r8₂ r9₂ r10₂ r11₂ ax₂
  refine ⟨_, _, _, _, p₁, p₂, ?_, cr₁, cw₁, cr₂, cw₂, by rw [pushed_rsp, pushed_rsp, he₁.rsp, he₂.rsp]⟩
  simp only [Proof.AesGcm.decryptBlocksToX86_64M, Proof.AesGcm.blocksToPub, Proof.AesGcm.arg, callU] at *
  simp only [gU₁ _ (by decide : Reg.rdi ≠ .rsp), gU₁ _ (by decide : Reg.rsi ≠ .rsp),
    gU₁ _ (by decide : Reg.rdx ≠ .rsp), gU₁ _ (by decide : Reg.rcx ≠ .rsp), gU₁ _ (by decide : Reg.r8 ≠ .rsp),
    gU₁ _ (by decide : Reg.r9 ≠ .rsp), gU₂ _ (by decide : Reg.rdi ≠ .rsp), gU₂ _ (by decide : Reg.rsi ≠ .rsp),
    gU₂ _ (by decide : Reg.rdx ≠ .rsp), gU₂ _ (by decide : Reg.rcx ≠ .rsp), gU₂ _ (by decide : Reg.r8 ≠ .rsp),
    gU₂ _ (by decide : Reg.r9 ≠ .rsp), di₁, di₂, si₁, si₂, dx₁, dx₂, cx₁, cx₂, r8₁, r8₂, r9₁, r9₂, hU₁, hU₂,
    a0₁, a0₂, a1₁, a1₂, a2₁, a2₂, and_self]

/-- `prefix`'s call, from states with the number of whole blocks in `rax`. -/
theorem callPartD_rel (T : BlkToDecFn M) :
    RelCT isa (fun a b => G₀ Ctx W SP sl σ a ∧ G₀ Ctx W SP sl σ' b)
      (.seq (.block SealSplit.preArgs) (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3)))
      fun a b => Mid2D Ctx W SP D S R sl σ a ∧ Mid2D Ctx W SP D S R sl σ' b := by
  refine RelCT.seq (step [.r13, .r14, .r15] preArgs_check (F₁ := G₀ Ctx W SP sl σ) (F₂ := G₀ Ctx W SP sl σ')
    (fun _ _ g r hr => by
      have e₁ := g.1.1; have e₂ := g.2.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [e₁.r13, e₂.r13]
      · rw [e₁.r14, e₂.r14]
      · rw [e₁.r15, e₂.r15])
    (fun _ _ g => g) (fun _ g => g₂_wp h g) (fun _ g => g₂_wp h' g)) ?_
  exact (rel_wp (callD_rel h h' T) (fun _ _ g => g) (fun _ g => mid2D_call_wp h T g)
    (fun _ g => mid2D_call_wp h' T g)).mono (fun _ _ g => g) fun _ _ g => g.2

omit h h' in
theorem restS_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block Impl.AesGcm.X86_64.OpenSplit.rest) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- After `prefix`'s call (or none): `rest`. -/
theorem restD_rel :
    RelCT isa (fun a b => Mid2D Ctx W SP D S R sl σ a ∧ Mid2D Ctx W SP D S R sl σ' b)
      (.block Impl.AesGcm.X86_64.OpenSplit.rest) fun _ _ => True :=
  (step [.r15] restS_check (F₁ := Mid2D Ctx W SP D S R sl σ) (F₂ := Mid2D Ctx W SP D S R sl σ')
    (fun _ _ g r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [g.1.env.r15, g.2.env.r15])
    (fun _ _ g => g) (fun _ g => restD_ok h g) (fun _ g => restD_ok h' g)).mono (fun _ _ g => g) fun _ _ _ => trivial

/-- `prefix`, in two runs. -/
theorem prefixD_ct (T : BlkToDecFn M) :
    RelCT isa (fun a b => a = σ ∧ b = σ') (Impl.AesGcm.X86_64.OpenSplit.prefix T.fn) fun _ _ => True := by
  have r15 : ∀ {s₁ s₂ : State}, Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ → Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ →
      ∀ r ∈ [Reg.r15], s₁.gpr r = s₂.gpr r := fun e₁ e₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [e₁.r15, e₂.r15]
  unfold Impl.AesGcm.X86_64.OpenSplit.prefix
  refine RelCT.seq (step [.r15] preTest_check (F₁ := (· = σ)) (F₂ := (· = σ'))
    (G₁ := G₁ Ctx W SP sl σ) (G₂ := G₁ Ctx W SP sl σ')
    (fun _ _ g => by obtain ⟨rfl, rfl⟩ := g; exact r15 h.env h'.env) (fun _ _ g => g)
    (fun _ hs => by rw [hs]; exact g₁_wp h) (fun _ hs => by rw [hs]; exact g₁_wp h')) ?_
  refine RelCT.seq (R := fun a b => Mid2D Ctx W SP D S R sl σ a ∧ Mid2D Ctx W SP D S R sl σ' b)
    (RelCT.ite (fun _ _ g => by simp only [eval, g.1.2.2.1, g.2.2.2.1]) ?_ ?_) ?_
  · refine StreamTo.RelCT.of_imp (sl / 16 = 0) (fun _ _ g => by
      have e := g.2; simp only [eval, g.1.1.2.2.1] at e; simpa using e) fun h0 => ?_
    exact skip_rel fun _ _ g => ⟨mid2D_zero g.1.1 h0, mid2D_zero g.1.2 h0⟩
  · exact (callPartD_rel h h' T).mono (fun _ _ g =>
      ⟨⟨g.1.1.1, g.1.1.2.1, g.1.1.2.2.2⟩, ⟨g.1.2.1, g.1.2.2.1, g.1.2.2.2.2⟩⟩) fun _ _ g => g
  exact restD_rel h h'

end

end VG.Proof.AesGcm.X86_64.OpenSplit
