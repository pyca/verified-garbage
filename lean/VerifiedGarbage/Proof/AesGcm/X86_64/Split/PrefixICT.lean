module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixIRun
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixIRun
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase

/-!
# AES-GCM `seal_split` on x86-64: `prefix` with the block index pushed, in two runs

Untrusted: everything here is checked by Lean. The index of the first counter
block is a constant: the taint analysis checks its `mov` (`prefixI_rel`),
and the push and pop of its frame move `rsp` alike in both runs
(`RelCT.frame`). `prefix` then runs as in `prefix_ct`, but for its call of
`vg_aes_gcm_encrypt_blocks_to_prepared_iv96`, whose public arguments
(`blocksToPubI`) are `blocksToPub`'s and the index, 2 in both runs
(`callI_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (step)
open VG.Spec.Gcm (blockAt ctrIndex)

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {σ σ' : State}
  (h : PP M Ctx W SP D S R n sl σ) (hI : IdxI Ctx W SP D n σ)

include h hI in
/-- The call of `vg_aes_gcm_encrypt_blocks_to_prepared_iv96`, in one run. -/
theorem mid2_callI_wp (T : BlkToFnI M) {s : State} (g : G₂ Ctx W SP D S R sl σ s) :
    WP isa (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3)) s
      (Mid2 Ctx W SP D S R sl σ) := by
  obtain ⟨he, di, si, dx, cx, r8, r9, r10, r11, ax, m, rd, wr⟩ := g
  have c := callInI h hI (q := sl / 16) (by omega) he.rsp rd wr m di si dx cx r8 r9 r10 r11 ax
  refine WP.mono (preCall_okG h _ rfl T.fn T.ok T.sp T.xd (q := sl / 16) (by omega) he.rsp rd wr m di si dx cx r8
      r9 r10 r11 ax _ c.1 c.2.1)
    fun s₃ ⟨cs₃, rd₃, wr₃, fr₃, bl₃, ct₃, y₃⟩ => ⟨he.keep (fun r hr => cs₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) rd₃ wr₃,
      rd₃.trans rd, wr₃.trans wr, by rw [m] at fr₃; exact fr₃, bl₃, ct₃, y₃⟩

variable (h' : PP M Ctx W SP D S R n sl σ') (hI' : IdxI Ctx W SP D n σ')
include h hI h' hI'

/-- The call of `vg_aes_gcm_encrypt_blocks_to_prepared_iv96`, in two runs: the
same public arguments, the index among them. -/
theorem callI_rel (T : BlkToFnI M) :
    RelCT isa (fun s₁ s₂ => G₂ Ctx W SP D S R sl σ s₁ ∧ G₂ Ctx W SP D S R sl σ' s₂)
      (.frame (.push [.rax, .r10, .r11]) (.call T.fn.name T.fn.code) (.pop .rax 3)) fun _ _ => True := by
  have hq : 16 * (sl / 16) ≤ sl := Nat.mul_div_le _ _
  refine RelCT.frame (fun _ _ g => by rw [g.1.1.rsp, g.2.1.rsp])
    (RelCT.callEx (k := Proof.AesGcm.encryptBlocksToIv96X86_64M M) T.ok T.ct fun _ _ hab => ?_)
  obtain ⟨s₁, s₂, ⟨g₁, g₂⟩, rfl, rfl⟩ := hab
  obtain ⟨he₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, r10₁, r11₁, ax₁, m₁, rd₁, wr₁⟩ := g₁
  obtain ⟨he₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂, r11₂, ax₂, m₂, rd₂, wr₂⟩ := g₂
  obtain ⟨-, -, cw₁, -, hU₁, a0₁, a1₁, a2₁⟩ :=
    callIn h hq he₁.rsp rd₁ wr₁ m₁ di₁ si₁ dx₁ cx₁ r8₁ r9₁ r10₁ r11₁ ax₁
  obtain ⟨-, -, cw₂, -, hU₂, a0₂, a1₂, a2₂⟩ :=
    callIn h' hq he₂.rsp rd₂ wr₂ m₂ di₂ si₂ dx₂ cx₂ r8₂ r9₂ r10₂ r11₂ ax₂
  obtain ⟨p₁, cr₁, i₁⟩ := callInI h hI hq he₁.rsp rd₁ wr₁ m₁ di₁ si₁ dx₁ cx₁ r8₁ r9₁ r10₁ r11₁ ax₁
  obtain ⟨p₂, cr₂, i₂⟩ := callInI h' hI' hq he₂.rsp rd₂ wr₂ m₂ di₂ si₂ dx₂ cx₂ r8₂ r9₂ r10₂ r11₂ ax₂
  have gU : ∀ {st : State} (r : Reg), r ≠ .rsp → (callUI M Ctx W SP D S (sl / 16) st).gpr r = st.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
  refine ⟨_, _, _, _, p₁, p₂, ?_, cr₁, cw₁, cr₂, cw₂, by rw [pushed_rsp, pushed_rsp, he₁.rsp, he₂.rsp]⟩
  refine ⟨?_, i₁.trans i₂.symm⟩
  simp only [Proof.AesGcm.blocksToPub, Proof.AesGcm.arg]
  have hU₁' : (callUI M Ctx W SP D S (sl / 16) s₁).gpr .rsp = SP - BitVec.ofNat 64 32 := hU₁
  have hU₂' : (callUI M Ctx W SP D S (sl / 16) s₂).gpr .rsp = SP - BitVec.ofNat 64 32 := hU₂
  have a0₁' : stackArg (callUI M Ctx W SP D S (sl / 16) s₁) 0 = D := a0₁
  have a0₂' : stackArg (callUI M Ctx W SP D S (sl / 16) s₂) 0 = D := a0₂
  have a1₁' : stackArg (callUI M Ctx W SP D S (sl / 16) s₁) 1 = BitVec.ofNat 64 (sl / 16) := a1₁
  have a1₂' : stackArg (callUI M Ctx W SP D S (sl / 16) s₂) 1 = BitVec.ofNat 64 (sl / 16) := a1₂
  have a2₁' : stackArg (callUI M Ctx W SP D S (sl / 16) s₁) 2 = W + BitVec.ofNat 64 448 := a2₁
  have a2₂' : stackArg (callUI M Ctx W SP D S (sl / 16) s₂) 2 = W + BitVec.ofNat 64 448 := a2₂
  simp only [gU _ (by decide : Reg.rdi ≠ .rsp), gU _ (by decide : Reg.rsi ≠ .rsp), gU _ (by decide : Reg.rdx ≠ .rsp),
    gU _ (by decide : Reg.rcx ≠ .rsp), gU _ (by decide : Reg.r8 ≠ .rsp), gU _ (by decide : Reg.r9 ≠ .rsp),
    di₁, di₂, si₁, si₂, dx₁, dx₂, cx₁, cx₂, r8₁, r8₂, r9₁, r9₂, hU₁', hU₂', a0₁', a0₂', a1₁', a1₂', a2₁', a2₂',
    and_self]

/-- `prefix` calling `vg_aes_gcm_encrypt_blocks_to_prepared_iv96`, in two runs. -/
theorem prefix_ctI (T : BlkToFnI M) :
    RelCT isa (fun a b => a = σ ∧ b = σ') (SealSplit.prefix T.fn) fun _ _ => True :=
  prefix_ctG h h' T.fn (callI_rel h hI h' hI' T) (fun _ g => mid2_callI_wp h hI T g)
    (fun _ g => mid2_callI_wp h' hI' T g)

end

/-- After the index is put into `rax`: what `pushedPI` needs. -/
def MovI (σ s : State) : Prop :=
  s.gpr .rax = BitVec.ofNat 64 2 ∧ (∀ r, r ≠ .rax → s.gpr r = σ.gpr r) ∧ s.mem = σ.mem ∧ s.rd = σ.rd ∧
    s.wr = σ.wr

theorem movI_wp (σ : State) : ∀ s, s = σ → WP isa (.block [.mov32 .rax (imm 2)]) s (MovI σ) := fun s hs => by
  subst hs
  obtain ⟨s₁, run₁, a, g, m, rd, wr⟩ := movIdx_ok s
  exact WP.of_runBlock ⟨s₁, run₁, a, g, m, rd, wr⟩

theorem movI_check : ∃ hc, (taint.check (Taint.ofRegs []) (.block [.mov32 .rax (imm 2)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {M : CtxMode} {Ctx W SP D S : Addr} {R n sl : Nat} {σ σ' : State}
  (h : PP M Ctx W SP D S R n sl σ) (h' : PP M Ctx W SP D S R n sl σ')
  (kw : (below SP 64).Disjoint ⟨W, 2560⟩) (kd : (below SP 64).Disjoint ⟨D, n⟩)
  (ks : (below SP 64).Disjoint ⟨S, sl⟩) (kM : (below SP 64).Disjoint ⟨Ctx, M.len⟩) (sp : 64 ≤ SP.toNat)
include h h' kw kd ks kM sp

/-- `prefixI`, in two runs: the index a constant, its frame, and `prefix`
calling `vg_aes_gcm_encrypt_blocks_to_prepared_iv96`. -/
theorem prefixI_rel (T : BlkToFnI M) (hcb : ctrIndex (blockAt σ.mem (cbA W)) = 2)
    (hcb' : ctrIndex (blockAt σ'.mem (cbA W)) = 2) :
    RelCT isa (fun a b => a = σ ∧ b = σ') (Impl.AesGcm.X86_64.Fast.prefixI T.fn) fun _ _ => True := by
  unfold Impl.AesGcm.X86_64.Fast.prefixI
  refine RelCT.seq (step [] movI_check (fun _ _ _ r hr => by simp at hr) (fun _ _ g => g) (movI_wp σ) (movI_wp σ'))
    (RelCT.frame (R := fun _ _ => True) (fun _ _ g => by
      rw [g.1.2.1 _ (by decide), g.2.2.1 _ (by decide), h.env.rsp, h'.env.rsp]) ?_)
  refine rel_each fun a b ⟨s₁, s₂, ⟨m₁, m₂⟩, ha, hb⟩ => ?_
  subst ha hb
  obtain ⟨P₁, I₁⟩ := pushedPI h kw kd ks kM sp hcb m₁.1 m₁.2.1 m₁.2.2.1 m₁.2.2.2.1 m₁.2.2.2.2
  obtain ⟨P₂, I₂⟩ := pushedPI h' kw kd ks kM sp hcb' m₂.1 m₂.2.1 m₂.2.2.1 m₂.2.2.2.1 m₂.2.2.2.2
  exact prefix_ctI P₁ I₁ P₂ I₂ T

end

end VG.Proof.AesGcm.X86_64.Split
