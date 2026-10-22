module

import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixS
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixNCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixS
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixNCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixN

/-!
# AES-GCM `seal_split` on x86-64: `prefixS` in constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public values take the same branch of `sTest` (on the lengths); on the
path for one to three whole blocks, each piece is checked by the taint
analysis from the registers that hold the same values in both (`W`, then the
copy's arguments, then the key context, the state and `W`, then the data
and the number of blocks that `rbx` and `rbp` keep across the call, as
`SA`–`SE` give them), and the call of `vg_aes_ctr32` by its contract; the
other path is `prefixN`'s (`prefixSRel`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.Split

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn step)

theorem sTest_check : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block SealSplit.sTest) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem sCopyArgs_check : ∃ hc, (taint.check (Taint.ofRegs [.r15])
    (.block [.mov .rsi (.mem (at_ .r15 tlO)), .mov .rdi (.mem (at_ .r15 dataO)), .mov .rcx (.mem (at_ .r15 tlenO))])
    hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem sCtrArgs_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15]) (.block SealSplit.sCtrArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem sGh_check :
    ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r13, .r14]) SealSplit.sGh hc).isSome = true :=
  ⟨_, by unfold SealSplit.sGh SealSplit.sGhPre SealSplit.sGhPost SealSplit.sGhStep; taint_decide⟩

section
variable {Ctx W SP D S : Addr} {R n sl : Nat} {σ σ' : State}
  (h : PP (CtxMode.preparedN np hpn) Ctx W SP D S R n sl σ) (h' : PP (CtxMode.preparedN np hpn) Ctx W SP D S R n sl σ')
include h h'

/-- After `sTest`. -/
abbrev STs (sl : Nat) (σ t : State) : Prop :=
  t.cf = some (decide ((BitVec.ofNat 64 sl - 16#64).toNat < SealSplit.sLim)) ∧
    (∀ r, r ≠ .rax → t.gpr r = σ.gpr r) ∧ t.mem = σ.mem ∧ t.rd = σ.rd ∧ t.wr = σ.wr

/-- The path for one to three whole blocks, in two runs. -/
theorem sPath_rel (hF : Short.ShortFacts) (v : Proof.Aes.X86_64.Ctr32Impl) (hq : 1 ≤ sl / 16 ∧ sl / 16 ≤ 3) {P : State → State → Prop}
    (hP : ∀ a b, P a b → STs sl σ a ∧ STs sl σ' b) :
    RelCT isa P (.seq SealSplit.copySrc (.seq (.block SealSplit.sCtrArgs) (.seq (.call v.callee.name v.callee.code)
      (.seq SealSplit.sGh (.block SealSplit.rest))))) fun _ _ => True := by
  unfold SealSplit.copySrc
  refine RelCT.seq (RelCT.seq (step [.r15] sCopyArgs_check (F₁ := STs sl σ) (F₂ := STs sl σ')
    (G₁ := SA D S sl σ) (G₂ := SA D S sl σ')
    (fun _ _ g r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨⟨-, g₁, -⟩, ⟨-, g₂, -⟩⟩ := hP _ _ g
      rw [g₁ _ (by decide), g₂ _ (by decide), h.env.r15, h'.env.r15])
    hP (fun _ ⟨_, g, m, rd, wr⟩ => sA_ok h g m rd wr) (fun _ ⟨_, g, m, rd, wr⟩ => sA_ok h' g m rd wr))
    (step [.rsi, .rdi, .rcx] Gather.copy_check (F₁ := SA D S sl σ) (F₂ := SA D S sl σ')
      (G₁ := SB Ctx W SP D S sl σ) (G₂ := SB Ctx W SP D S sl σ')
      (fun _ _ g r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [g.1.rsi, g.2.rsi]
        · rw [g.1.rdi, g.2.rdi]
        · rw [g.1.rcx, g.2.rcx])
      (fun _ _ g => g) (fun _ g => sB_ok h hq g) (fun _ g => sB_ok h' hq g))) ?_
  refine RelCT.seq (step [.r13, .r14, .r15] sCtrArgs_check (F₁ := SB Ctx W SP D S sl σ) (F₂ := SB Ctx W SP D S sl σ')
    (G₁ := SC Ctx W SP D S R sl σ) (G₂ := SC Ctx W SP D S R sl σ')
    (fun _ _ g r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g.1.env.r13, g.2.env.r13]
      · rw [g.1.env.r14, g.2.env.r14]
      · rw [g.1.env.r15, g.2.env.r15])
    (fun _ _ g => g) (fun _ g => sC_ok h g) (fun _ g => sC_ok h' g)) ?_
  refine RelCT.seq (rel_wp (ctr_rel v (P := fun s₁ s₂ => SC Ctx W SP D S R sl σ s₁ ∧ SC Ctx W SP D S R sl σ' s₂)
      fun s₁ s₂ g => ⟨_, _, _, _, _, _, g.1.call, g.2.call, by rw [g.1.env.rsp, g.2.env.rsp]⟩)
    (fun _ _ g => g) (fun _ g => sD_ok v g) (fun _ g => sD_ok v g)) ?_
  refine RelCT.seq (step [.rbx, .rbp, .r13, .r14] sGh_check
    (F₁ := SD Ctx W SP D S R sl σ) (F₂ := SD Ctx W SP D S R sl σ')
    (G₁ := SE Ctx W SP D S R sl σ) (G₂ := SE Ctx W SP D S R sl σ')
    (fun _ _ g r hr => by
      obtain ⟨-, g₁, g₂⟩ := g
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [g₁.rbx, g₂.rbx]
      · rw [g₁.rbp, g₂.rbp]
      · rw [g₁.env.r13, g₂.env.r13]
      · rw [g₁.env.r14, g₂.env.r14])
    (fun _ _ g => g.2) (fun _ g => sE_ok h hq g) (fun _ g => sE_ok h' hq g)) ?_
  exact (step [.r15] rest_check (F₁ := SE Ctx W SP D S R sl σ) (F₂ := SE Ctx W SP D S R sl σ')
    (G₁ := fun _ => True) (G₂ := fun _ => True)
    (fun _ _ g r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨⟨u, hu, -, -, gu, -⟩, ⟨u', hu', -, -, gu', -⟩⟩ := g
      rw [gu _ (by decide), gu' _ (by decide), hu.env.r15, hu'.env.r15])
    (fun _ _ g => g) (fun _ g => WP.mono (sF_ok h hq hF g) fun _ _ => trivial)
    (fun _ g => WP.mono (sF_ok h' hq hF g) fun _ _ => trivial)).mono
    (fun _ _ g => g) fun _ _ _ => trivial

end

/-- `prefixS` in two runs. -/
theorem prefixSRel (hF : Short.ShortFacts) (v : Proof.Aes.X86_64.Ctr32Impl) {ctr : Fn} (hc : ctr = ⟨v.callee.name, v.callee.code⟩)
    {c : Prog isa} (hE : EncNOk np hpn c)
    (hct : ∃ hc, (taint.check (Taint.ofRegs encNRegs) c hc).isSome = true) (T : BlkToFn (CtxMode.preparedN np hpn)) :
    PreRel (CtxMode.preparedN np hpn) (SealSplit.prefixS ctr T.fn c) := by
  intro Ctx W SP D S R n sl σ σ' h h'
  subst hc
  unfold SealSplit.prefixS
  have hsl : ∀ {σ : State}, PP (CtxMode.preparedN np hpn) Ctx W SP D S R n sl σ → sl < 2 ^ 64 := fun h => by
    have := h.sl_le; have := h.data.ok.lt; omega
  refine RelCT.seq (step [.r15] sTest_check (F₁ := (· = σ)) (F₂ := (· = σ'))
    (G₁ := STs sl σ) (G₂ := STs sl σ')
    (fun _ _ g r hr => by
      obtain ⟨rfl, rfl⟩ := g; simp only [List.mem_singleton] at hr; subst hr; rw [h.env.r15, h'.env.r15])
    (fun _ _ g => g) (fun _ hs => by rw [hs]; exact sTest_ok h.env h.slen)
    (fun _ hs => by rw [hs]; exact sTest_ok h'.env h'.slen)) ?_
  refine RelCT.ite (fun _ _ g => by simp only [eval, g.1.1, g.2.1]) ?_ ?_
  · refine StreamTo.RelCT.of_imp (1 ≤ sl / 16 ∧ sl / 16 ≤ 3) (fun _ _ g => by
      have e := g.2; simp only [eval, g.1.1.1] at e; exact sLim_sound (hsl h) (by simpa using e)) fun hq => ?_
    exact sPath_rel h h' hF v hq fun _ _ g => g.1
  · refine rel_each fun t t' g => ?_
    obtain ⟨⟨⟨-, g₁, m₁, rd₁, wr₁⟩, ⟨-, g₂, m₂, rd₂, wr₂⟩⟩, -⟩ := g
    have he : ∀ {σ t : State} {M : CtxMode} {R : Nat}, PP M Ctx W SP D S R n sl σ →
        (∀ r, r ≠ .rax → t.gpr r = σ.gpr r) → t.rd = σ.rd → t.wr = σ.wr →
        Env Ctx (W + BitVec.ofNat 64 16) W SP t := fun h g rd wr => h.env.keep (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide))
      rd wr
    exact prefixNRel hE hct T (h.of_eq (he h g₁ rd₁ wr₁) m₁ rd₁ wr₁) (h'.of_eq (he h' g₂ rd₂ wr₂) m₂ rd₂ wr₂)

/-! ## What every instruction of `prefixS` does not do -/

/-- The path for one to three whole blocks, but for the call. -/
theorem sParts_mx : (SealSplit.copySrc.allInstrs (fun i => !loadsMxcsr i) &&
    (Code.block SealSplit.sCtrArgs : Prog isa).allInstrs (fun i => !loadsMxcsr i) &&
    SealSplit.sGh.allInstrs (fun i => !loadsMxcsr i) &&
    (Code.block SealSplit.rest : Prog isa).allInstrs (fun i => !loadsMxcsr i)) = true := by
  decide +kernel
theorem sParts_spSafe : (SealSplit.copySrc.all (fun i => !X86_64.isa.writesSp i) &&
    (Code.block SealSplit.sCtrArgs : Prog isa).all (fun i => !X86_64.isa.writesSp i) &&
    SealSplit.sGh.all (fun i => !X86_64.isa.writesSp i) &&
    (Code.block SealSplit.rest : Prog isa).all (fun i => !X86_64.isa.writesSp i)) = true := by
  decide +kernel
theorem sParts_xdepth : SealSplit.copySrc.x86_64Depth = 0 ∧ SealSplit.sGh.x86_64Depth = 0 := by
  decide +kernel

theorem prefixS_mx {ctr fTo : Fn} {c : Prog isa} (hc : ctr.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (h : (SealSplit.prefixN fTo c).allInstrs (fun i => !loadsMxcsr i) = true) :
    (SealSplit.prefixS ctr fTo c).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := sParts_mx
  simp only [Bool.and_eq_true] at e
  simp only [SealSplit.prefixS, Code.allInstrs, Bool.and_eq_true] at h hc ⊢
  exact ⟨by decide, ⟨e.1.1.1, e.1.1.2, hc, e.1.2, e.2⟩, h⟩

theorem prefixS_spSafe {ctr fTo : Fn} {c : Prog isa} (hc : ctr.code.all (fun i => !X86_64.isa.writesSp i) = true)
    (h : (SealSplit.prefixN fTo c).all (fun i => !X86_64.isa.writesSp i) = true) :
    (SealSplit.prefixS ctr fTo c).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := sParts_spSafe
  simp only [Bool.and_eq_true] at e
  simp only [SealSplit.prefixS, Code.all, Bool.and_eq_true] at h hc ⊢
  exact ⟨by decide, ⟨e.1.1.1, e.1.1.2, hc, e.1.2, e.2⟩, h⟩

theorem prefixS_xdepth {ctr fTo : Fn} {c : Prog isa} (hc : ctr.code.x86_64Depth = 0) {d : Nat} (hd : 8 ≤ d)
    (h : (SealSplit.prefixN fTo c).x86_64Depth ≤ d) : (SealSplit.prefixS ctr fTo c).x86_64Depth ≤ d := by
  have e := sParts_xdepth
  simp only [SealSplit.prefixS, Code.x86_64Depth, hc, e.1, e.2] at h ⊢
  simp only [Nat.max_le] at h ⊢; omega

end VG.Proof.AesGcm.X86_64.Split
