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
import VerifiedGarbage.Proof.Framework.Cold
meta import VerifiedGarbage.Proof.Framework.Cold

/-!
# AES-GCM `seal_split` on x86-64: `prefixS` in constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public values take the same branches of `nTest`, `preTest3` and the
test of `rax` (on the lengths); on the path for one to three whole blocks,
each piece is checked by the taint analysis from the registers that hold the
same values in both (`W`, then the copy's arguments, then the key context,
the state and `W`, then the data and the number of blocks that `rbx` and
`rbp` keep across the call, as `SA`–`SE` give them), and the call of
`vg_aes_ctr32` by its contract; the others are `prefix`'s pieces
(`callPart_rel`, `tail_rel`) and `prefixN`'s (`prefixFRel`, `prefixSRel`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.Split

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn step)

theorem preTest3_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block SealSplit.preTest3) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem tst_check :
    ∃ hc, (taint.check (Taint.ofRegs [.rax]) (.block [.alu .test .rax (.reg .rax)]) hc).isSome = true :=
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

/-- What the path for one to three whole blocks starts from. -/
abbrev STs (σ t : State) : Prop :=
  (∀ r, r ≠ .rax → t.gpr r = σ.gpr r) ∧ t.mem = σ.mem ∧ t.rd = σ.rd ∧ t.wr = σ.wr

/-- After `preTest3`. -/
abbrev ST3 (sl : Nat) (σ t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (sl / 16) ∧ t.cf = some (decide (sl / 16 < 3)) ∧ STs σ t

/-- After its test of `rax`. -/
abbrev STz (sl : Nat) (σ t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (sl / 16) ∧ t.zf = some (decide (sl / 16 = 0)) ∧ STs σ t

/-- The path for one to three whole blocks, in two runs. -/
theorem sPath_rel (hF : Short.ShortFacts) (v : Proof.Aes.X86_64.Ctr32Impl) (hq : 1 ≤ sl / 16 ∧ sl / 16 ≤ 3) {P : State → State → Prop}
    (hP : ∀ a b, P a b → STs σ a ∧ STs σ' b) :
    RelCT isa P (.seq SealSplit.copySrc (.seq (.block SealSplit.sCtrArgs) (.seq (.call v.callee.name v.callee.code)
      (.seq SealSplit.sGh (.block SealSplit.rest))))) fun _ _ => True := by
  unfold SealSplit.copySrc
  refine RelCT.seq (RelCT.seq (step [.r15] sCopyArgs_check (F₁ := STs σ) (F₂ := STs σ')
    (G₁ := SA D S sl σ) (G₂ := SA D S sl σ')
    (fun _ _ g r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨⟨g₁, -⟩, ⟨g₂, -⟩⟩ := hP _ _ g
      rw [g₁ _ (by decide), g₂ _ (by decide), h.env.r15, h'.env.r15])
    hP (fun _ ⟨g, m, rd, wr⟩ => sA_ok h g m rd wr) (fun _ ⟨g, m, rd, wr⟩ => sA_ok h' g m rd wr))
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

/-- `prefixF` in two runs. -/
theorem prefixFRel (hF : Short.ShortFacts) (v : Proof.Aes.X86_64.Ctr32Impl)
    (T : BlkToFn (CtxMode.preparedN np hpn)) :
    PreRel (CtxMode.preparedN np hpn) (SealSplit.prefixF ⟨v.callee.name, v.callee.code⟩ T.fn) := by
  intro Ctx W SP D S R n sl σ σ' h h'
  unfold SealSplit.prefixF SealSplit.preTail
  have hsl : ∀ {σ : State}, PP (CtxMode.preparedN np hpn) Ctx W SP D S R n sl σ → sl < 2 ^ 64 := fun h => by
    have := h.sl_le; have := h.data.ok.lt; omega
  have he : ∀ {σ t : State}, PP (CtxMode.preparedN np hpn) Ctx W SP D S R n sl σ → STs σ t →
      Env Ctx (W + BitVec.ofNat 64 16) W SP t := fun h g => h.env.keep (fun r hr => g.1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide))
    g.2.2.1 g.2.2.2
  have pre4 : ∀ {σ : State}, PP (CtxMode.preparedN np hpn) Ctx W SP D S R n sl σ →
      WP isa (.block SealSplit.preTest3) σ (ST3 sl σ) := fun h =>
    WP.mono (preTest3_ok (hsl h) h.env h.slen) fun _ ⟨ax, cf, g, m, rd, wr⟩ => ⟨ax, cf, g, m, rd, wr⟩
  refine RelCT.seq (step [.r15] preTest3_check (F₁ := (· = σ)) (F₂ := (· = σ'))
    (G₁ := ST3 sl σ) (G₂ := ST3 sl σ')
    (fun _ _ g r hr => by
      obtain ⟨rfl, rfl⟩ := g; simp only [List.mem_singleton] at hr; subst hr; rw [h.env.r15, h'.env.r15])
    (fun _ _ g => g) (fun _ hs => by rw [hs]; exact pre4 h) (fun _ hs => by rw [hs]; exact pre4 h')) ?_
  refine RelCT.iteCold (RelCT.ite (fun _ _ g => by simp only [eval, g.1.2.1, g.2.2.1]) ?_ ?_)
  · refine StreamTo.RelCT.of_imp (sl / 16 < 3) (fun _ _ g => by
      have e := g.2; simp only [eval, g.1.1.2.1] at e; simpa using e) fun h4 => ?_
    have tz : ∀ {σ t : State}, ST3 sl σ t → WP isa (.block [.alu .test .rax (.reg .rax)]) t (STz sl σ) :=
      fun ⟨ax, _, g, m, rd, wr⟩ => WP.mono (tst_ok (q := sl / 16) (by omega) ax) fun _ ⟨zf, g', m', rd', wr'⟩ =>
        ⟨by rw [g' .rax]; exact ax, zf, fun r hr => (g' r).trans (g r hr), m'.trans m, rd'.trans rd, wr'.trans wr⟩
    refine RelCT.seq (step [.rax] tst_check (F₁ := ST3 sl σ) (F₂ := ST3 sl σ')
      (G₁ := STz sl σ) (G₂ := STz sl σ')
      (fun _ _ g r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [g.1.1.1, g.1.2.1])
      (fun _ _ g => g.1) (fun _ g => tz g) (fun _ g => tz g)) ?_
    refine RelCT.ite (fun _ _ g => by simp only [eval, g.1.2.1, g.2.2.1]) ?_ ?_
    · refine StreamTo.RelCT.of_imp (sl / 16 = 0) (fun _ _ g => by
        have e := g.2; simp only [eval, g.1.1.2.1] at e; simpa using e) fun h0 => ?_
      exact (tail_rel h h').mono (fun _ _ g =>
        ⟨mid2_zero ⟨he h g.1.1.2.2, g.1.1.1, g.1.1.2.1, g.1.1.2.2.2⟩ h0,
          mid2_zero ⟨he h' g.1.2.2.2, g.1.2.1, g.1.2.2.1, g.1.2.2.2.2⟩ h0⟩) fun _ _ g => g
    · refine StreamTo.RelCT.of_imp (sl / 16 ≠ 0) (fun _ _ g => by
        have e := g.2; simp only [eval, g.1.1.2.1] at e; simpa using e) fun h0 => ?_
      exact sPath_rel h h' hF v ⟨by omega, by omega⟩ fun _ _ g => ⟨g.1.1.2.2, g.1.2.2.2⟩
  · exact RelCT.seq ((callPart_rel h h' T).mono (fun _ _ g =>
      ⟨⟨he h g.1.1.2.2, g.1.1.1, g.1.1.2.2.2⟩, ⟨he h' g.1.2.2.2, g.1.2.1, g.1.2.2.2.2⟩⟩) fun _ _ g => g)
      (tail_rel h h')

/-- `prefixS` in two runs. -/
theorem prefixSRel (hF : Short.ShortFacts) (v : Proof.Aes.X86_64.Ctr32Impl) {ctr : Fn} (hc : ctr = ⟨v.callee.name, v.callee.code⟩)
    {c : Prog isa} (hE : EncNOk np hpn c)
    (hct : ∃ hc, (taint.check (Taint.ofRegs encNRegs) c hc).isSome = true) (T : BlkToFn (CtxMode.preparedN np hpn)) :
    PreRel (CtxMode.preparedN np hpn) (SealSplit.prefixS ctr T.fn c) := by
  intro Ctx W SP D S R n sl σ σ' h h'
  subst hc
  unfold SealSplit.prefixS
  refine RelCT.seq (step [.r15] nTest_check (F₁ := (· = σ)) (F₂ := (· = σ'))
    (G₁ := NT n sl σ) (G₂ := NT n sl σ')
    (fun _ _ g r hr => by
      obtain ⟨rfl, rfl⟩ := g; simp only [List.mem_singleton] at hr; subst hr; rw [h.env.r15, h'.env.r15])
    (fun _ _ g => g) (fun _ hs => by rw [hs]; exact nTest_ok h.data.ok.lt h.sl_le h.env h.slen h.len)
    (fun _ hs => by rw [hs]; exact nTest_ok h'.data.ok.lt h'.sl_le h'.env h'.slen h'.len)) ?_
  refine RelCT.ite (fun _ _ g => by simp only [eval, g.1.1, g.2.1]) ?_ ?_
  · refine StreamTo.RelCT.of_imp (1 ≤ sl / 256 ∧ sl / 256 < n / 256) (fun _ _ g => by
      have e := g.2; simp only [eval, g.1.1.1] at e; simpa using e) fun hC => ?_
    exact nPath_rel h h' hE hct hC fun _ _ g => g.1
  · refine rel_each fun t t' g => ?_
    obtain ⟨⟨⟨-, g₁, m₁, rd₁, wr₁⟩, ⟨-, g₂, m₂, rd₂, wr₂⟩⟩, -⟩ := g
    have he : ∀ {σ t : State} {M : CtxMode} {R : Nat}, PP M Ctx W SP D S R n sl σ →
        (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = σ.gpr r) → t.rd = σ.rd → t.wr = σ.wr →
        Env Ctx (W + BitVec.ofNat 64 16) W SP t := fun h g rd wr => h.env.keep (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide))
      rd wr
    exact prefixFRel hF v T (h.of_eq (he h g₁ rd₁ wr₁) m₁ rd₁ wr₁) (h'.of_eq (he h' g₂ rd₂ wr₂) m₂ rd₂ wr₂)

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
  simp only [SealSplit.prefixS, SealSplit.prefixN, SealSplit.prefixF, Code.iteCold, SealSplit.prefix, SealSplit.preTail,
    Code.allInstrs, Bool.and_eq_true] at e h hc ⊢
  simp only [e, h, hc, and_self, and_true, true_and]
  decide

theorem prefixS_spSafe {ctr fTo : Fn} {c : Prog isa} (hc : ctr.code.all (fun i => !X86_64.isa.writesSp i) = true)
    (h : (SealSplit.prefixN fTo c).all (fun i => !X86_64.isa.writesSp i) = true) :
    (SealSplit.prefixS ctr fTo c).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := sParts_spSafe
  simp only [SealSplit.prefixS, SealSplit.prefixN, SealSplit.prefixF, Code.iteCold, SealSplit.prefix, SealSplit.preTail,
    Code.all, Bool.and_eq_true] at e h hc ⊢
  simp only [e, h, hc, and_self, and_true, true_and]
  decide

theorem prefixS_xdepth {ctr fTo : Fn} {c : Prog isa} (hc : ctr.code.x86_64Depth = 0) {d : Nat} (hd : 8 ≤ d)
    (h : (SealSplit.prefixN fTo c).x86_64Depth ≤ d) : (SealSplit.prefixS ctr fTo c).x86_64Depth ≤ d := by
  have e := sParts_xdepth
  simp only [SealSplit.prefixS, SealSplit.prefixN, SealSplit.prefixF, Code.iteCold, SealSplit.prefix, SealSplit.preTail,
    Code.x86_64Depth, hc, e.1, e.2] at h ⊢
  simp only [Nat.max_le] at h ⊢; omega

end VG.Proof.AesGcm.X86_64.Split
