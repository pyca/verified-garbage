module
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Crypt

import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Correct
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorSplitVerified
import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Crypt
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Correct
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorSplitVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# ChaCha20-Poly1305 with the data's first bytes from `src`, x86-64: constant time

`sealSplitBody` leaks the same in two runs whose entry states agree on what
`seal`'s do and on `src` and `src_len` (`PubS`): as `seal_rel`, but for the
branch for more than 960 bytes, `cryptBigSplit`, whose arguments for the
inline code of `vg_chacha20_xor_split_avx512` the code computes from
`src_len`, which it loads from the stack, where the taint analysis does not
track it. So that branch is analysed in pieces: `cryptPre` and the last block
by the taint analysis, `splitArgs` by the taint analysis for its trace and by
correctness for the arguments it leaves (the same in both runs, `RelCT.wp`),
and the inline code by its own constant-time proof (`relCT_inline`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Split

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealSplit
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- `sealSplitBody`'s public data: `seal`'s, `src` and `src_len`. -/
def PubS (s₁ s₂ : State) : Prop :=
  pubX86_64 s₁ s₂ ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3

/-- Only the registers `rs` public, nothing known of the regions. -/
def τR (rs : List Reg) : X86_64.Taint.T := { regs := .ofList rs, flags := false }

theorem agreeR {rs : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    X86_64.Taint.Agree (τR rs) s₁ s₂ :=
  ⟨⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩, fun h => absurd rfl h,
    ⟨fun h => absurd rfl h, fun _ h => by simp [τR] at h⟩, ⟨fun h => absurd rfl h, fun _ h => by simp [τR] at h⟩,
    fun _ h => by simp [τR] at h, fun _ h => by simp [τR] at h, X86_64.Taint.noLo, X86_64.Taint.noXr⟩

theorem PubS.eqs {s₀ s₀' : State} (hq : PubS s₀ s₀') :
    L s₀ = L s₀' ∧ SL s₀ = SL s₀' ∧ mm s₀ = mm s₀' ∧ sp s₀ = sp s₀' := by
  obtain ⟨⟨-, -, -, -, -, p6, -, -, -⟩, p2, p3⟩ := hq
  have e1 : L s₀ = L s₀' := by simp only [L, p6]
  exact ⟨e1, by simp only [SL, p3], by simp only [mm, e1], p2⟩

/-! ## Up to the branch on the length -/

/-- At the branch on the length, with what the branch for more than 960
bytes needs: the ChaCha20 state, and the stack arguments, as on entry. -/
structure AtIteS (s₀ s : State) : Prop where
  at_ : AtIte 960 1024 s₀ s
  st : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  s2 : s.mem.readW (stackArgAddr s₀ 2) 64 = stackArg s₀ 2
  s3 : s.mem.readW (stackArgAddr s₀ 3) 64 = stackArg s₀ 3

theorem args_inv {s₀ : State} (hT : SPre s₀) {s : State} (h : Inv s₀ s) {j : Nat} (hj : j = 2 ∨ j = 3) :
    s.mem.readW (stackArgAddr s₀ j) 64 = stackArg s₀ j :=
  arg_frame hj h.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hT.g_c.sub_right (fun _ h => sub_ctx s₀ (by lit_omega) _ h), hT.g_d, hT.g_k⟩)

theorem sealMidS_ok (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State} (hT : SPre s₀) {s : State}
    (h : AfterF 960 1024 s₀ s) : WP isa (sealMid 960 b) s (AtIteS s₀) := by
  have hp := hT.hp
  have hM := mOf_le 960 1024 (L s₀)
  refine WP.seq (WP.mono (prologueB_ok (by lit_omega) hp h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (macPad_ok b hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.r15
    h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, _⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]), h₁.rbp]))
    fun s₃ ⟨i₃, _, f₃, _⟩ => ?_)
  refine WP.mono (cmpFold_ok (fold := 960) (by lit_omega) i₃.r13) fun s₄ ⟨g₄, rd₄, wr₄, m₄, c₄⟩ => ?_
  have a₄ : AtIte 960 1024 s₀ s₄ :=
    ⟨i₃.step (fun r _ => by rw [g₄]) rd₄ wr₄ (rs := []) (by rw [m₄]; exact Frame.refl _ _)
      (fun _ h => by simp at h) (fun _ h => by simp at h), c₄,
      by rw [m₄]; exact ks_frame f₃ (by rdisj_all) hM (ks_frame f₂ (by rdisj_all) hM h₁.ks)⟩
  exact ⟨a₄, by rw [m₄, stateAt_frame f₃ (by rdisj_all), stateAt_frame f₂ (by rdisj_all), h₁.st],
    args_inv hT a₄.inv (.inl rfl), args_inv hT a₄.inv (.inr rfl)⟩

/-! ## The branch for more than 960 bytes, in pieces -/

/-- After `cryptPre`: what `splitArgs` needs. -/
structure BigPre (s₀ s : State) : Prop where
  args : XArgsM s₀ (mm s₀) s
  rd : s.rd = s₀.rd
  r15 : s.gpr .r15 = cx s₀
  s2 : s.mem.readW (stackArgAddr s₀ 2) 64 = stackArg s₀ 2
  s3 : s.mem.readW (stackArgAddr s₀ 3) 64 = stackArg s₀ 3

theorem cryptPre_big {s₀ : State} (hT : SPre s₀) {s : State} (h : AtIteS s₀ s) :
    WP isa (cryptPre 960 1024 6) s (BigPre s₀) := by
  have hp := hT.hp
  have hML := mOf_le_len 960 1024 (L s₀)
  refine WP.mono (cryptPre_ok Proof.ChaCha20.X86_64.XorImpl.avx512 (pass_of _) hp h.at_.inv)
    fun s₁ ⟨a₁, cs₁, rd₁, mx, fx, dx, m₁⟩ => ?_
  change XArgsM s₀ (mm s₀) s₁ at a₁
  change Frame [⟨dp s₀, mm s₀⟩] s.mem mx at fx
  change s₁.mem = mx.writeW (off (cx s₀) 112) (BitVec.ofNat 32 (mm s₀ / 64 + 1)) at m₁
  have fw : Frame [sub s₀ 64 64] mx s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  have hpre : ∀ r ∈ [(⟨dp s₀, mm s₀⟩ : Region)], (arg2R s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hT.g_d.sub_right (Region.sub_prefix hML)
  have harg : ∀ r ∈ [sub s₀ 64 64], (arg2R s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hT.g_c.sub_right (sub_ctx s₀ (by lit_omega))
  exact ⟨a₁, by rw [rd₁, h.at_.inv.rd], by rw [cs₁ _ (by simp [calleeSaved]), h.at_.inv.r15],
    by rw [arg_frame (.inl rfl) fw harg, arg_frame (.inl rfl) fx hpre, h.s2],
    by rw [arg_frame (.inr rfl) fw harg, arg_frame (.inr rfl) fx hpre, h.s3]⟩

/-- After `splitArgs`: the inline code's arguments, and what `After` needs. -/
structure ArgsS (s₀ s : State) : Prop where
  sa : SArgs s₀ (mm s₀) s
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r15 : s.gpr .r15 = cx s₀
  r14 : s.gpr .r14 = dp s₀
  r13 : s.gpr .r13 = s₀.gpr .r9
  r12 : s.gpr .r12 = tp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem splitArgs_args {s₀ : State} (hT : SPre s₀) {s : State} (h : BigPre s₀ s) :
    WP isa (.block splitArgs) s (ArgsS s₀) :=
  WP.mono (splitArgs_ok hT h.args h.rd h.s2 h.s3) fun _ ⟨sa, cs, rd, wr, _⟩ =>
    ⟨sa, by rw [cs _ calleeSaved_rsp, h.args.rsp], by rw [cs _ (by simp [calleeSaved]), h.r15],
      by rw [cs _ (by simp [calleeSaved]), h.args.r14], by rw [cs _ (by simp [calleeSaved]), h.args.r13],
      by rw [cs _ (by simp [calleeSaved]), h.args.r12], by rw [rd, h.rd], by rw [wr, h.args.wr]⟩

/-- After the inline code: what the last block needs. -/
structure InlS (s₀ s : State) : Prop where
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r15 : s.gpr .r15 = cx s₀
  r14 : s.gpr .r14 = dp s₀
  r13 : s.gpr .r13 = s₀.gpr .r9
  r12 : s.gpr .r12 = tp s₀
  wr : s.wr = s₀.wr

theorem inline_inl {s₀ : State} (hT : SPre s₀) {s : State} (h : ArgsS s₀ s) :
    WP isa Impl.ChaCha20.X86_64.Avx512.xorSplit s (InlS s₀) :=
  h.sa.inline hT (mOf_le_len 960 1024 (L s₀)) h.rsp h.rd h.wr fun _ _ wr abi _ _ =>
    ⟨by rw [abi.1 _ calleeSaved_rsp, h.rsp], by rw [abi.1 _ (by simp [calleeSaved]), h.r15],
      by rw [abi.1 _ (by simp [calleeSaved]), h.r14], by rw [abi.1 _ (by simp [calleeSaved]), h.r13],
      by rw [abi.1 _ (by simp [calleeSaved]), h.r12], by rw [wr, h.wr]⟩

theorem ptr_after {s₀ : State} {s : State} (h : InlS s₀ s) :
    WP isa (.block (ptr .rsi .r15 128)) s (After s₀) :=
  WP.mono (ptr_ok .rsi .r15 (k := 128) (by lit_omega) s) fun _ ⟨e, g, _, wr, _⟩ =>
    ⟨by rw [e, h.r15, off_eq], by rw [g _ (by decide), h.rsp], by rw [g _ (by decide), h.r13],
      by rw [g _ (by decide), h.r14], by rw [g _ (by decide), h.r12], by rw [wr, h.wr]⟩

theorem splitArgs_taint : ∃ h, (taintS.check (τR [.rsp]) (.block splitArgs) h).isSome = true := by
  taint_decide_sum []

theorem ptr_taint : ∃ h, (taintS.check (τR [.r15]) (.block (ptr .rsi .r15 128)) h).isSome = true := by
  taint_decide_sum []

section
variable {s₀ s₀' : State} (hT : SPre s₀) (hT' : SPre s₀') (hq : PubS s₀ s₀')
include hT hT' hq

/-- The inline code, in two runs from the same arguments. -/
theorem inline_rel :
    RelCT isa (fun s₁ s₂ => ArgsS s₀ s₁ ∧ ArgsS s₀' s₂) Impl.ChaCha20.X86_64.Avx512.xorSplit
      fun s₁ s₂ => InlS s₀ s₁ ∧ InlS s₀' s₂ := by
  obtain ⟨eL, eSL, emm, esp⟩ := hq.eqs
  obtain ⟨⟨-, -, -, -, p5, -, p7, -, p9⟩, -, -⟩ := hq
  have hm := mOf_le_len 960 1024 (L s₀)
  have hm' := mOf_le_len 960 1024 (L s₀')
  have ct := regionModel.relCT_inline (c := Impl.ChaCha20.X86_64.Avx512.xorSplit)
    (Pre := Proof.ChaCha20.xorSplitX86_64.pre) (Pub := Proof.ChaCha20.xorSplitX86_64.pub)
    (fun s hs => let ⟨t, s', e, _, p⟩ := Proof.ChaCha20.X86_64.Avx512Split.xorSplit_correct s hs; ⟨t, s', e, p⟩)
    Proof.ChaCha20.X86_64.Avx512Split.xorSplit_ct
    (P := fun s₁ s₂ => ArgsS s₀ s₁ ∧ ArgsS s₀' s₂) fun s₁ s₂ ⟨a₁, a₂⟩ =>
    ⟨[srcM s₀ (mm s₀)], wrM s₀ (mm s₀), [srcM s₀' (mm s₀')], wrM s₀' (mm s₀'),
      a₁.sa.pre hT hm a₁.rsp, a₂.sa.pre hT' hm' a₂.rsp, by
        change State.gpr _ .rdi = State.gpr _ .rdi ∧ _
        simp only [regionModel, State.withRegions_gpr, a₁.sa.rdi, a₁.sa.rsi, a₁.sa.rdx, a₁.sa.rcx, a₁.sa.r8,
          a₁.sa.r9, a₂.sa.rdi, a₂.sa.rsi, a₂.sa.rdx, a₂.sa.rcx, a₂.sa.r8, a₂.sa.r9, a₁.rsp, a₂.rsp, cx, dp,
          eL, eSL, emm, esp, p5, p7, p9]
        exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩,
      SArgs.hc hT hm a₁.rd a₁.wr, SArgs.hw hT hm a₁.wr, SArgs.hc hT' hm' a₂.rd a₂.wr, SArgs.hw hT' hm' a₂.wr⟩
  exact (ct.wp fun _ _ h => ⟨inline_inl hT h.1, inline_inl hT' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The branch for more than 960 bytes, in two runs. -/
theorem big_rel :
    RelCT isa (fun s₁ s₂ => (AtIteS s₀ s₁ ∧ AtIteS s₀' s₂) ∧ isa.eval .b s₁ = some false) cryptBigSplit
      fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂ := by
  have hp := hT.hp
  have hp' := hT'.hp
  obtain ⟨-, -, -, -⟩ := hq.eqs
  have hq₀ := hq.1
  have hqi := hq
  obtain ⟨⟨-, -, -, -, -, -, p7, -, p9⟩, -, -⟩ := hq
  have hfp : FoldPoly 960 1024 6 .avx512 := .inr (.inr ⟨rfl, rfl, rfl, .inl rfl⟩)
  obtain ⟨_, hX⟩ := cryptPre_taint true hfp
  obtain ⟨_, hA⟩ := splitArgs_taint
  obtain ⟨_, hP⟩ := ptr_taint
  have pre := (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (AtIteS s₀ s₁ ∧ AtIteS s₀' s₂) ∧ isa.eval .b s₁ = some false)
    (τS true) (fun _ _ h => agreeS hp hp' hq₀ h.1.1.at_ h.1.2.at_) hX).wp
    (F₁ := BigPre s₀) (F₂ := BigPre s₀') fun _ _ h => ⟨cryptPre_big hT h.1.1, cryptPre_big hT' h.1.2⟩
  have args := (RelCT.taint (A := taintS) (P := fun s₁ s₂ => True ∧ BigPre s₀ s₁ ∧ BigPre s₀' s₂)
    (τR [.rsp]) (fun _ _ h => agreeR (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
      rw [h.2.1.args.rsp, h.2.2.args.rsp, p7])) hA).wp
    (F₁ := ArgsS s₀) (F₂ := ArgsS s₀') fun _ _ h => ⟨splitArgs_args hT h.2.1, splitArgs_args hT' h.2.2⟩
  have last := (RelCT.taint (A := taintS) (P := fun s₁ s₂ => InlS s₀ s₁ ∧ InlS s₀' s₂)
    (τR [.r15]) (fun _ _ h => agreeR (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
      rw [h.1.r15, h.2.r15, cx, cx, p9])) hP).wp
    (F₁ := After s₀) (F₂ := After s₀') fun _ _ h => ⟨ptr_after h.1, ptr_after h.2⟩
  exact (pre.seq ((args.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((inline_rel hT hT' hqi).seq (last.mono (fun _ _ h => h) fun _ _ h => h.2)))).mono (fun _ _ h => h)
    fun _ _ h => h

end

/-! ## `sealSplitBody` -/

theorem sealSplitBody_exec {x : Impl.ChaCha20.X86_64.Callee} {b : Impl.Poly1305.X86_64.Blocks}
    {s s' : State} {t : List Leak} (h : Exec isa (sealSplitBody x b) s t s') :
    Exec isa (.seq (.block entry) (.seq (prologueA 960 1024 6)
      (.seq (.call x.name x.code)
      (.seq (sealMid 960 b) (.seq (.ite .b (cryptSmall 6) cryptBigSplit) (sealPost 960 1024 6 b)))))) s t s' := by
  cases h with | seq e₀ h => cases h with | seq hP h => cases hP with | seq ePA hP => cases hP with
  | seq eC ePB => cases h with | seq eMA h => cases h with | seq eLEN h => cases h with | seq hC h =>
  cases hC with | seq eCMP hC => cases hC with | seq eITE hC => cases hC with | seq eANC hC =>
  cases hC with | seq eFM hC => cases hC with | seq eADD eZK => cases h with | seq eMC h =>
  cases h with | seq eFT eRE =>
  have := Exec.seq e₀ (Exec.seq ePA (Exec.seq eC (Exec.seq (Exec.seq ePB (Exec.seq eMA (Exec.seq eLEN eCMP)))
    (Exec.seq eITE (Exec.seq (Exec.seq eANC (Exec.seq eFM (Exec.seq eADD eZK)))
      (Exec.seq eMC (Exec.seq eFT eRE)))))))
  simp only [List.append_assoc] at this ⊢
  exact this

theorem sealSplitBody_rel {s₀ s₀' : State} (hT : SPre s₀) (hT' : SPre s₀') (hq : PubS s₀ s₀')
    (v : Proof.ChaCha20.X86_64.XorImpl) (b : Impl.Poly1305.X86_64.Blocks) (hvb : v.poly = b)
    (hb : b = .avx512 ∨ b = .ifma) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (sealSplitBody v.callee b) fun _ _ => True := by
  have c1 := call1_rel hT.hp hT'.hp hq.1 v (pass := 1024)
  rw [big_fold (hvb ▸ hb)] at c1
  have hp := hT.hp
  have hp' := hT'.hp
  have hq₀ := hq.1
  obtain ⟨eL, -, -, -⟩ := hq.eqs
  have hfp : FoldPoly 960 1024 6 b := .inr (.inr ⟨rfl, rfl, rfl, hb⟩)
  obtain ⟨_, hA⟩ := prologueA_taint true hfp
  have pA := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => s₁ = entryS s₀ ∧ s₂ = entryS s₀') (τ₀ true)
    (fun _ _ h => by rw [h.1, h.2]; exact agree₀ hp hp' hq₀) hA).wp
    (F₁ := FArgs 960 1024 s₀) (F₂ := FArgs 960 1024 s₀') fun _ _ h =>
    ⟨by rw [h.1]; exact prologueA_ok (by lit_omega) (.inr (.inl rfl)) (.inr (.inr rfl)) hp,
      by rw [h.2]; exact prologueA_ok (by lit_omega) (.inr (.inl rfl)) (.inr (.inr rfl)) hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨_, hmid⟩ := sealMid_taint hfp
  have mid := ((RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => AfterF 960 1024 s₀ s₁ ∧ AfterF 960 1024 s₀' s₂) (τA true)
    (fun _ _ h => agreeA hp hp' hq₀ h.1 h.2) hmid).wp (F₁ := AtIteS s₀) (F₂ := AtIteS s₀') fun _ _ h =>
      ⟨sealMidS_ok b hT h.1, sealMidS_ok b hT' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have hc : ∀ s₁ s₂, (AtIteS s₀ s₁ ∧ AtIteS s₀' s₂) → isa.eval .b s₁ = isa.eval .b s₂ := fun s₁ s₂ h => by
    simp [eval, h.1.at_.cf, h.2.at_.cf, eL]
  obtain ⟨_, hS⟩ := cryptSmall_taint true hfp
  have small := (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (AtIteS s₀ s₁ ∧ AtIteS s₀' s₂) ∧ isa.eval .b s₁ = some true)
    (τS true) (fun _ _ h => agreeS hp hp' hq₀ h.1.1.at_ h.1.2.at_) hS).wp (F₁ := After s₀) (F₂ := After s₀')
    fun s₁ s₂ h => by
      have e₁ := h.2
      have e₂ := (hc _ _ h.1).symm.trans h.2
      simp only [eval, h.1.1.at_.cf, h.1.2.at_.cf, Option.some.injEq, decide_eq_true_eq] at e₁ e₂
      exact ⟨small_ok hp (by lit_omega) (.inr (.inr rfl)) h.1.1.at_ (by omega_using [e₁]),
        small_ok hp' (by lit_omega) (.inr (.inr rfl)) h.1.2.at_ (by omega_using [e₂])⟩
  have ite := RelCT.ite hc (small.mono (fun _ _ h => h) fun _ _ h => h.2) (big_rel hT hT' hq)
  obtain ⟨_, hpost⟩ := sealPost_taint hfp
  have post := RelCT.taint (A := taintS) (P := fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂) (τ₁ true)
    (fun _ _ h => agree₁ hp hp' hq₀ h.1 h.2) hpost
  have all := (entry_rel hp hp' hq₀).seq (pA.seq (c1.seq (mid.seq (ite.seq post))))
  exact RelCT.of_exec sealSplitBody_exec all

end VG.Proof.ChaCha20Poly1305.X86_64.Split
