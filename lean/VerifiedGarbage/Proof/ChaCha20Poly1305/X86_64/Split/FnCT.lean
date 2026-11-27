module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.CT
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.CT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealSplit
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Correct
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealSplit
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Run
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Correct
meta import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-! ### `ChaCha20Poly1305.X86_64.Split.CT`, which only this module used -/

section

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
  refine WP.seq (WP.mono (lengths_ok hp i₂ (by rw [cs₂ _ (by decide), h₁.rbp]))
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
    WP isa (cryptPre 960 1024 6 false) s (BigPre s₀) := by
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
  exact ⟨a₁, by rw [rd₁, h.at_.inv.rd], by rw [cs₁ _ (by decide), h.at_.inv.r15],
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
    ⟨sa, by rw [cs _ calleeSaved_rsp, h.args.rsp], by rw [cs _ (by decide), h.r15],
      by rw [cs _ (by decide), h.args.r14], by rw [cs _ (by decide), h.args.r13],
      by rw [cs _ (by decide), h.args.r12], by rw [rd, h.rd], by rw [wr, h.args.wr]⟩

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
    ⟨by rw [abi.1 _ calleeSaved_rsp, h.rsp], by rw [abi.1 _ (by decide), h.r15],
      by rw [abi.1 _ (by decide), h.r14], by rw [abi.1 _ (by decide), h.r13],
      by rw [abi.1 _ (by decide), h.r12], by rw [wr, h.wr]⟩

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
  obtain ⟨⟨-, -, -, -, p5, -, p7, -, p9, -⟩, -, -⟩ := hq
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
  obtain ⟨⟨-, -, -, -, -, -, p7, -, p9, -⟩, -, -⟩ := hq
  have hfp : FoldPoly 960 1024 6 .avx512 := .inr (.inr ⟨rfl, rfl, rfl, .inl rfl⟩)
  obtain ⟨_, hX⟩ := cryptPre_taint true false hfp
  obtain ⟨_, hA⟩ := splitArgs_taint
  obtain ⟨_, hP⟩ := ptr_taint
  have pre := (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (AtIteS s₀ s₁ ∧ AtIteS s₀' s₂) ∧ isa.eval .b s₁ = some false)
    (τS true) (fun _ _ h => agreeS hp hp' hq₀ (tp_pub hq₀) h.1.1.at_ h.1.2.at_) hX).wp
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
      (.seq x.inPlace
      (.seq (sealMid 960 b) (.seq (.ite .b (cryptSmall 6 false) cryptBigSplit) (sealPost 960 1024 6 b)))))) s t s' := by
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
  have c1 := call1_rel hT.hp hT'.hp hq.1 v (pass := 1024) (t₁₂ := tp s₀) (t₁₂' := tp s₀')
  rw [big_fold (hvb ▸ hb)] at c1
  have hp := hT.hp
  have hp' := hT'.hp
  have hq₀ := hq.1
  obtain ⟨eL, -, -, -⟩ := hq.eqs
  have hfp : FoldPoly 960 1024 6 b := .inr (.inr ⟨rfl, rfl, rfl, hb⟩)
  obtain ⟨_, hA⟩ := prologueA_taint true hfp
  have pA := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => s₁ = entryS s₀ ∧ s₂ = entryS s₀') (τ₀ true)
    (fun _ _ h => by rw [h.1, h.2]; exact agree₀ hp hp' hq₀ (tp_pub hq₀)) hA).wp
    (F₁ := FArgs 960 1024 s₀) (F₂ := FArgs 960 1024 s₀') fun _ _ h =>
    ⟨by rw [h.1]; exact prologueA_ok (by lit_omega) (.inr (.inl rfl)) (.inr (.inr rfl)) hp,
      by rw [h.2]; exact prologueA_ok (by lit_omega) (.inr (.inl rfl)) (.inr (.inr rfl)) hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have hmid := sealMid_taint hfp
  have mid := ((relTaintMx
    (P := fun s₁ s₂ => AfterF 960 1024 s₀ s₁ ∧ AfterF 960 1024 s₀' s₂) (τA true)
    (fun _ _ h => agreeA hp hp' hq₀ (tp_pub hq₀) h.1 h.2) hmid).wp (F₁ := AtIteS s₀) (F₂ := AtIteS s₀') fun _ _ h =>
      ⟨sealMidS_ok b hT h.1.1, sealMidS_ok b hT' h.1.2⟩).mono
      (Q' := fun (s₁ s₂ : State) => (AtIteS s₀ s₁ ∧ AtIteS s₀' s₂) ∧ s₁.mxcsr = s₂.mxcsr) (fun _ _ h => h)
      fun _ _ h => ⟨h.2, h.1⟩
  have hc : ∀ s₁ s₂, (AtIteS s₀ s₁ ∧ AtIteS s₀' s₂) → isa.eval .b s₁ = isa.eval .b s₂ := fun s₁ s₂ h => by
    simp [eval, h.1.at_.cf, h.2.at_.cf, eL]
  obtain ⟨_, hS⟩ := cryptSmall_taint true false hfp
  have small := (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (AtIteS s₀ s₁ ∧ AtIteS s₀' s₂) ∧ isa.eval .b s₁ = some true)
    (τS true) (fun _ _ h => agreeS hp hp' hq₀ (tp_pub hq₀) h.1.1.at_ h.1.2.at_) hS).wp (F₁ := After s₀) (F₂ := After s₀')
    fun s₁ s₂ h => by
      have e₁ := h.2
      have e₂ := (hc _ _ h.1).symm.trans h.2
      simp only [eval, h.1.1.at_.cf, h.1.2.at_.cf, Option.some.injEq, decide_eq_true_eq] at e₁ e₂
      exact ⟨small_ok hp (by lit_omega) (.inr (.inr rfl)) h.1.1.at_ (fun h => nomatch h) (by omega_using [e₁]),
        small_ok hp' (by lit_omega) (.inr (.inr rfl)) h.1.2.at_ (fun h => nomatch h) (by omega_using [e₂])⟩
  have ite := relMx (MxDet.of_noLoad (by lit_decide))
    (RelCT.ite hc (small.mono (fun _ _ h => h) fun _ _ h => h.2) (big_rel hT hT' hq))
  have hpost := sealPost_taint hfp
  have post := (relTaintMx (P := fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂) (τ₁ true)
    (fun _ _ h => agree₁ hp hp' hq₀ (tp_pub hq₀) h.1 h.2) hpost).mono (Q' := fun _ _ => True) (fun _ _ h => h)
    fun _ _ _ => trivial
  have hm : s₀.mxcsr = s₀'.mxcsr := hq₀.2.2.2.2.2.2.2.2.2
  have c1m := relMx (MxDet.of_noLoad (inPlace_mx v)) c1
  have all := ((relMx (MxDet.of_noLoad (by lit_decide)) (entry_rel hp hp' hq₀)).mono
    (fun _ _ h => ⟨h, by rw [h.1, h.2]; exact hm⟩) fun _ _ h => h).seq
    ((relMx (MxDet.of_noLoad (by lit_decide)) pA).seq (c1m.seq (mid.seq (ite.seq post))))
  exact RelCT.of_exec sealSplitBody_exec all

end VG.Proof.ChaCha20Poly1305.X86_64.Split

end

end

/-! ### `ChaCha20Poly1305.X86_64.Split.Fn`, which only this module used -/

section

/-! ### `ChaCha20Poly1305.X86_64.Split.Head`, which only this module used -/

section

/-!
# ChaCha20-Poly1305 with the data's first bytes from `src`, x86-64: the copy

`vg_chacha20_poly1305_seal_split(key = rdi, nonce = rsi, aad = rdx,
aad_len = rcx, src = r8, src_len = r9, dst = [rsp + 8], len = [rsp + 16],
tag = [rsp + 24], work = [rsp + 32])`, from a state satisfying `FPre` (what
its contract with `work` gives), first copies the first `cnt` bytes of `src`
to `dst` (`head_ok`): all of them (`whole`), or as many as the prologue's
keystream covers (`cntOf`). It keeps `key`, `nonce`, `aad_len` and `src` in
`work[0, 32)` meanwhile, and leaves `work`, `tag` and `dst` in `r10`, `r11`
and `rax` for the frame.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealSplit
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width copyBytes)
open VG.Spec.Poly1305 (bytesAt)
open VG.WriteBytes

/-! ## The entry state -/

section
variable (s : State)
/-- The arguments on entry. -/
abbrev eSrc : Addr := s.gpr .r8
abbrev eSN : Nat := (s.gpr .r9).toNat
abbrev eDst : Addr := stackArg s 0
abbrev eLn : Nat := (stackArg s 1).toNat
abbrev eTg : Addr := stackArg s 2
abbrev eW : Addr := stackArg s 3
/-- Their regions, the stack arguments, the return address and the stack
below it. -/
abbrev ekR : Region := ⟨s.gpr .rdi, 32⟩
abbrev enR : Region := ⟨s.gpr .rsi, 12⟩
abbrev eaR : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
abbrev esR : Region := ⟨eSrc s, eSN s⟩
abbrev edR : Region := ⟨eDst s, eLn s⟩
abbrev etR : Region := ⟨eTg s, 16⟩
abbrev ewR : Region := ⟨eW s, 1696⟩
abbrev eargR : Region := ⟨stackArgAddr s 0, 32⟩
abbrev eretR : Region := ⟨s.gpr .rsp, 8⟩
abbrev estkR : Region := below (s.gpr .rsp) 64

/-- The number of bytes of `src` the copy copies. -/
def cntOf (whole : Bool) : Nat := if whole then eSN s else min (eSN s) (mOf 960 1024 (eLn s))
end

/-- What the contract of `vg_chacha20_poly1305_seal_split` with `work`
gives. -/
structure FPre (s : State) : Prop where
  rd : s.rd = [ekR s, enR s, eaR s, esR s, eargR s]
  wr : s.wr = [edR s, etR s, ewR s]
  k_d : (ekR s).Disjoint (edR s)
  k_t : (ekR s).Disjoint (etR s)
  k_w : (ekR s).Disjoint (ewR s)
  n_d : (enR s).Disjoint (edR s)
  n_t : (enR s).Disjoint (etR s)
  n_w : (enR s).Disjoint (ewR s)
  a_d : (eaR s).Disjoint (edR s)
  a_t : (eaR s).Disjoint (etR s)
  a_w : (eaR s).Disjoint (ewR s)
  s_d : (esR s).Disjoint (edR s)
  s_t : (esR s).Disjoint (etR s)
  s_w : (esR s).Disjoint (ewR s)
  d_t : (edR s).Disjoint (etR s)
  d_w : (edR s).Disjoint (ewR s)
  t_w : (etR s).Disjoint (ewR s)
  d_g : (edR s).Disjoint (eargR s)
  t_g : (etR s).Disjoint (eargR s)
  w_g : (ewR s).Disjoint (eargR s)
  r_a : (eretR s).Disjoint (eaR s)
  r_s : (eretR s).Disjoint (esR s)
  r_d : (eretR s).Disjoint (edR s)
  r_t : (eretR s).Disjoint (etR s)
  r_w : (eretR s).Disjoint (ewR s)
  b_k : (estkR s).Disjoint (ekR s)
  b_n : (estkR s).Disjoint (enR s)
  b_a : (estkR s).Disjoint (eaR s)
  b_s : (estkR s).Disjoint (esR s)
  b_d : (estkR s).Disjoint (edR s)
  b_t : (estkR s).Disjoint (etR s)
  b_w : (estkR s).Disjoint (ewR s)
  o_k : (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64
  o_n : (s.gpr .rsi).toNat + 12 ≤ 2 ^ 64
  o_a : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  o_s : (eSrc s).toNat + eSN s ≤ 2 ^ 64
  o_d : (eDst s).toNat + eLn s ≤ 2 ^ 64
  o_t : (eTg s).toNat + 16 ≤ 2 ^ 64
  o_w : (eW s).toNat + 1696 ≤ 2 ^ 64
  sp_lo : 64 ≤ (s.gpr .rsp).toNat
  sp_hi : (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64
  le : eSN s ≤ eLn s

/-! ## Steps -/

/-- `loadW`: `work` into `rax`. -/
theorem loadW_ok {a : State} {W : Addr} (hW : a.mem.readW (off (a.gpr .rsp) 32) 64 = W)
    (r₃₂ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 32) 8) :
    WP isa (.block loadW) a fun e => e.gpr .rax = W ∧ (∀ r, r ≠ .rax → e.gpr r = a.gpr r) ∧
      e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  apply WP.of_runBlock
  simp only [loadW, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ↓reduceIte, r₃₂, hW, Option.map_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨by simp, fun r h => by simp [h], by simp, by simp, by simp⟩

/-- `stash`: `key`, `nonce`, `aad_len` and `src` into `work[0, 32)`. -/
theorem stash_ok {a : State} {W : Addr} (hrax : a.gpr .rax = W)
    (w₀ : InRegions a.wr (off W 0) 8) (w₈ : InRegions a.wr (off W 8) 8)
    (w₁₆ : InRegions a.wr (off W 16) 8) (w₂₄ : InRegions a.wr (off W 24) 8) :
    WP isa (.block stash) a fun e => e.gpr = a.gpr ∧
      e.mem = (((a.mem.writeW (off W 0) (a.gpr .rdi)).writeW (off W 8) (a.gpr .rsi)).writeW
        (off W 16) (a.gpr .rcx)).writeW (off W 24) (a.gpr .r8) ∧
      e.rd = a.rd ∧ e.wr = a.wr := by
  subst hrax
  apply WP.of_runBlock
  simp only [stash, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_at,
    ↓reduceIte, w₀, w₈, w₁₆, w₂₄, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- `cmp x, src; cmovb rcx, r`. -/
theorem cmpB_ok {t : State} {x r : Reg} {src : VG.X86_64.Src} {b : BitVec 64} (hs : readSrc t src = some b) :
    WP isa (.block [.alu .cmp x src, .cmov .b .rcx (.reg r)]) t fun t' =>
      t'.gpr .rcx = (if (t.gpr x).toNat < b.toNat then t.gpr r else t.gpr .rcx) ∧
      (∀ q, q ≠ .rcx → t'.gpr q = t.gpr q) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, exec, execAlu, hs, Option.bind_some]
  by_cases h : (t.gpr x).toNat < b.toNat
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, eval, readSrc, h,
      gpr_arithFlags, cf_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, Option.bind_some, Option.map_some, decide_true, ↓reduceIte,
      Option.some.injEq, exists_eq_left']
    exact ⟨by simp, fun q hq => by simp [hq], trivial, trivial, trivial⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, eval, readSrc, h,
      gpr_arithFlags, cf_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, Option.bind_some, Option.map_some, decide_false, ↓reduceIte,
      Bool.false_eq_true, Option.some.injEq, exists_eq_left']
    exact ⟨by simp, fun q _ => by simp, by simp, by simp, by simp⟩

/-- `cmp x, src; cmovae rcx, r`. -/
theorem cmpAE_ok {t : State} {x r : Reg} {src : VG.X86_64.Src} {b : BitVec 64} (hs : readSrc t src = some b) :
    WP isa (.block [.alu .cmp x src, .cmov .ae .rcx (.reg r)]) t fun t' =>
      t'.gpr .rcx = (if (t.gpr x).toNat < b.toNat then t.gpr .rcx else t.gpr r) ∧
      (∀ q, q ≠ .rcx → t'.gpr q = t.gpr q) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, exec, execAlu, hs, Option.bind_some]
  by_cases h : (t.gpr x).toNat < b.toNat
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, eval, readSrc, h,
      gpr_arithFlags, cf_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, Option.bind_some, Option.map_some, decide_true, ↓reduceIte,
      Bool.not_true, Bool.false_eq_true, Option.some.injEq, exists_eq_left']
    exact ⟨by simp, fun q _ => by simp, by simp, by simp, by simp⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, eval, readSrc, h,
      gpr_arithFlags, cf_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, Option.bind_some, Option.map_some, decide_false, ↓reduceIte,
      Bool.not_false, Option.some.injEq, exists_eq_left']
    exact ⟨by simp, fun q hq => by simp [hq], by simp, by simp, by simp⟩

theorem and1023' (len : Nat) (hl : len < 2 ^ 64) :
    BitVec.ofNat 64 len &&& BitVec.signExtend 64 (1023 : BitVec 32) = BitVec.ofNat 64 (len % 1024) :=
  and1023 len hl

/-- The first instructions of `prefixLen false`: `len` in `r10` and `rcx`
its bytes past the last multiple of 1024, rounded up to a block. -/
theorem prefixA_ok {a : State} {Ln : Nat} (hLn : Ln < 2 ^ 64)
    (hL : a.mem.readW (off (a.gpr .rsp) 16) 64 = BitVec.ofNat 64 Ln)
    (r₁₆ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 16) 8) :
    WP isa (.block [.mov .r10 (.mem (at_ .rsp 16)), .mov .rcx (.reg .r10), .alu .and .rcx (.imm 1023),
      .alu .add .rcx (.imm 63), .alu .and .rcx (.imm (BitVec.ofInt 32 (-64))), .mov32 .rdi (.imm 0)]) a
      fun e => e.gpr .r10 = BitVec.ofNat 64 Ln ∧ e.gpr .rcx = BitVec.ofNat 64 ((Ln % 1024 + 63) / 64 * 64) ∧
        e.gpr .rdi = 0 ∧ (∀ q, q ≠ .rcx → q ≠ .rdi → q ≠ .r10 → e.gpr q = a.gpr q) ∧ e.mem = a.mem ∧
        e.rd = a.rd ∧ e.wr = a.wr := by
  obtain hr : Ln % 1024 + 63 < 1087 := by omega_using []
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.load64, ea_at,
    State.setReg32, r₁₆, hL, ↓reduceIte, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
    rd_arithFlags, wr_setReg, wr_arithFlags, reduceCtorEq, and1023' Ln hLn, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left', show BitVec.signExtend 64 (63 : BitVec 32) = 63 by decide]
  rw [show BitVec.ofNat 64 (Ln % 1024) + 63 = BitVec.ofNat 64 (Ln % 1024 + 63) by
    rw [BitVec.ofNat_add]; rfl, round64 _ hr]
  exact ⟨by simp, by simp, by simp, fun q h₁ h₂ h₃ => by simp [h₁, h₂, h₃], by simp, by simp, by simp⟩

theorem sx961 (t : State) : readSrc t (.imm 961) = some (BitVec.ofNat 64 961) :=
  congrArg some (by decide : BitVec.signExtend 64 (961 : BitVec 32) = BitVec.ofNat 64 961)

/-- `prefixLen false`: `rcx` = the smaller of `src_len` and `m`. -/
theorem prefixF_ok {a : State} {Ln : Nat} (hLn : Ln < 2 ^ 64)
    (hL : a.mem.readW (off (a.gpr .rsp) 16) 64 = BitVec.ofNat 64 Ln)
    (r₁₆ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 16) 8) :
    WP isa (.block (prefixLen false)) a fun e =>
      e.gpr .rcx = BitVec.ofNat 64 (min (a.gpr .r9).toNat (mOf 960 1024 Ln)) ∧
      (∀ q, q ≠ .rcx → q ≠ .rdi → q ≠ .r10 → e.gpr q = a.gpr q) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧
      e.wr = a.wr := by
  obtain hy : (Ln % 1024 + 63) / 64 * 64 < 2 ^ 64 := by omega_using []
  obtain hS := (a.gpr .r9).isLt
  rw [show prefixLen false = [.mov .r10 (.mem (at_ .rsp 16)), .mov .rcx (.reg .r10), .alu .and .rcx (.imm 1023),
      .alu .add .rcx (.imm 63), .alu .and .rcx (.imm (BitVec.ofInt 32 (-64))), .mov32 .rdi (.imm 0)] ++
      ([.alu .cmp .rcx (.imm 961), .cmov .ae .rcx (.reg .rdi)] : List Instr) ++
      ([.alu .cmp .r10 (.imm 961), .cmov .b .rcx (.reg .r10)] : List Instr) ++
      ([.alu .cmp .r9 (.reg .rcx), .cmov .b .rcx (.reg .r9)] : List Instr) from rfl]
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono (prefixA_ok hLn hL r₁₆)
    fun e₁ ⟨r10₁, rcx₁, rdi₁, g₁, m₁, rd₁, wr₁⟩ => ?_)))
  refine WP.mono (cmpAE_ok (x := .rcx) (r := .rdi) (src := .imm 961) (b := BitVec.ofNat 64 961) (sx961 _))
    fun e₂ ⟨rcx₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  refine WP.mono (cmpB_ok (x := .r10) (r := .r10) (src := .imm 961) (b := BitVec.ofNat 64 961) (sx961 _))
    fun e₃ ⟨rcx₃, g₃, m₃, rd₃, wr₃⟩ => ?_
  refine WP.mono (cmpB_ok (x := .r9) (r := .r9) (src := .reg .rcx) (b := e₃.gpr .rcx) rfl)
    fun e₄ ⟨rcx₄, g₄, m₄, rd₄, wr₄⟩ => ?_
  obtain r9₃ : e₃.gpr .r9 = a.gpr .r9 := by
    rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide) (by decide) (by decide)]
  obtain c₃ : e₃.gpr .rcx = BitVec.ofNat 64 (mOf 960 1024 Ln) := by
    rw [rcx₃, g₂ _ (by decide), r10₁, rcx₂, rcx₁, rdi₁, toNat_ofNat_lt hLn, toNat_ofNat_lt hy,
      toNat_ofNat_lt (by decide)]
    simp only [mOf, splitOf, show (1024 : Nat) ≠ 0 by decide, show (1024 : Nat) ≠ 512 by decide, ite_false]
    by_cases h₁ : Ln < 961
    · have h₁' : Ln ≤ 960 := by omega_using [h₁]
      simp only [h₁, h₁', ↓reduceIte]
    · have h₁' : ¬ Ln ≤ 960 := by omega_using [h₁]
      simp only [h₁, h₁', ↓reduceIte]
      by_cases h₂ : (Ln % 1024 + 63) / 64 * 64 < 961
      · have h₂' : (Ln % 1024 + 63) / 64 * 64 ≤ 960 := by omega_using [h₂]
        simp only [h₂, h₂', ↓reduceIte]
      · have h₂' : ¬ (Ln % 1024 + 63) / 64 * 64 ≤ 960 := by omega_using [h₂]
        simp only [h₂, h₂', ↓reduceIte]; rfl
  refine ⟨?_, fun q h₁ h₂ h₃ => ?_, by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁],
    by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · have hm := mOf_le 960 1024 Ln
    rw [rcx₄, r9₃, c₃, toNat_ofNat_lt (by omega_using [hm])]
    by_cases h : (a.gpr .r9).toNat < mOf 960 1024 Ln
    · simp only [h, ↓reduceIte, Nat.min_eq_left (Nat.le_of_lt h), BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [h, ↓reduceIte, Nat.min_eq_right (Nat.le_of_not_lt h)]
  · rw [g₄ _ h₁, g₃ _ h₁, g₂ _ h₁, g₁ _ h₁ h₂ h₃]

/-! ## The stash -/

/-- The memory after `stash`. -/
def stashM (s : State) : Mem :=
  (((s.mem.writeW (off (eW s) 0) (s.gpr .rdi)).writeW (off (eW s) 8) (s.gpr .rsi)).writeW
    (off (eW s) 16) (s.gpr .rcx)).writeW (off (eW s) 24) (s.gpr .r8)

theorem w_in (s : State) {k : Nat} (hk : k + 8 ≤ 1696) : (ewR s).Contains (off (eW s) k) 8 := by
  rw [off_eq]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])

theorem stashM_frame (s : State) : Frame [ewR s] s.mem (stashM s) :=
  ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (w_in s (by decide))).writeW
    (List.mem_singleton_self _) _ (w_in s (by decide))).writeW (List.mem_singleton_self _) _
    (w_in s (by decide))).writeW (List.mem_singleton_self _) _ (w_in s (by decide))

/-- `stash` writes only the first 32 bytes of `work`. -/
theorem stashM_frame32 (s : State) : Frame [⟨eW s, 32⟩] s.mem (stashM s) := by
  obtain w32 : ∀ k, k + 8 ≤ 32 → (⟨eW s, 32⟩ : Region).Contains (off (eW s) k) 8 := fun k hk => by
    rw [off_eq]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (w32 0 (by decide))).writeW
    (List.mem_singleton_self _) _ (w32 8 (by decide))).writeW (List.mem_singleton_self _) _
    (w32 16 (by decide))).writeW (List.mem_singleton_self _) _ (w32 24 (by decide))

theorem wsep {W : Addr} {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 1696) (he : e + 8 ≤ 1696) :
    Mem.Sep (off W d) (64 / 8) (off W e) (64 / 8) := by
  rw [off_eq, off_eq]; exact Offset.sep W h (by omega_using [hd]) (by omega_using [he])

theorem stashM_rdi (s : State) : (stashM s).readW (off (eW s) 0) 64 = s.gpr .rdi := by
  simp only [stashM]
  rw [Mem.readW_writeW_sep (wsep (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
    Mem.readW_writeW_sep (wsep (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
    Mem.readW_writeW_sep (wsep (by omega_using []) (by omega_using []) (by omega_using [])) (by decide), Mem.readW_writeW_self64]

theorem stashM_rsi (s : State) : (stashM s).readW (off (eW s) 8) 64 = s.gpr .rsi := by
  simp only [stashM]
  rw [Mem.readW_writeW_sep (wsep (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
    Mem.readW_writeW_sep (wsep (by omega_using []) (by omega_using []) (by omega_using [])) (by decide), Mem.readW_writeW_self64]

theorem stashM_rcx (s : State) : (stashM s).readW (off (eW s) 16) 64 = s.gpr .rcx := by
  simp only [stashM]
  rw [Mem.readW_writeW_sep (wsep (by omega_using []) (by omega_using []) (by omega_using [])) (by decide), Mem.readW_writeW_self64]

theorem stashM_r8 (s : State) : (stashM s).readW (off (eW s) 24) 64 = s.gpr .r8 := by
  simp only [stashM]; rw [Mem.readW_writeW_self64]

/-! ## The copy -/

/-- The memory after the copy of `n` bytes. -/
def headM (s : State) (n : Nat) : Mem :=
  writeBytes (stashM s) (eDst s) (Spec.Aes.bytesAt (stashM s) (eSrc s) n)

/-- A byte of a region that does not wrap around, by its address. -/
theorem contains_nat {b : Addr} {l x : Nat} (hx : b.toNat ≤ x ∧ x < b.toNat + l) (hl : b.toNat + l ≤ 2 ^ 64) :
    (⟨b, l⟩ : Region).Contains (BitVec.ofNat 64 x) 1 := by
  rw [show BitVec.ofNat 64 x = b + BitVec.ofNat 64 (x - b.toNat) by
    rw [BitVec.add_comm, ← Offset.ofNat_sub_ofNat hx.1, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.sub_add_cancel]]
  exact Offset.contains_base _ (by omega_using [hx]) (by omega_using [hx, hl])

/-- No byte is in both of two disjoint regions that do not wrap around. -/
theorem disj_nat {b₁ b₂ : Addr} {l₁ l₂ : Nat} (h : (⟨b₁, l₁⟩ : Region).Disjoint ⟨b₂, l₂⟩)
    (h₁ : b₁.toNat + l₁ ≤ 2 ^ 64) (h₂ : b₂.toNat + l₂ ≤ 2 ^ 64) (x : Nat) :
    ¬ ((b₁.toNat ≤ x ∧ x < b₁.toNat + l₁) ∧ (b₂.toNat ≤ x ∧ x < b₂.toNat + l₂)) :=
  fun ⟨hx₁, hx₂⟩ => h _ (contains_nat hx₁ h₁) (contains_nat hx₂ h₂)

namespace FPre

variable {s : State} (hs : FPre s)
include hs

/-- `src` is shorter than half the address space: it, the data (as long at
least) and the return address do not overlap. -/
theorem sn_lt : eSN s < 2 ^ 63 := by
  have o_s := hs.o_s
  have o_d := hs.o_d
  have hr := hs.sp_hi
  have hle := hs.le
  obtain a₁ := disj_nat hs.s_d o_s o_d (eSrc s).toNat
  obtain a₂ := disj_nat hs.s_d o_s o_d (eDst s).toNat
  obtain a₃ := disj_nat hs.r_s (by omega_using [hr]) o_s (s.gpr .rsp).toNat
  obtain a₄ := disj_nat hs.r_d (by omega_using [hr]) o_d (s.gpr .rsp).toNat
  omega_using [o_s, o_d, hle, a₁, a₂, a₃, a₄]

omit hs in
theorem cnt_le (whole : Bool) : cntOf s whole ≤ eSN s := by
  unfold cntOf; split <;> omega_using []

theorem cnt_lt (whole : Bool) : cntOf s whole < 2 ^ 63 := Nat.lt_of_le_of_lt (cnt_le whole) hs.sn_lt

omit hs in
theorem arg_contains {j : Nat} (hj : j < 4) : (eargR s).Contains (off (s.gpr .rsp) (8 * (j + 1))) 8 := by
  rw [off_eq]; exact Offset.contains _ (e := 8 * (0 + 1)) (by omega_using []) (by omega_using [hj]) (by omega_using [])

/-- A stack argument is readable. -/
theorem arg_in {j : Nat} (hj : j < 4) : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 * (j + 1))) 8 :=
  ⟨eargR s, by rw [hs.rd]; simp, arg_contains hj⟩

/-- A stack argument, in memory that changed only in the working space and
the data. -/
theorem arg_eq {m : Mem} (hf : Frame [ewR s, edR s] s.mem m) {j : Nat} (hj : j < 4) :
    m.readW (off (s.gpr .rsp) (8 * (j + 1))) 64 = stackArg s j := by
  rw [hf.readW (r := eargR s) (arg_contains hj) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hs.w_g.symm
        · exact hs.d_g.symm) (by decide)]
  rfl

theorem headM_frame (n : Nat) (hn : n ≤ eSN s) : Frame [ewR s, edR s] s.mem (headM s n) := by
  have hle := hs.le
  intro x hx
  rw [headM, writeBytes_frame _ _ _ (R := edR s) (by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Proof.AesGcm.X86_64.length_bytesAt]; omega_using [hn, hle])
      x (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx _ (by simp)),
    stashM_frame s x (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx _ (by simp))]

/-- `head` writes only the first 32 bytes of `work`, and the data. -/
theorem headM_frame32 (n : Nat) (hn : n ≤ eSN s) : Frame [⟨eW s, 32⟩, edR s] s.mem (headM s n) := by
  have hle := hs.le
  intro x hx
  rw [headM, writeBytes_frame _ _ _ (R := edR s) (by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Proof.AesGcm.X86_64.length_bytesAt]; omega_using [hn, hle])
      x (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx _ (by simp)),
    stashM_frame32 s x (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx _ (by simp))]

/-- The working space after the copy, as `stash` left it. -/
theorem headM_w (n : Nat) (hn : n ≤ eSN s) {k : Nat} (hk : k + 8 ≤ 1696) :
    (headM s n).readW (off (eW s) k) 64 = (stashM s).readW (off (eW s) k) 64 := by
  have hle := hs.le
  refine Frame.readW (writeBytes_frame _ _ _ (R := edR s) (by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Proof.AesGcm.X86_64.length_bytesAt]; omega_using [hn, hle]))
    (w_in s hk) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.d_w.symm) (by decide)

end FPre

/-- `copyArgs`. -/
theorem copyArgs_ok {a : State} {D : Addr} (hD : a.mem.readW (off (a.gpr .rsp) 8) 64 = D)
    (r₈ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 8) 8) :
    WP isa (.block copyArgs) a fun e => e.gpr .rsi = a.gpr .r8 ∧ e.gpr .rdi = D ∧
      (∀ r, r ≠ .rsi → r ≠ .rdi → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  apply WP.of_runBlock
  simp only [copyArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ↓reduceIte, r₈, hD,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp, by simp, fun r h₁ h₂ => by simp [h₁, h₂], by simp, by simp, by simp⟩

/-- `unstash`. -/
theorem unstash_ok {a : State} {W T D : Addr} (hrax : a.gpr .rax = W)
    (hW : a.mem.readW (off (a.gpr .rsp) 32) 64 = W)
    (hT : a.mem.readW (off (a.gpr .rsp) 24) 64 = T) (hD : a.mem.readW (off (a.gpr .rsp) 8) 64 = D)
    (r₃₂ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 32) 8)
    (r₂₄ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 24) 8)
    (r₈ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 8) 8)
    (w₀ : InRegions (a.rd ++ a.wr) (off W 0) 8) (w₈ : InRegions (a.rd ++ a.wr) (off W 8) 8)
    (w₁₆ : InRegions (a.rd ++ a.wr) (off W 16) 8) (w₂₄ : InRegions (a.rd ++ a.wr) (off W 24) 8) :
    WP isa (.block unstash) a fun e => e.gpr .rdi = a.mem.readW (off W 0) 64 ∧
      e.gpr .rsi = a.mem.readW (off W 8) 64 ∧ e.gpr .rcx = a.mem.readW (off W 16) 64 ∧
      e.gpr .r8 = a.mem.readW (off W 24) 64 ∧ e.gpr .r10 = W ∧ e.gpr .r11 = T ∧ e.gpr .rax = D ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .r10 → r ≠ .r11 → e.gpr r = a.gpr r) ∧
      e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  subst hrax
  apply WP.of_runBlock
  simp only [unstash, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ↓reduceIte, r₃₂, r₂₄, r₈, hW, hT, hD, w₀, w₈,
    w₁₆, w₂₄, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp,
    fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ => by simp [h₁, h₂, h₃, h₄, h₅, h₆, h₇], by simp, by simp, by simp⟩

/-- `prefixLen true`. -/
theorem prefixT_ok (a : State) :
    WP isa (.block (prefixLen true)) a fun e => e.gpr .rcx = a.gpr .r9 ∧
      (∀ q, q ≠ .rcx → q ≠ .rdi → q ≠ .r10 → e.gpr q = a.gpr q) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧
      e.wr = a.wr := by
  apply WP.of_runBlock
  simp only [prefixLen, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, gpr_setReg, mem_setReg,
    rd_setReg, wr_setReg, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp, fun q h₁ _ _ => by simp [h₁], by simp, by simp, by simp⟩

/-- After the first `loadW`. -/
def Loaded (s a : State) : Prop :=
  a.gpr .rax = eW s ∧ (∀ r, r ≠ .rax → a.gpr r = s.gpr r) ∧ a.mem = s.mem ∧ a.rd = s.rd ∧ a.wr = s.wr

theorem loaded_ok {s : State} (hs : FPre s) : WP isa (.block loadW) s (Loaded s) :=
  loadW_ok (hs.arg_eq (Frame.refl _ _) (j := 3) (by decide)) (hs.arg_in (j := 3) (by decide))

/-- After `stash`, `prefixLen` and `copyArgs`: ready for the copy. -/
def Ready (whole : Bool) (s b : State) : Prop :=
  b.mem = stashM s ∧ b.gpr .rsi = eSrc s ∧ b.gpr .rdi = eDst s ∧
    b.gpr .rcx = BitVec.ofNat 64 (cntOf s whole) ∧
    (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .rsi → r ≠ .r10 → b.gpr r = s.gpr r) ∧ b.rd = s.rd ∧ b.wr = s.wr

theorem ready_ok (whole : Bool) {s a : State} (hs : FPre s) (ha : Loaded s a) :
    WP isa (.block (stash ++ prefixLen whole ++ copyArgs)) a (Ready whole s) := by
  obtain ⟨rax₀, g₀, m₀, rd₀, wr₀⟩ := ha
  obtain fS : Frame [ewR s, edR s] s.mem (stashM s) := (stashM_frame s).mono (by simp)
  obtain win : ∀ {k : Nat}, k + 8 ≤ 1696 → InRegions a.wr (off (eW s) k) 8 :=
    fun hk => ⟨ewR s, by rw [wr₀, hs.wr]; simp, w_in s hk⟩
  refine WP.block_append (WP.block_append (WP.mono (stash_ok rax₀ (win (by decide)) (win (by decide))
    (win (by decide)) (win (by decide))) fun e₁ ⟨g₁', m₁, rd₁, wr₁⟩ => ?_))
  obtain g₁ : ∀ r, r ≠ .rax → e₁.gpr r = s.gpr r := fun r h => by rw [g₁', g₀ r h]
  rw [m₀, g₀ _ (by decide), g₀ _ (by decide), g₀ _ (by decide), g₀ _ (by decide)] at m₁
  rw [rd₀] at rd₁
  rw [wr₀] at wr₁
  obtain sp₁ : e₁.gpr .rsp = s.gpr .rsp := g₁ _ (by decide)
  obtain in₁ : ∀ {j}, j < 4 → InRegions (e₁.rd ++ e₁.wr) (off (e₁.gpr .rsp) (8 * (j + 1))) 8 := fun hj => by
    rw [rd₁, wr₁, sp₁]; exact hs.arg_in hj
  obtain at₁ : ∀ {j}, j < 4 → e₁.mem.readW (off (e₁.gpr .rsp) (8 * (j + 1))) 64 = stackArg s j := fun hj => by
    rw [m₁, sp₁]; exact hs.arg_eq fS hj
  obtain post : ∀ e₂ : State, e₂.gpr .rcx = BitVec.ofNat 64 (cntOf s whole) →
      (∀ q, q ≠ .rcx → q ≠ .rdi → q ≠ .r10 → e₂.gpr q = e₁.gpr q) → e₂.mem = e₁.mem → e₂.rd = e₁.rd →
      e₂.wr = e₁.wr → WP isa (.block copyArgs) e₂ (Ready whole s) := by
    intro e₂ rcx₂ g₂ m₂ rd₂ wr₂
    obtain sp₂ : e₂.gpr .rsp = s.gpr .rsp := by rw [g₂ _ (by decide) (by decide) (by decide), sp₁]
    refine WP.mono (copyArgs_ok (D := eDst s) (by rw [m₂, m₁, sp₂]; exact hs.arg_eq fS (j := 0) (by decide))
      (by rw [rd₂, wr₂, rd₁, wr₁, sp₂]; exact hs.arg_in (j := 0) (by decide)))
      fun b ⟨rsi, rdi, g, m, rd, wr⟩ => ⟨by rw [m, m₂, m₁]; rfl, by
        rw [rsi, g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide)], rdi,
        by rw [g _ (by decide) (by decide), rcx₂], fun r a c d i t => by
        rw [g r i d, g₂ r c d t, g₁ r a], by rw [rd, rd₂, rd₁], by rw [wr, wr₂, wr₁]⟩
  cases whole with
  | true =>
    exact WP.mono (prefixT_ok e₁) fun e₂ ⟨rcx₂, g₂, m₂, rd₂, wr₂⟩ =>
      post e₂ (by rw [rcx₂, g₁ _ (by decide)]; simp [cntOf]) g₂ m₂ rd₂ wr₂
  | false =>
    obtain hL := at₁ (j := 1) (by decide)
    rw [show stackArg s 1 = BitVec.ofNat 64 (eLn s) by simp] at hL
    exact WP.mono (prefixF_ok (stackArg s 1).isLt hL (in₁ (j := 1) (by decide)))
      fun e₂ ⟨rcx₂, g₂, m₂, rd₂, wr₂⟩ =>
        post e₂ (by rw [rcx₂, g₁ _ (by decide)]; rfl) g₂ m₂ rd₂ wr₂

/-- After the copy. -/
def Copied (whole : Bool) (s c : State) : Prop :=
  c.mem = headM s (cntOf s whole) ∧
    (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .r10 → c.gpr r = s.gpr r) ∧
    c.rd = s.rd ∧ c.wr = s.wr

theorem ready_copy (whole : Bool) {s b : State} (hs : FPre s) (hb : Ready whole s b) :
    Proof.AesGcm.X86_64.Short.CopyPre b (eSrc s) (eDst s) (cntOf s whole) := by
  obtain ⟨_, rsi, rdi, rcx, _, rd, wr⟩ := hb
  obtain hc := FPre.cnt_le (s := s) whole
  have hle := hs.le
  refine ⟨rsi, rdi, rcx, hs.cnt_lt whole, ?_, ?_, ?_⟩
  · exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨esR s, by rw [rd, hs.rd]; simp, 0, by simp, by simp only; omega_using [hc]⟩
  · exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨edR s, by rw [wr, hs.wr]; simp, 0, by simp, by simp only; omega_using [hc, hle]⟩
  · exact (hs.s_d.sub_left (Region.sub_prefix hc)).sub_right (Region.sub_prefix (by omega_using [hc, hle]))

theorem copied_ok (whole : Bool) (w : Width) {s b : State} (hs : FPre s) (hb : Ready whole s b) :
    WP isa (copyBytes w) b (Copied whole s) :=
  WP.mono (Gather.copyBytes_ok (ready_copy whole hs hb) w) fun c ⟨mc, gc, rdc, wrc⟩ => by
    obtain ⟨m, _, _, _, g, rd, wr⟩ := hb
    exact ⟨by rw [mc, m]; rfl, fun r a c' d e f t => by rw [gc r a f t, g r a c' d e t], by rw [rdc, rd],
      by rw [wrc, wr]⟩

/-- After the second `loadW`. -/
def Loaded2 (whole : Bool) (s d : State) : Prop :=
  d.gpr .rax = eW s ∧ Copied whole s d

theorem loaded2_ok (whole : Bool) {s c : State} (hs : FPre s) (hc : Copied whole s c) :
    WP isa (.block loadW) c (Loaded2 whole s) := by
  obtain ⟨mc, gc, rdc, wrc⟩ := hc
  obtain spc : c.gpr .rsp = s.gpr .rsp :=
    gc _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain fH := hs.headM_frame (cntOf s whole) (FPre.cnt_le whole)
  exact WP.mono (loadW_ok (by rw [mc, spc]; exact hs.arg_eq fH (j := 3) (by decide))
      (by rw [rdc, wrc, spc]; exact hs.arg_in (j := 3) (by decide)))
    fun d ⟨rax, g, m, rd, wr⟩ => ⟨rax, by rw [m, mc], fun r a b' c' e f t => by rw [g r a, gc r a b' c' e f t],
      by rw [rd, rdc], by rw [wr, wrc]⟩

/-- After `head`. -/
structure Headed (whole : Bool) (s h : State) : Prop where
  mem : h.mem = headM s (cntOf s whole)
  rdi : h.gpr .rdi = s.gpr .rdi
  rsi : h.gpr .rsi = s.gpr .rsi
  rcx : h.gpr .rcx = s.gpr .rcx
  r8 : h.gpr .r8 = s.gpr .r8
  r10 : h.gpr .r10 = eW s
  r11 : h.gpr .r11 = eTg s
  rax : h.gpr .rax = eDst s
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .r10 → r ≠ .r11 → h.gpr r = s.gpr r
  rd : h.rd = s.rd
  wr : h.wr = s.wr
  mx : h.mxcsr = s.mxcsr

theorem headed_ok (whole : Bool) {s d : State} (hs : FPre s) (hd : Loaded2 whole s d) :
    WP isa (.block unstash) d fun h => h.mxcsr = s.mxcsr → Headed whole s h := by
  obtain ⟨rax, mc, gc, rdc, wrc⟩ := hd
  obtain hc := FPre.cnt_le (s := s) whole
  obtain win : ∀ {k : Nat}, k + 8 ≤ 1696 → InRegions (s.rd ++ s.wr) (off (eW s) k) 8 :=
    fun hk => ⟨ewR s, by rw [hs.wr]; simp, w_in s hk⟩
  obtain spc : d.gpr .rsp = s.gpr .rsp :=
    gc _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain fH := hs.headM_frame (cntOf s whole) hc
  obtain at₁ : ∀ {j}, j < 4 → d.mem.readW (off (d.gpr .rsp) (8 * (j + 1))) 64 = stackArg s j := fun hj => by
    rw [mc, spc]; exact hs.arg_eq fH hj
  obtain in₁ : ∀ {j}, j < 4 → InRegions (d.rd ++ d.wr) (off (d.gpr .rsp) (8 * (j + 1))) 8 := fun hj => by
    rw [rdc, wrc, spc]; exact hs.arg_in hj
  obtain rw' : d.rd ++ d.wr = s.rd ++ s.wr := by rw [rdc, wrc]
  refine WP.mono (unstash_ok rax (at₁ (j := 3) (by decide)) (at₁ (j := 2) (by decide))
    (at₁ (j := 0) (by decide)) (in₁ (j := 3) (by decide)) (in₁ (j := 2) (by decide)) (in₁ (j := 0) (by decide))
    (by rw [rw']; exact win (by decide)) (by rw [rw']; exact win (by decide))
    (by rw [rw']; exact win (by decide)) (by rw [rw']; exact win (by decide)))
    fun h ⟨rdi', rsi', rcx', r8', r10', r11', rax', g', m', rd', wr'⟩ mxh => ?_
  refine ⟨by rw [m', mc], ?_, ?_, ?_, ?_, r10', r11', rax', fun r a b' c' e f t u => ?_,
    by rw [rd', rdc], by rw [wr', wrc], mxh⟩
  · rw [rdi', mc, hs.headM_w _ hc (by decide), stashM_rdi]
  · rw [rsi', mc, hs.headM_w _ hc (by decide), stashM_rsi]
  · rw [rcx', mc, hs.headM_w _ hc (by decide), stashM_rcx]
  · rw [r8', mc, hs.headM_w _ hc (by decide), stashM_r8]
  · rw [g' r a b' c' e f t u, gc r a b' c' e f t]

theorem head_mx (whole : Bool) (w : Width) : (head whole w).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases whole <;> cases w <;> decide +kernel

theorem head_ok (whole : Bool) (w : Width) {s : State} (hs : FPre s) : WP isa (head whole w) s (Headed whole s) :=
  WP.mono_mx (Q := fun h => h.mxcsr = s.mxcsr → Headed whole s h) (head_mx whole w)
    (WP.seq (WP.mono (loaded_ok hs) fun _ ha =>
      WP.seq (WP.mono (ready_ok whole hs ha) fun _ hb =>
      WP.seq (WP.mono (copied_ok whole w hs hb) fun _ hc =>
      WP.seq (WP.mono (loaded2_ok whole hs hc) fun _ hd => headed_ok whole hs hd)))))
    fun _ hh mx => hh mx

end VG.Proof.ChaCha20Poly1305.X86_64.Split

end

end



/-!
# ChaCha20-Poly1305 with the data's first bytes from `src`, x86-64: the function

`sealSplitFor` is `head` (`Head.lean`), then `seal`'s body in a frame laid
out as `seal`'s entry (`framed`): it runs inline, from its contract, with
the state's permissions narrowed to `seal`'s regions (`WP.inlineF`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealSplit
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (bytesAt)
open VG.WriteBytes

theorem sealSplitBody_spSafe (v : Proof.ChaCha20.X86_64.XorImpl) (b : Impl.Poly1305.X86_64.Blocks)
    (hb : b = .avx512 ∨ b = .ifma) :
    (sealSplitBody v.callee b).all (fun i => !isa.writesSp i) = true := by
  have hx := v.spSafe
  simp only [sealSplitBody, prologue, bigCallee, Impl.ChaCha20.X86_64.Callee.inPlace, Code.all, hx, Bool.and_true]
  rcases hb with rfl | rfl <;> lit_decide

theorem xorSplit_xdepth : Impl.ChaCha20.X86_64.Avx512.xorSplit.x86_64Depth ≤ 24 := by
  rw [x86_64Depth_noSp xorSplit_nosp]; have := xorSplit_depth; omega_using [this]

theorem sealSplitBody_xdepth (v : Proof.ChaCha20.X86_64.XorImpl) (b : Impl.Poly1305.X86_64.Blocks) :
    (sealSplitBody v.callee b).x86_64Depth ≤ 24 := by
  have hx : v.callee.code.x86_64Depth ≤ 16 := v.xdepth
  obtain hb := blocks_xdepth b
  have hs := xorSplit_xdepth
  obtain hc := padRest_xdepth (dataCopy b) b 2
  obtain ha := padSite_xdepth (dataCopy b) b .rbx .rbp
  simp only [sealSplitBody, bigCallee, Impl.ChaCha20.X86_64.Callee.inPlace, prologue, prologueA, prologueB, zeroKs, macPad, macPadLengths, Code.iteCold, wholeBlocks,
    padRest, padCopy, padTail, cryptSplit, cryptBigSplit, cryptPre, xorKs, Bool.cond_false, absorbLengths, finalizeTag, finalizeWith, Code.x86_64Depth,
    xorBuf_xdepth, foldM_xdepth, init_xdepth, finalize_xdepth, Nat.max_le] at hx hc ha ⊢
  omega_using [hx, hb, hs, hc, ha]

/-! ## The frame -/

/-- The bottom of the 64 bytes of stack below `rsp` that the frame and
`seal`'s calls use. -/
abbrev fB (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 64

/-- The registers the frame pushes. -/
abbrev frameRegs : List Reg := [.r9, .r8, .r10, .r11, .rax]

theorem add_ofNat_sub_ofNat' (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem stk_sub (s : State) {d n : Nat} (h : d + n ≤ 64) :
    Region.Sub ⟨fB s + BitVec.ofNat 64 d, n⟩ (estkR s) :=
  Offset.sub_base _ h

theorem rsp_eq (s : State) : s.gpr .rsp = fB s + BitVec.ofNat 64 64 := (BitVec.sub_add_cancel _ _).symm

namespace FPre

variable {s : State} (hs : FPre s)
include hs

theorem fB_lt : (fB s).toNat + 104 ≤ 2 ^ 64 := by
  have := hs.sp_lo; have := hs.sp_hi
  rw [toNat_sub_ofNat (by omega_arith)]; omega_using [this]

omit hs in
/-- A part of the 64 bytes of stack is apart from a region apart from all of
them. -/
theorem stk_disj {r : Region} (h : (estkR s).Disjoint r) {d n : Nat} (hd : d + n ≤ 64) :
    (⟨fB s + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r :=
  h.sub_left (stk_sub s hd)

/-- The return address, at `fB + 64`, is apart from the stack below it. -/
theorem ret_stk {d n : Nat} (hd : d + n ≤ 64) :
    (eretR s).Disjoint ⟨fB s + BitVec.ofNat 64 d, n⟩ := by
  have := hs.fB_lt
  show (⟨s.gpr .rsp, 8⟩ : Region).Disjoint _
  rw [rsp_eq s]; exact Offset.disjoint _ (.inr hd) (by omega_using []) (by omega_using [hd])

end FPre

/-- The state `seal`'s body starts in: after the frame's push and
`dataArgs`. -/
structure Body (whole : Bool) (s u : State) : Prop where
  rdi : u.gpr .rdi = s.gpr .rdi
  rsi : u.gpr .rsi = s.gpr .rsi
  rdx : u.gpr .rdx = s.gpr .rdx
  rcx : u.gpr .rcx = s.gpr .rcx
  r8 : u.gpr .r8 = eDst s
  r9 : u.gpr .r9 = stackArg s 1
  rsp : u.gpr .rsp = fB s + BitVec.ofNat 64 24
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → u.gpr r = s.gpr r
  a0 : u.mem.readW (fB s + BitVec.ofNat 64 32) 64 = eTg s
  a1 : u.mem.readW (fB s + BitVec.ofNat 64 40) 64 = eW s
  a2 : u.mem.readW (fB s + BitVec.ofNat 64 48) 64 = eSrc s
  a3 : u.mem.readW (fB s + BitVec.ofNat 64 56) 64 = s.gpr .r9
  mem : Frame [⟨fB s + BitVec.ofNat 64 24, 40⟩] (headM s (cntOf s whole)) u.mem
  rd : u.rd = s.rd
  wr : u.wr = ⟨fB s + BitVec.ofNat 64 24, 40⟩ :: s.wr
  mx : u.mxcsr = s.mxcsr

theorem argR_eq (s : State) : eargR s = ⟨fB s + BitVec.ofNat 64 72, 32⟩ := by
  show (⟨s.gpr .rsp + BitVec.ofNat 64 (8 * (0 + 1)), 32⟩ : Region) = _
  rw [rsp_eq s, Offset.add_ofNat_add_ofNat]

theorem arg_addr (s : State) (j : Nat) :
    off (s.gpr .rsp) (8 * (j + 1)) = fB s + BitVec.ofNat 64 (64 + 8 * (j + 1)) := by
  rw [off_eq, rsp_eq s, Offset.add_ofNat_add_ofNat]

theorem pushed_rsp' {s h : State} (hsp : h.gpr .rsp = s.gpr .rsp) :
    (pushed frameRegs h).gpr .rsp = fB s + BitVec.ofNat 64 24 := by
  rw [pushed_rsp, hsp, rsp_eq s, add_ofNat_sub_ofNat' _ (by decide)]; rfl

/-- `dataArgs`, after the push. -/
theorem body_ok {whole : Bool} {s h : State} (hs : FPre s) (hh : Headed whole s h) :
    WP isa (.block dataArgs) (pushed frameRegs h) (Body whole s) := by
  obtain hsp : h.gpr .rsp = s.gpr .rsp :=
    hh.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hB := hs.fB_lt
  obtain hn : 8 * frameRegs.length ≤ (h.gpr .rsp).toNat := by rw [hsp]; have := hs.sp_lo; simp; omega_using [this]
  obtain ⟨pf, pw⟩ := pushRegs_mem h frameRegs (by decide) hn
  rw [hsp, rsp_eq s, add_ofNat_sub_ofNat' _ (by decide)] at pf
  rw [hsp, rsp_eq s] at pw
  replace pf : Frame [⟨fB s + BitVec.ofNat 64 24, 40⟩] h.mem (pushed frameRegs h).mem := pf
  obtain pw' : ∀ j (hj : j < 5) (d : Nat), d + 8 * (j + 1) = 64 →
      (pushed frameRegs h).mem.readW (fB s + BitVec.ofNat 64 d) 64 = h.gpr frameRegs[j] := by
    intro j hj d hd
    have := pw j hj
    rw [add_ofNat_sub_ofNat' _ (by omega_using [hj]), show 64 - 8 * (j + 1) = d by omega_using [hd]] at this
    exact this
  obtain fH := hs.headM_frame (cntOf s whole) (FPre.cnt_le whole)
  obtain sp' := pushed_rsp' hsp
  obtain ga : ∀ r, r ≠ .rsp → (pushed frameRegs h).gpr r = h.gpr r := fun r hr => pushed_gpr _ _ hr
  obtain a16 : off (fB s + BitVec.ofNat 64 24) 56 = off (s.gpr .rsp) (8 * (1 + 1)) := by
    rw [arg_addr s, off_eq, Offset.add_ofNat_add_ofNat]
  obtain r₅₆ : InRegions ((pushed frameRegs h).rd ++ (pushed frameRegs h).wr) (off (fB s + BitVec.ofNat 64 24) 56) 8 := by
    rw [pushed_rd, hh.rd, a16]
    exact ⟨eargR s, List.mem_append_left _ (by rw [hs.rd]; simp), FPre.arg_contains (j := 1) (by decide)⟩
  obtain v₅₆ : (pushed frameRegs h).mem.readW (off (fB s + BitVec.ofNat 64 24) 56) 64 = stackArg s 1 := by
    rw [a16, pf.readW (r := eargR s) (w := 64) (FPre.arg_contains (j := 1) (by decide)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [argR_eq s]; exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using []) (by omega_using [])) (by decide),
      hh.mem]
    exact hs.arg_eq fH (j := 1) (by decide)
  apply WP.of_runBlock
  simp only [dataArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at, sp',
    r₅₆, v₅₆, ↓reduceIte, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, mxcsr_setReg, reduceCtorEq,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr hr' => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, mxcsr_setReg, reduceCtorEq, ↓reduceIte]
  · rw [ga _ (by decide), hh.rdi]
  · rw [ga _ (by decide), hh.rsi]
  · rw [ga _ (by decide)]
    exact hh.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [ga _ (by decide), hh.rcx]
  · rw [ga _ (by decide), hh.rax]
  · exact sp'
  · have h₁ : r ≠ .r8 := by rintro rfl; simp [calleeSaved] at hr
    obtain h₂ : r ≠ .r9 := by rintro rfl; simp [calleeSaved] at hr
    simp only [h₁, h₂, ↓reduceIte, ga r hr']
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hh.keep r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) h₁
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [pw' 3 (by decide) 32 (by decide)]; exact hh.r11
  · rw [pw' 2 (by decide) 40 (by decide)]; exact hh.r10
  · rw [pw' 1 (by decide) 48 (by decide)]; exact hh.r8
  · rw [pw' 0 (by decide) 56 (by decide)]
    exact hh.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [← hh.mem]; exact pf
  · rw [pushed_rd, hh.rd]
  · rw [pushed_wr, hsp, rsp_eq s, add_ofNat_sub_ofNat' _ (show 8 * frameRegs.length ≤ 64 by decide), hh.wr]
    rfl
  · rw [pushed_mxcsr, hh.mx]

/-! ## `seal`'s precondition, narrowed -/

theorem stackArg_wr (s : State) (rd wr : List Region) (j : Nat) :
    stackArg (s.withRegions rd wr) j = stackArg s j := rfl
theorem stackArgAddr_wr (s : State) (rd wr : List Region) (j : Nat) :
    stackArgAddr (s.withRegions rd wr) j = stackArgAddr s j := rfl

/-- What `seal` may read and write, narrowed from the frame's state. -/
abbrev rdB (u : State) : List Region := [kR u, nR u, aR u, argR u]
abbrev wrB (u : State) : List Region := [dR u, tR u, ctxR u]

theorem FPre.stk0 {s : State} {r : Region} (h : (estkR s).Disjoint r) {n : Nat} (hn : n ≤ 64) :
    (⟨fB s, n⟩ : Region).Disjoint r :=
  h.sub_left (Region.sub_prefix hn)

theorem sub24 (B : Addr) : B + BitVec.ofNat 64 24 - 24 = B := BitVec.add_sub_cancel _ _

namespace Body

variable {whole : Bool} {s u : State} (hs : FPre s) (hb : Body whole s u)
include hb

theorem addr (j : Nat) : stackArgAddr u j = fB s + BitVec.ofNat 64 (24 + 8 * (j + 1)) := by
  show u.gpr .rsp + _ = _
  rw [hb.rsp, Offset.add_ofNat_add_ofNat]

theorem arg0 : stackArg u 0 = eTg s := by
  show u.mem.readW (stackArgAddr u 0) 64 = _; rw [hb.addr]; exact hb.a0
theorem arg1 : stackArg u 1 = eW s := by
  show u.mem.readW (stackArgAddr u 1) 64 = _; rw [hb.addr]; exact hb.a1
theorem arg2 : stackArg u 2 = eSrc s := by
  show u.mem.readW (stackArgAddr u 2) 64 = _; rw [hb.addr]; exact hb.a2
theorem arg3 : stackArg u 3 = s.gpr .r9 := by
  show u.mem.readW (stackArgAddr u 3) 64 = _; rw [hb.addr]; exact hb.a3

include hs

/-- `seal`'s precondition, narrowed. -/
theorem pre : preX86_64 true (u.withRegions (rdB u) (wrB u)) := by
  have e0 := hb.arg0
  have e1 := hb.arg1
  obtain eA := hb.addr 0
  simp only [preX86_64, stackArg_wr, stackArgAddr_wr, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, ite_true, kR, nR, aR, argR, dR, tR, ctxR, kp, np, ad, AL, dp, L, tp, cx, e0, e1, eA,
    hb.rdi, hb.rsi, hb.rdx, hb.rcx, hb.r8, hb.r9, hb.rsp, true_and, sub24, rdB, wrB,
    Nat.reduceAdd, Nat.reduceMul]
  refine ⟨hs.k_w.symm, hs.n_w.symm, hs.a_w.symm, hs.d_w.symm, hs.t_w.symm,
    (FPre.stk_disj hs.b_w (d := 32) (n := 16) (by decide)).symm, hs.k_d.symm, hs.n_d.symm, hs.a_d.symm, hs.d_t,
    (FPre.stk_disj hs.b_d (d := 32) (n := 16) (by decide)).symm,
    FPre.stk_disj hs.b_w (d := 24) (n := 8) (by decide), FPre.stk_disj hs.b_a (d := 24) (n := 8) (by decide),
    FPre.stk_disj hs.b_d (d := 24) (n := 8) (by decide), FPre.stk_disj hs.b_t (d := 24) (n := 8) (by decide),
    FPre.stk0 hs.b_w (by decide), FPre.stk0 hs.b_k (by decide), FPre.stk0 hs.b_n (by decide),
    FPre.stk0 hs.b_a (by decide), FPre.stk0 hs.b_d (by decide), FPre.stk0 hs.b_t (by decide),
    hs.o_w, hs.o_a, hs.o_d, hs.o_t, hs.o_k, hs.o_n, by
      have := hs.sp_lo
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega⟩

end Body

/-- `sealSplitBody`'s precondition, narrowed. -/
theorem Body.spre {whole : Bool} {s u : State} (hs : FPre s) (hb : Body whole s u) :
    SPre (u.withRegions (rdB u ++ [arg2R u, spR u]) (wrB u)) := by
  obtain hp := APre.of_more (more := [arg2R u, spR u]) (hb.pre hs)
  have e1 := hb.arg1
  have e2 := hb.arg2
  have e3 := hb.arg3
  obtain eA := hb.addr 2
  have hB := hs.fB_lt
  refine ⟨hp, List.mem_append_right _ (List.mem_cons_self ..),
    List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [SL, L, spR, sp, arg2R, ctxR, dR, tR, stkR, cx, dp, tp, stackArg_wr, stackArgAddr_wr,
      State.withRegions_gpr, e1, e2, e3, eA, hb.r8, hb.r9, hb.rsp, hb.arg0, sub24, below, BitVec.add_sub_cancel, Nat.reduceAdd,
      Nat.reduceMul]
  · exact hs.le
  · exact hs.s_w
  · exact hs.s_d
  · exact (FPre.stk0 hs.b_s (by decide)).symm
  · exact FPre.stk_disj hs.b_w (d := 48) (n := 16) (by decide)
  · exact FPre.stk_disj hs.b_d (d := 48) (n := 16) (by decide)
  · exact FPre.stk_disj hs.b_t (d := 48) (n := 16) (by decide)
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact hs.o_s

/-! ## The regions, within the frame's -/

namespace Body

variable {whole : Bool} {s u : State} (hb : Body whole s u)
include hb

/-- A part of the frame's words. -/
theorem in_frame {d n : Nat} (h : 24 ≤ d) (h' : d + n ≤ 64) :
    Covers [⟨fB s + BitVec.ofNat 64 d, n⟩] (u.rd ++ u.wr) :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨fB s + BitVec.ofNat 64 24, 40⟩, List.mem_append_right _ (by rw [hb.wr]; simp), d - 24,
      by simp only; rw [Offset.add_ofNat_add_ofNat, Nat.add_sub_cancel' h], by simp only; omega_using [h, h']⟩

theorem rdB_cov (hs : FPre s) : Covers (rdB u) (u.rd ++ u.wr) := by
  obtain eA := hb.addr 0
  refine Covers.cons (Covers.of_mem ?_) (Covers.cons (Covers.of_mem ?_) (Covers.cons (Covers.of_mem ?_)
    (Covers.cons ?_ Covers.nil)))
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr
    refine List.mem_append_left _ ?_
    show (⟨u.gpr .rdi, 32⟩ : Region) ∈ _; rw [hb.rd, hb.rdi, hs.rd]; simp
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr
    refine List.mem_append_left _ ?_
    show (⟨u.gpr .rsi, 12⟩ : Region) ∈ _; rw [hb.rd, hb.rsi, hs.rd]; simp
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr
    refine List.mem_append_left _ ?_
    show (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region) ∈ _; rw [hb.rd, hb.rdx, hb.rcx, hs.rd]; simp
  · show Covers [⟨stackArgAddr u 0, 16⟩] _
    rw [eA]; exact hb.in_frame (by decide) (by decide)

theorem more_cov (hs : FPre s) : Covers [arg2R u, spR u] (u.rd ++ u.wr) := by
  obtain eA := hb.addr 2
  refine Covers.cons ?_ (Covers.cons (Covers.of_mem ?_) Covers.nil)
  · show Covers [⟨stackArgAddr u 2, 16⟩] _
    rw [eA]; exact hb.in_frame (by decide) (by decide)
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr
    refine List.mem_append_left _ ?_
    show (⟨stackArg u 2, (stackArg u 3).toNat⟩ : Region) ∈ u.rd
    rw [hb.rd, hb.arg2, hb.arg3, hs.rd]; simp

theorem wrB_cov (hs : FPre s) : Covers (wrB u) u.wr := by
  refine Covers.of_mem fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [hb.wr, hs.wr]
  rcases hr with rfl | rfl | rfl
  · show (⟨u.gpr .r8, (u.gpr .r9).toNat⟩ : Region) ∈ _; rw [hb.r8, hb.r9]; simp
  · show (⟨stackArg u 0, 16⟩ : Region) ∈ _; rw [hb.arg0]; simp
  · show (⟨stackArg u 1, 1696⟩ : Region) ∈ _; rw [hb.arg1]; simp

end Body

/-! ## The frame around `seal`'s body -/

/-- `framed c`, for verified code `c` that writes `rsp` only in its frames'
pushes and pops and uses at most 24 bytes of stack below `rsp`, run from
`seal`'s entry state in the frame with its permissions narrowed to `seal`'s
regions and `more`. The frame's pop loses its 40 bytes: the memory on return
is the callee's but there. -/
theorem framed_ok {whole : Bool} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : SpSafe c) (hd : c.x86_64Depth ≤ 24) (more : State → List Region)
    {s h : State} (hs : FPre s) (hh : Headed whole s h)
    (hpre : ∀ u, Body whole s u → k.pre (u.withRegions (rdB u ++ more u) (wrB u)))
    (hmore : ∀ u, Body whole s u → Covers (more u) (u.rd ++ u.wr)) :
    WP isa (framed c) h fun z => ∃ u s₂ : State, Body whole s u ∧
      k.post (u.withRegions (rdB u ++ more u) (wrB u)) (s₂.withRegions (rdB u ++ more u) (wrB u)) ∧
      Frame [⟨fB s + BitVec.ofNat 64 24, 40⟩] s₂.mem z.mem ∧ Frame (wrB u ++ [below (u.gpr .rsp) 24]) u.mem s₂.mem ∧
      (∀ r ∈ calleeSaved, z.gpr r = s.gpr r) ∧ z.rd = s.rd ∧ z.wr = s.wr ∧
      z.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  obtain hsp' : h.gpr .rsp = s.gpr .rsp :=
    hh.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hB := hs.fB_lt
  obtain hn : 8 * frameRegs.length ≤ (h.gpr .rsp).toNat := by rw [hsp']; have := hs.sp_lo; simp; omega_using [this]
  refine WP.frame (by decide) (by decide) (by decide) hn ?_
  refine WP.seq (WP.mono (body_ok hs hh) fun u hu => ?_)
  refine WP.inlineF hv hsp (by omega_using [hd]) (hpre u hu)
    (Covers.append_left (Covers.append_left (hu.rdB_cov hs) (hmore u hu)) (hu.wrB_cov hs).right)
    (hu.wrB_cov hs)
    fun s₂ rd₂ wr₂ ab₂ f₂ _ post₂ => ?_
  obtain rsp₂ : s₂.gpr .rsp = u.gpr .rsp := ab₂.1 _ calleeSaved_rsp
  obtain pw : (pushed frameRegs h).wr = ⟨fB s + BitVec.ofNat 64 24, 40⟩ :: s.wr := by
    rw [pushed_wr, hsp', rsp_eq s, add_ofNat_sub_ofNat' _ (show 8 * frameRegs.length ≤ 64 by decide), hh.wr]
    rfl
  refine ⟨by rw [rsp₂, hu.rsp, pushed_rsp' hsp'], by rw [wr₂, hu.wr, pw], fun m uk fm => ?_⟩
  obtain hreg : (⟨h.gpr .rsp - BitVec.ofNat 64 (8 * frameRegs.length), 8 * frameRegs.length⟩ : Region) =
      ⟨fB s + BitVec.ofNat 64 24, 40⟩ := by
    have := pw; rw [pushed_wr] at this; exact (List.cons.inj this).1
  rw [hreg] at fm
  dsimp only
  refine ⟨u, s₂, hu, post₂, fm, Frame.below_mono f₂ hd (by decide), fun r hr => ?_,
    by rw [popped_rd, rd₂, hu.rd], by rw [popped_wr, wr₂, hu.wr]; rfl, by rw [popped_mxcsr, ab₂.2.2, hu.mx]⟩
  by_cases hr' : r = .rsp
  · subst hr'
    rw [popped_rsp, rsp₂, hu.rsp, Offset.add_ofNat_add_ofNat, rsp_eq s]; rfl
  · have hra : r ≠ .rax := by rintro rfl; simp [calleeSaved] at hr
    rw [popped_gpr _ _ _ hr' hra, ab₂.1 r hr, hu.cs r hr hr']

/-! ## The bytes `seal` encrypts -/

theorem FPre.headM_dst {s : State} (hs : FPre s) {n : Nat} (hn : n ≤ eSN s) {k : Nat} (hk : k < eLn s) :
    headM s n (eDst s + BitVec.ofNat 64 k) =
      if k < n then s.mem (eSrc s + BitVec.ofNat 64 k) else s.mem (eDst s + BitVec.ofNat 64 k) := by
  have hle := hs.le
  obtain hL : eLn s < 2 ^ 64 := (stackArg s 1).isLt
  obtain nw : ∀ {x : Addr}, (∀ r ∈ [ewR s], ¬ r.Contains x 1) → stashM s x = s.mem x :=
    fun h => stashM_frame s _ h
  simp only [headM, writeBytes, Offset.add_sub_cancel_left, toNat_ofNat_lt (show k < 2 ^ 64 by omega_using [hk, hL]),
    Proof.AesGcm.X86_64.length_bytesAt]
  split
  · rename_i h
    rw [Gather.getD_bytesAt _ _ h]
    refine nw fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.s_w _ (Offset.contains_base _ (by omega_using [hn, h]) (by have := hs.o_s; omega_using [hk, hL])) hc
  · refine nw fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.d_w _ (Offset.contains_base _ hk (by have := hs.o_d; omega_using [hk, hL])) hc

namespace Body

variable {whole : Bool} {s u : State} (hs : FPre s) (hb : Body whole s u)
include hs hb

/-- The memory of `seal`'s entry, apart from the working space, the data and
the frame. -/
theorem frameS : Frame [ewR s, edR s, ⟨fB s + BitVec.ofNat 64 24, 40⟩] s.mem u.mem :=
  ((hs.headM_frame _ (FPre.cnt_le whole)).mono (by simp)).trans (hb.mem.mono (by simp))

/-- A byte of `src`. -/
theorem src_byte {k : Nat} (hk : k < eSN s) : u.mem (eSrc s + BitVec.ofNat 64 k) = s.mem (eSrc s + BitVec.ofNat 64 k) :=
  (frameS hs hb).bytes (R := esR s) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.s_w
      · exact hs.s_d
      · exact (FPre.stk_disj hs.b_s (d := 24) (n := 40) (by decide)).symm)
    (Nat.le_of_lt (s.gpr .r9).isLt) hk

/-- A byte of the data: from `src` if copied. -/
theorem dst_byte {k : Nat} (hk : k < eLn s) : u.mem (eDst s + BitVec.ofNat 64 k) =
    if k < cntOf s whole then s.mem (eSrc s + BitVec.ofNat 64 k) else s.mem (eDst s + BitVec.ofNat 64 k) := by
  rw [hb.mem _ (fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact FPre.stk_disj hs.b_d (d := 24) (n := 40) (by decide) _ hc
        (Offset.contains_base _ hk (by have := hs.o_d; omega_using [hk, this]))),
    hs.headM_dst (FPre.cnt_le whole) hk]

/-- Bytes apart from the working space, the data and the stack. -/
theorem bytes_eq {p : Addr} {n : Nat} (hw : (⟨p, n⟩ : Region).Disjoint (ewR s))
    (hd : (⟨p, n⟩ : Region).Disjoint (edR s)) (hk : (estkR s).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt u.mem p n = bytesAt s.mem p n :=
  bytesAt_frame (frameS hs hb) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hw
    · exact hd
    · exact (FPre.stk_disj hk (d := 24) (n := 40) (by decide)).symm) hn

end Body

/-- The bytes `seal_split` encrypts: `src`'s, then the data's after them. -/
abbrev inSplit (s : State) : List Byte :=
  bytesAt s.mem (eSrc s) (eSN s) ++ (bytesAt s.mem (eDst s) (eLn s)).drop (eSN s)

theorem length_inSplit {s : State} (hs : FPre s) : (inSplit s).length = eLn s := by
  have := hs.le
  simp only [inSplit, List.length_append, List.length_drop, VG.Proof.Poly1305.length_bytesAt]; omega_using [this]

theorem inSplit_getD {s : State} {k : Nat} (hk : k < eLn s) :
    (inSplit s).getD k 0 = if k < eSN s then s.mem (eSrc s + BitVec.ofNat 64 k) else s.mem (eDst s + BitVec.ofNat 64 k) := by
  rw [inSplit, getD_split (VG.Proof.Poly1305.length_bytesAt _ _ _)]
  split
  · exact bytesAt_getD _ _ (by assumption)
  · exact bytesAt_getD _ _ hk

theorem eq_of_getD {xs ys : List Byte} {n : Nat} (hx : xs.length = n) (hy : ys.length = n)
    (h : ∀ k < n, xs.getD k 0 = ys.getD k 0) : xs = ys := by
  apply List.ext_getElem (by omega_using [hx, hy])
  intro k h₁ h₂
  have := h k (by omega_using [hx, h₁])
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some] at this

/-! ## The function -/

/-- What `seal_split` leaves: `seal` of `inSplit`. -/
def splitPost (s z : State) : Prop :=
  Spec.ChaCha20Poly1305.encrypt (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 12)
      (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (inSplit s) =
    (bytesAt z.mem (eDst s) (eLn s), bytesAt z.mem (eTg s) 16)

/-- `sealSplitBody`'s contract. -/
def splitK : Contract isa where
  pre := SPre
  post s₀ s' := Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (PTs s₀ s₀.mem) =
    (bytesAt s'.mem (dp s₀) (L s₀), bytesAt s'.mem (tp s₀) 16)
  pub _ _ := True

theorem split_hv (v : Proof.ChaCha20.X86_64.XorImpl) (b : Impl.Poly1305.X86_64.Blocks) (hvb : v.poly = b)
    (hb : b = .avx512 ∨ b = .ifma) :
    ∀ s, splitK.pre s → ∃ t s', Exec isa (sealSplitBody v.callee b) s t s' ∧ abiPreserved s s' ∧
      splitK.post s s' :=
  fun _ h => by
    obtain ⟨t, s', he, ha, hp⟩ := sealSplitBody_correct v b hvb hb h
    exact ⟨t, s', he, ha, hp⟩

theorem sealFor_hv (v : Proof.ChaCha20.X86_64.XorImpl) :
    ∀ s, sealX86_64.pre s → ∃ t s', Exec isa (Stitch.sealFor v.callee v.poly) s t s' ∧ abiPreserved s s' ∧
      sealX86_64.post s s' := by
  cases hb : v.poly with
  | avx2 => have h₂ := Proof.ChaCha20Poly1305.X86_64.Stitch.sealS_ok v hb; rw [hb] at h₂; exact h₂
  | avx512 =>
    obtain h₁ := seal_ok v; rw [hb] at h₁
    have := Proof.ChaCha20Poly1305.X86_64.Stitch.sealSmall_ok v.small v.small_poly h₁
    rwa [Proof.ChaCha20.X86_64.XorImpl.small_callee] at this
  | _ => have h₁ := seal_ok v; rw [hb] at h₁; exact h₁

namespace Body

variable {whole : Bool} {s u : State} (hs : FPre s) (hb : Body whole s u)
include hs hb

theorem key_eq : bytesAt u.mem (u.gpr .rdi) 32 = bytesAt s.mem (s.gpr .rdi) 32 := by
  rw [hb.rdi]; exact hb.bytes_eq hs hs.k_w hs.k_d hs.b_k (by decide)
theorem nonce_eq : bytesAt u.mem (u.gpr .rsi) 12 = bytesAt s.mem (s.gpr .rsi) 12 := by
  rw [hb.rsi]; exact hb.bytes_eq hs hs.n_w hs.n_d hs.b_n (by decide)
theorem aad_eq : bytesAt u.mem (u.gpr .rdx) (u.gpr .rcx).toNat =
    bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat := by
  rw [hb.rdx, hb.rcx]; exact hb.bytes_eq hs hs.a_w hs.a_d hs.b_a (Nat.le_of_lt (s.gpr .rcx).isLt)

omit hs in
theorem wrB_eq : wrB u = [edR s, etR s, ewR s] := by
  show [(⟨u.gpr .r8, (u.gpr .r9).toNat⟩ : Region), ⟨stackArg u 0, 16⟩, ⟨stackArg u 1, 1696⟩] = _
  rw [hb.r8, hb.r9, hb.arg0, hb.arg1]

/-- `seal_split`'s calling-convention obligations, from those of `seal`'s
body in the frame. -/
theorem abi {s₂ z : State} (hm : Frame [⟨fB s + BitVec.ofNat 64 24, 40⟩] s₂.mem z.mem) (hf : Frame (wrB u ++ [below (u.gpr .rsp) 24]) u.mem s₂.mem)
    (hcs : ∀ r ∈ calleeSaved, z.gpr r = s.gpr r)
    (hmx : z.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10) : abiPreserved s z := by
  rw [hb.wrB_eq, hb.rsp] at hf
  simp only [below, BitVec.add_sub_cancel] at hf
  refine ⟨hcs, ?_, hmx⟩
  rw [hm.readW (r := eretR s) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hs.ret_stk (d := 24) (n := 40) (by decide)) (by decide),
    hf.readW (r := eretR s) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl
      · exact hs.r_d
      · exact hs.r_t
      · exact hs.r_w
      · have := hs.ret_stk (d := 0) (n := 24) (by decide)
        rwa [BitVec.add_zero] at this) (by decide),
    (frameS hs hb).readW (r := eretR s) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.r_w
      · exact hs.r_d
      · exact hs.ret_stk (d := 24) (n := 40) (by decide)) (by decide)]

end Body

/-- A buffer apart from the stack below `rsp` keeps its bytes when the frame
around `seal`'s body loses its own. -/
theorem bytes_lost {s : State} {m m' : Mem} (hf : Frame [⟨fB s + BitVec.ofNat 64 24, 40⟩] m m')
    {p : Addr} {n : Nat} (hd : (estkR s).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hd.sub_left (stk_sub s (d := 24) (n := 40) (by decide))).symm) hn
    (List.mem_range.mp hi)

/-- The AVX-512 instances: the copy of the bytes the prologue's keystream
covers, then `seal`'s body with the rest read from `src`. -/
theorem split_wp (v : Proof.ChaCha20.X86_64.XorImpl) (b : Impl.Poly1305.X86_64.Blocks) (hvb : v.poly = b)
    (hb : b = .avx512 ∨ b = .ifma) {s : State} (hs : FPre s) :
    WP isa (.seq (head false .z64) (framed (sealSplitBody v.callee b))) s fun z =>
      abiPreserved s z ∧ splitPost s z := by
  refine WP.seq (WP.mono (head_ok false .z64 hs) fun h hh => ?_)
  refine WP.mono (framed_ok (k := splitK) (split_hv v b hvb hb) (SpSafe.of_all (sealSplitBody_spSafe v b hb))
    (sealSplitBody_xdepth v b) (fun u => [arg2R u, spR u]) hs hh (fun u hu => hu.spre hs) (fun u hu => hu.more_cov hs))
    fun z ⟨u, s₂, hu, post, hm, hf, hcs, _, _, hmx⟩ => ⟨hu.abi hs hm hf hcs hmx, ?_⟩
  have post' : Spec.ChaCha20Poly1305.encrypt (bytesAt u.mem (u.gpr .rdi) 32) (bytesAt u.mem (u.gpr .rsi) 12)
      (bytesAt u.mem (u.gpr .rdx) (u.gpr .rcx).toNat)
      (PTs (u.withRegions (rdB u ++ [arg2R u, spR u]) (wrB u)) u.mem) =
      (bytesAt s₂.mem (u.gpr .r8) (u.gpr .r9).toNat, bytesAt s₂.mem (stackArg u 0) 16) := post
  obtain hL : eLn s < 2 ^ 64 := (stackArg s 1).isLt
  have hle := hs.le
  obtain eP : PTs (u.withRegions (rdB u ++ [arg2R u, spR u]) (wrB u)) u.mem = inSplit s := by
    refine eq_of_getD (n := eLn s) (by rw [length_PTs]; show (u.gpr .r9).toNat = _; rw [hu.r9])
      (length_inSplit hs) fun k hk => ?_
    rw [PTs_getD _ (by show k < (u.gpr .r9).toNat; rw [hu.r9]; exact hk), inSplit_getD hk]
    obtain em : mm (u.withRegions (rdB u ++ [arg2R u, spR u]) (wrB u)) = mOf 960 1024 (eLn s) := by
      show mOf 960 1024 (u.gpr .r9).toNat = _; rw [hu.r9]
    obtain eSL : SL (u.withRegions (rdB u ++ [arg2R u, spR u]) (wrB u)) = eSN s := by
      show (stackArg u 3).toNat = _; rw [hu.arg3]
    have esp : sp (u.withRegions (rdB u ++ [arg2R u, spR u]) (wrB u)) = eSrc s := hu.arg2
    have edp : dp (u.withRegions (rdB u ++ [arg2R u, spR u]) (wrB u)) = eDst s := hu.r8
    rw [em, eSL, esp, edp, hu.dst_byte hs hk]
    simp only [cntOf, Bool.false_eq_true, ↓reduceIte]
    by_cases h₁ : k < eSN s
    · by_cases h₂ : mOf 960 1024 (eLn s) ≤ k
      · rw [ite_eq_left (show _ ∧ _ from ⟨h₂, h₁⟩), ite_eq_left h₁, hu.src_byte hs h₁]
      · rw [ite_eq_right (fun h => h₂ h.1), ite_eq_left (show k < min _ _ by omega_using [h₁, h₂]), ite_eq_left h₁]
    · rw [ite_eq_right (fun h => h₁ h.2), ite_eq_right (show ¬ k < min _ _ by omega_using [h₁]), ite_eq_right h₁]
  rw [hu.key_eq hs, hu.nonce_eq hs, hu.aad_eq hs, eP, hu.r8, hu.r9, hu.arg0,
    ← bytes_lost hm hs.b_d (by omega_using [hL]), ← bytes_lost hm hs.b_t (by decide)] at post'
  exact post'

/-- `splitK`, with what the code leaves in the keystream area (`KsLeftZ`). -/
def splitKK (v : Proof.ChaCha20.X86_64.XorImpl) : Contract isa where
  pre := SPre
  post s₀ s' := splitK.post s₀ s' ∧ KsLeftZ v (cx s₀) (L s₀) s₀.mem s'.mem
  pub _ _ := True

theorem split_hvK (v : Proof.ChaCha20.X86_64.XorImpl) (b : Impl.Poly1305.X86_64.Blocks) (hvb : v.poly = b)
    (hb : b = .avx512 ∨ b = .ifma) :
    ∀ s, (splitKK v).pre s → ∃ t s', Exec isa (sealSplitBody v.callee b) s t s' ∧ abiPreserved s s' ∧
      (splitKK v).post s s' :=
  fun _ h => by
    obtain ⟨t, s', he, ha, hp, hk⟩ := sealSplitBody_correctK v b hvb hb h
    exact ⟨t, s', he, ha, hp, hk⟩

/-- What the AVX-512 instances leave in the keystream area of `work`:
as `KsLeftZ` says, from `work` on entry. -/
theorem split_wpK (v : Proof.ChaCha20.X86_64.XorImpl) (b : Impl.Poly1305.X86_64.Blocks) (hvb : v.poly = b)
    (hb : b = .avx512 ∨ b = .ifma) {s : State} (hs : FPre s) :
    WP isa (.seq (head false .z64) (framed (sealSplitBody v.callee b))) s fun z =>
      KsLeftZ v (eW s) (eLn s) s.mem z.mem := by
  refine WP.seq (WP.mono (head_ok false .z64 hs) fun h hh => ?_)
  refine WP.mono (framed_ok (k := splitKK v) (split_hvK v b hvb hb) (SpSafe.of_all (sealSplitBody_spSafe v b hb))
    (sealSplitBody_xdepth v b) (fun u => [arg2R u, spR u]) hs hh (fun u hu => hu.spre hs) (fun u hu => hu.more_cov hs))
    fun z ⟨u, s₂, hu, ⟨_, post⟩, hm, _⟩ => ?_
  obtain ec : cx (u.withRegions (rdB u ++ [arg2R u, spR u]) (wrB u)) = eW s :=
    (stackArg_wr _ _ _ 1).trans hu.arg1
  obtain eL : L (u.withRegions (rdB u ++ [arg2R u, spR u]) (wrB u)) = eLn s := by
    show (u.gpr .r9).toNat = _; rw [hu.r9]
  simp only [ec, eL, State.withRegions_mem] at post
  obtain F : Frame [⟨eW s, 32⟩, edR s, ⟨fB s + BitVec.ofNat 64 24, 40⟩] s.mem u.mem :=
    ((hs.headM_frame32 _ (FPre.cnt_le false)).mono (by simp)).trans (hu.mem.mono (by simp))
  have ow := hs.o_w
  refine post.frame (rs := [⟨fB s + BitVec.ofNat 64 24, 40⟩]) hm (fun k hk r hr hc => ?_) F fun k hk r hr hc => ?_
  · -- The frame's lost bytes are on the stack, apart from `work`.
    obtain hxw : (ewR s).Contains (off (eW s) (672 + k)) 1 := by
      rw [off_eq]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
    rw [List.mem_singleton.mp hr] at hc
    exact hs.b_w _ (stk_sub s (d := 24) (n := 40) (by decide) _ hc) hxw
  obtain hxw : (ewR s).Contains (off (eW s) (672 + k)) 1 := by
    rw [off_eq]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have hks : (⟨eW s + BitVec.ofNat 64 672, 1024⟩ : Region).Contains (off (eW s) (672 + k)) 1 := by
      rw [off_eq]; exact Offset.contains _ (by omega_using []) (by omega_using [hk]) (by omega_using [ow])
    exact Offset.base_disjoint (eW s) (e := 672) (n := 1024) (k := 32) (by decide) (by omega_using [ow]) _ hc hks
  · exact hs.d_w _ hc hxw
  · exact hs.b_w _ (stk_sub s (d := 24) (n := 40) (by decide) _ hc) hxw

/-- The other instances: the copy of all of `src`, then `seal`. -/
theorem whole_wp {x : Impl.ChaCha20.X86_64.Callee} {b : Impl.Poly1305.X86_64.Blocks}
    (hv : ∀ s, sealX86_64.pre s → ∃ t s', Exec isa (Stitch.sealFor x b) s t s' ∧ abiPreserved s s' ∧
      sealX86_64.post s s')
    (hsp : SpSafe (Stitch.sealFor x b)) (hd : (Stitch.sealFor x b).x86_64Depth ≤ 24) (w : SealGather.Width)
    {s : State} (hs : FPre s) :
    WP isa (.seq (head true w) (framed (Stitch.sealFor x b))) s fun z => abiPreserved s z ∧ splitPost s z := by
  refine WP.seq (WP.mono (head_ok true w hs) fun h hh => ?_)
  refine WP.mono (framed_ok (k := sealX86_64) hv hsp hd (fun _ => []) hs hh
    (fun u hu => by rw [List.append_nil]; exact hu.pre hs) (fun _ _ => Covers.nil))
    fun z ⟨u, s₂, hu, post, hm, hf, hcs, _, _, hmx⟩ => ⟨hu.abi hs hm hf hcs hmx, ?_⟩
  have post' : Spec.ChaCha20Poly1305.encrypt (bytesAt u.mem (u.gpr .rdi) 32) (bytesAt u.mem (u.gpr .rsi) 12)
      (bytesAt u.mem (u.gpr .rdx) (u.gpr .rcx).toNat) (bytesAt u.mem (u.gpr .r8) (u.gpr .r9).toNat) =
      (bytesAt s₂.mem (u.gpr .r8) (u.gpr .r9).toNat, bytesAt s₂.mem (stackArg u 0) 16) := post
  obtain eD : bytesAt u.mem (eDst s) (eLn s) = inSplit s := by
    refine eq_of_getD (VG.Proof.Poly1305.length_bytesAt _ _ _) (length_inSplit hs) fun k hk => ?_
    rw [bytesAt_getD _ _ hk, hu.dst_byte hs hk, inSplit_getD hk]
    rfl
  obtain hL : eLn s < 2 ^ 64 := (stackArg s 1).isLt
  rw [hu.key_eq hs, hu.nonce_eq hs, hu.aad_eq hs, hu.r8, hu.r9, eD, hu.arg0,
    ← bytes_lost hm hs.b_d (by omega_using [hL]), ← bytes_lost hm hs.b_t (by decide)] at post'
  exact post'

/-- `vg_chacha20_poly1305_seal_split` of the instance calling the
implementation `v` of `vg_chacha20_xor`. -/
theorem sealSplit_wp (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} (hs : FPre s) :
    WP isa (sealSplitFor v.callee v.poly) s fun z => abiPreserved s z ∧ splitPost s z := by
  obtain hv := sealFor_hv v
  obtain hsp := SpSafe.of_all (Stitch.sealFor_spSafe v)
  obtain hd := Stitch.sealFor_xdepth v
  cases hp : v.poly with
  | avx512 => exact split_wp v .avx512 hp (.inl rfl) hs
  | ifma => exact split_wp v .ifma hp (.inr rfl) hs
  | scalar => rw [hp] at hv hsp hd; exact whole_wp hv hsp hd _ hs
  | avx2 => rw [hp] at hv hsp hd; exact whole_wp hv hsp hd _ hs

end VG.Proof.ChaCha20Poly1305.X86_64.Split

end

end

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
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧ s₁.mxcsr = s₂.mxcsr

theorem sealSplitBody_ct (v : Proof.ChaCha20.X86_64.XorImpl) (b : Impl.Poly1305.X86_64.Blocks)
    (hvb : v.poly = b) (hb : b = .avx512 ∨ b = .ifma) :
    ConstantTime isa SPre PubS (sealSplitBody v.callee b) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (sealSplitBody_rel h₁ h₂ hq v b hvb hb _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem sealFor_ct (v : Proof.ChaCha20.X86_64.XorImpl) :
    ConstantTime isa sealX86_64.pre sealX86_64.pub (Stitch.sealFor v.callee v.poly) := by
  cases hb : v.poly with
  | avx2 => have h₂ := Proof.ChaCha20Poly1305.X86_64.Stitch.sealS_ct v hb; rw [hb] at h₂; exact h₂
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
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, qsp, a₀, a₁, a₂, a₃, -⟩ := hq
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
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, qsp, a₀, a₁, a₂, a₃, qm⟩ := hq
  have hB : fB σ₁ = fB σ₂ := by simp only [fB, qsp]
  exact ⟨⟨by rw [hu₁.rdi, hu₂.rdi, q₁], by rw [hu₁.rsi, hu₂.rsi, q₂], by rw [hu₁.rdx, hu₂.rdx, q₃],
    by rw [hu₁.rcx, hu₂.rcx, q₄], by rw [hu₁.r8, hu₂.r8, eDst, eDst, a₀], by rw [hu₁.r9, hu₂.r9, a₁],
    by rw [hu₁.rsp, hu₂.rsp, hB], by rw [hu₁.arg0, hu₂.arg0, eTg, eTg, a₂],
    by rw [hu₁.arg1, hu₂.arg1, eW, eW, a₃], by rw [hu₁.mx, hu₂.mx, qm]⟩, by rw [hu₁.arg2, hu₂.arg2, eSrc, eSrc, q₅],
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
