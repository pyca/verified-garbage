module

import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
public import VerifiedGarbage.Impl.AesGcm.X86_64.FastOpen
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenTag
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Tail
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
meta import VerifiedGarbage.Impl.AesGcm.X86_64.FastOpen
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenTag
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Tail
meta import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith

/-!
# AES-GCM `open`'s path for TLS records, in two runs

Untrusted: everything here is checked by Lean. `FastOpen.tagP` addresses
memory from the environment's registers, the key context's address and the
address and number of the bytes left, which are public, and branches on that
number (`tagP_rel`), so it meets `TagRel` (`tagRel_tagP`). Two runs test the
same public lengths, so `FastOpen.sel` takes `other` in both, or
`FastOpen.run` in both, whose additional data (`Fast.aad_rel`) and tag do
what `openOkW_rel` needs, and so does `tailK`, which loads the number and the
address of the bytes left from `W` and loops over them (`crRel_tailK`):
`openSel_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.FastOpen

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Impl.AesGcm.X86_64.FastOpen (incJ tagP lenTest)
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk KsRel FinI LongRel finTest_ok finTextArgs_ok
  rel_env_regs rel_next rel_piece keepsEnv condS_of add_ofNat_ofNat)
open VG.Proof.AesGcm.X86_64.Fast (IsFast)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph)

variable {any : Bool}

/-- `incJ` keeps what `FinI` says. -/
theorem incJ_finI {Ctx W SP D : Addr} {R r : Nat} (s : State) (h : FinI Ctx W SP D R r s) :
    WP isa (.block incJ) s (FinI Ctx W SP D R r) := by
  obtain ⟨t, run, -, f, g, rd, wr, -⟩ := incJ_ok s h.env
  have e28 : W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12 = W + BitVec.ofNat 64 28 := add_ofNat_ofNat W 16 12
  have kp : ∀ d, 32 ≤ d → d + 8 ≤ 2560 →
      t.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => f.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      rw [e28]; exact Offset.disjoint W (.inr (by omega)) (by omega) (by decide)) (by decide)
  refine WP.of_runBlock ⟨t, run, h.env.keep (fun g' hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> exact g _ (by decide)) rd wr,
    by rw [kp 176 (by decide) (by decide)]; exact h.rounds, by rw [kp 200 (by decide) (by decide)]; exact h.dat,
    by rw [kp 208 (by decide) (by decide)]; exact h.len⟩

/-- `FinI` after code that writes only `W + 512` to `W + 544`. -/
theorem finI_keepG {Ctx W SP D : Addr} {R r : Nat} {s s' : State} (h : FinI Ctx W SP D R r s)
    (hg : ∀ g ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr g = s.gpr g) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame [⟨W + BitVec.ofNat 64 512, 32⟩] s.mem s'.mem) : FinI Ctx W SP D R r s' := by
  have kp : ∀ d, d + 8 ≤ 512 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact Offset.disjoint W (.inl (by omega)) (by omega) (by decide))
      (by decide)
  exact ⟨h.env.keep hg hrd hwr, by rw [kp 176 (by decide)]; exact h.rounds, by rw [kp 200 (by decide)]; exact h.dat,
    by rw [kp 208 (by decide)]; exact h.len⟩

/-- `tagP` in two runs with the same rounds and bytes left (fewer than 16,
readable, outside `W`), the prepared key context readable. -/
theorem tagP_rel {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) {Ctx W SP D : Addr} {R r : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hr : r < 16) (hDW : (⟨D, r⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => (FinI Ctx W SP D R r s₁ ∧ Covers [⟨Ctx, 1024⟩] (s₁.rd ++ s₁.wr) ∧
          Covers [⟨D, r⟩] (s₁.rd ++ s₁.wr)) ∧
        (FinI Ctx W SP D R r s₂ ∧ Covers [⟨Ctx, 1024⟩] (s₂.rd ++ s₂.wr) ∧ Covers [⟨D, r⟩] (s₂.rd ++ s₂.wr)))
      (tagP ks) fun _ _ => True := by
  -- What the code before the keystream keeps: `FinI`, and the bytes left readable.
  let FinC : State → Prop := fun s => FinI Ctx W SP D R r s ∧ Covers [⟨D, r⟩] (s.rd ++ s.wr)
  have wPow : ∀ s, FinI Ctx W SP D R r s ∧ Covers [⟨Ctx, 1024⟩] (s.rd ++ s.wr) ∧ Covers [⟨D, r⟩] (s.rd ++ s.wr) →
      WP isa (.block finPowP) s FinC := fun s h =>
    WP.mono (Fast.finPowP_run s h.1.env.r13 (in_off h.2.1 (show 272 + 16 ≤ 1024 by decide) (by decide))
      (in_off h.2.1 (show 256 + 16 ≤ 1024 by decide) (by decide))) fun _ ⟨_, _, _, _, o⟩ =>
      ⟨h.1.keep (fun g hg => o.gpr g (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> decide)) o.rd o.wr (by rw [o.mem]; exact Frame.refl _ _),
        by rw [o.rd, o.wr]; exact h.2.2⟩
  have p := rel_next (rel_env_regs [] (fun _ h => h.1.env) (fun _ h => h.1.env) (fun _ _ _ _ _ hr => by cases hr)
    (c := .block finPowP) ⟨_, by taint_decide⟩) wPow wPow
  have wTest : ∀ {F : State → Prop}, (∀ {s s' : State}, F s → FinI Ctx W SP D R r s' → s'.rd = s.rd → s'.wr = s.wr →
      F s') → (∀ s, F s → FinI Ctx W SP D R r s) → ∀ s, F s → WP isa (.block lenTest) s fun t =>
        t.zf = some (decide (r = 0)) ∧ F t := fun hF hI s h =>
    WP.mono (finTest_ok (by omega) s (hI s h).env (hI s h).len) fun _ ⟨z, g, m, rd, wr, _⟩ => ⟨z, hF h
      ((hI s h).keep (fun g' hg => g _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> decide)) rd wr (by rw [m]; exact Frame.refl _ _)) rd wr⟩
  have wTestC := wTest (F := FinC) (fun h I rd wr => ⟨I, by rw [rd, wr]; exact h.2⟩) fun _ h => h.1
  have wTestI := wTest (F := FinI Ctx W SP D R r) (fun _ I _ _ => I) fun _ h => h
  have t₁ := rel_next (rel_env_regs [] (fun _ h => h.1.env) (fun _ h => h.1.env) (fun _ _ _ _ _ hr => by cases hr)
    (c := .block lenTest) ⟨_, by taint_decide⟩) wTestC wTestC
  -- The blocks `GHASH` reads: the lengths block, and with bytes left, them first.
  have wLens : ∀ s, FinI Ctx W SP D R r s → WP isa (.block finLens) s (FinI Ctx W SP D R r) := fun s h => by
    obtain ⟨t, run, f, -, g, rd, wr, -⟩ := Short.finLens_ok (al := (s.mem.readW (W + BitVec.ofNat 64 184) 64).toNat)
      (n := (s.mem.readW (W + BitVec.ofNat 64 192) 64).toNat) s h.env (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    exact WP.of_runBlock ⟨t, run, finI_keepG h (fun g' hg => g _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> decide)) rd wr
      (f.sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)⟩
  have b₀ := rel_next (rel_env_regs [] (F₁ := FinC) (F₂ := FinC) (fun _ h => h.1.env) (fun _ h => h.1.env)
    (fun _ _ _ _ _ hr => by cases hr) (c := .block finLens) ⟨_, by taint_decide⟩)
    (fun s h => wLens s h.1) (fun s h => wLens s h.1)
  have wArgs : ∀ s, FinC s → WP isa (.block finTextArgs) s fun t =>
      t.gpr .rdi = W + BitVec.ofNat 64 512 ∧ t.gpr .rsi = D ∧ t.gpr .rdx = W + BitVec.ofNat 64 1040 ∧
        t.gpr .rcx = BitVec.ofNat 64 r := fun s h => by
    obtain ⟨t, run, -, di, si, dx, cx, -⟩ := finTextArgs_ok s h.1.env h.1.dat h.1.len
    exact WP.of_runBlock ⟨t, run, di, si, dx, cx⟩
  have wTail : r ≠ 0 → ∀ s, FinC s →
      WP isa (.seq (.block finTextArgs) (.seq copyLoop (.block finLens))) s (FinI Ctx W SP D R r) := fun h0 s h => by
    have he := h.1.env
    obtain ⟨s₁, run₁, m₁, di₁, si₁, -, cx₁, g₁, rd₁, wr₁, -⟩ := finTextArgs_ok s he h.1.dat h.1.len
    refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
    have lp : LoopPre s₁ D (W + BitVec.ofNat 64 512) r :=
      ⟨si₁, di₁, cx₁, by omega, by omega, by rw [rd₁, wr₁]; exact h.2, by rw [wr₁]; exact he.perm.wC (by omega),
        hDW.sub_right (Lay.wSub (by omega))⟩
    refine WP.seq (WP.mono (copyLoopX_ok s₁ lp) fun s₂ ⟨m₂, g₂, rd₂, wr₂, _⟩ => ?_)
    have f₁ : Frame [⟨W + BitVec.ofNat 64 512, 16⟩] s.mem s₁.mem := by
      rw [m₁]; exact writeBytes_frame' _ (List.length_replicate ..)
    have f₂ : Frame [⟨W + BitVec.ofNat 64 512, r⟩] s₁.mem s₂.mem := by
      rw [m₂]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
    have F₂ : Frame [⟨W + BitVec.ofNat 64 512, 32⟩] s.mem s₂.mem := by
      refine (f₁.sub fun q hq => ?_).trans (f₂.sub fun q hq => ?_) <;>
        simp only [List.mem_singleton] at hq <;> subst hq <;>
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    have I₂ : FinI Ctx W SP D R r s₂ := finI_keepG h.1 (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;>
        rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)])
      (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) F₂
    exact wLens s₂ I₂
  have b₁p := rel_piece [.rdi, .rsi, .rdx, .rcx] (F₁ := FinC) (F₂ := FinC)
      (fun _ h => h.1.env) (fun _ h => h.1.env) (keepsEnv (by decide +kernel)) ⟨_, by taint_decide⟩ wArgs wArgs
      (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2.1, h₂.2.2.1]
        · rw [h₁.2.2.2, h₂.2.2.2])
      (c := .seq copyLoop (.block finLens)) ⟨_, by taint_decide⟩
  have b₁ : r ≠ 0 → RelCT isa (fun s₁ s₂ => FinC s₁ ∧ FinC s₂)
      (.seq (.block finTextArgs) (.seq copyLoop (.block finLens)))
      fun s₁ s₂ => FinI Ctx W SP D R r s₁ ∧ FinI Ctx W SP D R r s₂ := fun h0 =>
    rel_next b₁p (wTail h0) (wTail h0)
  have prep : RelCT isa (fun s₁ s₂ => (s₁.zf = some (decide (r = 0)) ∧ FinC s₁) ∧
        (s₂.zf = some (decide (r = 0)) ∧ FinC s₂))
      (.ite .e (.block finLens) (.seq (.block finTextArgs) (.seq copyLoop (.block finLens))))
      fun s₁ s₂ => FinI Ctx W SP D R r s₁ ∧ FinI Ctx W SP D R r s₂ := rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    (b₀.mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h)
    (StreamTo.RelCT.of_imp (r ≠ 0) (fun _ _ h => by
        have e := h.1.1.1.symm.trans h.2
        simp only [Option.some.injEq, decide_eq_false_iff_not] at e
        exact e) fun h0 => (b₁ h0).mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h)
  -- The keystream, `J₀` incremented, and the test again.
  have wKs : ∀ s, FinI Ctx W SP D R r s → WP isa ks s (FinI Ctx W SP D R r) := fun s h =>
    WP.mono (hks s h.env h.rounds hR) fun _ ⟨_, _, f, g, rd, wr, _⟩ => h.keep (fun g' hg => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) rd wr f
  have k := rel_next (hkr hR) wKs wKs
  have j := rel_next (rel_env_regs [] (F₁ := FinI Ctx W SP D R r) (F₂ := FinI Ctx W SP D R r)
    (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr) (c := .block incJ) ⟨_, by taint_decide⟩)
    incJ_finI incJ_finI
  have t₂ := rel_next (rel_env_regs [] (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr)
    (c := .block lenTest) ⟨_, by taint_decide⟩) wTestI wTestI
  -- `GHASH` and the tag.
  have e₀ := rel_env_regs [] (F₁ := FinI Ctx W SP D R r) (F₂ := FinI Ctx W SP D R r) (fun _ h => h.env)
    (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr) (c := .block (finGh1 ++ tagK uO)) ⟨_, by taint_decide⟩
  have e₁ := rel_env_regs [] (F₁ := FinI Ctx W SP D R r) (F₂ := FinI Ctx W SP D R r) (fun _ h => h.env)
    (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr) (c := .block (finGh2 ++ tagK uO)) ⟨_, by taint_decide⟩
  unfold tagP
  exact RelCT.seq p (RelCT.seq t₁ (RelCT.seq prep (RelCT.seq k (RelCT.seq j (RelCT.seq t₂
    (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
      (e₀.mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h)
      (e₁.mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h)))))))

theorem tagRel_tagP {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) : TagRel (CtxMode.preparedN np hpn) (tagP ks) :=
  fun {_ _ _} _ {R _ _ _ _ _} hDW h16 =>
  StreamTo.RelCT.of_imp (R = 10 ∨ R = 12 ∨ R = 14) (fun _ _ h => h.1.rounds.2)
    fun hR => (tagP_rel hks hkr hR h16 hDW).mono (fun _ _ h =>
      ⟨⟨⟨h.1.env, h.1.rounds.1, h.1.dat, h.1.len⟩, h.1.ext.cov, h.1.dD.ok.rd⟩,
        ⟨⟨h.2.env, h.2.rounds.1, h.2.dat, h.2.len⟩, h.2.ext.cov, h.2.dD.ok.rd⟩⟩)
      fun _ _ h => h

/-- `tailK` in two runs: the length and the data's address loaded from `W`
(public), then a loop over that many bytes. -/
theorem crRel_tailK : CrRel Impl.AesGcm.X86_64.FastOpen.tailK := by
  intro M Ctx W SP L R A al D n T hDW hn
  have hL : ∀ s, OneS M Ctx W SP R A al D n T s → WP isa (.block [.mov .rcx (.mem (at_ .r15 lenO)),
      .alu .test .rcx (.reg .rcx)]) s fun s₁ => OneS M Ctx W SP R A al D n T s₁ ∧
        s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .rcx = BitVec.ofNat 64 n := fun s h => by
    have q₂ := h.env.perm.wR (show 208 + 8 ≤ 2560 by decide)
    obtain ⟨s₁, run₁, hz₁, hcx₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .rcx (.mem (at_ .r15 lenO)),
        .alu .test .rcx (.reg .rcx)] s = some s₁ ∧ s₁.zf = some (decide (n = 0)) ∧
        s₁.gpr .rcx = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
        s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [h.env.r15, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [zf_arithFlags, h.len]; exact congrArg some (and_self_beq (by omega))
      · simp [gpr_setReg, h.len]
      · intro r a; simp [gpr_setReg, a]
      all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
    exact WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hm₁ hrd₁ hwr₁, hz₁, hcx₁⟩
  let F : State → Prop := fun s => OneS M Ctx W SP R A al D n T s ∧ s.gpr .rcx = BitVec.ofNat 64 n
  let K : State → Prop := fun s => OneS M Ctx W SP R A al D n T s ∧ s.gpr .rdi = D ∧
    s.gpr .rsi = W + BitVec.ofNat 64 1040 ∧ s.gpr .rcx = BitVec.ofNat 64 n
  have hB : ∀ s, F s → WP isa (.block (([.mov .rdi (.mem (at_ .r15 dataO))] : List Instr) ++
      ptr .rsi .r15 (Impl.AesGcm.X86_64.Short.kO + 16))) s K := fun s ⟨h, hcx⟩ => by
    have q₁ := h.env.perm.wR (show 200 + 8 ≤ 2560 by decide)
    obtain ⟨s₁, run₁, hdi₁, hsi₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
        (([.mov .rdi (.mem (at_ .r15 dataO))] : List Instr) ++ ptr .rsi .r15 (Impl.AesGcm.X86_64.Short.kO + 16)) s =
          some s₁ ∧ s₁.gpr .rdi = D ∧ s₁.gpr .rsi = W + BitVec.ofNat 64 1040 ∧
        (∀ r, r ≠ .rdi → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [h.env.r15, q₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h.dat]
      · simp [gpr_setReg]; rfl
      · intro r a b; simp [gpr_setReg, a, b]
      all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
    exact WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hm₁ hrd₁ hwr₁, hdi₁, hsi₁,
      by rw [hg₁ _ (by decide) (by decide), hcx]⟩
  have a := rel_wp (rel_taint (P := OneS₂ M Ctx W SP R A al D n T) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩) (fun _ _ h => h) hL hL
  have b := rel_wp (rel_taint (P := fun s₁ s₂ => (True ∧ (OneS M Ctx W SP R A al D n T s₁ ∧
        s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .rcx = BitVec.ofNat 64 n) ∧ (OneS M Ctx W SP R A al D n T s₂ ∧
        s₂.zf = some (decide (n = 0)) ∧ s₂.gpr .rcx = BitVec.ofNat 64 n)) ∧ s₁.zf = some false)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env ⟨h.1.2.1.1, h.1.2.2.1⟩) ⟨_, by taint_decide⟩)
    (F₁ := F) (F₂ := F) (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩) hB hB
  have c := rel_taint (P := fun s₁ s₂ => True ∧ K s₁ ∧ K s₂) (c := xorLoop)
    [.rdi, .rsi, .rcx, .r13, .r14, .r15, .rsp]
    (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2.1, h.2.2.2.2.1]
      · rw [h.2.1.2.2.2, h.2.2.2.2.2]
      · rw [h.2.1.1.env.r13, h.2.2.1.env.r13]
      · rw [h.2.1.1.env.r14, h.2.2.1.env.r14]
      · rw [h.2.1.1.env.r15, h.2.2.1.env.r15]
      · rw [h.2.1.1.env.rsp, h.2.2.1.env.rsp]) ⟨_, by taint_decide⟩
  unfold Impl.AesGcm.X86_64.FastOpen.tailK
  exact ((rel_env (by decide) (fun _ _ h => ⟨h.1.env, h.2.env⟩)
    (RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.2.1, h.2.2.2.1]) (RelCT.block_nil fun _ _ _ => trivial)
      (RelCT.seq b c)))).mono (fun _ _ h => h) fun _ _ h => h.2)

/-- `sel` in two runs: the same path, and on it the same addresses and
branches. -/
theorem openSel_rel (hF : ShortFacts) (v : GcmImpl) (B : BlkFn (CtxMode.preparedN np hpn)) {ks : Prog isa} (hks : KsOk ks)
    (hkr : KsRel ks) {other : Prog isa} (ho : LongRel (CtxMode.preparedN np hpn) other) :
    LongRel (CtxMode.preparedN np hpn) (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) other ks any) := by
  intro s₀ s₀' Ctx W SP Np A D Tp nl al n R t C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' hTr hTr' oT hres hok
  have hlt := C.data.ok.lt
  unfold Impl.AesGcm.X86_64.FastOpen.sel
  have hw : ∀ {s₀ : State} {Np : Addr} (C : OneCtx s₀ 5 Ctx W SP Np A D nl al n), (s₀.gpr .rcx).toNat = nl →
      (s₀.gpr .r9).toNat = al → ∀ s, OpenIn s₀ Ctx W SP A D n t s →
      WP isa (Impl.AesGcm.X86_64.Fast.cond any) s fun u => u.zf = some (decide ¬IsFast nl al n any) ∧
        OpenIn s₀ Ctx W SP A D n t u :=
    fun C hnl hal s h => WP.mono (Fast.condE_ok C h.1 hnl hal) fun _ ⟨z, E, K⟩ =>
      ⟨z, E, by rw [K.gpr _ (by decide) (by decide) (by decide), h.2.1], by rw [K.mem]; exact h.2.2⟩
  have c := rel_next (Fast.cond_rel (F₁ := OpenIn s₀ Ctx W SP A D n t) (F₂ := OpenIn s₀' Ctx W SP A D n t)
      (fun _ h => condS_of h.1 hnl hal) (fun _ h => condS_of h.1 hnl' hal')
      (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _) (by omega))
    (hw C hnl hal) (hw C' hnl' hal')
  refine RelCT.seq c (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    ((ho C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' hTr hTr' oT hres hok).mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h) ?_)
  by_cases hs : IsFast nl al n any
  · obtain ⟨h12, h17, -⟩ := hs
    subst h12
    have L := C.lay
    exact (openOkW_rel v B (tagRel_tagP hks hkr) (tagP_ok hF hks) crRel_tailK C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' hTr hTr' oT
      hres hok ((Fast.aad_rel L C.dE (M := (CtxMode.preparedN np hpn)) (R := R) (Np := Np) (A := A) (al := al) (by omega)).mono
        (P' := fun (s₁ s₂ : State) => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
        (fun _ _ g => ⟨g.1.1.aadPre C X hNp hnl hal hR, g.2.1.aadPre C' X' hNp' hnl' hal' hR'⟩) fun _ _ _ => trivial)
      (fun _ h => Fast.aad_mid hF C X h.1 hNp hnl hal (by omega))
      (fun _ h => Fast.aad_mid hF C' X' h.1 hNp' hnl' hal' (by omega))).mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h
  · exact RelCT.of_false fun _ _ h => by have := h.1.1.1.symm.trans h.2; simp [hs] at this

/-- `openFin lng` in two runs, for `lng` that two runs go through alike. -/
theorem openFinW_rel {M : CtxMode} {lng : Prog isa} (hlr : LongRel M lng) {s₀ s₀' : State}
    (hp : (Proof.AesGcm.openX86_64M M).pre s₀) (hp' : (Proof.AesGcm.openX86_64M M).pre s₀')
    (hq : Proof.AesGcm.openX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (Impl.AesGcm.X86_64.FastOpen.openFin lng) fun _ _ => True :=
  openM_relOf hp hp' hq fun C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' hTr hTr' oT hres hok =>
    hlr C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' hTr hTr' oT hres hok

theorem openFinW_ct {M : CtxMode} {lng : Prog isa} (hlr : LongRel M lng) :
    ConstantTime isa (Proof.AesGcm.openX86_64M M).pre Proof.AesGcm.openX86_64.pub
      (Impl.AesGcm.X86_64.FastOpen.openFin lng) :=
  ct_of_rel fun _ _ hp hp' hq => openFinW_rel hlr hp hp' hq

end VG.Proof.AesGcm.X86_64.FastOpen
