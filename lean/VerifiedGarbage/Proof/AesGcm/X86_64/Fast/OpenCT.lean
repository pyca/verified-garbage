module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenSel
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenSel
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT

/-!
# AES-GCM `open`'s path for TLS records, in two runs

Untrusted: everything here is checked by Lean. `FastOpen.tagP` addresses
memory from the environment's registers, the key context's address and the
address and number of the bytes left, which are public, and branches on that
number (`tagP_rel`), so it meets `TagRel` (`tagRel_tagP`). Two runs test the
same public lengths, so `FastOpen.sel` takes `other` in both, or
`FastOpen.run` in both, whose additional data (`Fast.aad_rel`) and tag do
what `openOkW_rel` needs: `openSel_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.FastOpen

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Impl.AesGcm.X86_64.FastOpen (incJ tagP)
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk KsRel FinI LongRel finTest_ok finTextArgs_ok
  rel_env_regs rel_next rel_piece keepsEnv condS_of add_ofNat_ofNat)
open VG.Proof.AesGcm.X86_64.Fast (IsFast)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph)

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

/-- `tagP` in two runs with the same rounds and bytes left, the prepared key
context readable. -/
theorem tagP_rel {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) {Ctx W SP D : Addr} {R r : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hr : r < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => (FinI Ctx W SP D R r s₁ ∧ Covers [⟨Ctx, 1024⟩] (s₁.rd ++ s₁.wr)) ∧
        (FinI Ctx W SP D R r s₂ ∧ Covers [⟨Ctx, 1024⟩] (s₂.rd ++ s₂.wr)))
      (tagP ks) fun _ _ => True := by
  have wPow : ∀ s, FinI Ctx W SP D R r s ∧ Covers [⟨Ctx, 1024⟩] (s.rd ++ s.wr) →
      WP isa (.block finPowP) s (FinI Ctx W SP D R r) := fun s h =>
    WP.mono (Fast.finPowP_run s h.1.env.r13 (in_off h.2 (show 272 + 16 ≤ 1024 by decide) (by decide))
      (in_off h.2 (show 256 + 16 ≤ 1024 by decide) (by decide))) fun _ ⟨_, _, _, _, o⟩ =>
      h.1.keep (fun g hg => o.gpr g (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> decide)) o.rd o.wr (by rw [o.mem]; exact Frame.refl _ _)
  have p := rel_next (rel_env_regs [] (fun _ h => h.1.env) (fun _ h => h.1.env) (fun _ _ _ _ _ hr => by cases hr)
    (c := .block finPowP) ⟨_, by taint_decide⟩) wPow wPow
  have wKs : ∀ s, FinI Ctx W SP D R r s → WP isa ks s (FinI Ctx W SP D R r) := fun s h =>
    WP.mono (hks s h.env h.rounds hR) fun _ ⟨_, _, f, g, rd, wr, _⟩ => h.keep (fun g' hg => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) rd wr f
  have k := rel_next (hkr hR) wKs wKs
  have j := rel_next (rel_env_regs [] (F₁ := FinI Ctx W SP D R r) (F₂ := FinI Ctx W SP D R r)
    (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr) (c := .block incJ) ⟨_, by taint_decide⟩)
    incJ_finI incJ_finI
  have wTest : ∀ s, FinI Ctx W SP D R r s → WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)),
      .alu .test .rax (.reg .rax)]) s fun t => t.zf = some (decide (r = 0)) ∧ FinI Ctx W SP D R r t := fun s h =>
    WP.mono (finTest_ok hr s h.env h.len) fun _ ⟨z, g, m, rd, wr, _⟩ => ⟨z, h.keep (fun g' hg => g _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> decide)) rd wr (by rw [m]; exact Frame.refl _ _)⟩
  have t := rel_next (rel_env_regs [] (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr)
    (c := .block [.mov .rax (.mem (at_ .r15 lenO)), .alu .test .rax (.reg .rax)]) ⟨_, by taint_decide⟩) wTest wTest
  have wArgs : ∀ s, FinI Ctx W SP D R r s → WP isa (.block finTextArgs) s fun t =>
      t.gpr .rdi = W + BitVec.ofNat 64 512 ∧ t.gpr .rsi = D ∧ t.gpr .rdx = W + BitVec.ofNat 64 1040 ∧
        t.gpr .rcx = BitVec.ofNat 64 r := fun s h => by
    obtain ⟨t, run, -, di, si, dx, cx, -⟩ := finTextArgs_ok s h.env h.dat h.len
    exact WP.of_runBlock ⟨t, run, di, si, dx, cx⟩
  have b₀ := rel_env_regs [] (F₁ := FinI Ctx W SP D R r) (F₂ := FinI Ctx W SP D R r) (fun _ h => h.env)
    (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr) (c := .block (finLens ++ finGh1 ++ tagK uO))
    ⟨_, by taint_decide⟩
  have b₁ := rel_piece [.rdi, .rsi, .rdx, .rcx] (F₁ := FinI Ctx W SP D R r) (F₂ := FinI Ctx W SP D R r)
    (fun _ h => h.env) (fun _ h => h.env) (keepsEnv (by decide +kernel)) ⟨_, by taint_decide⟩ wArgs wArgs
    (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2])
    (c := .seq copyLoop (.block (finLens ++ finGh2 ++ tagK uO))) ⟨_, by taint_decide⟩
  unfold tagP
  exact RelCT.seq p (RelCT.seq k (RelCT.seq j (RelCT.seq t (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    (b₀.mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h)
    (b₁.mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h)))))

theorem tagRel_tagP {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) : TagRel CtxMode.prepared (tagP ks) :=
  fun {_ _ _} _ {R _ _ _ n _} _ =>
  StreamTo.RelCT.of_imp ((R = 10 ∨ R = 12 ∨ R = 14) ∧ n < 2 ^ 64) (fun _ _ h => ⟨h.1.rounds.2, h.1.dD.ok.lt⟩)
    fun ⟨hR, hr⟩ => (tagP_rel hks hkr hR hr).mono (fun _ _ h =>
      ⟨⟨⟨h.1.env, h.1.rounds.1, h.1.dat, h.1.len⟩, h.1.ext.cov⟩, ⟨⟨h.2.env, h.2.rounds.1, h.2.dat, h.2.len⟩, h.2.ext.cov⟩⟩)
      fun _ _ h => h

/-- `sel` in two runs: the same path, and on it the same addresses and
branches. -/
theorem openSel_rel (hF : ShortFacts) (v : GcmImpl) (B : BlkFn CtxMode.prepared) {ks : Prog isa} (hks : KsOk ks)
    (hkr : KsRel ks) {other : Prog isa} (ho : LongRel CtxMode.prepared other) :
    LongRel CtxMode.prepared (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) other ks) := by
  intro s₀ s₀' Ctx W SP Np A D Tp nl al n R t C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' hTr hTr' oT hres hok
  have hlt := C.data.ok.lt
  unfold Impl.AesGcm.X86_64.FastOpen.sel
  have hw : ∀ {s₀ : State} {Np : Addr} (C : OneCtx s₀ 5 Ctx W SP Np A D nl al n), (s₀.gpr .rcx).toNat = nl →
      (s₀.gpr .r9).toNat = al → ∀ s, OpenIn s₀ Ctx W SP A D n t s →
      WP isa Impl.AesGcm.X86_64.Fast.cond s fun u => u.zf = some (decide ¬IsFast nl al n) ∧
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
  by_cases hs : IsFast nl al n
  · obtain ⟨h12, h17, -⟩ := hs
    subst h12
    have L := C.lay
    exact (openOkW_rel v B (tagRel_tagP hks hkr) (tagP_ok hF hks) C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' hTr hTr' oT
      hres hok ((Fast.aad_rel L C.dE (M := CtxMode.prepared) (R := R) (Np := Np) (A := A) (al := al) (by omega)).mono
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
