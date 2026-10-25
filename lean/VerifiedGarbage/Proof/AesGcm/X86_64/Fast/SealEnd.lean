module

import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Fin
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Tail
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT

/-!
# AES-GCM `seal`'s path for TLS records: the end after the whole blocks

Untrusted: everything here is checked by Lean. `FastSeal.run` ends with
`Short.finishP`, which loads `H'` and `H'²` from the prepared key context
(`finPowP_ok`) where `Short.finishWith` computes them from `H`, and then ends
as `finishWith` does (`Short.finRest_ok`): it does what `Split.FinOk` asks of
an end after `oneBlocks` (`finOk_finishP`). The long `seal` with any such end
leaves what `Short.sealRunW_ok` does (`sealRunFin_ok`), and with
`finishP` does it in two runs with the same addresses and branches
(`sealRunP_rel`, as `Short.sealRunW_rel` for `finishWith`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Fast

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Split (FinOk)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk KsRel FinI finRest_ok)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks inc32 zeros padLen toBytes ofBytes ctxH ctxCiph)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Absorbed xorKs lensBlock padded)

/-- `finishP ks` after `oneBlocks`, with a prepared key context: what
`finishWith ks` does (`Short.finishF_ok`). -/
theorem finOk_finishP (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) :
    FinOk (CtxMode.preparedN np hpn) (Short.finishP ks) := by
  intro Ctx W SP L R D n al N H icb a s s₃ h he₃ rd₃ wr₃ fr₃ tl₃ _ dat₃ len₃ o hH hcb hal habs
  have hD := h.data.ok.w
  have hlt := h.data.ok.lt
  have hxa : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  obtain ⟨o₁, o₂, o₃⟩ := o
  obtain ⟨f₃, hR₃, hH₃, hc₃, hJ₃, hw₃, ct₃, ab₃, ht₃⟩ := ob_facts L h fr₃ hH hcb habs hxa o₁ o₂
    (Z := bytesAt s₃.mem D (16 * (n / 16))) (by rw [length_bytesAt]; omega_arith)
    (by rw [o₃, show (Ctx + 240 : Addr) = Ctx + BitVec.ofNat 64 240 from rfl, hH, Proof.Gcm.blocksAt_eq])
  have hcb₃ : blockAt s₃.mem (cbA W) = Nat.repeat inc32 (n / 16) icb := by rw [ct₃.1]; congr 1; omega_arith
  generalize hq : n / 16 = q at *
  have Plen := len₃
  generalize hr : n % 16 = r at Plen
  have hnr : n = 16 * q + r := by omega_arith
  rw [show n - 16 * q = r by omega_arith] at ht₃
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [f₃.readW (r := ⟨W + BitVec.ofNat 64 184, 8⟩) (Region.contains_self _ _)
      (kept_oneFrameB L hD h.t_w (.inl ⟨by decide, by decide⟩)) (by decide), hal]
  -- `H'` and `H'²`, from the prepared key context.
  have X := h.ext
  have hX : VG.Proof.Gcm.X86_64.Stitch.PowersN np s₃.mem Ctx :=
    (CtxMode.preparedN np hpn).frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact X.cw.sub_right (by simpa using Offset.sub_base W (d := 0) (n := 128) (k := 2560) (by decide))
      · exact X.cw.sub_right (Lay.wSub (by decide))
      · exact X.cw.sub_right (Lay.wSub (by decide))
      · exact X.cd
      · exact X.ct.symm) X.w X.ok
  have p0 := hX 0 (by have := hpn.1; omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at p0
  rw [ctxH_eq, hH₃] at p0
  have cov₃ := X.cov
  rw [← rd₃, ← wr₃] at cov₃
  unfold Short.finishP
  refine WP.seq (WP.mono (finPowP_ok hF s₃ he₃.r13 (in_off cov₃ (show 272 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64)))
    (in_off cov₃ (show 256 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64))) p0.2 p0.1) fun s₄ ⟨x0, x1, h1, h2, o₄⟩ => ?_)
  have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₃.keep (fun g hg => o₄.gpr _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> decide)) o₄.rd o₄.wr
  exact finRest_ok hks h hnr (by omega_arith) f₃ hR₃ hc₃ hJ₃ hw₃ hcb₃ ab₃ ht₃ tl₃ dat₃ Plen hal₃ he₄ o₄.mem
    (o₄.rd.trans rd₃) (o₄.wr.trans wr₃) x0 x1 h1 h2

/-- After the entry, the long `seal` up to the tag at `W`, with the additional
data absorbed by `aadP`, which leaves what `oneAad` does, then `oneBlocks`
and an end `fin` that does what `FinOk` asks: what `Short.sealRunW_ok`
leaves. -/
theorem sealRunFin_ok {M : CtxMode} (B : BlkFn M) {fin : Prog isa} (hfin : FinOk M fin)
    {aadP : Prog isa} {s₀ s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (hal : (s₀.gpr .r9).toNat = al)
    (ha : WP isa aadP s₁
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s₁.mem)) :
    WP isa (.seq aadP (.seq (oneBlocks B.enc) fin)) s₁ (SealRunPost s₀ Ctx W SP Np A D nl al n) := by
  have L := C.lay
  unfold SealRunPost
  generalize hR : (s₀.gpr .rsi).toNat = R
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  refine WP.seq (WP.mono ha fun s₂ Mi => ?_)
  generalize hH : ctxH s₀.mem Ctx = H at Mi ⊢
  generalize hiv : bytesAt s₀.mem Np nl = iv at Mi ⊢
  generalize ha : bytesAt s₀.mem A al = a at Mi ⊢
  have hRo : RoundsAt s₂.mem W R := hR ▸ Mi.rounds
  have hd₂ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n := C.data.of_eq Mi.rd Mi.wr
  have hal₂ : s₂.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [Mi.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have X₂ := X.keep Mi.rd Mi.wr Mi.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact X.cw
    · exact (X.ct.sub_left (below_sub (by decide) (by decide))).symm
  have h : ObPre M Ctx W SP R D n s₂ := ⟨Mi.env, hRo, Mi.dat, Mi.len, hd₂, C.t_c, C.t_w, C.t_d, C.sp24, X₂⟩
  refine WP.seq (WP.mono (oneBlocksE_ok L B h) fun s₃ ⟨P, o⟩ => ?_)
  refine WP.mono (WP.with_rdwr (hfin L (icb := inc32 (Spec.Gcm.j0 H iv)) (a := a) h P.env P.rd P.wr P.frame
    P.tlen hd₂.ok.lt P.dat P.len o Mi.hH Mi.cb hal₂ Mi.abs))
    fun s₄ ⟨⟨he₄, _, _, f₄, hC, hT₄⟩, hrd₄, hwr₄⟩ => ?_
  have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint ⟨p, k⟩ →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have hc₂ : ciphOf s₂.mem Ctx R = ctxCiph s₀.mem Ctx R :=
    ciph_frame Mi.frame (fun r hr => dM _ _ L.cw' L.kc r hr) hR'
  have hp₂ : bytesAt s₂.mem D n = bytesAt s₀.mem D n :=
    bytesAt_frame Mi.frame (dM _ _ C.dE C.data.ok.stk) (by have := C.data.ok.lt; omega)
  rw [Mi.j0, hc₂] at hT₄
  refine ⟨he₄, hrd₄.trans (P.rd.trans Mi.rd), hwr₄.trans (P.wr.trans Mi.wr),
    Mi.saved.frame f₄ (saved_oneFrameB L C.dE C.t_w), ?_, by rw [hC, hc₂, hp₂, Proof.Gcm.gctr_eq], hT₄⟩
  refine (Mi.frame.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
    · exact ⟨below SP 24, by simp, fun _ h => h⟩

/-- After the entry, the long `seal` with `finishP ks` in two runs, with the
additional data absorbed by `aadP`, which leaves what `oneAad` does: `aadP`
(which branches alike in both runs), `oneBlocks` and `finishP ks`, as
`Short.sealRunW_rel` for `finishWith ks`. -/
theorem sealRunP_rel {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks)
    (B : BlkFn (CtxMode.preparedN np hpn)) {aadP : Prog isa} {s₀ s₀' : State} {Ctx W SP Np A D : Addr} {nl al n R : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 4 Ctx W SP Np A D nl al n)
    (X : CtxExt (CtxMode.preparedN np hpn) Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (X' : CtxExt (CtxMode.preparedN np hpn) Ctx (W + BitVec.ofNat 64 16) W SP D n s₀')
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R)
    (har : RelCT isa (fun s₁ s₂ => OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂) aadP
      fun _ _ => True)
    (ha : ∀ s, OneEntry s₀ Ctx W SP A D n s → WP isa aadP s
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s.mem))
    (ha' : ∀ s, OneEntry s₀' Ctx W SP A D n s → WP isa aadP s
      (OneMid s₀' Ctx W SP D n (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np nl) (bytesAt s₀'.mem A al) s.mem)) :
    RelCT isa (fun s₁ s₂ => OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
      (.seq aadP (.seq (oneBlocks B.enc) (Short.finishP ks))) fun _ _ => True := by
  have L := C.lay
  have hn := C.data.ok.lt
  have hRr : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  have w : ∀ {s₀ : State} {Np : Addr} (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n)
      (X : CtxExt (CtxMode.preparedN np hpn) Ctx (W + BitVec.ofNat 64 16) W SP D n s₀), s₀.gpr .rdx = Np →
      (s₀.gpr .rcx).toNat = nl → (s₀.gpr .r9).toNat = al → (s₀.gpr .rsi).toNat = R →
      ∀ s, OneEntry s₀ Ctx W SP A D n s →
      WP isa aadP s (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s.mem) →
      WP isa aadP s (OneS (CtxMode.preparedN np hpn) Ctx W SP R A al D n none) :=
    fun C X hNp hnl hal hR _ h ha => WP.mono ha fun _ Mi =>
      (h.aadPre C X hNp hnl hal hR).1.frame L Mi.env (Mi.rd.trans h.rd.symm) (Mi.wr.trans h.wr.symm)
        C.dE (wFrame_one (.inl rfl) (wFrame_cons Mi.fr))
  have a := rel_wp har (fun _ _ h => h) (fun s h => w C X hNp hnl hal hR s h (ha s h))
    (fun s h => w C' X' hNp' hnl' hal' hR' s h (ha' s h))
  have bl := oneBlocksE_rel B L (R := R) (A := A) (al := al) (T := none) C.t_c C.t_w C.t_d C.sp24
  have fi : ∀ {s : State},
      OneS (CtxMode.preparedN np hpn) Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s →
      FinI Ctx W SP (D + BitVec.ofNat 64 (16 * (n / 16))) R (n - 16 * (n / 16)) s ∧
        Covers [⟨Ctx, 1024⟩] (s.rd ++ s.wr) :=
    fun h => ⟨⟨h.env, h.rounds.1, h.dat, h.len⟩, h.ext.cov⟩
  exact (RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩)
    (RelCT.seq bl ((finishP_rel hks hkr hRr (by omega)).mono (fun _ _ h => ⟨fi h.1, fi h.2⟩)
    fun _ _ h => h))).mono (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.AesGcm.X86_64.Fast
