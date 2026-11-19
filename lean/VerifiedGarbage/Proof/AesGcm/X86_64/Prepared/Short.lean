module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Impl.AesGcm.X86_64.SealFin
public import VerifiedGarbage.Impl.AesGcm.X86_64.FastSeal
public import VerifiedGarbage.Impl.AesGcm.X86_64.FastOpen
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
meta import VerifiedGarbage.Impl.AesGcm.X86_64.FastOpen
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
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
public import VerifiedGarbage.Proof.AesGcm.X86_64.Open
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Finish
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Open
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Finish
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
meta import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Bcast
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Bcast
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Body
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT

/-! ### `AesGcm.X86_64.Fast.SealEnd`, which only this module used -/

section

/-!
# AES-GCM `seal`'s path for TLS records: the end after the whole blocks

Untrusted: everything here is checked by Lean. `FastSeal.run` ends with
`Short.finishP`, which loads `H'` and `H'²` from the prepared key context
(`finPowP_ok`) where `Short.finishWith` computes them from `H`, and then ends
as `finishWith` does (`Short.finRest_ok`): it does what `Split.FinOk` asks of
an end after `oneBlocks` (`finOk_finishP`). The long `seal` with any such end
leaves what `Short.sealRunW_ok` does (`sealRunFin_ok`), and with
`finishP` does it in two runs with the same addresses and branches
(`sealRunP_rel`).
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
  have p0 := hX 0 (by have := hpn.1; omega_using [hpn])
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
    bytesAt_frame Mi.frame (dM _ _ C.dE C.data.ok.stk) (by have := C.data.ok.lt; omega_using [this])
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
(which branches alike in both runs), `oneBlocks` and `finishP ks`. -/
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
    (RelCT.seq bl ((finishP_rel hks hkr hRr (by omega_using [])).mono (fun _ _ h => ⟨fi h.1, fi h.2⟩)
    fun _ _ h => h))).mono (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.AesGcm.X86_64.Fast

end

end

/-! ### `AesGcm.X86_64.Short.PowP`, which only this module used -/

section

/-!
# AES-GCM's short path on x86-64: the powers from a prepared context

Untrusted: everything here is checked by Lean. A prepared key context
(`VG.Spec.Gcm.PreparedPowersRepr`) holds `H'¹`–`H'⁴⁸` in pairs, the 64 bytes
at `ctx + 256 + 64 j` being `H'⁴ʲ⁺²`, `H'⁴ʲ⁺¹`, `H'⁴ʲ⁺⁴`, `H'⁴ʲ⁺³`. `powersP`
leaves only the constants (`powersP_run`), and `ghashP` loads each group of
powers from the context, swapped by halves (`vshufi32x4` with `0x4E`), in
the table's order `H'⁴ʲ⁺⁴`–`H'⁴ʲ⁺¹` (`ghLoadP_ok`): it computes what `ghash`
does from the table `tabView` puts at `W + 1536` (`ghashP_ok`), which holds
what `powers` computes (`tabView_ok`): `powOk_powersP`. Both address memory
only from the key context's and `W`'s registers (`powersP_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB Only const_ok ea_at)
open VG.Proof.Gcm.X86_64.StitchZ (lane_ld lane_ld_ok zlane_load)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode zero_xor_b)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block ctxH blockAt)

/-! ## The table as `ghashP` sees it -/

/-- `m`, but for the table at `W + 1536`: there, the first eight groups of
the key context's powers, each swapped by halves. -/
def tabView (Ctx W : Addr) (m : Mem) : Mem := fun a =>
  if (a - (W + BitVec.ofNat 64 1536)).toNat < 512 then
    m (Ctx + BitVec.ofNat 64 (256 + 64 * ((a - (W + BitVec.ofNat 64 1536)).toNat / 64) +
      ((a - (W + BitVec.ofNat 64 1536)).toNat % 64 + 32) % 64))
  else m a

theorem read_shift {m m' : Mem} {a b : Addr} {n : Nat}
    (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = m' (b + BitVec.ofNat 64 i)) : m.read a n = m'.read b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have h0 := h 0 (by omega_arith)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih fun i hi => ?_]
    have := h (i + 1) (by omega_arith)
    rwa [Offset.add_ofNat_succ, Offset.add_ofNat_succ] at this

/-- Lane `l` of the view's group `j`: lane `(l + 2) % 4` of the context's. -/
theorem tabView_readW (Ctx W : Addr) (m : Mem) {j l : Nat} (hj : j < 8) (hl : l < 4) :
    (tabView Ctx W m).readW (W + BitVec.ofNat 64 1536 + BitVec.ofNat 64 (64 * j + 16 * l)) 128 =
      m.readW (Ctx + BitVec.ofNat 64 (256 + 64 * j + 16 * ((l + 2) % 4))) 128 := by
  simp only [Mem.readW]
  refine congrArg (BitVec.setWidth 128) (read_shift fun i hi => ?_)
  have e : (W + BitVec.ofNat 64 1536 + BitVec.ofNat 64 (64 * j + 16 * l) + BitVec.ofNat 64 i -
      (W + BitVec.ofNat 64 1536)).toNat = 64 * j + 16 * l + i := by
    rw [BitVec.add_assoc (W + _), BitVec.ofNat_add_ofNat, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith)]
  simp only [tabView, e, show 64 * j + 16 * l + i < 512 by omega_arith, ite_true]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact congrArg (fun k => m (Ctx + BitVec.ofNat 64 k)) (by omega_arith)

/-- The view is `m` outside the table. -/
theorem tabView_out (Ctx W : Addr) (m : Mem) : Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] m (tabView Ctx W m) :=
  fun x hx => by
    have h := hx _ (List.mem_singleton_self _)
    simp only [Region.Contains] at h
    simp only [tabView, show ¬ (x - (W + BitVec.ofNat 64 1536)).toNat < 512 by omega_arith, ite_false]

/-- The view of a context disjoint from `W` and the data. -/
theorem tabView_view {Ctx W D : Addr} {n : Nat} (hcw : (⟨Ctx, 1024⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hcd : (⟨Ctx, 1024⟩ : Region).Disjoint ⟨D, n⟩) : TabView (tabView Ctx W) W D n where
  keep f hd j hj l hl := by
    rw [tabView_readW _ _ _ hj hl, tabView_readW _ _ _ hj hl]
    have hs : Region.Sub ⟨Ctx + BitVec.ofNat 64 (256 + 64 * j + 16 * ((l + 2) % 4)), 16⟩ ⟨Ctx, 1024⟩ :=
      Offset.sub_base Ctx (by omega_arith)
    refine f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases (hd r hr).2 with h | h
    · exact (hcw.sub_left hs).sub_right fun a ha => Region.sub_prefix (by decide) a (h a ha)
    · exact (hcd.sub_left hs).sub_right h
  out := tabView_out Ctx W

/-- With a prepared key context, the view holds what `powers` computes. -/
theorem tabView_ok {m : Mem} {Ctx W : Addr} (hok : Spec.Gcm.PreparedPowersRepr m Ctx) {g : Nat} (hg : g ≤ 8) :
    TabOk (tabView Ctx W m) (W + BitVec.ofNat 64 1536) (ctxH m Ctx) g := fun j hj l hl => by
  rw [tabView_readW _ _ _ (by omega_arith) hl]
  have h2 := hok (2 * j) (by omega_arith)
  have h3 := hok (2 * j + 1) (by omega_arith)
  rcases (by omega_arith : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · rw [show 256 + 64 * j + 16 * ((0 + 2) % 4) = 256 + 32 * (2 * j + 1) by omega_arith, h3.1,
      show 2 * (2 * j + 1) + 2 = 4 * j + 4 - 0 by omega_arith]; rfl
  · rw [show 256 + 64 * j + 16 * ((1 + 2) % 4) = 272 + 32 * (2 * j + 1) by omega_arith, h3.2,
      show 2 * (2 * j + 1) + 1 = 4 * j + 4 - 1 by omega_arith]; rfl
  · rw [show 256 + 64 * j + 16 * ((2 + 2) % 4) = 256 + 32 * (2 * j) by omega_arith, h2.1,
      show 2 * (2 * j) + 2 = 4 * j + 4 - 2 by omega_arith]; rfl
  · rw [show 256 + 64 * j + 16 * ((3 + 2) % 4) = 272 + 32 * (2 * j) by omega_arith, h2.2,
      show 2 * (2 * j) + 1 = 4 * j + 4 - 3 by omega_arith]; rfl

/-! ## `powersP` -/

/-- `vshufi32x4` with `0x4E`: the two halves swapped. -/
theorem shuf4E (a : Nat → BitVec 128) {l : Nat} (hl : l < 4) : shuf4Lanes a a 0x4E l = a ((l + 2) % 4) := by
  rcases (by omega_arith : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- `powersP`: the constants in every lane of `zmm0` and `zmm1`. -/
theorem powersP_run (s : State) :
    WP isa powersP s fun t => t.mem = s.mem ∧
      (∀ l < 4, t.zlane .xmm0 l = revMask) ∧ (∀ l < 4, t.zlane .xmm1 l = poly) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [powersP, List.append_assoc, WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have O₂ := o₁.trans o₂
  refine WP.mono (pow4c_ok s₂) fun s₃ ⟨b0, b1, f₃⟩ => ⟨by rw [f₃.mem, O₂.mem], fun l hl => ?_,
    fun l hl => ?_, fun r hr => by rw [f₃.gpr, O₂.gpr r hr], by rw [f₃.rd, O₂.rd], by rw [f₃.wr, O₂.wr]⟩
  · rw [b0 l hl, o₂.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq]
  · rw [b1 l hl, c₂]

/-! ## `ghashP` -/

/-- `ghSetupP`: `rdx` 128 bytes before `G`, `r11` 128 bytes before the
context's powers of `G`'s first group, `r9` the `g` groups, the products
cleared. -/
theorem ghSetupP_ok {Ctx W : Addr} {g : Nat} (s : State) (h13 : s.gpr .r13 = Ctx) (h15 : s.gpr .r15 = W)
    (hmp : s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g)) (hg : g ≤ 8)
    (r288 : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 288) 8) :
    WP isa (.block ghSetupP) s fun t =>
      t.gpr .rdx = W + BitVec.ofNat 64 384 ∧ t.gpr .r9 = BitVec.ofNat 64 g ∧
      t.gpr .r11 = Ctx + BitVec.ofNat 64 (64 + 64 * g) ∧ (∀ l < 4, prod (t.zproj l) = Prod.zero) ∧
      (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm8, .xmm9, .xmm10] s t := by
  rw [show ghSetupP = (ptr .rdx .r15 (gO - 128) ++ [.mov .r9 (.mem (at_ .r15 mpO)), .shift .shr .r9 2,
      .mov .r11 (.reg .r9), .shift .shl .r11 6, .alu .add .r11 (.reg .r13), .alu .add .r11 (imm 64)]) ++
      [.zop (.zbin .vpxord .xmm8 .xmm8 .xmm8), .zop (.zbin .vpxord .xmm9 .xmm9 .xmm9),
       .zop (.zbin .vpxord .xmm10 .xmm10 .xmm10)] from rfl, WP.block_append_iff]
  have e₁ : BitVec.ofNat 64 (4 * g) >>> 2 = BitVec.ofNat 64 g := by rw [shr2 _ (by omega_arith)]; congr 1; omega_arith
  have e₂ : BitVec.ofNat 64 g <<< 6 = BitVec.ofNat 64 (64 * g) := by
    rw [shl_ofNat (by omega_arith)]; congr 1; omega_arith
  apply WP.of_runBlock
  refine ⟨_, by xrun [execShift, h15, hmp, r288, mpO, gO, e₁, e₂], ?_⟩
  refine WP.mono (clear3_ok _) fun t ⟨p, f⟩ => ⟨?_, ?_, ?_, p, fun r h₁ h₂ h₃ => ?_, f.mem, f.rd, f.wr,
    fun r hr l hl => f.zlane r (by simpa using hr) l hl⟩
  · rw [f.gpr]; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h15]
  · rw [f.gpr]; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags]
  · rw [f.gpr]; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h13]
    rw [BitVec.add_comm (BitVec.ofNat 64 (64 * g)) Ctx, BitVec.add_assoc, ofNat_add_ofNat, Nat.add_comm]
  · rw [f.gpr]; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h₁, h₂, h₃]

/-- Four powers from `r11 + 128`, swapped by halves, into `zmm12`, and four
blocks at `rdx + 128` with their products added. -/
theorem ghLoadP_ok (t : State) (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr .rdx + BitVec.ofInt 64 ((128 : Nat) : Int)) 64)
    (hpin : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((128 : Nat) : Int)) 64) :
    WP isa (.block ghLoadP) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = (prod (t.zproj l)).acc
        (blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((128 : Nat) : Int) + BitVec.ofNat 64 (16 * l)))
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((128 : Nat) : Int) + BitVec.ofNat 64 (16 * ((l + 2) % 4)))
          128)) ∧
      ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  let ap := t.gpr .r11 + BitVec.ofInt 64 ((128 : Nat) : Int)
  let ad := t.gpr .rdx + BitVec.ofInt 64 ((128 : Nat) : Int)
  let vp := t.mem.readW ap 512
  let t₁ := t.setZ .xmm12 (vp.extractLsb' 0 128) (vp.extractLsb' 128 128) (vp.extractLsb' 256 128)
    (vp.extractLsb' 384 128)
  let t₁' := (ZOp.vshufi32x4 .xmm12 .xmm12 .xmm12 0x4E).exec t₁
  let vd := t₁'.mem.readW ad 512
  let t₂ := t₁'.setZ .xmm7 (vd.extractLsb' 0 128) (vd.extractLsb' 128 128) (vd.extractLsb' 256 128)
    (vd.extractLsb' 384 128)
  rw [show ghLoadP = .vmovdqu32Load .xmm12 (at_ .r11 128) :: .zop (.vshufi32x4 .xmm12 .xmm12 .xmm12 0x4E) ::
      .vmovdqu32Load .xmm7 (at_ .rdx 128) :: VG.Proof.Gcm.X86_64.StitchZ.restZ 2 from rfl, WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load512, State.ea, at_, hpin, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨t₁', rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨t₂, by simp only [isa, exec, State.load512, State.ea, at_, t₁', t₁, ZOp.exec_gpr, ZOp.exec_rd, ZOp.exec_wr,
    ZOp.exec_mem, State.setZ_gpr, State.setZ_rd, State.setZ_wr, State.setZ_mem, hin, ite_true, Option.map_some]; rfl, ?_⟩
  have keep : ∀ r, r ≠ .xmm12 → r ≠ .xmm7 → ∀ l < 4, t₂.zlane r l = t.zlane r l := fun r h12 h7 l hl => by
    simp only [t₂, t₁', t₁]
    rw [State.zlane_setZ_ne _ h7 _ _ _ _ hl, zlane_vshufi32x4 _ _ _ _ _ _ hl]
    simp only [h12, ite_false]
    rw [State.zlane_setZ_ne _ h12 _ _ _ _ hl]
  have l12 : ∀ l < 4, t₂.zlane .xmm12 l = t.mem.readW (ap + BitVec.ofNat 64 (16 * ((l + 2) % 4))) 128 :=
    fun l hl => by
      simp only [t₂]
      rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl, zlane_vshufi32x4 _ _ _ _ _ _ hl]
      simp only [ite_true, shuf4E _ hl]
      exact zlane_load t .xmm12 ap (by omega_arith)
  have l7 : ∀ l < 4, t₂.zlane .xmm7 l = t.mem.readW (ad + BitVec.ofNat 64 (16 * l)) 128 := fun l hl =>
    zlane_load t₁' .xmm7 ad hl
  refine WP.mono (WP.zlanes (lane_ld (k := 2) (by decide)) fun l _ => lane_ld_ok (k := 2) (t₂.zproj l))
    fun t' ⟨hk', hq⟩ => ⟨fun l hl => ?_, ?_⟩
  · rw [(hq l hl).1]
    have hp : prod (t₂.zproj l) = prod (t.zproj l) := by
      simp only [prod, State.zproj_xmm, keep .xmm8 (by decide) (by decide) l hl,
        keep .xmm9 (by decide) (by decide) l hl, keep .xmm10 (by decide) (by decide) l hl]
    simp only [hp, State.zproj_xmm, l7 l hl, l12 l hl, keep .xmm0 (by decide) (by decide) l hl, h0 l hl,
      show (2 : Nat) ≠ VG.Impl.Gcm.X86_64.StitchZ.ord 0 by decide, show (2 : Nat) ≠ 0 by decide, ite_false,
      zero_xor_b]
    rw [← blockAt_eq]
  · refine ⟨hk'.gpr, hk'.mem, hk'.rd, hk'.wr, fun r hr l hl => ?_⟩
    have := (hq l hl).2.xmm r (fun h => hr (List.mem_cons_of_mem _ h))
    simp only [State.zproj_xmm] at this
    rw [this, keep r (fun h => hr (h ▸ List.mem_cons_self))
      (fun h => hr (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)) l hl]

/-- A step of the loop: group `j` of `G` times its powers from the
context, added to the products. -/
theorem ghStepP_ok {Ctx W : Addr} {g j : Nat} {m : Mem} (t : State) (hj : j < g) (hg : g ≤ 8)
    (hm : t.mem = m) (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask)
    (hrdx : t.gpr .rdx = W + BitVec.ofNat 64 (384 + 64 * j))
    (hr11 : t.gpr .r11 = Ctx + BitVec.ofNat 64 (64 + 64 * (g - j)))
    (hin : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 (512 + 64 * j)) 64)
    (hpin : InRegions (t.rd ++ t.wr) (Ctx + BitVec.ofNat 64 (192 + 64 * (g - j))) 64)
    (hp : ∀ l < 4, prod (t.zproj l) = gacc (tabView Ctx W m) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g l j) :
    WP isa (.block ghBodyP) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) =
        gacc (tabView Ctx W m) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g l (j + 1)) ∧
      t'.gpr .rdx = W + BitVec.ofNat 64 (384 + 64 * (j + 1)) ∧
      t'.gpr .r11 = Ctx + BitVec.ofNat 64 (64 + 64 * (g - (j + 1))) ∧ t'.gpr .r9 = t.gpr .r9 - 1 ∧
      t'.zf = some (t.gpr .r9 - 1 == 0) ∧ (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t'.gpr r = t.gpr r) ∧
      t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      ZKeep [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  have ea₁ : t.gpr .rdx + BitVec.ofInt 64 ((128 : Nat) : Int) = W + BitVec.ofNat 64 (512 + 64 * j) := by
    rw [hrdx, BitVec.ofInt_natCast, add_ofNat_ofNat, show 384 + 64 * j + 128 = 512 + 64 * j by omega_arith]
  have ea₂ : t.gpr .r11 + BitVec.ofInt 64 ((128 : Nat) : Int) = Ctx + BitVec.ofNat 64 (192 + 64 * (g - j)) := by
    rw [hr11, BitVec.ofInt_natCast, add_ofNat_ofNat, show 64 + 64 * (g - j) + 128 = 192 + 64 * (g - j) by omega_arith]
  rw [ghBodyP, WP.block_append_iff]
  refine WP.mono (ghLoadP_ok t h0 (by rw [ea₁]; exact hin) (by rw [ea₂]; exact hpin)) fun t₁ ⟨p₁, f₁⟩ => ?_
  apply WP.of_runBlock
  refine ⟨_, by xrun [], ?_⟩
  refine ⟨fun l hl => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show prod (t₁.zproj l) = _
    rw [p₁ l hl, gacc_succ, ← hp l hl, ea₁, ea₂, add_ofNat_ofNat, add_ofNat_ofNat,
      tabView_readW _ _ _ (by omega_arith) hl, ← hm]
    have hb : blockAt (tabView Ctx W t.mem) (W + BitVec.ofNat 64 512 + BitVec.ofNat 64 (64 * j + 16 * l)) =
        blockAt t.mem (W + BitVec.ofNat 64 (512 + 64 * j + 16 * l)) := by
      rw [add_ofNat_ofNat, show 512 + (64 * j + 16 * l) = 512 + 64 * j + 16 * l by omega_arith, blockAt_eq, blockAt_eq,
        (tabView_out Ctx W t.mem).readW
          (r := ⟨W + BitVec.ofNat 64 (512 + 64 * j + 16 * l), 16⟩) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    rw [hb, show 192 + 64 * (g - j) + 16 * ((l + 2) % 4) = 256 + 64 * (g - 1 - j) + 16 * ((l + 2) % 4) by omega_arith]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rw [f₁.gpr, hrdx, add_ofNat_ofNat]; congr 1
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rw [f₁.gpr, hr11, show 64 + 64 * (g - j) = (64 + 64 * (g - (j + 1))) + 64 by omega_arith, ← add_ofNat_ofNat]
    exact BitVec.add_sub_cancel _ _
  · simp [gpr_setReg, gpr_arithFlags, f₁.gpr]
  · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, f₁.gpr]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, f₁.gpr]
  · exact f₁.mem
  · exact f₁.rd
  · exact f₁.wr
  · intro r hr l hl; exact f₁.zlane r hr l hl

/-- `ghashP` computes what `ghash` does from the table `tabView` puts at
`W + 1536`. -/
theorem ghashP_ok {s₀ : State} {Ctx W SP : Addr} (hcov : Covers [⟨Ctx, 1024⟩] (s₀.rd ++ s₀.wr)) :
    GhFrom ghashP (tabView Ctx W) s₀ Ctx W SP := by
  intro g s he hmp hg1 hg h0 h1 hrd hwr
  have wR : ∀ {d n : Nat}, d + n ≤ 2560 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
    fun h => in_left (in_off he.perm.w h (by decide))
  have cR : ∀ {d n : Nat}, d + n ≤ 1024 → InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 d) n :=
    fun h => by rw [hrd, hwr]; exact in_off hcov h (by decide)
  refine WP.seq (WP.mono (ghSetupP_ok s he.r13 he.r15 hmp hg (wR (by decide)))
    fun s₁ ⟨dx₁, r9₁, r11₁, p₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (t : State) => (∀ l < 4, prod (t.zproj l) =
      gacc (tabView Ctx W s.mem) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g l g) ∧
      (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s t) ?_
    fun t ⟨pt, gt, mt, rdt, wrt, zt⟩ => ?_)
  · refine WP.loop (M := isa) (body := .block ghBodyP) (c := .ne)
      (fun (n : Nat) (t : State) => ∃ j, n = g - j ∧ j < g ∧
        t.gpr .rdx = W + BitVec.ofNat 64 (384 + 64 * j) ∧ t.gpr .r11 = Ctx + BitVec.ofNat 64 (64 + 64 * (g - j)) ∧
        t.gpr .r9 = BitVec.ofNat 64 (g - j) ∧
        (∀ l < 4, prod (t.zproj l) =
          gacc (tabView Ctx W s.mem) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g l j) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr ∧ ZKeep [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s t) ?_ (g - 0) s₁
      ⟨0, rfl, hg1, by rw [dx₁], by rw [r11₁, Nat.sub_zero], by rw [r9₁, Nat.sub_zero],
        fun l hl => by rw [p₁ l hl]; rfl, g₁, m₁, rd₁, wr₁, z₁.mono (by simp)⟩
    rintro n t ⟨j, rfl, hj, dxt, r11t, r9t, pt, gt, mt, rdt, wrt, zt⟩
    have h0t : ∀ l < 4, t.zlane .xmm0 l = revMask := fun l hl => by rw [zt _ (by decide) l hl, h0 l hl]
    refine WP.mono (ghStepP_ok t hj hg mt h0t dxt r11t (by rw [rdt, wrt]; exact wR (by omega_arith))
      (by rw [rdt, wrt]; exact cR (by omega_arith)) pt)
      fun t' ⟨p', dx', r11', r9', zf', g', m', rd', wr', z'⟩ => ?_
    have hz : t'.zf = some (decide (g - j = 1)) := by
      rw [zf', r9t, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, sub_beq (a := g - j) (b := 1) (by omega_arith)
        (by omega_arith)]
    have gg : ∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t'.gpr r = s.gpr r := fun r a b c => by
      rw [g' r a b c, gt r a b c]
    by_cases he : j + 1 = g
    · left
      exact ⟨by simp [eval, hz]; omega_arith, fun l hl => by rw [p' l hl, he], gg, by rw [m', mt], by rw [rd', rdt],
        by rw [wr', wrt], zt.trans (z'.mono (by simp))⟩
    · right
      refine ⟨by simp [eval, hz]; omega_arith, g - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, dx', r11', ?_, p', gg,
        by rw [m', mt], by rw [rd', rdt], by rw [wr', wrt], zt.trans (z'.mono (by simp))⟩
      rw [r9', r9t, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_sub (by omega_arith) (by omega_arith)]; congr 1
  · have h1t : ∀ l < 4, t.zlane .xmm1 l = poly := fun l hl => by rw [zt _ (by decide) l hl, h1 l hl]
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.fin_ok t h1t) fun t' ⟨y0, y1, f'⟩ => ⟨?_, y1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [y0, pt 0 (by decide), pt 1 (by decide), pt 2 (by decide), pt 3 (by decide)]
    · intro r a b c; rw [f'.gpr, gt r a b c]
    · rw [f'.mem, mt]
    · rw [f'.rd, rdt]
    · rw [f'.wr, wrt]
    · intro r hr l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨n2, n7, n8, n9, n10, n11, n12⟩ := hr
      rw [f'.zlane r (by simp [n2, n8, n9, n10, n11]) l hl, zt r (by simp [n7, n8, n9, n10, n11, n12]) l hl]

/-! ## The short path with a prepared context -/

/-- With a prepared key context, `powersP` and `ghashP` compute what
`powers` and `ghash` do. -/
theorem powOk_powersP : PowOk CtxMode.prepared powersP ghashP := by
  intro s₀ Ctx W SP D n X
  refine ⟨tabView Ctx W, tabView_view X.cw X.cd, ghashP_ok X.cov, ?_⟩
  intro g s he _ hg1 hg8 f rd wr
  have hok : Spec.Gcm.PreparedPowersRepr s.mem Ctx :=
    CtxMode.prepared.frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact X.cw
      · exact X.cd
      · exact X.ct.symm) X.w X.ok
  refine WP.mono (powersP_run s) fun t ⟨mt, z0, z1, gt, rdt, wrt⟩ =>
    ⟨by rw [mt]; exact tabView_ok hok hg8, by rw [mt]; exact Frame.refl _ _, z0, z1,
      fun r ha _ => gt r ha, rdt, wrt⟩

/-- `ghashP` in two runs. -/
theorem ghashP_taint : GhTaint ghashP := by
  intro s₀ s₀' Ctx W SP A D R al n J J' tl tl' h32
  have h32' := h32
  simp only [nb16] at h32'
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega_arith
  have hw : ∀ {s₀ : State} {J : Block} {tl : BitVec 64} (s : State), SJ s₀ Ctx W SP A D R al n J tl s →
      WP isa (.block ghSetupP) s fun t => t.gpr .rdx = W + BitVec.ofNat 64 384 ∧
        t.gpr .r9 = BitVec.ofNat 64 (grp al n) ∧ t.gpr .r11 = Ctx + BitVec.ofNat 64 (64 + 64 * grp al n) :=
    fun s h => WP.mono (ghSetupP_ok s h.sm.env.r13 h.sm.env.r15 h.sm.r288 hg8 (h.sm.env.perm.wR (by decide)))
      fun _ ⟨dx, r9, r11, _⟩ => ⟨dx, r9, r11⟩
  exact rel_piece [.rdx, .r9, .r11] (fun _ h => h.sm.env) (fun _ h => h.sm.env) (keepsEnv (by decide +kernel))
      ⟨_, by taint_decide⟩ hw hw (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) ⟨_, by taint_decide⟩

/-- `powersP` and `ghashP` in two runs: their addresses are the key
context's and `W`'s. -/
theorem powersP_ct : PowCT powersP ghashP := by
  refine ⟨fun {s₀ s₀' Ctx W SP A D R al n J J' tl tl'} => ?_, ghashP_taint⟩
  exact rel_env_regs [] (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.X86_64.Short

end

end

/-! ### `AesGcm.X86_64.Fast.OpenCT`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.Fast.OpenTag`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.Fast.OpenTail`, which this module and modules that import it used -/

section

/-!
# AES-GCM `open`'s path for TLS records: the bytes left

Untrusted: everything here is checked by Lean. `FastOpen.tagP` leaves `K[1]`,
at `W + 1040`, the keystream of the counter block (`KOk`), which the code
until the end of `open` keeps (`pStable_kOk`). `FastOpen.tailK` decrypts the
bytes left with it, as `oneCrypt` does with a call of `vg_aes_ctr32`:
`crOk_tailK`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.FastOpen

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt inc32)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Ctr xorKs)

/-- `K[1]` is the keystream of the counter block. -/
def KOk (Ctx W : Addr) (R : Nat) (s : State) : Prop :=
  blockAt s.mem (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16) =
    ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48))

theorem pStable_kOk : PStable KOk := by
  intro Ctx W SP R s s' L hR f h
  have e : W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16 = W + BitVec.ofNat 64 1040 := by rw [add_ofNat_assoc]
  unfold KOk at h ⊢
  rw [blockAt_frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [e]; rcases hr with rfl | rfl | rfl <;> exact L.w_w (.inr (by decide)) (by decide) (by decide)),
    ciph_frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact L.cw'.sub_right (Lay.wSub (by decide))) hR,
    blockAt_frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩))]
  exact h

/-- `ctr_tail` with the keystream block anywhere: fewer than 16 bytes from a
block boundary, XORed with the keystream of the counter block. -/
theorem ctr_tailK {m m₁ : Mem} {cb ks k : Addr} {ciph : Block → Block} {icb : Block} {n : Nat}
    (h : Ctr m cb ks ciph icb n) (h0 : n % 16 = 0) (hk : blockAt m₁ k = ciph (blockAt m cb))
    {d : List Byte} (hd : d.length < 16) :
    List.zipWith (· ^^^ ·) d (bytesAt m₁ k d.length) = xorKs ciph icb n d := by
  have hcb : blockAt m cb = Nat.repeat inc32 (n / 16) icb := by rw [h.1]; congr 1; omega_using [h0]
  refine Proof.Gcm.zipWith_eq_xorKs (Cmac.bytesAt_length _ _ _) fun j hj => ?_
  rw [Proof.Gcm.getD_bytesAt' _ _ hj, Proof.Gcm.bytes_toBytes_blockAt m₁ k (k := j) (by omega_using [hd, hj]), hk, hcb,
    Proof.Gcm.ksByte, show (n + j) / 16 = n / 16 by omega_using [h0, hd, hj], show (n + j) % 16 = j by omega_using [h0, hd, hj]]

/-- `tailK`: the bytes left decrypted with `K[1]`. -/
theorem crOk_tailK : CrOk KOk Impl.AesGcm.X86_64.FastOpen.tailK := by
  intro Ctx W SP L R icb P₀ D n s hP hn he hR hdat hlen hd hK
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hcx₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .rcx (.mem (at_ .r15 lenO)),
      .alu .test .rcx (.reg .rcx)] s = some s₁ ∧ s₁.gpr .rcx = BitVec.ofNat 64 n ∧ s₁.zf = some (decide (n = 0)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hlen]
    · simp only [zf_arithFlags, hlen]
      exact congrArg some (and_self_beq (by omega_using [hn]))
    · intro r a; simp [gpr_setReg, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (eval_e hz₁) (fun h0 => ?_) (fun h0 => ?_)
  · -- No bytes left.
    have h0' : n = 0 := of_decide_eq_true h0
    subst h0'
    exact WP.block_nil ⟨he₁, by rw [hm₁]; exact Frame.refl _ _, hrd₁, hwr₁, fun _ => by
      rw [hm₁]; rfl⟩
  · have h0' : n ≠ 0 := of_decide_eq_false h0
    have q₁ := he₁.perm.wR (show 200 + 8 ≤ 2560 by decide)
    obtain ⟨s₂, run₂, hdi₂, hsi₂, hcx₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        (([.mov .rdi (.mem (at_ .r15 dataO))] : List Instr) ++ ptr .rsi .r15 (Impl.AesGcm.X86_64.Short.kO + 16)) s₁ =
          some s₂ ∧ s₂.gpr .rdi = D ∧ s₂.gpr .rsi = W + BitVec.ofNat 64 1040 ∧ s₂.gpr .rcx = BitVec.ofNat 64 n ∧
        (∀ r, r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by xrun [he₁.r15, q₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, hm₁, hdat]
      · simp [gpr_setReg]; rfl
      · simp [gpr_setReg, hcx₁]
      · intro r a b; simp [gpr_setReg, a, b]
      all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have hlt := hd.ok.lt
    have lp : LoopPre s₂ (W + BitVec.ofNat 64 1040) D n :=
      ⟨hsi₂, hdi₂, hcx₂, by omega_using [h0'], by omega_using [hn],
        by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact covers_left (he.perm.wC (by omega_using [hn])),
        by rw [hwr₂, hwr₁]; exact hd.wr, (hd.ok.w.sub_right (Lay.wSub (by omega_using [hn]))).symm⟩
    refine WP.mono (xorLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_
    rw [hm₂, hm₁] at hm₃
    have hxl := length_xorBytes s.mem D (W + BitVec.ofNat 64 1040) n
    have fw : Frame [⟨D, n⟩] s.mem s₃.mem := by rw [hm₃]; exact writeBytes_frame' _ hxl
    refine ⟨he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;>
          rw [hg₃ _ (by decide) (by decide) (by decide), hg₂ _ (by decide) (by decide)])
        (by rw [hrd₃, hrd₂]) (by rw [hwr₃, hwr₂]),
      fw.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩,
      by rw [hrd₃, hrd₂, hrd₁], by rw [hwr₃, hwr₂, hwr₁], fun hc => ?_⟩
    have e : W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16 = W + BitVec.ofNat 64 1040 := by rw [add_ofNat_assoc]
    unfold KOk at hK
    rw [e] at hK
    have t := ctr_tailK hc hP hK (d := bytesAt s.mem D n) (by rw [length_bytesAt]; omega_using [hn])
    rw [length_bytesAt] at t
    have hb := bytesAt_writeBytes_self s.mem D (xorBytes s.mem D (W + BitVec.ofNat 64 1040) n) (by rw [hxl]; omega_using [hn])
    rw [hxl] at hb
    rw [hm₃, hb, xorBytes, t]

end VG.Proof.AesGcm.X86_64.FastOpen

end

end

/-!
# AES-GCM `open`'s path for TLS records: the tag

Untrusted: everything here is checked by Lean. `FastOpen.tagP` leaves what
`oneTag 112` does (`TagOk`, `oneTag_ok`), without calls: `H'` and `H'²` from
the prepared key context (`Fast.finPowP_ok`), the keystream of `J₀` and of the
counter block (`Short.finKs_ksOk`), the bytes left copied to `G[0]`
(`openTail_ok`, by `copyLoop`) or none (`openNoTail_ok`), `GHASH` continued
over `G`, the tag at `W + 112`, and `J₀` incremented (`incJ_ok`): `tagP_ok`.
It leaves `K[1]` too, the keystream of the counter block (`KOk`): `tagP_okP`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.FastOpen

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Impl.AesGcm.X86_64.FastOpen (incJ tagP)
open VG.Proof.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk IsH1 IsH2 finTextArgs_ok finLens_ok finGh1_ok finGh2_ok finTest_ok
  tagK_ok finKs_ksOk writeW_zero128 ghash_snoc bytesAt_toBytes' add_ofNat_ofNat)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks inc32 zeros padLen toBytes ofBytes ctxH)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Absorbed lensBlock)

/-! ## `J₀` incremented -/

/-- The last word of the block at `St`, big-endian, incremented in place:
`inc32` of the block. -/
theorem inc_block (m : Mem) (St : Addr) :
    blockAt (m.writeW (St + BitVec.ofNat 64 12)
      (X86_64.bswap32 (X86_64.bswap32 (m.readW (St + BitVec.ofNat 64 12) 32) + (BitVec.ofNat 64 1).setWidth 32))) St =
      inc32 (blockAt m St) := by
  refine VG.Proof.Aes.X86_64.ctr_after (n := 1) fun k hk => ?_
  rw [VG.Proof.Aes.X86_64.writeW_apply, Offset.sub_toNat' St (show 12 < 2 ^ 64 by decide) (by omega_arith)]
  by_cases h : k < 12
  · rw [ite_eq_right (show ¬ 12 ≤ k by omega_arith), ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega_arith),
      ite_eq_left h]
  · rw [ite_eq_left (show 12 ≤ k by omega_arith), ite_eq_left (show k - 12 < 32 / 8 by omega_arith), ite_eq_right h,
      BitVec.setWidth_eq]

/-- `incJ`: `J₀`, at `St`, incremented. -/
theorem incJ_ok {Ctx St W SP : Addr} (s : State) (he : Env Ctx St W SP s) :
    ∃ t, runBlock isa incJ s = some t ∧ blockAt t.mem St = inc32 (blockAt s.mem St) ∧
      Frame [⟨St + BitVec.ofNat 64 12, 4⟩] s.mem t.mem ∧ (∀ g, g ≠ .rsi → t.gpr g = s.gpr g) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.xmm = s.xmm := by
  obtain r₃ := he.perm.stR (show 12 + 4 ≤ 80 by decide)
  obtain w₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  refine ⟨_, by xrun [incJ, he.r14, r₃, w₃], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, ww32]
    exact inc_block _ _
  · simp only [mem_setReg, mem_arithFlags]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · intro g hg; simp [gpr_setReg, gpr_arithFlags, hg]
  all_goals rfl

/-! ## The two ends of the tag -/

/-- What both ends of `tagP` start from: `FinPre` without the bytes left
writable, which `open` only reads. -/
structure TagPre (Ctx W SP : Addr) (H : Block) (al n r : Nat) (D : Addr) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  x0 : s.xmm .xmm0 = revMask
  x1 : s.xmm .xmm1 = poly
  h1 : IsH1 H (s.xmm .xmm3)
  h2 : IsH2 H (s.xmm .xmm3) (s.xmm .xmm6)
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 r
  r16 : r ≤ 16
  rd : Covers [⟨D, r⟩] (s.rd ++ s.wr)
  dW : (⟨D, r⟩ : Region).Disjoint ⟨W, 2560⟩

/-- After the blocks `GHASH` reads from memory are stored, from `s`: the
lengths block at `W + 528` and, with bytes left, them and zeros at
`W + 512`. -/
structure TagMid (Ctx W SP : Addr) (al n r : Nat) (D : Addr) (s t : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨W + BitVec.ofNat 64 512, 32⟩] s.mem t.mem
  xmm : ∀ q, q ≠ .xmm7 → t.xmm q = s.xmm q
  lens : blockAt t.mem (W + BitVec.ofNat 64 528) = ofBytes (lensBlock al n)
  tail : r ≠ 0 → blockAt t.mem (W + BitVec.ofNat 64 512) = ofBytes (bytesAt s.mem D r ++ zeros (16 - r))

/-- Without bytes left: the lengths block. -/
theorem prepNo_ok {Ctx W SP D : Addr} {H : Block} {al n r : Nat} {s : State} (P : TagPre Ctx W SP H al n r D s)
    (h0 : r = 0) : WP isa (.block finLens) s (TagMid Ctx W SP al n r D s) := by
  have he := P.env
  obtain ⟨s₃, run₃, f₃, hL₃, g₃, rd₃, wr₃, x₃⟩ := finLens_ok s he P.alen P.tlen
  refine WP.of_runBlock ⟨s₃, run₃, he.keep (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) rd₃ wr₃, rd₃, wr₃,
    f₃.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩,
    fun q _ => by rw [x₃], by rw [blockAt, hL₃], fun h => absurd h0 h⟩

/-- With bytes left: they are copied to `G[0]`, padded with zeros, and the
lengths block. -/
theorem prepTail_ok {Ctx W SP D : Addr} {H : Block} {al n r : Nat} {s : State} (P : TagPre Ctx W SP H al n r D s)
    (h0 : r ≠ 0) :
    WP isa (.seq (.block finTextArgs) (.seq copyLoop (.block finLens))) s (TagMid Ctx W SP al n r D s) := by
  have he := P.env
  have hr := P.r16
  obtain dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨D, r⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h => P.dW.sub_right (Lay.wSub h)
  obtain dWW : ∀ {d k e j : Nat}, d + k ≤ e ∨ e + j ≤ d → d + k ≤ 2560 → e + j ≤ 2560 →
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
    fun h _ _ => Offset.disjoint W h (by have := he.perm.w; omega_arith) (by omega_arith)
  -- `G[0]` zeroed, and the arguments.
  obtain ⟨s₁, run₁, m₁, di₁, si₁, -, cx₁, g₁, rd₁, wr₁, x₁⟩ := finTextArgs_ok s he P.dat P.len
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain lp : LoopPre s₁ D (W + BitVec.ofNat 64 512) r :=
    ⟨si₁, di₁, cx₁, by omega_arith, by omega_arith, by rw [rd₁, wr₁]; exact P.rd, by rw [wr₁]; exact he.perm.wC (by omega_arith),
      dW (by omega_arith)⟩
  -- The copy.
  refine WP.seq (WP.mono (copyLoopX_ok s₁ lp) fun s₂ ⟨m₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  obtain he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide) (by decide)) rd₁ wr₁
  obtain he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide)) rd₂ wr₂
  obtain x₂' : ∀ q, q ≠ .xmm7 → s₂.xmm q = s.xmm q := fun q hq => by rw [x₂, x₁ q hq]
  generalize hc : bytesAt s₁.mem D r = c at m₂
  obtain hcl : c.length = r := by rw [← hc, length_bytesAt]
  obtain f₁ : Frame [⟨W + BitVec.ofNat 64 512, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame' _ (List.length_replicate ..)
  obtain f₂ : Frame [⟨W + BitVec.ofNat 64 512, r⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact writeBytes_frame' _ hcl
  obtain F₂ : Frame [⟨W + BitVec.ofNat 64 512, 32⟩] s.mem s₂.mem := by
    refine (f₁.sub fun q hq => ?_).trans (f₂.sub fun q hq => ?_) <;>
      simp only [List.mem_singleton] at hq <;> subst hq <;>
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩
  obtain kW : ∀ {d k : Nat}, d + k ≤ 512 ∨ (544 ≤ d ∧ d + k ≤ 2560) →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 512, 32⟩ : Region)], (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact dWW (by omega_arith) (by omega_arith) (by decide)
  obtain rW₂ : ∀ d, d + 8 ≤ 512 → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h => F₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kW (.inl h)) (by decide)
  -- The lengths block.
  obtain ⟨s₃, run₃, f₃, hL₃, g₃, rd₃, wr₃, x₃⟩ := finLens_ok s₂ he₂ (by rw [rW₂ 184 (by decide)]; exact P.alen)
    (by rw [rW₂ 192 (by decide)]; exact P.tlen)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  obtain he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) rd₃ wr₃
  obtain F₃ : Frame [⟨W + BitVec.ofNat 64 512, 32⟩] s.mem s₃.mem :=
    F₂.trans (f₃.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)
  obtain hc' : c = bytesAt s.mem D r := by
    rw [← hc, bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact dW (by decide)) (by omega_arith)]
  -- `G[0]`: the ciphertext and zeros.
  obtain z₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 512 + BitVec.ofNat 64 r) (16 - r) = zeros (16 - r) := by
    obtain e := bytesAt_add s₁.mem (W + BitVec.ofNat 64 512) r (16 - r)
    obtain e16 : bytesAt s₁.mem (W + BitVec.ofNat 64 512) 16 = List.replicate 16 0 := by
      rw [m₁]; exact bytesAt_writeBytes_self _ _ _ (by decide)
    rw [Nat.add_sub_cancel' (by omega_arith), e16, show List.replicate 16 (0 : Byte) = List.replicate r 0 ++
      List.replicate (16 - r) 0 by rw [List.replicate_append_replicate, Nat.add_sub_cancel' (by omega_arith)]] at e
    exact ((List.append_inj e (by rw [List.length_replicate, length_bytesAt])).2).symm
  obtain hG0 : bytesAt s₃.mem (W + BitVec.ofNat 64 512) 16 = c ++ zeros (16 - r) := by
    rw [bytesAt_frame f₃ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dWW (.inl (by decide)) (by decide) (by decide))
      (by decide), ← Nat.add_sub_cancel' (show r ≤ 16 by omega_arith), bytesAt_add, Nat.add_sub_cancel' (by omega_arith), m₂]
    obtain a₁ : bytesAt (writeBytes s₁.mem (W + BitVec.ofNat 64 512) c) (W + BitVec.ofNat 64 512) r = c := by
      rw [← hcl]; exact bytesAt_writeBytes_self _ _ _ (by omega_arith)
    obtain a₂ : bytesAt (writeBytes s₁.mem (W + BitVec.ofNat 64 512) c) (W + BitVec.ofNat 64 512 + BitVec.ofNat 64 r)
        (16 - r) = bytesAt s₁.mem (W + BitVec.ofNat 64 512 + BitVec.ofNat 64 r) (16 - r) :=
      bytesAt_frame (writeBytes_frame' _ hcl) (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          exact Offset.disjoint_base (W + BitVec.ofNat 64 512) (Nat.le_refl r) (by omega_arith)) (by omega_arith)
    rw [a₁, a₂, z₁]
  exact ⟨he₃, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], F₃, fun q hq => by rw [x₃, x₂' q hq],
    by rw [blockAt, hL₃], fun _ => by rw [blockAt, hG0, hc']⟩

/-- Without bytes left: `GHASH` continued over the lengths block, and the tag
at `W + 112`. -/
theorem endNo_ok {Ctx W SP : Addr} {H : Block} {u : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP u)
    (x0 : u.xmm .xmm0 = revMask) (x1 : u.xmm .xmm1 = poly) (h1 : IsH1 H (u.xmm .xmm3)) :
    WP isa (.block (finGh1 ++ tagK uO)) u fun t =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧ t.rd = u.rd ∧ t.wr = u.wr ∧
      Frame [⟨W + BitVec.ofNat 64 112, 16⟩] u.mem t.mem ∧
      blockAt t.mem (W + BitVec.ofNat 64 112) =
        ghashFrom H (blockAt u.mem (yA W)) [blockAt u.mem (W + BitVec.ofNat 64 528)] ^^^
          blockAt u.mem (W + BitVec.ofNat 64 1024) := by
  rw [WP.block_append_iff]
  refine WP.mono (finGh1_ok u he (H := H) x0 x1 h1) fun s₄ ⟨y₄, o₄⟩ => ?_
  obtain ⟨s₅, run₅, tag₅, fW, g₅, rd₅, wr₅⟩ := tagK_ok (W := W) (o := 112) s₄
    ((o₄.gpr _ (by decide)).trans he.r15) (by rw [o₄.wr]; exact he.perm.w) (by decide)
    (by rw [o₄.xmm _ (by decide)]; exact x0)
  refine WP.of_runBlock ⟨s₅, run₅, he.keep (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> rw [g₅, o₄.gpr _ (by decide)]) (by rw [rd₅, o₄.rd]) (by rw [wr₅, o₄.wr]),
    by rw [rd₅, o₄.rd], by rw [wr₅, o₄.wr], by rw [← o₄.mem]; exact fW, ?_⟩
  rw [tag₅, y₄, o₄.mem]

/-- With bytes left: `GHASH` continued over `G[0]` and the lengths block, and
the tag at `W + 112`. -/
theorem endTail_ok {Ctx W SP : Addr} {H : Block} {u : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP u)
    (x0 : u.xmm .xmm0 = revMask) (x1 : u.xmm .xmm1 = poly) (h2 : IsH2 H (u.xmm .xmm3) (u.xmm .xmm6)) :
    WP isa (.block (finGh2 ++ tagK uO)) u fun t =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧ t.rd = u.rd ∧ t.wr = u.wr ∧
      Frame [⟨W + BitVec.ofNat 64 112, 16⟩] u.mem t.mem ∧
      blockAt t.mem (W + BitVec.ofNat 64 112) =
        ghashFrom H (blockAt u.mem (yA W))
          [blockAt u.mem (W + BitVec.ofNat 64 512), blockAt u.mem (W + BitVec.ofNat 64 528)] ^^^
          blockAt u.mem (W + BitVec.ofNat 64 1024) := by
  rw [WP.block_append_iff]
  refine WP.mono (finGh2_ok u he (H := H) x0 x1 h2) fun s₄ ⟨y₄, o₄⟩ => ?_
  obtain ⟨s₅, run₅, tag₅, fW, g₅, rd₅, wr₅⟩ := tagK_ok (W := W) (o := 112) s₄
    ((o₄.gpr _ (by decide)).trans he.r15) (by rw [o₄.wr]; exact he.perm.w) (by decide)
    (by rw [o₄.xmm _ (by decide)]; exact x0)
  refine WP.of_runBlock ⟨s₅, run₅, he.keep (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> rw [g₅, o₄.gpr _ (by decide)]) (by rw [rd₅, o₄.rd]) (by rw [wr₅, o₄.wr]),
    by rw [rd₅, o₄.rd], by rw [wr₅, o₄.wr], by rw [← o₄.mem]; exact fW, ?_⟩
  rw [tag₅, y₄, o₄.mem]

/-! ## The tag -/

/-- `tagP ks` with a prepared key context: what `oneTag 112` does, and `K[1]`
the keystream of the counter block. -/
theorem tagP_okP (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) : TagOkP (CtxMode.preparedN np hpn) KOk (tagP ks) := by
  intro Ctx W SP L R D n N al H x s hx he hH hR hdat hlen hn16 htl hN hal hd hDW X
  -- `H'` and `H'²`.
  have hX : VG.Proof.Gcm.X86_64.Stitch.PowersN np s.mem Ctx := X.1
  obtain p0 := hX 0 (by have := hpn.1; omega_arith)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at p0
  rw [show ctxH s.mem Ctx = H by rw [ctxH_eq, hH]] at p0
  unfold tagP Impl.AesGcm.X86_64.FastOpen.lenTest
  refine WP.seq (WP.mono (Fast.finPowP_ok hF s he.r13 (in_off X.2 (show 272 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64)))
    (in_off X.2 (show 256 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64))) p0.2 p0.1) fun s₁ ⟨x0, x1, h1, h2, o₁⟩ => ?_)
  obtain he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun g hg => o₁.gpr _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> decide)) o₁.rd o₁.wr
  have m₁ := o₁.mem
  -- The test.
  refine WP.seq (WP.mono (finTest_ok (r := n) (by omega_arith) s₁ he₁ (by rw [m₁]; exact hlen))
    fun s₂ ⟨z₂, g₂, m₂, rd₂, wr₂, x₂⟩ => ?_)
  obtain he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide)) rd₂ wr₂
  obtain M₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  obtain TP : TagPre Ctx W SP H al N n D s₂ :=
    { env := he₂
      x0 := by rw [x₂]; exact x0
      x1 := by rw [x₂]; exact x1
      h1 := by rw [x₂]; exact h1
      h2 := by rw [x₂]; exact h2
      alen := by rw [M₂]; exact hal
      tlen := by rw [M₂]; exact htl
      dat := by rw [M₂]; exact hdat
      len := by rw [M₂]; exact hlen
      r16 := by omega_arith
      rd := by rw [rd₂, wr₂, o₁.rd, o₁.wr]; exact hd.rd
      dW := hDW }
  -- The blocks `GHASH` reads, stored before the keystream.
  refine WP.seq (WP.mono (Q := TagMid Ctx W SP al N n D s₂) (WP.ite (decide (n = 0)) (eval_e z₂)
    (fun h0 => prepNo_ok TP (of_decide_eq_true h0)) (fun h0 => prepTail_ok TP (of_decide_eq_false h0))) fun u U => ?_)
  obtain FU : Frame [⟨W + BitVec.ofNat 64 512, 32⟩] s.mem u.mem := by rw [← M₂]; exact U.frame
  obtain rU : ∀ d, d + 8 ≤ 512 → u.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h => FU.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact Offset.disjoint W (.inl h) (by omega_arith) (by decide))
      (by decide)
  -- The keystream of `J₀` and of the counter block.
  refine WP.seq (WP.mono (hks u U.env (by rw [rU 176 (by decide)]; exact hR.1) hR.2)
    fun s₃ ⟨k₀, k₁, fK, g₃, rd₃, wr₃, x₃⟩ => ?_)
  obtain he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := U.env.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide) (by decide)) rd₃ wr₃
  -- `J₀` incremented.
  obtain ⟨s₄, run₄, j₄, fJ, gJ, rdJ, wrJ, xJ⟩ := incJ_ok s₃ he₃
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  obtain he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₃.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact gJ _ (by decide)) rdJ wrJ
  obtain e28 : W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12 = W + BitVec.ofNat 64 28 := add_ofNat_ofNat W 16 12
  obtain FK : Frame [⟨W + BitVec.ofNat 64 1024, 64⟩, ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12, 4⟩] u.mem s₄.mem :=
    (fK.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; simp [hq], fun _ h => h⟩).trans
      (fJ.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; simp [hq], fun _ h => h⟩)
  obtain rK : ∀ d, 32 ≤ d → d + 8 ≤ 512 →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => by
      rw [← rU d h₂]
      exact FK.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact Offset.disjoint W (.inl (by omega_arith)) (by omega_arith) (by decide)
        · rw [e28]; exact Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by decide))
        (by decide)
  -- The test again.
  refine WP.seq (WP.mono (finTest_ok (r := n) (by omega_arith) s₄ he₄ (by rw [rK 208 (by decide) (by decide)]; exact hlen))
    fun s₅ ⟨z₅, g₅, m₅, rd₅, wr₅, x₅⟩ => ?_)
  obtain he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide)) rd₅ wr₅
  obtain xx : ∀ q, q ≠ .xmm5 → q ≠ .xmm7 → q ≠ .xmm8 → q ≠ .xmm13 → s₅.xmm q = s₁.xmm q := fun q a b c d => by
    rw [x₅, xJ, x₃ q a b c d, U.xmm q b, x₂]
  -- The regions of the state and of `W` that the code writes.
  obtain dS : ∀ {a k : Nat}, a + k ≤ 80 → a + k ≤ 12 ∨ 16 ≤ a →
      ∀ q ∈ [(⟨W + BitVec.ofNat 64 1024, 64⟩ : Region), ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12, 4⟩] ++
        [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 512, 32⟩],
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a, k⟩ : Region).Disjoint q := fun ha h q hq => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.st_w ha (.inr ⟨by decide, by decide⟩)
    · exact L.st_st (by omega_arith) ha (by decide)
    · exact L.st_w ha (.inr ⟨by decide, by decide⟩)
    · exact L.st_w ha (.inr ⟨by decide, by decide⟩)
  obtain F₅ : Frame ([⟨W + BitVec.ofNat 64 1024, 64⟩, ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12, 4⟩] ++
      [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 512, 32⟩]) s.mem s₅.mem := by
    rw [m₅]
    refine (FU.sub fun q hq => ?_).trans (FK.sub fun q hq => ?_)
    · simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨q, List.mem_append_left _ hq, fun _ h => h⟩
  -- The blocks `GHASH` reads, and the keystream of `J₀`, after the keystream.
  obtain bK : ∀ {d : Nat}, d = 512 ∨ d = 528 →
      blockAt s₅.mem (W + BitVec.ofNat 64 d) = blockAt u.mem (W + BitVec.ofNat 64 d) := fun h => by
    rw [m₅]
    refine blockAt_frame FK fun q hq => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Offset.disjoint W (.inl (by omega_arith)) (by omega_arith) (by decide)
    · rw [e28]; exact Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain hCtx : ciphOf u.mem Ctx R = ciphOf s.mem Ctx R := by
    simp only [ciphOf]
    rw [bytesAt_frame FU (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact L.cw'.sub_left (Region.sub_prefix (by rcases hR.2 with h | h | h <;> subst h <;> decide))
        |>.sub_right (Lay.wSub (by decide))) (by rcases hR.2 with h | h | h <;> subst h <;> decide)]
  obtain hK₀ : blockAt s₅.mem (W + BitVec.ofNat 64 1024) = ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)) := by
    rw [m₅, blockAt_frame fJ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.st_w (a := 12) (n := 4) (d := 1024) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm), k₀,
      hCtx, blockAt_frame FU (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 32) (by decide) (.inr ⟨by decide, by decide⟩))]
  obtain hY : Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x →
      blockAt s₅.mem (yA W) = ghash H (blocks x) := fun hab => by
    rw [blockAt_frame F₅ (fun q hq => dS (a := 16) (k := 16) (by decide) (.inr (by decide)) q hq),
      hab.1, Proof.Gcm.whole_of_mod hx, List.take_length]
  -- Either end leaves the post.
  have fin : ∀ t : State, Env Ctx (W + BitVec.ofNat 64 16) W SP t → t.rd = s₅.rd → t.wr = s₅.wr →
      Frame [⟨W + BitVec.ofNat 64 112, 16⟩] s₅.mem t.mem →
      (Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x →
        bytesAt t.mem (W + BitVec.ofNat 64 112) 16 =
          toBytes (ghashFrom H (ghash H (blocks (x ++ bytesAt s.mem D n ++
              zeros (padLen (x ++ bytesAt s.mem D n).length))))
            [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)))) →
      (Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧
        Frame (⟨W + BitVec.ofNat 64 112, 16⟩ :: wFrame W SP) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
          blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) ∧
        blockAt t.mem (W + BitVec.ofNat 64 16) = inc32 (blockAt s.mem (W + BitVec.ofNat 64 16)) ∧
        (Absorbed s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H x →
          bytesAt t.mem (W + BitVec.ofNat 64 112) 16 =
            toBytes (ghashFrom H (ghash H (blocks (x ++ bytesAt s.mem D n ++
                zeros (padLen (x ++ bytesAt s.mem D n).length))))
              [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16))))) ∧
        KOk Ctx W R t := by
    intro t et rdt wrt ft tt
    obtain rd' : t.rd = s.rd := by rw [rdt, rd₅, rdJ, rd₃, U.rd, rd₂, o₁.rd]
    obtain wr' : t.wr = s.wr := by rw [wrt, wr₅, wrJ, wr₃, U.wr, wr₂, o₁.wr]
    obtain FT : Frame ([⟨W + BitVec.ofNat 64 1024, 64⟩, ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12, 4⟩] ++
        [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 512, 32⟩]) s.mem t.mem :=
      F₅.trans (ft.sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact ⟨_, by simp, fun _ h => h⟩)
    obtain cbT : blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
        blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) :=
      blockAt_frame FT fun q hq => dS (by decide) (.inr (by decide)) q hq
    obtain e40 : W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16 = W + BitVec.ofNat 64 1040 := add_ofNat_ofNat W 1024 16
    obtain kT : KOk Ctx W R t := by
      unfold KOk
      obtain cU : blockAt u.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
          blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) :=
        blockAt_frame FU (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          exact L.st_w (a := 48) (n := 16) (d := 512) (k := 32) (by decide) (.inr ⟨by decide, by decide⟩))
      obtain kt : blockAt t.mem (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16) =
          blockAt s₃.mem (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16) := by
        rw [e40, blockAt_frame ft (fun q hq => by
            simp only [List.mem_singleton] at hq; subst hq
            exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)), m₅,
          blockAt_frame fJ (fun q hq => by
            simp only [List.mem_singleton] at hq; subst hq; rw [e28]
            exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide))]
      obtain cT : ciphOf t.mem Ctx R = ciphOf s.mem Ctx R :=
        ciph_frame FT (fun q hq => by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl
          · exact L.cw'.sub_right (Lay.wSub (by decide))
          · exact L.cs.sub_right (Lay.stSub (by decide))
          · exact L.cw'.sub_right (Lay.wSub (by decide))
          · exact L.cw'.sub_right (Lay.wSub (by decide))) hR.2
      rw [kt, k₁, hCtx, cU, cT, cbT]
    refine ⟨⟨et, ?_, rd', wr', ?_, ?_, tt⟩, kT⟩
    · refine FT.sub fun q hq => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨W + BitVec.ofNat 64 240, 2320⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact cbT
    · have e : ∀ q ∈ [(⟨W + BitVec.ofNat 64 112, 16⟩ : Region)],
          (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint q := fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        simpa using L.st_w (a := 0) (n := 16) (d := 112) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
      rw [blockAt_frame ft e, m₅, j₄,
        blockAt_frame fK (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          simpa using L.st_w (a := 0) (n := 16) (d := 1024) (k := 64) (by decide) (.inr ⟨by decide, by decide⟩)),
        blockAt_frame FU (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 32) (by decide) (.inr ⟨by decide, by decide⟩))]
  obtain x0₅ : s₅.xmm .xmm0 = revMask := by rw [xx _ (by decide) (by decide) (by decide) (by decide)]; exact x0
  obtain x1₅ : s₅.xmm .xmm1 = poly := by rw [xx _ (by decide) (by decide) (by decide) (by decide)]; exact x1
  refine WP.ite (decide (n = 0)) (eval_e z₅) (fun h0 => ?_) (fun h0 => ?_)
  · -- No bytes left.
    obtain h0' : n = 0 := of_decide_eq_true h0
    subst h0'
    refine WP.mono (endNo_ok (H := H) he₅ x0₅ x1₅ (by rw [xx _ (by decide) (by decide) (by decide) (by decide)]; exact h1))
      fun t ⟨het, rdt, wrt, ft, tagt⟩ => fin t het rdt wrt ft fun hab => ?_
    rw [bytesAt_toBytes', tagt, hY hab, hK₀, bK (.inr rfl), U.lens, show bytesAt s.mem D 0 = [] from rfl,
      List.append_nil, Proof.Gcm.padLen_of_mod hx, show zeros 0 = [] from rfl, List.append_nil]
  · -- Bytes left.
    obtain h0' : n ≠ 0 := of_decide_eq_false h0
    refine WP.mono (endTail_ok (H := H) he₅ x0₅ x1₅ (by
        rw [xx .xmm3 (by decide) (by decide) (by decide) (by decide),
          xx .xmm6 (by decide) (by decide) (by decide) (by decide)]; exact h2))
      fun t ⟨het, rdt, wrt, ft, tagt⟩ => fin t het rdt wrt ft fun hab => ?_
    obtain hpl : padLen (x ++ bytesAt s.mem D n).length = 16 - n := by
      simp only [padLen, List.length_append, length_bytesAt]; omega_arith
    obtain bs := Proof.Gcm.blocks_single (bs := bytesAt s.mem D n ++ zeros (16 - n))
      (by rw [List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; omega_arith)
    rw [bytesAt_toBytes', tagt, hY hab, hK₀, bK (.inl rfl), bK (.inr rfl), U.tail h0', U.lens, M₂, hpl,
      List.append_assoc, Proof.Gcm.blocks_append hx, bs, ghash_snoc, ← Proof.Gcm.ghashFrom_append]
    rfl

/-- `tagP ks` with a prepared key context: what `oneTag 112` does. -/
theorem tagP_ok (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) : TagOk (CtxMode.preparedN np hpn) (tagP ks) :=
  TagOkP.tagOk (tagP_okP hF hks)

end VG.Proof.AesGcm.X86_64.FastOpen

end

end

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
  obtain e28 : W + BitVec.ofNat 64 16 + BitVec.ofNat 64 12 = W + BitVec.ofNat 64 28 := add_ofNat_ofNat W 16 12
  obtain kp : ∀ d, 32 ≤ d → d + 8 ≤ 2560 →
      t.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => f.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      rw [e28]; exact Offset.disjoint W (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by decide)) (by decide)
  refine WP.of_runBlock ⟨t, run, h.env.keep (fun g' hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> exact g _ (by decide)) rd wr,
    by rw [kp 176 (by decide) (by decide)]; exact h.rounds, by rw [kp 200 (by decide) (by decide)]; exact h.dat,
    by rw [kp 208 (by decide) (by decide)]; exact h.len⟩

/-- `FinI` after code that writes only `W + 512` to `W + 544`. -/
theorem finI_keepG {Ctx W SP D : Addr} {R r : Nat} {s s' : State} (h : FinI Ctx W SP D R r s)
    (hg : ∀ g ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr g = s.gpr g) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame [⟨W + BitVec.ofNat 64 512, 32⟩] s.mem s'.mem) : FinI Ctx W SP D R r s' := by
  obtain kp : ∀ d, d + 8 ≤ 512 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact Offset.disjoint W (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide))
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
  obtain wPow : ∀ s, FinI Ctx W SP D R r s ∧ Covers [⟨Ctx, 1024⟩] (s.rd ++ s.wr) ∧ Covers [⟨D, r⟩] (s.rd ++ s.wr) →
      WP isa (.block finPowP) s FinC := fun s h =>
    WP.mono (Fast.finPowP_run s h.1.env.r13 (in_off h.2.1 (show 272 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64)))
      (in_off h.2.1 (show 256 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64)))) fun _ ⟨_, _, _, _, o⟩ =>
      ⟨h.1.keep (fun g hg => o.gpr g (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> decide)) o.rd o.wr (by rw [o.mem]; exact Frame.refl _ _),
        by rw [o.rd, o.wr]; exact h.2.2⟩
  obtain p := rel_next (rel_env_regs [] (fun _ h => h.1.env) (fun _ h => h.1.env) (fun _ _ _ _ _ hr => by cases hr)
    (c := .block finPowP) ⟨_, by taint_decide⟩) wPow wPow
  obtain wTest : ∀ {F : State → Prop}, (∀ {s s' : State}, F s → FinI Ctx W SP D R r s' → s'.rd = s.rd → s'.wr = s.wr →
      F s') → (∀ s, F s → FinI Ctx W SP D R r s) → ∀ s, F s → WP isa (.block lenTest) s fun t =>
        t.zf = some (decide (r = 0)) ∧ F t := fun hF hI s h =>
    WP.mono (finTest_ok (by omega_using [hr]) s (hI s h).env (hI s h).len) fun _ ⟨z, g, m, rd, wr, _⟩ => ⟨z, hF h
      ((hI s h).keep (fun g' hg => g _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> decide)) rd wr (by rw [m]; exact Frame.refl _ _)) rd wr⟩
  obtain wTestC := wTest (F := FinC) (fun h I rd wr => ⟨I, by rw [rd, wr]; exact h.2⟩) fun _ h => h.1
  obtain wTestI := wTest (F := FinI Ctx W SP D R r) (fun _ I _ _ => I) fun _ h => h
  obtain t₁ := rel_next (rel_env_regs [] (fun _ h => h.1.env) (fun _ h => h.1.env) (fun _ _ _ _ _ hr => by cases hr)
    (c := .block lenTest) ⟨_, by taint_decide⟩) wTestC wTestC
  -- The blocks `GHASH` reads: the lengths block, and with bytes left, them first.
  obtain wLens : ∀ s, FinI Ctx W SP D R r s → WP isa (.block finLens) s (FinI Ctx W SP D R r) := fun s h => by
    obtain ⟨t, run, f, -, g, rd, wr, -⟩ := Short.finLens_ok (al := (s.mem.readW (W + BitVec.ofNat 64 184) 64).toNat)
      (n := (s.mem.readW (W + BitVec.ofNat 64 192) 64).toNat) s h.env (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    exact WP.of_runBlock ⟨t, run, finI_keepG h (fun g' hg => g _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> decide)) rd wr
      (f.sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩)⟩
  obtain b₀ := rel_next (rel_env_regs [] (F₁ := FinC) (F₂ := FinC) (fun _ h => h.1.env) (fun _ h => h.1.env)
    (fun _ _ _ _ _ hr => by cases hr) (c := .block finLens) ⟨_, by taint_decide⟩)
    (fun s h => wLens s h.1) (fun s h => wLens s h.1)
  obtain wArgs : ∀ s, FinC s → WP isa (.block finTextArgs) s fun t =>
      t.gpr .rdi = W + BitVec.ofNat 64 512 ∧ t.gpr .rsi = D ∧ t.gpr .rdx = W + BitVec.ofNat 64 1040 ∧
        t.gpr .rcx = BitVec.ofNat 64 r := fun s h => by
    obtain ⟨t, run, -, di, si, dx, cx, -⟩ := finTextArgs_ok s h.1.env h.1.dat h.1.len
    exact WP.of_runBlock ⟨t, run, di, si, dx, cx⟩
  obtain wTail : r ≠ 0 → ∀ s, FinC s →
      WP isa (.seq (.block finTextArgs) (.seq copyLoop (.block finLens))) s (FinI Ctx W SP D R r) := fun h0 s h => by
    have he := h.1.env
    obtain ⟨s₁, run₁, m₁, di₁, si₁, -, cx₁, g₁, rd₁, wr₁, -⟩ := finTextArgs_ok s he h.1.dat h.1.len
    refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
    obtain lp : LoopPre s₁ D (W + BitVec.ofNat 64 512) r :=
      ⟨si₁, di₁, cx₁, by omega_using [h0], by omega_using [hr], by rw [rd₁, wr₁]; exact h.2, by rw [wr₁]; exact he.perm.wC (by omega_using [hr]),
        hDW.sub_right (Lay.wSub (by omega_using [hr]))⟩
    refine WP.seq (WP.mono (copyLoopX_ok s₁ lp) fun s₂ ⟨m₂, g₂, rd₂, wr₂, _⟩ => ?_)
    obtain f₁ : Frame [⟨W + BitVec.ofNat 64 512, 16⟩] s.mem s₁.mem := by
      rw [m₁]; exact writeBytes_frame' _ (List.length_replicate ..)
    obtain f₂ : Frame [⟨W + BitVec.ofNat 64 512, r⟩] s₁.mem s₂.mem := by
      rw [m₂]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
    obtain F₂ : Frame [⟨W + BitVec.ofNat 64 512, 32⟩] s.mem s₂.mem := by
      refine (f₁.sub fun q hq => ?_).trans (f₂.sub fun q hq => ?_) <;>
        simp only [List.mem_singleton] at hq <;> subst hq <;>
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩
    obtain I₂ : FinI Ctx W SP D R r s₂ := finI_keepG h.1 (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;>
        rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)])
      (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) F₂
    exact wLens s₂ I₂
  obtain b₁p := rel_piece [.rdi, .rsi, .rdx, .rcx] (F₁ := FinC) (F₂ := FinC)
      (fun _ h => h.1.env) (fun _ h => h.1.env) (keepsEnv (by decide +kernel)) ⟨_, by taint_decide⟩ wArgs wArgs
      (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2.1, h₂.2.2.1]
        · rw [h₁.2.2.2, h₂.2.2.2])
      (c := .seq copyLoop (.block finLens)) ⟨_, by taint_decide⟩
  obtain b₁ : r ≠ 0 → RelCT isa (fun s₁ s₂ => FinC s₁ ∧ FinC s₂)
      (.seq (.block finTextArgs) (.seq copyLoop (.block finLens)))
      fun s₁ s₂ => FinI Ctx W SP D R r s₁ ∧ FinI Ctx W SP D R r s₂ := fun h0 =>
    rel_next b₁p (wTail h0) (wTail h0)
  obtain prep : RelCT isa (fun s₁ s₂ => (s₁.zf = some (decide (r = 0)) ∧ FinC s₁) ∧
        (s₂.zf = some (decide (r = 0)) ∧ FinC s₂))
      (.ite .e (.block finLens) (.seq (.block finTextArgs) (.seq copyLoop (.block finLens))))
      fun s₁ s₂ => FinI Ctx W SP D R r s₁ ∧ FinI Ctx W SP D R r s₂ := rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    (b₀.mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h)
    (StreamTo.RelCT.of_imp (r ≠ 0) (fun _ _ h => by
        obtain e := h.1.1.1.symm.trans h.2
        simp only [Option.some.injEq, decide_eq_false_iff_not] at e
        exact e) fun h0 => (b₁ h0).mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h)
  -- The keystream, `J₀` incremented, and the test again.
  obtain wKs : ∀ s, FinI Ctx W SP D R r s → WP isa ks s (FinI Ctx W SP D R r) := fun s h =>
    WP.mono (hks s h.env h.rounds hR) fun _ ⟨_, _, f, g, rd, wr, _⟩ => h.keep (fun g' hg => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) rd wr f
  obtain k := rel_next (hkr hR) wKs wKs
  obtain j := rel_next (rel_env_regs [] (F₁ := FinI Ctx W SP D R r) (F₂ := FinI Ctx W SP D R r)
    (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr) (c := .block incJ) ⟨_, by taint_decide⟩)
    incJ_finI incJ_finI
  obtain t₂ := rel_next (rel_env_regs [] (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr)
    (c := .block lenTest) ⟨_, by taint_decide⟩) wTestI wTestI
  -- `GHASH` and the tag.
  obtain e₀ := rel_env_regs [] (F₁ := FinI Ctx W SP D R r) (F₂ := FinI Ctx W SP D R r) (fun _ h => h.env)
    (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr) (c := .block (finGh1 ++ tagK uO)) ⟨_, by taint_decide⟩
  obtain e₁ := rel_env_regs [] (F₁ := FinI Ctx W SP D R r) (F₂ := FinI Ctx W SP D R r) (fun _ h => h.env)
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
  obtain hL : ∀ s, OneS M Ctx W SP R A al D n T s → WP isa (.block [.mov .rcx (.mem (at_ .r15 lenO)),
      .alu .test .rcx (.reg .rcx)]) s fun s₁ => OneS M Ctx W SP R A al D n T s₁ ∧
        s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .rcx = BitVec.ofNat 64 n := fun s h => by
    obtain q₂ := h.env.perm.wR (show 208 + 8 ≤ 2560 by decide)
    obtain ⟨s₁, run₁, hz₁, hcx₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .rcx (.mem (at_ .r15 lenO)),
        .alu .test .rcx (.reg .rcx)] s = some s₁ ∧ s₁.zf = some (decide (n = 0)) ∧
        s₁.gpr .rcx = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
        s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [h.env.r15, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [zf_arithFlags, h.len]; exact congrArg some (and_self_beq (by omega_using [hn]))
      · simp [gpr_setReg, h.len]
      · intro r a; simp [gpr_setReg, a]
      all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
    exact WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hm₁ hrd₁ hwr₁, hz₁, hcx₁⟩
  let F : State → Prop := fun s => OneS M Ctx W SP R A al D n T s ∧ s.gpr .rcx = BitVec.ofNat 64 n
  let K : State → Prop := fun s => OneS M Ctx W SP R A al D n T s ∧ s.gpr .rdi = D ∧
    s.gpr .rsi = W + BitVec.ofNat 64 1040 ∧ s.gpr .rcx = BitVec.ofNat 64 n
  obtain hB : ∀ s, F s → WP isa (.block (([.mov .rdi (.mem (at_ .r15 dataO))] : List Instr) ++
      ptr .rsi .r15 (Impl.AesGcm.X86_64.Short.kO + 16))) s K := fun s ⟨h, hcx⟩ => by
    obtain q₁ := h.env.perm.wR (show 200 + 8 ≤ 2560 by decide)
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
  obtain a := rel_wp (rel_taint (P := OneS₂ M Ctx W SP R A al D n T) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩) (fun _ _ h => h) hL hL
  obtain b := rel_wp (rel_taint (P := fun s₁ s₂ => (True ∧ (OneS M Ctx W SP R A al D n T s₁ ∧
        s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .rcx = BitVec.ofNat 64 n) ∧ (OneS M Ctx W SP R A al D n T s₂ ∧
        s₂.zf = some (decide (n = 0)) ∧ s₂.gpr .rcx = BitVec.ofNat 64 n)) ∧ s₁.zf = some false)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env ⟨h.1.2.1.1, h.1.2.2.1⟩) ⟨_, by taint_decide⟩)
    (F₁ := F) (F₂ := F) (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩) hB hB
  obtain c := rel_taint (P := fun s₁ s₂ => True ∧ K s₁ ∧ K s₂) (c := xorLoop)
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
  obtain hw : ∀ {s₀ : State} {Np : Addr} (C : OneCtx s₀ 5 Ctx W SP Np A D nl al n), (s₀.gpr .rcx).toNat = nl →
      (s₀.gpr .r9).toNat = al → ∀ s, OpenIn s₀ Ctx W SP A D n t s →
      WP isa (Impl.AesGcm.X86_64.Fast.cond any) s fun u => u.zf = some (decide ¬IsFast nl al n any) ∧
        OpenIn s₀ Ctx W SP A D n t u :=
    fun C hnl hal s h => WP.mono (Fast.condE_ok C h.1 hnl hal) fun _ ⟨z, E, K⟩ =>
      ⟨z, E, by rw [K.gpr _ (by decide) (by decide) (by decide), h.2.1], by rw [K.mem]; exact h.2.2⟩
  obtain c := rel_next (Fast.cond_rel (F₁ := OpenIn s₀ Ctx W SP A D n t) (F₂ := OpenIn s₀' Ctx W SP A D n t)
      (fun _ h => condS_of h.1 hnl hal) (fun _ h => condS_of h.1 hnl' hal')
      (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _) (by omega_using [hlt]))
    (hw C hnl hal) (hw C' hnl' hal')
  refine RelCT.seq c (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    ((ho C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' hTr hTr' oT hres hok).mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h) ?_)
  by_cases hs : IsFast nl al n any
  · obtain ⟨h12, h17, -⟩ := hs
    subst h12
    have L := C.lay
    exact (openOkW_rel v B (tagRel_tagP hks hkr) (tagP_ok hF hks) crRel_tailK C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' hTr hTr' oT
      hres hok ((Fast.aad_rel L C.dE (M := (CtxMode.preparedN np hpn)) (R := R) (Np := Np) (A := A) (al := al) (by omega_using [h17])).mono
        (P' := fun (s₁ s₂ : State) => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
        (fun _ _ g => ⟨g.1.1.aadPre C X hNp hnl hal hR, g.2.1.aadPre C' X' hNp' hnl' hal' hR'⟩) fun _ _ _ => trivial)
      (fun _ h => Fast.aad_mid hF C X h.1 hNp hnl hal (by omega_using [h17]))
      (fun _ h => Fast.aad_mid hF C' X' h.1 hNp' hnl' hal' (by omega_using [h17]))).mono
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

end

end

/-! ### `AesGcm.X86_64.Short.VerifiedP`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.Fast.SealSel`, which this module and modules that import it used -/

section

/-!
# AES-GCM `seal`'s path for TLS records

Untrusted: everything here is checked by Lean. With a prepared key context,
`FastSeal.run` is `Short.sealLong` with `Fast.aad`, which leaves what
`oneAad` does (`Fast.aad_mid`) and branches alike in two runs
(`Fast.aad_rel`), and `Short.finishP`, which ends as `Short.finishWith` does
(`Fast.finOk_finishP`), so it leaves what `sealRunW_ok` does
(`Fast.sealRunFin_ok`), and does it in two runs with the same addresses and
branches (`Fast.sealRunP_rel`); so `FastSeal.sel`
does, with `other` for the inputs `Fast.cond` turns away: `sealSel_ok`,
`sealSel_rel`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.FastSeal

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk KsRel SealLongOk SealLongRel rel_next condS_of)
open VG.Proof.AesGcm.X86_64.Fast (IsFast aad_mid condE_ok finOk_finishP sealRunFin_ok sealRunP_rel)

variable {any : Bool}

/-- `sel`: this path for the inputs it takes, `other` for the rest. -/
theorem sealSel_ok (hF : ShortFacts) (v : GcmImpl) (B : BlkFn (CtxMode.preparedN np hpn)) {ks : Prog isa} (hks : KsOk ks)
    {other : Prog isa} (ho : SealLongOk (CtxMode.preparedN np hpn) other) :
    SealLongOk (CtxMode.preparedN np hpn) (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) other ks any) := by
  intro s s₁ Ctx W SP Np A D nl al n C X E hNp hnl hal
  unfold Impl.AesGcm.X86_64.FastSeal.sel
  refine WP.seq (WP.mono (condE_ok C E hnl hal) fun s₃ ⟨hz, E₃, _⟩ => ?_)
  refine WP.ite (decide ¬IsFast nl al n any) (eval_e hz) (fun _ => ho C X E₃ hNp hnl hal) fun h => ?_
  obtain ⟨h12, h17, -⟩ : IsFast nl al n any := Decidable.not_not.mp (of_decide_eq_false h)
  subst h12
  exact sealRunFin_ok B (finOk_finishP hF hks) C X hal (aad_mid hF C X E₃ hNp hnl hal (by omega_using [h17]))

/-- `sel` in two runs: the same path, and on it the same addresses and
branches. -/
theorem sealSel_rel (hF : ShortFacts) (v : GcmImpl) (B : BlkFn (CtxMode.preparedN np hpn)) {ks : Prog isa} (hks : KsOk ks)
    (hkr : KsRel ks) {other : Prog isa} (ho : SealLongRel (CtxMode.preparedN np hpn) other) :
    SealLongRel (CtxMode.preparedN np hpn) (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) other ks any) := by
  intro s₀ s₀' Ctx W SP Np A D nl al n R C C' X X' hNp hnl hal hR hNp' hnl' hal' hR'
  have hlt := C.data.ok.lt
  unfold Impl.AesGcm.X86_64.FastSeal.sel
  have hw : ∀ {s₀ : State} {Np : Addr} (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n), (s₀.gpr .rcx).toNat = nl →
      (s₀.gpr .r9).toNat = al → ∀ s, OneEntry s₀ Ctx W SP A D n s →
      WP isa (Impl.AesGcm.X86_64.Fast.cond any) s fun u => u.zf = some (decide ¬IsFast nl al n any) ∧
        OneEntry s₀ Ctx W SP A D n u :=
    fun C hnl hal s h => WP.mono (condE_ok C h hnl hal) fun _ ⟨z, E, _⟩ => ⟨z, E⟩
  have c := rel_next (Fast.cond_rel (F₁ := OneEntry s₀ Ctx W SP A D n) (F₂ := OneEntry s₀' Ctx W SP A D n)
      (fun _ h => condS_of h hnl hal) (fun _ h => condS_of h hnl' hal')
      (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _) (by omega_using [hlt]))
    (hw C hnl hal) (hw C' hnl' hal')
  refine RelCT.seq c (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    ((ho C C' X X' hNp hnl hal hR hNp' hnl' hal' hR').mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h) ?_)
  by_cases hs : IsFast nl al n any
  · obtain ⟨h12, h17, -⟩ := hs
    subst h12
    have L := C.lay
    exact (sealRunP_rel hks hkr B C C' X X' hNp hnl hal hR hNp' hnl' hal' hR'
      ((Fast.aad_rel L C.dE (M := (CtxMode.preparedN np hpn)) (R := R) (Np := Np) (A := A) (al := al) (by omega_using [h17])).mono
        (P' := fun (s₁ s₂ : State) => OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
        (fun _ _ g => ⟨g.1.aadPre C X hNp hnl hal hR, g.2.aadPre C' X' hNp' hnl' hal' hR'⟩) fun _ _ _ => trivial)
      (fun _ h => aad_mid hF C X h hNp hnl hal (by omega_using [h17]))
      (fun _ h => aad_mid hF C' X' h hNp' hnl' hal' (by omega_using [h17]))).mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h
  · exact RelCT.of_false fun _ _ h => by have := h.1.1.1.symm.trans h.2; simp [hs] at this

end VG.Proof.AesGcm.X86_64.FastSeal

end

end

/-! ### `AesGcm.X86_64.Short.Verified`, which this module and modules that import it used -/

section

/-!
# AES-GCM's short path on x86-64: the functions verified

Untrusted: everything here is checked by Lean. `seal` and `open` with the
short path load no `mxcsr`, never write `rsp` and use as much stack as the
other instances (the short path's code and the end of the long `seal` use none: `cond_xdepth`,
`sealShort_xdepth`, `openShort_xdepth`, `finish_xdepth`), and so they preserve what the ABI
says (`sealM_correct`, `openM_correct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

theorem cond_xdepth : Impl.AesGcm.X86_64.Short.cond.x86_64Depth = 0 := by decide +kernel
theorem sealShort_xdepth : Impl.AesGcm.X86_64.Short.sealShort.x86_64Depth = 0 := by decide +kernel
theorem openShort_xdepth : Impl.AesGcm.X86_64.Short.openShort.x86_64Depth = 0 := by decide +kernel
theorem finish_xdepth : Impl.AesGcm.X86_64.Short.finish.x86_64Depth = 0 := by decide +kernel

variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M)

theorem sealM_mx : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealM_spSafe : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealM_xdepth : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, cond_xdepth, sealShort_xdepth, finish_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [e]

theorem sealM_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.sealX86_64M M).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealM_wp hF v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealM_mx v B) he hg, hp⟩

theorem openM_mx : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openM_spSafe : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openM_xdepth : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, cond_xdepth, openShort_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte,
    Bool.false_eq_true]
  omega_using [d]

theorem openM_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.openX86_64M M).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := openM_wp hF v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (openM_mx v B) he hg, hp⟩

end VG.Proof.AesGcm.X86_64.Short

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

namespace GcmImpl

/-- `vg_aes_gcm_seal`'s code calling `c`, with the short path if `v` has it,
or else ending without calls if `v` does. -/
def sealCode (v : GcmImpl) (c : Callees) : Prog isa :=
  if v.short then Impl.AesGcm.X86_64.Short.«seal» c
  else if v.fin then Impl.AesGcm.X86_64.SealFin.«seal» c else «seal» c

/-- `vg_aes_gcm_open`'s code calling `c`, with the short path if `v` has it. -/
def openCode (v : GcmImpl) (c : Callees) : Prog isa :=
  if v.short then Impl.AesGcm.X86_64.Short.«open» c else «open» c

end GcmImpl

variable (v : GcmImpl)

theorem sealCode_spSafe {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCode (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.sealCode; split
  · exact Short.sealM_spSafe v B
  · split
    · exact SealFin.sealFM_spSafe v B
    · exact sealM_spSafe v B

theorem openCode_spSafe {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.openCode (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.openCode; split
  · exact Short.openM_spSafe v B
  · exact openM_spSafe v B

/-- `vg_aes_gcm_seal`, with the short path if `v` has it, or ending without
calls if `v` does. -/
theorem sealSel_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode v.callees))
      (Proof.AesGcm.sealRoundsContract X86_64.abi 2624) := by
  unfold GcmImpl.sealCode; split
  · exact sealCode_framed (sealCode_verified (fun s hs => Short.sealM_correct v v.blkB hF s ⟨hs, trivial⟩)
      (ct_of_rel fun _ _ hp hp' hq => Short.sealM_rel hF v v.blkB ⟨hp, trivial⟩ ⟨hp', trivial⟩ hq))
      (Short.sealM_spSafe v v.blkB) (Short.sealM_xdepth v v.blkB)
  · split
    · exact sealCode_framed (sealCode_verified (fun s hs => SealFin.sealFM_correct v v.blkB hF s ⟨hs, trivial⟩)
        (ct_of_rel fun _ _ hp hp' hq => SealFin.sealFMW_rel v v.blkB (SealFin.sealLongOk_mid v v.blkB hF)
          (SealFin.sealLongRel_mid v v.blkB hF) ⟨hp, trivial⟩ ⟨hp', trivial⟩ hq))
        (SealFin.sealFM_spSafe v v.blkB) (SealFin.sealFM_xdepth v v.blkB)
    · exact seal_framed v

/-- `vg_aes_gcm_open`, with the short path if `v` has it. -/
theorem openSel_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode v.callees))
      (Proof.AesGcm.openRoundsContract X86_64.abi 2632) := by
  unfold GcmImpl.openCode; split
  · exact openCode_framed (openCode_verified (fun s hs => Short.openM_correct v v.blkB hF s ⟨hs, trivial⟩)
      (ct_of_rel fun _ _ hp hp' hq => Short.openM_rel hF v v.blkB ⟨hp, trivial⟩ ⟨hp', trivial⟩ hq))
      (Short.openM_spSafe v v.blkB) (Short.openM_xdepth v v.blkB)
  · exact open_framed v

/-- `vg_aes_gcm_seal_precomputed`, with the short path if `v` has it. -/
theorem sealSelP_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode (v.withBlk v.blkP)))
      (Proof.AesGcm.sealPrecomputedRoundsContract X86_64.abi 2624) := by
  unfold GcmImpl.sealCode; split
  · exact sealPCode_framed (sealPCode_verified (Short.sealM_correct v v.blkP hF) (Short.sealM_ct hF v v.blkP))
      (Short.sealM_spSafe v v.blkP) (Short.sealM_xdepth v v.blkP)
  · split
    · exact sealPCode_framed (sealPCode_verified (SealFin.sealFM_correct v v.blkP hF) (SealFin.sealFM_ct v v.blkP hF))
        (SealFin.sealFM_spSafe v v.blkP) (SealFin.sealFM_xdepth v v.blkP)
    · exact sealP_framed v

/-- `vg_aes_gcm_open_precomputed`, with the short path if `v` has it. -/
theorem openSelP_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCode (v.withBlk v.blkP)))
      (Proof.AesGcm.openPrecomputedRoundsContract X86_64.abi 2632) := by
  unfold GcmImpl.openCode; split
  · exact openPCode_framed (openPCode_verified (Short.openM_correct v v.blkP hF) (Short.openM_ct hF v v.blkP))
      (Short.openM_spSafe v v.blkP) (Short.openM_xdepth v v.blkP)
  · exact openP_framed v

end VG.Proof.AesGcm.X86_64

end

end

/-! ### `AesGcm.X86_64.Fast.OpenSel`, which only this module used -/

section

/-!
# AES-GCM `open`'s path for TLS records: after the entry

Untrusted: everything here is checked by Lean. With a prepared key context,
`FastOpen.run` is `Short.openLong` with `Fast.aad`, which leaves what
`oneAad` does (`Fast.aad_mid`), `tagP`, which leaves what `oneTag 112` does
and `K[1]` (`tagP_okP`), and `tailK`, which decrypts the bytes left with it
(`crOk_tailK`), so it leaves what `openOk_ok` does (`openOkW_ok`), and
`FastOpen.sel` too, with `other` for the inputs `Fast.cond` turns away:
`openSel_ok`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.FastOpen

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk LongOk)
open VG.Proof.AesGcm.X86_64.Fast (IsFast aad_mid condE_ok)

variable {any : Bool}

theorem tagP_mx : (Impl.AesGcm.X86_64.FastOpen.tagP : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel
theorem tagPA_mx :
    (Impl.AesGcm.X86_64.FastOpen.tagP Impl.AesGcm.X86_64.Short.finKsA : Prog isa).allInstrs (fun i => !loadsMxcsr i) =
      true := by
  decide +kernel
theorem tagPA_spSafe :
    (Impl.AesGcm.X86_64.FastOpen.tagP Impl.AesGcm.X86_64.Short.finKsA : Prog isa).all
      (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem tagPA_xdepth : (Impl.AesGcm.X86_64.FastOpen.tagP Impl.AesGcm.X86_64.Short.finKsA : Prog isa).x86_64Depth = 0 := by
  decide +kernel
theorem tagP_spSafe : (Impl.AesGcm.X86_64.FastOpen.tagP : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem tagP_xdepth : (Impl.AesGcm.X86_64.FastOpen.tagP : Prog isa).x86_64Depth = 0 := by decide +kernel

/-- `sel`: this path for the inputs it takes, `other` for the rest. -/
theorem openSel_ok (hF : ShortFacts) (v : GcmImpl) (B : BlkFn (CtxMode.preparedN np hpn)) {ks : Prog isa} (hks : KsOk ks)
    {other : Prog isa} (ho : LongOk (CtxMode.preparedN np hpn) other) :
    LongOk (CtxMode.preparedN np hpn) (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) other ks any) := by
  intro s s₂ Ctx W SP Np A D T nl al n t C X E hNp hnl hal hTa hTar hTr oT oA htl hok
  unfold Impl.AesGcm.X86_64.FastOpen.sel
  refine WP.seq (WP.mono (condE_ok C E hnl hal) fun s₃ ⟨hz, E₃, K⟩ => ?_)
  rw [← K.mem] at htl
  refine WP.ite (decide ¬IsFast nl al n any) (eval_e hz) (fun _ => ho C X E₃ hNp hnl hal hTa hTar hTr oT oA htl hok)
    fun h => ?_
  obtain ⟨h12, h17, -⟩ : IsFast nl al n any := Decidable.not_not.mp (of_decide_eq_false h)
  subst h12
  exact openOkW_ok v B (tagP_okP hF hks) pStable_kOk crOk_tailK C X hal hTa hTar hTr oT oA htl hok
    (aad_mid hF C X E₃ hNp hnl hal (by omega_using [h17]))

/-- `openFin lng`, for `lng` that leaves what `openOk_ok` does. -/
theorem openFinW_wp {M : CtxMode} {lng : Prog isa} (hlng : LongOk M lng) {s : State}
    (hp : (Proof.AesGcm.openX86_64M M).pre s) :
    WP isa (Impl.AesGcm.X86_64.FastOpen.openFin lng) s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' :=
  openM_of hp fun C X E hNp hnl hal _ hTa hTar hTr oT oA htl hok => hlng C X E hNp hnl hal hTa hTar hTr oT oA htl hok

end VG.Proof.AesGcm.X86_64.FastOpen

end

end


/-!
# AES-GCM's short path on x86-64 with a prepared key context: the functions verified

Untrusted: everything here is checked by Lean. With a prepared key context,
`seal` and `open` take their powers from it (`Short.powersP`, `Short.ghashP`):
`sealMP_correct`, `openMP_correct`, as `sealM_correct` and `openM_correct`
for `powers`, and the code of the instances with the short path
(`GcmImpl.sealCodeP`, `GcmImpl.openCodeP`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

theorem sealShortP_xdepth :
    (Impl.AesGcm.X86_64.Short.sealShort Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP).x86_64Depth = 0 := by decide +kernel
theorem finishK_xdepth : (Impl.AesGcm.X86_64.Short.finishWith Impl.AesGcm.X86_64.Short.finKs).x86_64Depth = 0 :=
  finish_xdepth
theorem finishPK_xdepth : (Impl.AesGcm.X86_64.Short.finishP Impl.AesGcm.X86_64.Short.finKs).x86_64Depth = 0 := by
  decide +kernel
theorem finishPA_xdepth : (Impl.AesGcm.X86_64.Short.finishP Impl.AesGcm.X86_64.Short.finKsA).x86_64Depth = 0 := by
  decide +kernel

theorem openShortP_xdepth :
    (Impl.AesGcm.X86_64.Short.openShort Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP).x86_64Depth = 0 := by decide +kernel

variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M)

theorem sealMP_mx : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)))).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_mx, Fast.fastAad_mx, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealMP_spSafe : (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)))).all
    (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_spSafe, Fast.fastAad_spSafe, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealMP_xdepth :
    (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)))).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.Short.«seal», Impl.AesGcm.X86_64.Short.sealLong, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_xdepth, Fast.fastAad_xdepth, cond_xdepth, sealShortP_xdepth, finish_xdepth, finishK_xdepth, finishPK_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [e]

theorem openMP_mx : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))) Impl.AesGcm.X86_64.Short.ghashP).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_mx, Fast.fastAad_mx, FastOpen.tagP_mx, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openMP_spSafe : (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))) Impl.AesGcm.X86_64.Short.ghashP).all
    (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_spSafe, Fast.fastAad_spSafe, FastOpen.tagP_spSafe, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openMP_xdepth :
    (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))) Impl.AesGcm.X86_64.Short.ghashP).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.Short.«open», Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Impl.AesGcm.X86_64.FastOpen.tailK, Fast.fastCond_xdepth,
    Fast.fastAad_xdepth, FastOpen.tagP_xdepth, cond_xdepth, openShortP_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte,
    Bool.false_eq_true]
  omega_using [d]

theorem sealFinP_mx : (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.SealFin.mid (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.SealFin.«seal», Impl.AesGcm.X86_64.SealFin.mid, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_mx, Fast.fastAad_mx, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealFinP_spSafe : (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.SealFin.mid (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).all
    (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.SealFin.«seal», Impl.AesGcm.X86_64.SealFin.mid, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_spSafe, Fast.fastAad_spSafe, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealFinP_xdepth : (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.SealFin.mid (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.SealFin.«seal», Impl.AesGcm.X86_64.SealFin.mid, Impl.AesGcm.X86_64.FastSeal.sel, Impl.AesGcm.X86_64.FastSeal.run, Fast.fastCond_xdepth, Fast.fastAad_xdepth, SealFin.finishA_xdepth, finishPA_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [e]

theorem openFinP_mx : (Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, Impl.AesGcm.X86_64.FastOpen.openFin, Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_mx, Fast.fastAad_mx, FastOpen.tagPA_mx, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openFinP_spSafe : (Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).all
    (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, Impl.AesGcm.X86_64.FastOpen.openFin, Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Fast.fastCond_spSafe, Fast.fastAad_spSafe, FastOpen.tagPA_spSafe, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all,
    GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem openFinP_xdepth : (Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B)) Impl.AesGcm.X86_64.Short.finKsA true)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [Impl.AesGcm.X86_64.FastOpen.openFin, Impl.AesGcm.X86_64.Short.openLong, Impl.AesGcm.X86_64.FastOpen.sel, Impl.AesGcm.X86_64.FastOpen.run, Impl.AesGcm.X86_64.FastOpen.tailK, Fast.fastCond_xdepth, Fast.fastAad_xdepth, FastOpen.tagPA_xdepth, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, tagLenOk, recv, Impl.AesGcm.X86_64.cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState,
    Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [d]

section
variable (B : BlkFn CtxMode.prepared)

theorem sealMP_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.sealX86_64M CtxMode.prepared).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)))) s t s' ∧
      abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealMW_wp hF v B powOk_powersP
    (FastSeal.sealSel_ok hF v B finKs_ksOk (sealLongOk_sealLong hF v B)) hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealMP_mx v B) he hg, hp⟩

theorem openMP_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.openX86_64M CtxMode.prepared).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))) Impl.AesGcm.X86_64.Short.ghashP) s t s' ∧
      abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := openMW_wp hF v B powOk_powersP
    (FastOpen.openSel_ok hF v B finKs_ksOk (longOk_openLong v B)) hs
  exact ⟨t, s', he, abiPreserved_of_exec (openMP_mx v B) he hg, hp⟩

end

section
variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24} (B : BlkFn (CtxMode.preparedN np hpn))

theorem sealFinP_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.sealX86_64M (CtxMode.preparedN np hpn)).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.SealFin.«seal» (v.withBlk B)
      (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) (Impl.AesGcm.X86_64.SealFin.mid (v.withBlk B))
        Impl.AesGcm.X86_64.Short.finKsA true)) s t s' ∧
      abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := SealFin.sealFMW_wp v B
    (FastSeal.sealSel_ok hF v B finKsA_ksOk (SealFin.sealLongOk_mid v B hF)) hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealFinP_mx v B) he hg, hp⟩

theorem openFinP_correct (hF : ShortFacts) (s : State) (hs : (Proof.AesGcm.openX86_64M (CtxMode.preparedN np hpn)).pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B))
        Impl.AesGcm.X86_64.Short.finKsA true)) s t s' ∧
      abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := FastOpen.openFinW_wp (FastOpen.openSel_ok hF v B finKsA_ksOk (longOk_openLong v B)) hs
  exact ⟨t, s', he, abiPreserved_of_exec (openFinP_mx v B) he hg, hp⟩

end

end VG.Proof.AesGcm.X86_64.Short

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

namespace GcmImpl

/-- `vg_aes_gcm_seal_prepared`'s code calling `c`: `sealCode`, with the short
path's table of powers from the prepared key context, and the path for TLS
records (`FastSeal.sel`) when the short path does not apply, or, ending
without calls, before `SealFin.mid`, at every length (`any`), since there
it is faster than `SealFin.mid` at every length. -/
def sealCodeP (v : GcmImpl) (c : Callees) : Prog isa :=
  if v.short then
    Impl.AesGcm.X86_64.Short.«seal» c Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel c (Impl.AesGcm.X86_64.Short.sealLong c))
  else if v.fin then
    Impl.AesGcm.X86_64.SealFin.«seal» c
      (Impl.AesGcm.X86_64.FastSeal.sel c (Impl.AesGcm.X86_64.SealFin.mid c) Impl.AesGcm.X86_64.Short.finKsA true)
  else «seal» c

/-- `vg_aes_gcm_open_prepared`'s code calling `c`: `openCode`, with the short
path's table of powers from the prepared key context, and the path for TLS
records (`FastOpen.sel`) when the short path does not apply; without the
short path, at every length (`any`), since it is faster there than the other
instances' body at every length. -/
def openCodeP (v : GcmImpl) (c : Callees) : Prog isa :=
  if v.short then
    Impl.AesGcm.X86_64.Short.«open» c Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel c (Impl.AesGcm.X86_64.Short.openLong c)) Impl.AesGcm.X86_64.Short.ghashP
  else
    Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel c (Impl.AesGcm.X86_64.Short.openLong c) Impl.AesGcm.X86_64.Short.finKsA true)

end GcmImpl

variable (v : GcmImpl)

theorem sealCodeP_spSafe {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCodeP (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.sealCodeP; split
  · exact Short.sealMP_spSafe v B
  · split
    · exact Short.sealFinP_spSafe v B
    · exact sealM_spSafe v B

theorem openCodeP_spSafe {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.openCodeP (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.openCodeP; split
  · exact Short.openMP_spSafe v B
  · exact Short.openFinP_spSafe v B

end VG.Proof.AesGcm.X86_64

end

end

/-! # Prepared contexts: the short path with the context's powers

`vg_aes_gcm_seal_prepared` and `vg_aes_gcm_open_prepared` take the short
path with its table of powers copied from the prepared key context
(`GcmImpl.sealCodeP`, `GcmImpl.openCodeP`), and otherwise the code of the
other instances, which `seal` and `open` replace for TLS records with
`FastSeal.sel` and `FastOpen.sel`. -/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
variable (v : GcmImpl) (B : BlkFn CtxMode.prepared)

theorem sealSelPrepared_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCodeP (v.withBlk B)))
      (Proof.AesGcm.sealPreparedRoundsContract X86_64.abi 2624) := by
  unfold GcmImpl.sealCodeP; split
  · exact sealPreparedCode_framed (sealPreparedCode_verified (Short.sealMP_correct v B hF)
      (Short.sealMW_ct hF v B Short.powOk_powersP Short.powersP_ct
        (FastSeal.sealSel_ok hF v B Short.finKs_ksOk (Short.sealLongOk_sealLong hF v B))
        (FastSeal.sealSel_rel hF v B Short.finKs_ksOk Short.finKs_rel (Short.sealLongRel_sealLong hF v B)))) (Short.sealMP_spSafe v B)
      (Short.sealMP_xdepth v B)
  · split
    · exact sealPreparedCode_framed (sealPreparedCode_verified (Short.sealFinP_correct v B hF)
        (SealFin.sealFMW_ct v B (FastSeal.sealSel_ok hF v B Short.finKsA_ksOk (SealFin.sealLongOk_mid v B hF))
          (FastSeal.sealSel_rel hF v B Short.finKsA_ksOk Short.finKsA_rel (SealFin.sealLongRel_mid v B hF))))
        (Short.sealFinP_spSafe v B) (Short.sealFinP_xdepth v B)
    · exact sealPrepared_framed v B

/-- `vg_aes_gcm_open_prepared`, with the short path if `v` has it. -/
theorem openSelPrepared_framed (hF : Short.ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 (v.openCodeP (v.withBlk B)))
      (Proof.AesGcm.openPreparedRoundsContract X86_64.abi 2632) := by
  unfold GcmImpl.openCodeP; split
  · exact openPreparedCode_framed (openPreparedCode_verified (Short.openMP_correct v B hF)
      (Short.openMW_ct hF v B Short.powOk_powersP Short.powersP_ct
        (FastOpen.openSel_rel hF v B Short.finKs_ksOk Short.finKs_rel (Short.longRel_openLong v B)))) (Short.openMP_spSafe v B)
      (Short.openMP_xdepth v B)
  · exact openPreparedCode_framed (openPreparedCode_verified (Short.openFinP_correct v B hF)
      (FastOpen.openFinW_ct (FastOpen.openSel_rel hF v B Short.finKsA_ksOk Short.finKsA_rel
        (Short.longRel_openLong v B)))) (Short.openFinP_spSafe v B) (Short.openFinP_xdepth v B)

end VG.Proof.AesGcm.X86_64
