module

public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Run
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.PrefixCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptCT
import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
import VerifiedGarbage.Proof.AesGcm.X86_64.OneCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CryptCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.Run
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenSplit.PrefixCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesGcm.X86_64
meta import VerifiedGarbage.Impl.AesGcm.X86_64.OpenSplit
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State

/-!
# AES-GCM `open_split` on x86-64: constant time

Untrusted: everything here is checked by Lean. As `open` (`OpenCT.lean`):
the first branch is on the tag length (public); then both runs go through
`oneAad` (`oneAad_rel`), `seal_split`'s `prefix` with the call of
`vg_aes_gcm_decrypt_blocks_to` (`prefixD_ct`), the tag length kept (the
taint analysis), `oneTag` and the comparison as `open` does. The second
branch is on the comparison, which `open_split` may leak: correctness says it
is whether `openResult` succeeds (`frontS_ok`, `osK_eq`), the same in both
runs by `pub`; then both runs decrypt the bytes left (`oneCrypt`) or not.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.OpenSplit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64.Split (PP)
open VG.Proof.AesGcm.X86_64.StreamTo (skip_rel)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashFrom ghash blocks ofBytes toBytes inc32)
open VG.Proof.Gcm (xorKs lensBlock padded)

/-- What `open_split`'s entry leaves, for a tag length `t`, after its check. -/
abbrev OpenInS (s₀ : State) (Ctx W SP A D S : Addr) (n t : Nat) (s : State) : Prop :=
  OneEntry s₀ Ctx W SP A D n s ∧ s.gpr .rbx = BitVec.ofNat 64 t ∧
    s.mem.readW (W + BitVec.ofNat 64 224) 64 = S ∧ s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n

/-- The tag length, in the argument at `[SP + 32]`, which may be read. -/
abbrev ArgL (SP : Addr) (t : Nat) (s : State) : Prop :=
  s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t ∧
    InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 32) 8

/-- `osK`, by `openResult`, for a tag length it allows. -/
theorem osK_eq {s₀ : State} {Ctx Np A S Tp : Addr} {nl al n t R : Nat} (hok : Spec.Gcm.tagLenOk t = true) :
    osK s₀ Ctx Np A S Tp nl al n t R = if (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) t
      (bytesAt s₀.mem Np nl) (bytesAt s₀.mem S n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tp t)).isSome then 1 else 0 := by
  simp only [osK, Spec.Gcm.openResult, hok, ↓reduceIte, Spec.Gcm.decryptWith, Proof.Gcm.fullTag_eq, length_bytesAt]
  split <;> simp

/-- A stack argument between `[SP + 8]` and `[SP + 48]` is apart from `W`,
the data and the 56 bytes below `SP`. -/
theorem argD {s : State} {Ctx W SP Np A D : Addr} {nl al n : Nat} (C : OneCtx s 7 Ctx W SP Np A D nl al n)
    {e : Nat} (h₁ : 8 ≤ e) (h₂ : e + 8 ≤ 56) {r : Region}
    (hr : r.Sub ⟨W, 2560⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub (below SP 56)) :
    (⟨SP + BitVec.ofNat 64 e, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨SP + BitVec.ofNat 64 e, 8⟩ ⟨SP + BitVec.ofNat 64 8, 8 * 7⟩ := by
    rw [show e = 8 + (e - 8) by omega_arith, ← add_ofNat_assoc]; exact Offset.sub_base _ (by omega_arith)
  rcases hr with hr | hr | hr
  · exact (C.dA.sub_left hs).sub_right hr
  · exact (C.dAD.sub_left hs).sub_right hr
  · exact (Offset.disjoint_below SP (n := 56) (d := e) (k := 8) (by omega_arith)).sub_right hr

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
  {M : CtxMode} (B : BlkFn M) (T : BlkToDecFn M)
include L

/-- `OneS`, after code that writes only the tag length's slot. -/
theorem OneS.keep224 {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {Tn : Option Nat} {s s' : State}
    (h : OneS M Ctx W SP R A al D n Tn s) (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s'.mem) :
    OneS M Ctx W SP R A al D n Tn s' := by
  have kp : ∀ d, d + 8 ≤ 224 ∨ 232 ≤ d → d + 8 ≤ 2560 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d hd hd' =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega_arith) hd' (by decide)) (by decide)
  exact ⟨h.env.keep hg hrd hwr, ⟨by rw [kp 176 (.inl (by decide)) (by decide)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [kp 232 (.inr (by decide)) (by decide)]; exact h.aad, by rw [kp 184 (.inl (by decide)) (by decide)]; exact h.alen,
    by rw [kp 200 (.inl (by decide)) (by decide)]; exact h.dat, by rw [kp 208 (.inl (by decide)) (by decide)]; exact h.len,
    h.dA.of_eq hrd hwr, h.dD.of_eq hrd hwr, fun N hN => by rw [kp 192 (.inl (by decide)) (by decide)]; exact h.tlen N hN,
    h.ext.keep hrd hwr hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.ext.cw.sub_right (Lay.wSub (by decide)))⟩

/-- `J₀` and the additional data, in each run: `OneS`, what `prefix` needs,
and the arguments it keeps. -/
theorem aadS_ok {s₀ s : State} {Np A D S Tp : Addr} {nl al n t R : Nat}
    (C : OSCtx s₀ M.len Ctx W SP Np A D S Tp nl al n t) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R) (hT : ArgT SP Tp s₀) (htl : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t)
    (h : OpenInS s₀ Ctx W SP A D S n t s) :
    WP isa (oneAad (v.withBlk B)) s fun s' => (OneS M Ctx W SP R A al D n none s' ∧ PP M Ctx W SP D S R n n s') ∧
      ArgR SP Tp s' ∧ ArgL SP t s' := by
  refine WP.mono (oneMid_ok v C.toOneCtx h.1 hNp hnl hal) fun s₃ M₃ => ?_
  have b8 : Region.Sub (below SP 8) (below SP 56) := below_sub (by decide) (by decide)
  have dM : ∀ {Y : Region}, Y.Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint Y →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], Y.Disjoint r := by
    intro Y h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have f₃ : Frame (oneFrame W D SP n) s.mem s₃.mem := wFrame_one (o := 0) (.inl rfl) (wFrame_cons M₃.fr)
  have k₃ : ∀ d, d = 192 ∨ d = 224 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    f₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrame L C.dE (by rcases hd with rfl | rfl <;> decide)) (by decide)
  have kA : ∀ {e : Nat}, 8 ≤ e → e + 8 ≤ 56 →
      s₃.mem.readW (SP + BitVec.ofNat 64 e) 64 = s₀.mem.readW (SP + BitVec.ofNat 64 e) 64 := fun h₁ h₂ =>
    M₃.frame.readW (Region.contains_self _ _) (dM (argD C.toOneCtx h₁ h₂ (.inl fun _ h => h))
      ((argD C.toOneCtx h₁ h₂ (.inr (.inr b8))).symm)) (by decide)
  refine ⟨⟨(h.1.aadPre C.toOneCtx X hNp hnl hal hR).1.frame L M₃.env (M₃.rd.trans h.1.rd.symm)
      (M₃.wr.trans h.1.wr.symm) C.dE f₃,
    ⟨M₃.env, L, hR ▸ M₃.rounds, M₃.dat, M₃.len, by rw [k₃ 224 (.inr rfl)]; exact h.2.2.1,
      by rw [k₃ 192 (.inl rfl)]; exact h.2.2.2, C.data.of_eq M₃.rd M₃.wr, by rw [M₃.rd, M₃.wr]; exact C.src,
      C.sW, C.sD, C.sWrap, Nat.le_refl _, C.kw, C.kd, C.ks, C.kM, C.sp56,
      X.keep M₃.rd M₃.wr M₃.frame (dM X.cw (X.ct.sub_left (below_sub (by decide) (by decide))))⟩⟩,
    ⟨by rw [ArgT, kA (e := 24) (by decide) (by decide)]; exact hT, by rw [M₃.rd, M₃.wr]; exact C.args 2 (by decide)⟩,
    ⟨by rw [kA (e := 32) (by decide) (by decide)]; exact htl, by rw [M₃.rd, M₃.wr]; exact C.args 3 (by decide)⟩⟩

/-- What stays between the pieces after `prefix`, in each run: `OneT` for the
bytes left at `src`, and the arguments kept. -/
abbrev GB (Ctx W SP : Addr) (R al : Nat) (S : Addr) (n t : Nat) (Tp : Addr) (s : State) : Prop :=
  OneT Ctx W SP R al (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) n s ∧ ArgR SP Tp s ∧ ArgL SP t s

/-- After `prefix`, in each run: `OneT` for the bytes left at `src`, with the
total length, and the arguments it keeps. -/
theorem prefixS_ok {σ : State} {Np A D S Tp : Addr} {s₀ : State} {nl al n t R : Nat}
    (C : OSCtx s₀ M.len Ctx W SP Np A D S Tp nl al n t)
    (h : (OneS M Ctx W SP R A al D n none σ ∧ PP M Ctx W SP D S R n n σ) ∧ ArgR SP Tp σ ∧ ArgL SP t σ) :
    WP isa (OpenSplit.prefix T.fn) σ (GB Ctx W SP R al S n t Tp) := by
  obtain ⟨⟨O, P⟩, ⟨hT, hTr⟩, ⟨hl, hlr⟩⟩ := h
  have hq : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hn := P.data.ok.lt
  have b8 : Region.Sub (below SP 8) (below SP 56) := below_sub (by decide) (by decide)
  refine WP.mono (prefixD_ok P T) fun s Q => ?_
  have F : Frame (Split.ppListG W D SP n) σ.mem s.mem := Q.frame.sub fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨W + BitVec.ofNat 64 200, 24⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 200) ∨ (224 ≤ d ∧ d + 8 ≤ 448) →
      s.mem.readW (W + BitVec.ofNat 64 d) 64 = σ.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    F.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (Split.pp_wG L P.data.ok.w P.kw (.inr hd)) (by decide)
  have argPP : ∀ {e : Nat}, 8 ≤ e → e + 8 ≤ 56 → ∀ r ∈ Split.ppListG W D SP n,
      (⟨SP + BitVec.ofNat 64 e, 8⟩ : Region).Disjoint r := by
    intro e h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact argD C.toOneCtx h₁ h₂ (.inl (fun a hc => Split.st_w a (Split.cb_sub a hc)))
    · exact argD C.toOneCtx h₁ h₂ (.inl (fun a hc => Split.st_w a (Split.y_sub a hc)))
    · exact argD C.toOneCtx h₁ h₂ (.inr (.inl fun _ h => h))
    · exact argD C.toOneCtx h₁ h₂ (.inl Split.sc_w)
    · exact argD C.toOneCtx h₁ h₂ (.inl (Lay.wSub (by decide)))
    · exact argD C.toOneCtx h₁ h₂ (.inr (.inr fun _ h => h))
  have hS : DataOk (W + BitVec.ofNat 64 16) W SP s S n :=
    ⟨by rw [Q.rd, Q.wr]; exact P.srcCov, hn, P.sWrap, P.sW.sub_right (Lay.wSub (by decide)), P.sW, P.ks.sub_left b8⟩
  refine ⟨⟨Q.env, ⟨by rw [kp 176 (.inl ⟨by decide, by decide⟩)]; exact O.rounds.1, O.rounds.2⟩,
    by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact O.alen, Q.dat, by rw [Q.len]; congr 1; omega_arith,
    hS.drop hq, by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact P.slen⟩,
    ⟨by rw [ArgT, F.readW (Region.contains_self _ _) (argPP (e := 24) (by decide) (by decide)) (by decide)]; exact hT,
      by rw [Q.rd, Q.wr]; exact hTr⟩,
    ⟨by rw [F.readW (Region.contains_self _ _) (argPP (e := 32) (by decide) (by decide)) (by decide)]; exact hl,
      by rw [Q.rd, Q.wr]; exact hlr⟩⟩

/-- `OneT`, after code that writes only the tag length's slot. -/
theorem OneT.keep224 {R al : Nat} {D : Addr} {n N : Nat} {s s' : State}
    (h : OneT Ctx W SP R al D n N s) (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s'.mem) :
    OneT Ctx W SP R al D n N s' := by
  have kp : ∀ d, d + 8 ≤ 224 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl hd) (by omega_arith) (by decide)) (by decide)
  exact ⟨h.env.keep hg hrd hwr, ⟨by rw [kp 176 (by decide)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [kp 184 (by decide)]; exact h.alen, by rw [kp 200 (by decide)]; exact h.dat,
    by rw [kp 208 (by decide)]; exact h.len, h.dD.of_eq hrd hwr, by rw [kp 192 (by decide)]; exact h.tlen⟩

/-- What stays after the tag length is kept at `tlO`, in each run. -/
abbrev GC (Ctx W SP : Addr) (R al : Nat) (S : Addr) (n t : Nat) (Tp : Addr) (s : State) : Prop :=
  OneT Ctx W SP R al (S + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) n s ∧
    s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s

/-- The tag length kept at `tlO`, in each run. -/
theorem tagLenS_ok {R al : Nat} {S : Addr} {n t : Nat} {Tp : Addr} {s : State}
    (oA : OutWS W SP ⟨SP + BitVec.ofNat 64 24, 8⟩) (h : GB Ctx W SP R al S n t Tp s) :
    WP isa (.block OpenSplit.tagLen) s (GC Ctx W SP R al S n t Tp) := by
  have w₁ := h.1.env.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hg, hm, hrd, hwr⟩ : ∃ s₁, runBlock isa OpenSplit.tagLen s = some s₁ ∧
      (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 224) (BitVec.ofNat 64 t) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by simp only [OpenSplit.tagLen]; xrun [h.1.env.rsp, h.1.env.r15, h.2.2.2, w₁, h.2.2.1], ?_, ?_, ?_, ?_⟩
    · intro r a; simp [gpr_setReg, a]
    · simp [mem_setReg, gpr_setReg, h.2.2.1]
    all_goals rfl
  have f₁ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s.mem s₁.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (by simp) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨s₁, run₁, OneT.keep224 L h.1 (fun r hr => hg r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd hwr f₁, by rw [hm, Mem.readW_writeW_self64], ?_, ?_⟩
  · have hd : (⟨SP + BitVec.ofNat 64 24, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 224, 8⟩ :=
      oA _ (.inl (Lay.wSub (by decide)))
    rw [ArgT, f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)]; exact h.2.1.1
  · rw [hrd, hwr]; exact h.2.1.2

/-- `oneTag` keeps `GC`, in each run. -/
theorem tagS_ok {R al : Nat} {S : Addr} {n t : Nat} {Tp : Addr} {s : State} (hn : n < 2 ^ 64)
    (hSW : (⟨S + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ : Region).Disjoint ⟨W, 2560⟩)
    (oA : OutWS W SP ⟨SP + BitVec.ofNat 64 24, 8⟩) (h : GC Ctx W SP R al S n t Tp s) :
    WP isa (oneTag v.callees uO) s (GC Ctx W SP R al S n t Tp) :=
  WP.mono (oneTag_ok v L (o := 112) (.inr rfl) (x := []) (by decide) h.1.env rfl h.1.rounds h.1.dat h.1.len h.1.tlen
    hn h.1.alen h.1.dD hSW) fun _ ⟨he, f, hrd, hwr, _⟩ => by
    have f' := wFrame_one (D := S + BitVec.ofNat 64 (16 * (n / 16))) (n := n - 16 * (n / 16)) (.inr rfl) f
    exact ⟨h.1.frame L he hrd hwr hSW f', by
      rw [f'.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _)
        (kept_oneFrame L hSW (.inr ⟨by decide, by decide⟩)) (by decide), h.2.1], by
      rw [ArgT, f.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _)
        (oA.tagFrame (o := 112) (by decide)) (by decide), h.2.2.1], by rw [hrd, hwr]; exact h.2.2.2⟩

omit L in
/-- The tag length loaded into `rbx`, and the address of the received tag into `rsi`. -/
theorem loadTlS_ok {R al : Nat} {S : Addr} {n t : Nat} {Tp : Addr} {s : State} (h : GC Ctx W SP R al S n t Tp s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) s fun s' =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.gpr .rsi = Tp := by
  have r₁ := h.1.env.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have r₂ := h.2.2.2
  obtain ⟨s₁, run₁, hbx, hsi, hg, hm, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 24))] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t ∧ s₁.gpr .rsi = Tp ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.env.r15, h.1.env.rsp, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.2.1]
    · simp [gpr_setReg, h.2.2.1]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.1.env.keep (fun r hr => ?_) hrd hwr, hbx, hsi⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

/-- From the entry to the comparison, in two runs, for an allowed tag length. -/
theorem frontS_rel {s₀ s₀' : State} {Np A D S Tp : Addr} {nl al n t R : Nat}
    (C : OSCtx s₀ M.len Ctx W SP Np A D S Tp nl al n t) (C' : OSCtx s₀' M.len Ctx W SP Np A D S Tp nl al n t)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (X' : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀')
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R) (hT : ArgT SP Tp s₀) (hT' : ArgT SP Tp s₀')
    (htl : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t)
    (htl' : s₀'.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t) :
    RelCT isa (fun s₁ s₂ => OpenInS s₀ Ctx W SP A D S n t s₁ ∧ OpenInS s₀' Ctx W SP A D S n t s₂)
      (frontS (v.withBlk B) T.fn) fun _ _ => True := by
  have hlt := C.data.ok.lt
  have hSW' := C.sW.sub_left (Offset.sub_base S (d := 16 * (n / 16)) (n := n - 16 * (n / 16)) (by omega_arith))
  have oA := C.toOneCtx.arg24 (by decide)
  let GA : State → Prop := fun s => (OneS M Ctx W SP R A al D n none s ∧ PP M Ctx W SP D S R n n s) ∧
    ArgR SP Tp s ∧ ArgL SP t s
  have a := rel_wp ((oneAad_rel v L (R := R) (Np := Np) (nl := nl) (A := A) (al := al) (T := none) C.dE).mono
      (P' := fun (s₁ s₂ : State) => OpenInS s₀ Ctx W SP A D S n t s₁ ∧ OpenInS s₀' Ctx W SP A D S n t s₂)
      (fun _ _ h => ⟨h.1.1.aadPre C.toOneCtx X hNp hnl hal hR, h.2.1.aadPre C'.toOneCtx X' hNp' hnl' hal' hR'⟩)
      fun _ _ _ => trivial) (fun _ _ h => h) (G₁ := GA) (G₂ := GA)
    (fun _ h => aadS_ok v L B C X hNp hnl hal hR hT htl h) (fun _ h => aadS_ok v L B C' X' hNp' hnl' hal' hR' hT' htl' h)
  have b : RelCT isa (fun s₁ s₂ => True ∧ GA s₁ ∧ GA s₂) (OpenSplit.prefix T.fn)
      fun s₁ s₂ => True ∧ GB Ctx W SP R al S n t Tp s₁ ∧ GB Ctx W SP R al S n t Tp s₂ :=
    Split.rel_each fun σ σ' g => (rel_wp (prefixD_ct g.2.1.1.2 g.2.2.1.2 T) (F₁ := (· = σ)) (F₂ := (· = σ'))
      (fun _ _ h => h) (G₁ := GB Ctx W SP R al S n t Tp) (G₂ := GB Ctx W SP R al S n t Tp)
      (fun _ hs => by subst hs; exact prefixS_ok L T C g.2.1)
      (fun _ hs => by subst hs; exact prefixS_ok L T C g.2.2)).mono (fun _ _ h => h) fun _ _ h => h
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ GB Ctx W SP R al S n t Tp s₁ ∧ GB Ctx W SP R al S n t Tp s₂)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.2.1.1.env h.2.2.1.env) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (G₁ := GC Ctx W SP R al S n t Tp) (G₂ := GC Ctx W SP R al S n t Tp)
    (fun _ h => tagLenS_ok L oA.ws h) (fun _ h => tagLenS_ok L oA.ws h)
  have d := rel_wp ((oneTag_relT v L (R := R) (al := al) (N := n) (o := 112) (.inr rfl) hSW').mono
      (P' := fun (s₁ s₂ : State) => True ∧ GC Ctx W SP R al S n t Tp s₁ ∧ GC Ctx W SP R al S n t Tp s₂)
      (fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩) fun _ _ h => h) (fun _ _ h => h.2)
    (G₁ := GC Ctx W SP R al S n t Tp) (G₂ := GC Ctx W SP R al S n t Tp)
    (fun _ h => tagS_ok v L hlt hSW' oA.ws h) (fun _ h => tagS_ok v L hlt hSW' oA.ws h)
  have e := rel_wp (rel_taint (P := fun (s₁ s₂ : State) => True ∧ GC Ctx W SP R al S n t Tp s₁ ∧
      GC Ctx W SP R al S n t Tp s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.2.1.1.env h.2.2.1.env) ⟨_, by taint_decide⟩) (fun _ _ h => h.2)
    (fun _ h => loadTlS_ok h) (fun _ h => loadTlS_ok h)
  have f := rel_taint (P := fun (s₁ s₂ : State) => True ∧
      (Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t ∧ s₁.gpr .rsi = Tp) ∧
      (Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 t ∧ s₂.gpr .rsi = Tp))
    (c := .seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))
    ([.rbx, .rsi] ++ [.r13, .r14, .r15, .rsp])
    (fun _ _ h => EnvAgree.regs ⟨h.2.1.1, h.2.2.1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩) ⟨_, by taint_decide⟩
  exact RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨trivial, h.2⟩)
    (RelCT.seq (RelCT.seq b c) (RelCT.seq (d.mono (fun _ _ h => h) fun _ _ h => ⟨trivial, h.2⟩) (RelCT.seq e f)))

/-- After the comparison, in two runs with the same result: the bytes left
decrypted from `src` to `dst` if the tags match (`oneCryptG` out of place,
`cryptTailG_rel`), and the result loaded. -/
theorem endS_rel {s₀ s₀' : State} {Np A D S Tp : Addr} {nl al n t R : Nat}
    (hk : osK s₀ Ctx Np A S Tp nl al n t R = osK s₀' Ctx Np A S Tp nl al n t R) :
    RelCT isa (fun s₁ s₂ => FrontS M s₀ Ctx W SP Np A D S Tp nl al n t R s₁ ∧
        FrontS M s₀' Ctx W SP Np A D S Tp nl al n t R s₂)
      (.seq (.ite .e (.block []) (oneCryptG (v.withBlk B) true)) (.block [.mov .rax (.mem (at_ .r15 auxO))]))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have tb := skip_rel (P := fun (s₁ s₂ : State) => (FrontS M s₀ Ctx W SP Np A D S Tp nl al n t R s₁ ∧
      FrontS M s₀' Ctx W SP Np A D S Tp nl al n t R s₂) ∧ s₁.zf = some true)
    (Q := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂)
    fun _ _ h => ⟨h.1.1.env, h.1.2.env⟩
  let D' := D + BitVec.ofNat 64 (16 * (n / 16))
  let S' := S + BitVec.ofNat 64 (16 * (n / 16))
  let n' := n - 16 * (n / 16)
  have hq : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  -- Each run, after `oneCryptG`'s first block: `CrMid` from its memory then, and `TailSrc`.
  let G : Mem → State → Prop := fun m s₁ => CrMid Ctx (W + BitVec.ofNat 64 16) W SP R 0 0 D' n' m 0 s₁ ∧
    TailSrc true (W + BitVec.ofNat 64 16) W SP s₁ m D' 0 n' S'
  have hB : ∀ {s₀ : State} (s : State), FrontS M s₀ Ctx W SP Np A D S Tp nl al n t R s →
      WP isa (.block (oneCryptBlk true)) s fun s₁ => ∃ m, G m s₁ := fun s F => by
    have hn := F.dD.ok.lt
    refine WP.mono (oneCryptBlkTo_ok (R := R) (icb := 0) (P := 0) rfl F.env F.rounds F.dat F.len (F.dD.drop hq) ?_)
      fun s₁ ⟨hm, hts, _⟩ => ⟨_, hm, hts⟩
    simp only [CryptSrc, ↓reduceIte]
    refine ⟨by omega_arith, F.argR, ?_, F.src, F.sD⟩
    rw [F.argD, F.tlen, ofNat_sub (by omega_arith) hn]
    congr 2; omega_arith
  have ts : ∀ {m : Mem} {s₁ : State}, G m s₁ → (true = true → s₁.gpr .rbx = S') := fun h _ => by
    have h2 := h.2; simp only [TailSrc, ↓reduceIte] at h2; exact h2.1
  have hT : ∀ {m : Mem} (s₁ : State), G m s₁ → WP isa (cryptTailG (v.withBlk B) true) s₁
      (Env Ctx (W + BitVec.ofNat 64 16) W SP) := fun _ h =>
    WP.mono (cryptTailG_ok v L true h.1 (by omega_arith) (h.1.ciph L) h.2) fun _ o => o.env
  have eb : RelCT isa (fun (s₁ s₂ : State) => (FrontS M s₀ Ctx W SP Np A D S Tp nl al n t R s₁ ∧
      FrontS M s₀' Ctx W SP Np A D S Tp nl al n t R s₂) ∧ s₁.zf = some false) (oneCryptG (v.withBlk B) true)
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
    simp only [oneCryptG, ↓reduceIte]
    have a := rel_wp (rel_taint (P := fun (s₁ s₂ : State) => (FrontS M s₀ Ctx W SP Np A D S Tp nl al n t R s₁ ∧
        FrontS M s₀' Ctx W SP Np A D S Tp nl al n t R s₂) ∧ s₁.zf = some false) [.r13, .r14, .r15, .rsp]
        (fun _ _ h => env_agree h.1.1.env h.1.2.env) ⟨_, by taint_decide⟩)
      (fun _ _ h => h.1) (fun s h => hB s h) (fun s h => hB s h)
    refine RelCT.seq a ((RelCT.exists_ (P := fun m₁ s₁ s₂ => G m₁ s₁ ∧ ∃ m, G m s₂) fun m₁ =>
      (RelCT.exists_ (P := fun m₂ s₁ s₂ => G m₁ s₁ ∧ G m₂ s₂) fun m₂ => ?_).mono
        (fun _ _ ⟨h₁, m₂, h₂⟩ => ⟨m₂, h₁, h₂⟩) fun _ _ h => h).mono
      (fun _ _ ⟨_, ⟨m₁, h₁⟩, h₂⟩ => ⟨m₁, h₁, h₂⟩) fun _ _ h => h)
    exact (rel_wp ((cryptTailG_rel v L true (Q := S') (R := R) (icb₁ := 0) (icb₂ := 0)
      (P₁ := 0) (P₂ := 0) (D := D') (n := n') (m₁ := m₁) (m₂ := m₂) (j := 0)).mono
        (P' := fun s₁ s₂ => G m₁ s₁ ∧ G m₂ s₂) (fun _ _ h => ⟨⟨h.1.1, ts h.1⟩, h.2.1, ts h.2⟩) fun _ _ h => h)
      (F₁ := G m₁) (F₂ := G m₂) (fun _ _ h => h) (fun s h => hT s h) (fun s h => hT s h)).mono
        (fun _ _ h => h) fun _ _ h => h.2
  have f := rel_wp (rel_taint (P := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.1 h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h)
    (fun _ h => loadAux_ok h) (fun _ h => loadAux_ok h)
  exact RelCT.seq (rel_ite_e (fun _ _ h => by rw [h.1.zf, h.2.zf, hk]) tb eb)
    (f.mono (fun _ _ h => h) fun _ _ h => h.2)

end

/-- `open_split` after the entry, in two runs with the same result, for an
allowed tag length. -/
theorem midS_rel (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToDecFn M) {s₀ s₀' : State}
    {Ctx W SP Np A D S Tp : Addr} {nl al n t R : Nat}
    (C : OSCtx s₀ M.len Ctx W SP Np A D S Tp nl al n t) (C' : OSCtx s₀' M.len Ctx W SP Np A D S Tp nl al n t)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (X' : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀')
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R) (hT : ArgT SP Tp s₀) (hT' : ArgT SP Tp s₀')
    (hDa : s₀.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hDa' : s₀'.mem.readW (SP + BitVec.ofNat 64 8) 64 = D)
    (htl : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t)
    (htl' : s₀'.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 t)
    (hres : (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) t (bytesAt s₀.mem Np nl)
        (bytesAt s₀.mem S n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tp t)).isSome =
      (Spec.Gcm.openResult (ctxCiph s₀'.mem Ctx R) (ctxH s₀'.mem Ctx) t (bytesAt s₀'.mem Np nl)
        (bytesAt s₀'.mem S n) (bytesAt s₀'.mem A al) (bytesAt s₀'.mem Tp t)).isSome)
    (hok : Spec.Gcm.tagLenOk t = true) :
    RelCT isa (fun s₁ s₂ => OpenInS s₀ Ctx W SP A D S n t s₁ ∧ OpenInS s₀' Ctx W SP A D S n t s₂)
      (midS (v.withBlk B) T.fn)
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have L := C.lay
  have hk : osK s₀ Ctx Np A S Tp nl al n t R = osK s₀' Ctx Np A S Tp nl al n t R := by
    rw [osK_eq hok, osK_eq hok, hres]
  refine rel_reassoc7 (RelCT.seq ?_ (endS_rel v L B (s₀ := s₀) (s₀' := s₀') (Np := Np) (D := D) (S := S) (Tp := Tp)
    (nl := nl) (t := t) hk))
  exact (rel_wp (frontS_rel v L B T C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' htl htl') (fun _ _ h => h)
    (fun _ h => frontS_ok v B T C X h.1 h.2.2.1 h.2.2.2 hNp hnl hal hR hT hDa htl hok)
    (fun _ h => frontS_ok v B T C' X' h.1 h.2.2.1 h.2.2.2 hNp' hnl' hal' hR' hT' hDa' htl' hok)).mono (fun _ _ h => h)
    fun _ _ h => h.2

/-- After the entry: the tag length checked, then, if it is allowed, `mid`. -/
theorem openBodyS_relOf {s₀ s₀' : State} {Ctx W SP A D S : Addr} {n t : Nat} {mid : Prog isa}
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) (ht : t < 2 ^ 64)
    (hrel : Spec.Gcm.tagLenOk t = true →
      RelCT isa (fun s₁ s₂ => OpenInS s₀ Ctx W SP A D S n t s₁ ∧ OpenInS s₀' Ctx W SP A D S n t s₂) mid
        fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂) :
    RelCT isa (fun s₁ s₂ => True ∧ OpenInS s₀ Ctx W SP A D S n t s₁ ∧ OpenInS s₀' Ctx W SP A D S n t s₂)
      (.seq tagLenOk (.ite .e (.block [.mov32 .rax (imm 0)]) mid))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have hK : ∀ {s₀ s : State}, OpenInS s₀ Ctx W SP A D S n t s → WP isa tagLenOk s fun s' =>
      OpenInS s₀ Ctx W SP A D S n t s' ∧ s'.zf = some (!Spec.Gcm.tagLenOk t) := fun h =>
    WP.mono (tagLenOk_ok _ h.2.1 ht) fun _ ⟨hz, k⟩ =>
      ⟨⟨h.1.keep L (fun r hr => k.gpr r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) k.rd k.wr
          (by rw [k.mem]; exact Frame.refl _ _), by rw [k.gpr _ (by decide), h.2.1],
        by rw [k.mem]; exact h.2.2.1, by rw [k.mem]; exact h.2.2.2⟩, hz⟩
  have a := rel_wp (rel_regs (P := fun (s₁ s₂ : State) => True ∧ OpenInS s₀ Ctx W SP A D S n t s₁ ∧
      OpenInS s₀' Ctx W SP A D S n t s₂) ([.rbx] ++ [.r13, .r14, .r15, .rsp]) [] true
      (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun _ h => hK h) (fun _ h => hK h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_)
  · -- A length `tagLenOk` does not allow.
    exact (rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.1.env, h.1.2.2.1.1.env⟩)
      (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.1.1.env h.1.2.2.1.1.env)
        ⟨_, by taint_decide⟩)).mono (fun _ _ h => h) fun _ _ h => h.2
  · by_cases hok : Spec.Gcm.tagLenOk t = true
    swap
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hok] at this
    exact (hrel hok).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h

/-- `vg_aes_gcm_open_split`, in two runs from states with the same public
values. -/
theorem openSplitM_rel (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToDecFn M) {s₀ s₀' : State}
    (hp : (Proof.AesGcm.openSplitX86_64M M).pre s₀) (hp' : (Proof.AesGcm.openSplitX86_64M M).pre s₀')
    (hq : (Proof.AesGcm.openSplitX86_64M M).pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (OpenSplit.openSplit (v.withBlk B) T.fn) fun _ _ => True := by
  have X := CtxExt.ofOS hp.1 hp.2
  have X' := CtxExt.ofOS hp'.1 hp'.2
  have C := OSCtx.of hp.1 M.ge
  have C' := OSCtx.of hp'.1 M.ge
  have L := C.lay
  obtain ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩, hres⟩ := hq
  have hres' : ∀ {s : State}, Proof.AesGcm.rounds s → Proof.AesGcm.openSplitLeak s = [if (Spec.Gcm.openResult
      (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) (stackArg s 3).toNat
      (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)).isSome
      then 1 else 0] := fun h => by
    simp only [Proof.AesGcm.openSplitLeak, Proof.AesGcm.openSplitResult, Proof.AesGcm.arg, h, not_true_eq_false,
      ↓reduceIte]
  rw [hres' C.rounds, hres' C'.rounds] at hres
  have hres := leak_bool hres
  have a₀ := qa 0 (by decide); have a₁ := qa 1 (by decide); have a₂ := qa 2 (by decide)
  have a₃ := qa 3 (by decide); have a₄ := qa 4 (by decide); have a₆ := qa 6 (by decide)
  simp only [Proof.AesGcm.arg] at a₀ a₁ a₂ a₃ a₄ a₆
  have ha₆ := C.args 6 (by decide); have ha₆' := C'.args 6 (by decide)
  have hw56 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 56) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 56) 64 := a₆
  have hT₁ : ArgT (s₀.gpr .rsp) (stackArg s₀ 2) s₀ := rfl
  have hT₂ : ArgT (s₀.gpr .rsp) (stackArg s₀ 2) s₀' := by rw [ArgT, q₇, a₂]; rfl
  have hDa₁ : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s₀ 0 := rfl
  have hDa₂ : s₀'.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s₀ 0 := by rw [q₇, a₀]; rfl
  have htl₁ : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s₀ 3 := rfl
  have htl₂ : s₀'.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s₀ 3 := by rw [q₇, a₃]; rfl
  rw [← q₁, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← a₀, ← a₁, ← a₂, ← a₃, ← a₄, ← a₆] at C'
  rw [← q₁, ← q₇, ← a₀, ← a₁, ← a₆] at X'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← a₁, ← a₂, ← a₃, ← a₄] at hres
  generalize ht : (stackArg s₀ 3).toNat = t at hres C C'
  have hst : stackArg s₀ 3 = BitVec.ofNat 64 t := by rw [← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hst] at htl₁ htl₂
  have hE : ∀ {s : State} (C : OneCtx s 7 (s₀.gpr .rdi) (stackArg s₀ 6) (s₀.gpr .rsp) (s₀.gpr .rdx) (s₀.gpr .r8)
      (stackArg s₀ 0) (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (stackArg s₀ 1).toNat),
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .rsp = s₀.gpr .rsp → s.gpr .r8 = s₀.gpr .r8 →
      stackArg s 0 = stackArg s₀ 0 → (stackArg s 1).toNat = (stackArg s₀ 1).toNat →
      s.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 56) 64 = stackArg s₀ 6 → stackArg s 3 = stackArg s₀ 3 →
      stackArg s 4 = stackArg s₀ 4 →
      WP isa (.block OpenSplit.entry) s
        (OpenInS s (s₀.gpr .rdi) (stackArg s₀ 6) (s₀.gpr .rsp) (s₀.gpr .r8) (stackArg s₀ 0) (stackArg s₀ 4)
          (stackArg s₀ 1).toNat t) :=
    fun C h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ => WP.mono (entryS_ok C h₁ h₂ h₃ h₄ h₅ h₆) fun _ ⟨E, hbx, hS, hN, _⟩ =>
      ⟨E, by rw [hbx, h₇, hst], by rw [hS, h₈], hN⟩
  have hE₁ := hE C.toOneCtx rfl rfl rfl rfl rfl rfl rfl rfl
  have hE₂ := hE C'.toOneCtx q₁.symm q₇.symm q₅.symm a₀.symm (by rw [a₁]) (by rw [q₇, a₆]; rfl) a₃.symm a₄.symm
  rw [OpenSplit.entry, oneEntry] at hE₁ hE₂
  simp only [List.append_assoc] at hE₁ hE₂
  unfold OpenSplit.openSplit openBody
  rw [OpenSplit.entry, oneEntry]
  simp only [List.append_assoc]
  refine rel_reassoc_inner (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := stackArg s₀ 6 + BitVec.ofNat 64 16)
    (W := stackArg s₀ 6) (SP := s₀.gpr .rsp) (k := 56) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp)
    ⟨_, by taint_decide⟩ (one_pub ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩) hw56 ha₆ ha₆' ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  exact openBodyS_relOf L (by rw [← ht]; exact (stackArg s₀ 3).isLt) fun hok =>
    midS_rel v B T C C' X X' rfl rfl rfl rfl q₃.symm (by rw [← q₄]) (by rw [← q₆]) (by rw [← q₂]) hT₁ hT₂ hDa₁ hDa₂
      htl₁ htl₂ hres hok

theorem openSplitM_ct (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (T : BlkToDecFn M) :
    ConstantTime isa (Proof.AesGcm.openSplitX86_64M M).pre (Proof.AesGcm.openSplitX86_64M M).pub
      (OpenSplit.openSplit (v.withBlk B) T.fn) :=
  ct_of_rel fun _ _ hp hp' hq => openSplitM_rel v B T hp hp' hq

end VG.Proof.AesGcm.X86_64.OpenSplit
