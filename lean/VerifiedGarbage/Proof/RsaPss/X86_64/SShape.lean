module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SCTBase
public import VerifiedGarbage.Proof.RsaPss.X86_64.SEnc
public import VerifiedGarbage.Proof.RsaPss.X86_64.VPieces
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: the points of `signEnc`, for two runs

As verification's `VS` (`VShape.lean`): `SS P`, in the frame, with the
argument slots, `DB`'s address and length (words 33 and 44) and what `P`
says of the frame's words, after the checks; the words of the public slots,
as the entry state's public data fix them (`swv`), and the streaming
functions the code calls (`SSib.calls`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes oEm oBuf oRsa)
open VG.Proof.RsaOaep.X86_64 (decStack fb Lay Rep upd nW tw Calls frT lenOf FnsD wp_good keep_cs3 StepW)
open VG.Proof.MlKem.X86_64 (Keep ifp ifn)

/-- `DB`'s offset in our working space, `dbLen`, and `hLen`. -/
abbrev sgE (s : State) : Nat := oEm + loV (sn0v s)
abbrev sgDb (s : State) : Nat := sk s - loV (sn0v s) - (lenOf (sselH s) + 2) + 1
abbrev sgD (s : State) : Nat := lenOf (sselH s)

/-- The argument slots, as after the checks. -/
def SArgs (s : State) (W : Nat → BitVec 64) : Prop := ∀ k ∈ vKs, W k = scW s k

/-- In the frame, with the argument slots, `DB`'s address and length, and `P`
of the frame's words, after the checks. -/
def SS (P : State → (Nat → BitVec 64) → Prop) (s t : State) : Prop :=
  SEnv s t ∧ Lay t (fb s) (stackArg s 14) ∧
    (∃ V W, Rep t.mem (fb s) (stackArg s 14) V W ∧ SArgs s W ∧ W 33 = off (stackArg s 14) (sgE s) ∧
      W 44 = BitVec.ofNat 64 (sgDb s) ∧ P s W) ∧ SFit s

/-- The public slots' words. -/
def swv (s : State) (k : Nat) : BitVec 64 :=
  if k = 33 then off (stackArg s 14) (sgE s) else if k = 44 then BitVec.ofNat 64 (sgDb s) else scW s k

variable {kH kG : Nat}

theorem SSib.e_eq {a s : State} (S : SSib kH kG a s) : sgE s = sgE a := by simp only [sgE, S.n0]

theorem SSib.db_eq {a s : State} (S : SSib kH kG a s) : sgDb s = sgDb a := by
  simp only [sgDb, sk, S.n0, S.gpr (r := .rcx) (by decide), sselH, S.arg (j := 16) (by decide)]

theorem SSib.d_eq {a s : State} (S : SSib kH kG a s) : sgD s = sgD a := by
  simp only [sgD, sselH, S.arg (j := 16) (by decide)]

theorem SSib.sl_eq {a s : State} (S : SSib kH kG a s) : ssl s = ssl a := by
  simp only [ssl, S.arg (j := 13) (by decide)]

theorem SSib.wv_eq {a s : State} (S : SSib kH kG a s) {k : Nat} (hk : VKey k) : swv s k = swv a k := by
  unfold swv
  by_cases h33 : k = 33
  · rw [ifp h33, ifp h33, S.e_eq, S.arg (j := 14) (by decide)]
  · rw [ifn h33, ifn h33]
    by_cases h44 : k = 44
    · rw [ifp h44, ifp h44, S.db_eq]
    · rw [ifn h44, ifn h44]
      rcases hk with hk | hk | hk
      · exact S.cw hk
      · exact absurd hk h33
      · exact absurd hk h44

theorem SS.words {P : State → (Nat → BitVec 64) → Prop} {s t : State} (h : SS P s t) {k : Nat}
    (hk : VKey k) : word t.mem (fb s) (8 * k) = swv s k := by
  obtain ⟨-, -, ⟨V, W, R, hA, h33, h44, -⟩, -⟩ := h
  rw [R.fr k (vkey_lt hk)]
  unfold swv
  by_cases e33 : k = 33
  · subst e33; rw [ifp rfl]; exact h33
  · rw [ifn e33]
    by_cases e44 : k = 44
    · subst e44; rw [ifp rfl]; exact h44
    · rw [ifn e44]
      rcases hk with hk | hk | hk
      · exact hA k hk
      · exact absurd hk e33
      · exact absurd hk e44

/-- Code the taint analysis checks from the public slots `ks`, at a point
`SS P`. -/
theorem s_taintS {J : State → State → Prop} {P : State → (Nat → BitVec 64) → Prop} (hJ : ∀ s t, J s t → SS P s t)
    (rs : List Reg) (ks : List Nat) (hks : ∀ k ∈ ks, VKey k) (hpin : Pins (SAt kH kG J) rs)
    {c : Prog isa} (h : ∃ hc, (taint.check (frT rs ks 2) c hc).isSome = true) :
    RelCT isa (Two (SAt kH kG J)) c fun _ _ => True :=
  s_taintF (ks := ks) swv (fun s t _ j => ⟨(hJ s t j).1, fun k hk => (hJ s t j).words (hks k hk)⟩)
    (fun _ _ S k hk => S.wv_eq (hks k hk)) rs (fun k hk => vkey_lt (hks k hk)) hpin h

/-- The streaming functions of the table `j` (18 or 19), the anchor's, which a
state in the frame of a run from a sibling of the anchor may call. -/
theorem SSib.calls {a s t : State} (S : SSib kH kG a s) (he : SEnv s t) {T : Spec.HashFns.Streaming} {j : Nat}
    (hj : j = 18 ∨ j = 19) (fF : FnsD s T j) :
    Calls decStack T a (VG.Proof.RsaOaep.X86_64.fb a) (stackArg a 14) (VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a j) 0)
      (VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a j) 1) (VG.Proof.RsaOaep.X86_64.tw a.mem (stackArg a j) 2) t := by
  refine ⟨s, ?_, ?_, S.like⟩
  · have := he.here; rwa [S.fb, S.arg (j := 14) (by decide)] at this
  · have e0 := S.tw hj (i := 0) (by decide)
    have e1 := S.tw hj (i := 1) (by decide)
    have e2 := S.tw hj (i := 2) (by decide)
    unfold FnsD at fF
    rwa [e0, e1, e2] at fF

/-! ## The steps of `SS` -/

variable {s : State}

/-- What a piece leaves of `SS`, from what it leaves of the frame's words. -/
theorem ss_step {P P' : State → (Nat → BitVec 64) → Prop} {c : Prog isa} (hc : VG.Proof.RsaOaep.X86_64.Good c)
    {rs : List Reg} (hrs : rs.all (fun r => !calleeSaved.contains r) = true) {X : State → Prop} {t : State}
    (h : SS P s t)
    (hw : ∀ V W, Rep t.mem (fb s) (stackArg s 14) V W → SArgs s W → W 33 = off (stackArg s 14) (sgE s) →
      W 44 = BitVec.ofNat 64 (sgDb s) → P s W → WP isa c t fun t' => Lay t' (fb s) (stackArg s 14) ∧
        Keep rs t t' ∧ (∃ V' W', Rep t'.mem (fb s) (stackArg s 14) V' W' ∧ (∀ k, VKey k → W' k = W k) ∧
          P' s W') ∧ X t') :
    WP isa c t fun t' => SS P' s t' ∧ X t' := by
  obtain ⟨he, -, ⟨V, W, R, hA, h33, h44, hP⟩, hf⟩ := h
  refine WP.mono (wp_good hc (hw V W R hA h33 h44 hP))
    fun t' ⟨⟨L', k', ⟨V', W', R', hW, hP'⟩, hx⟩, sp', mx', f'⟩ => ?_
  exact ⟨⟨he.step k'.2.1 k'.2.2 sp' (keep_cs3 k' hrs) mx' f', L', ⟨V', W', R',
    fun k hk => (hW k (.inl hk)).trans (hA k hk), (hW 33 (.inr (.inl rfl))).trans h33,
    (hW 44 (.inr (.inr rfl))).trans h44, hP'⟩, hf⟩, hx⟩

/-- A piece that keeps the memory. -/
theorem ss_stepM {P : State → (Nat → BitVec 64) → Prop} {c : Prog isa} (hc : VG.Proof.RsaOaep.X86_64.Good c)
    {rs : List Reg} (hrs : rs.all (fun r => !calleeSaved.contains r) = true) (hsp : Reg.rsp ∉ rs)
    {X : State → Prop} {t : State} (h : SS P s t)
    (hw : ∀ V W, Rep t.mem (fb s) (stackArg s 14) V W → SArgs s W → W 33 = off (stackArg s 14) (sgE s) →
      W 44 = BitVec.ofNat 64 (sgDb s) → P s W → WP isa c t fun t' => t'.mem = t.mem ∧ Keep rs t t' ∧ X t') :
    WP isa c t fun t' => SS P s t' ∧ X t' :=
  ss_step hc hrs h fun V W R hA h33 h44 hP => WP.mono (hw V W R hA h33 h44 hP) fun _ ⟨hm, k, x⟩ =>
    ⟨h.2.1.congr (k.gpr hsp) k.2.2 (by rw [hm]), k, ⟨V, W, hm ▸ R, fun _ _ => rfl, hP⟩, x⟩

/-- A piece that keeps the frame's words. -/
theorem ss_stepW {P : State → (Nat → BitVec 64) → Prop} {c : Prog isa} (hc : VG.Proof.RsaOaep.X86_64.Good c)
    {rs : List Reg} (hrs : rs.all (fun r => !calleeSaved.contains r) = true) {X : State → Prop} {t : State}
    (h : SS P s t)
    (hw : ∀ V W, Rep t.mem (fb s) (stackArg s 14) V W → SArgs s W → W 33 = off (stackArg s 14) (sgE s) →
      W 44 = BitVec.ofNat 64 (sgDb s) → P s W → WP isa c t fun t' => Lay t' (fb s) (stackArg s 14) ∧
        Keep rs t t' ∧ (∃ V', Rep t'.mem (fb s) (stackArg s 14) V' W) ∧ X t') :
    WP isa c t fun t' => SS P s t' ∧ X t' :=
  ss_step hc hrs h fun V W R hA h33 h44 hP => WP.mono (hw V W R hA h33 h44 hP) fun _ ⟨L', k, ⟨V', R'⟩, x⟩ =>
    ⟨L', k, ⟨V', W, R', fun _ _ => rfl, hP⟩, x⟩

/-- The sizes the checks give. -/
theorem SFit.sizes (hp : SPre s) (hf : SFit s) :
    1 ≤ sgDb s ∧ sgE s + sgDb s + sgD s ≤ oBuf ∧ 16 ≤ sgD s ∧ sgD s ≤ 64 ∧ sgE s ≤ 1 ∧ ssl s + 1 ≤ sgDb s ∧
      sgDb s ≤ 1007 ∧ sgE s + sgDb s + sgD s + 1 = oEm + sk s := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hlo := loV_le (sn0v s)
  have hD : 16 ≤ lenOf (sselH s) ∧ lenOf (sselH s) ≤ 64 := by
    have h := hp.iH
    simp only [Spec.RsaPss.hashIds, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  have := hf.2
  simp only [sgDb, sgE, sgD, sk, ssl, oEm, oBuf] at *
  omega

/-- The argument slots' words. -/
theorem SArgs.w {W : Nat → BitVec 64} (h : SArgs s W) :
    W 14 = stackArg s 14 ∧ W 21 = s.gpr .rdi ∧ W 22 = s.gpr .rdx ∧ W 23 = s.gpr .rcx ∧ W 24 = s.gpr .r8 ∧
      W 25 = s.gpr .r9 ∧ W 26 = stackArg s 15 ∧ W 27 = stackArg s 10 ∧ W 28 = stackArg s 12 ∧
      W 29 = stackArg s 13 ∧ W 30 = maskV (sn0v s) ∧ W 31 = BitVec.ofNat 64 (loV (sn0v s)) := by
  obtain ⟨w14, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31⟩ := scW_w s
  exact ⟨(h 14 (by decide)).trans w14, (h 21 (by decide)).trans w21, (h 22 (by decide)).trans w22,
    (h 23 (by decide)).trans w23, (h 24 (by decide)).trans w24, (h 25 (by decide)).trans w25,
    (h 26 (by decide)).trans w26, (h 27 (by decide)).trans w27, (h 28 (by decide)).trans w28,
    (h 29 (by decide)).trans w29, (h 30 (by decide)).trans w30, (h 31 (by decide)).trans w31⟩

/-- The selectors' slots. -/
theorem SArgs.sel {W : Nat → BitVec 64} (h : SArgs s W) :
    W 39 = BitVec.ofNat 64 (sgD s) ∧ W 43 = BitVec.ofNat 64 (lenOf (sselG s)) ∧
    (W 45 = tw s.mem (stackArg s 18) 0 ∧ W 46 = tw s.mem (stackArg s 18) 1 ∧ W 47 = tw s.mem (stackArg s 18) 2) ∧
    (W 48 = tw s.mem (stackArg s 19) 0 ∧ W 49 = tw s.mem (stackArg s 19) 1 ∧
      W 50 = tw s.mem (stackArg s 19) 2) := by
  obtain ⟨w39, w43, ⟨h45, h46, h47⟩, ⟨h48, h49, h50⟩⟩ := scW_sel s
  exact ⟨(h 39 (by decide)).trans w39, (h 43 (by decide)).trans w43,
    ⟨(h 45 (by decide)).trans h45, (h 46 (by decide)).trans h46, (h 47 (by decide)).trans h47⟩,
    ⟨(h 48 (by decide)).trans h48, (h 49 (by decide)).trans h49, (h 50 (by decide)).trans h50⟩⟩

theorem SArgs.upd' {W : Nat → BitVec 64} (h : SArgs s W) {j : Nat}
    (hj : j < 14 ∨ (14 < j ∧ j < 21) ∨ (31 < j ∧ j < 37) ∨ j = 44) (v : BitVec 64) : SArgs s (upd W j v) :=
  fun k hk => by have := vKs_iff hk; simp only [upd]; rw [ifn (show ¬ k = j by omega)]; exact h k hk

end VG.Proof.RsaPss.X86_64
