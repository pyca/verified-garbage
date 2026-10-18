module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncSteps
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncSteps
public import VerifiedGarbage.Proof.RsaOaep.X86_64.SelCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.SelCT
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub

/-!
# RSAES-OAEP encryption on x86-64: constant time

Each point of the code is described, in each run, by what correctness says of
it from that run's entry state, which has the same public data as an anchor
(`EAt`, as in `Proof/RsaPkcs1Sig/X86_64/SignCT.lean`). The pieces between the
calls are checked by the taint analysis from the frame's public slots
(`e_taintF`); the branches are on `k` and the message's length, which are
public; MGF1 and the label's hash are constant time for the same public data
in both runs (`mgf_ct`, `hashLabel_ct`); and the call of
`vg_rsa_public_checked` is constant time for its contract, whose public data
(its registers, its stack arguments, `n` and `e`) are the same in both runs.
The hash functions are those the selectors name, the same in both runs, and
so are their tables' words: the calls of their streaming functions are of
the same addresses in both runs, from entries of the same program (`Like`),
and the code reads their lengths from the frame's public slots.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.Dispatch.X86_64 (FlagsOnly)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.HashFns (StreamingOK)
open VG.Proof.RsaPkcs1Sig.X86_64 (pubChecked pubChk)

/-! ## Entry states and the anchor -/

section
variable (H G : Spec.Mgf1.Hash) (P : State → State → Prop)

/-- An entry state with the public data of the anchor `a`, and what `P`
relates them by: more public data, for a variant with more arguments
(`PcCT`). -/
def ESib (a s : State) : Prop := EPre H s ∧ (encK H G).pub a s ∧ P a s

/-- What `J` says of a run from an entry state with the anchor's public data. -/
def EAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, ESib H G P a s ∧ J s t

theorem encPub_refl (s : State) : (encK H G).pub s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp only [abi, Option.elim]⟩

end

variable {H G : Spec.Mgf1.Hash} {P : State → State → Prop}

theorem ESib.gpr {a s : State} (h : ESib H G P a s) {r : Reg}
    (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r := (h.2.1.1 r hr).symm

theorem ESib.arg {a s : State} (h : ESib H G P a s) {i : Nat} (hi : i < 14) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.1.2.1) i (List.mem_range.mpr hi)).symm

theorem ESib.fb {a s : State} (h : ESib H G P a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _; rw [h.gpr (r := .rsp) (by decide)]

theorem ESib.out_eq {a s : State} (h : ESib H G P a s) : outR s = outR a := by
  unfold outR; rw [h.gpr (r := .rdi) (by decide), h.gpr (r := .rsi) (by decide)]

theorem ESib.scr_eq {a s : State} (h : ESib H G P a s) : scrR s = scrR a := by
  unfold scrR; rw [h.arg (i := 6) (by decide), h.arg (i := 7) (by decide)]

theorem ESib.k {a s : State} (h : ESib H G P a s) : (s.gpr .rcx).toNat = (a.gpr .rcx).toNat := by
  rw [h.gpr (r := .rcx) (by decide)]

theorem ESib.w_eq {a s : State} (h : ESib H G P a s) {k : Nat} (hk : k ∈ encKs) : encW s k = encW a k := by
  simp only [encKs, List.mem_cons, List.not_mem_nil, or_false] at hk
  have e : ∀ i < 14, stackArg s i = stackArg a i := fun i hi => h.arg hi
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;>
  simp [encW, fnW, selW, encPW, upd, selH, selG, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide),
    e 4 (by decide), e 6 (by decide), e 7 (by decide), e 10 (by decide), e 11 (by decide),
    h.gpr (r := .rdi) (by decide), h.gpr (r := .rdx) (by decide), h.gpr (r := .rcx) (by decide),
    h.gpr (r := .r8) (by decide), h.gpr (r := .r9) (by decide)]

/-- The words of the tables, the stack arguments 12 and 13. -/
theorem ESib.tw {a s : State} (h : ESib H G P a s) {j : Nat} (hj : j = 12 ∨ j = 13) {i : Nat} (hi : i < 3) :
    tw s.mem (stackArg s j) i = tw a.mem (stackArg a j) i := by
  rcases hj with rfl | rfl
  · exact (tw_eq h.2.1.2.2.2.2.1 hi).symm
  · exact (tw_eq h.2.1.2.2.2.2.2.1 hi).symm

/-- An entry with the anchor's public data and regions is like it. -/
theorem ESib.like {a s : State} (h : ESib H G P a s) (hr : s.rd = a.rd ∧ s.wr = a.wr) : Like a s := by
  obtain ⟨f, c, y⟩ := h.2.1.2.2.2.2.2.2
  simp only [abi, Option.elim] at y
  exact ⟨⟨f.symm, c.symm, by simp only [abi, Option.elim]; exact y.symm⟩, hr.1, hr.2, h.gpr (r := .rsp) (by decide)⟩

/-! ## The pieces -/

/-- Code the taint analysis checks from the frame's argument slots `ks`. -/
theorem e_taintF {J : State → State → Prop} (hJ : ∀ s t, EPre H s → J s t → EW s t)
    (rs : List Reg) (ks : List Nat) (hks : ∀ k ∈ ks, k ∈ encKs) (hpin : Pins (EAt H G P J) rs) {c : Prog isa}
    (h : ∃ hc, (taint.check (frT rs ks 2) c hc).isSome = true) :
    RelCT isa (Two (EAt H G P J)) c fun _ _ => True :=
  two_taintF rs ks fb (fun a => [outR a, scrR a]) encW (fun a t ⟨s, S, j⟩ => by
      have e := hJ s t S.1 j
      rw [← S.fb, ← S.out_eq, ← S.scr_eq]
      exact ⟨e.he.frv S.1, fun k hk => (e.words k (hks k hk)).trans (S.w_eq (hks k hk))⟩)
    hpin (fun k hk => encKs_lt k (hks k hk)) h

/-- What correctness says after a piece. -/
theorem e_post {J J' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Two (EAt H G P J)) c fun _ _ => True)
    (hw : ∀ a s t, ESib H G P a s → J s t → WP isa c t (J' s)) :
    RelCT isa (Two (EAt H G P J)) c (Two (EAt H G P J')) :=
  two_post hct fun a t ⟨s, S, j⟩ => WP.mono (hw a s t S j) fun _ j' => ⟨s, S, j'⟩

theorem e_pins_rsp {J : State → State → Prop} (hJ : ∀ s t, EPre H s → J s t → t.gpr .rsp = fb s) :
    Pins (EAt H G P J) [.rsp] :=
  fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ r hr => by
    rw [List.mem_singleton.mp hr, hJ _ _ S₁.1 j₁, hJ _ _ S₂.1 j₂, S₁.fb, S₂.fb]

/-- A branch on a condition that the entry state's public data fixes. -/
theorem e_ite {J : State → State → Prop} {cond : isa.Cond} {th el : Prog isa} {Q : State → State → Prop}
    (f : State → Option Bool) (hf : ∀ s t, J s t → isa.eval cond t = f s) (hs : ∀ a s, ESib H G P a s → f s = f a)
    (ht : RelCT isa (Two fun a t => EAt H G P J a t ∧ isa.eval cond t = some true) th Q)
    (he : RelCT isa (Two fun a t => EAt H G P J a t ∧ isa.eval cond t = some false) el Q) :
    RelCT isa (Two (EAt H G P J)) (.ite cond th el) Q :=
  two_ite (fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ => by rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]) ht he

/-- In a branch, what its condition says of the entry state. -/
theorem e_branch {J J' : State → State → Prop} {cond : isa.Cond} {b : Bool} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ s t, EPre H s → J s t → isa.eval cond t = some b → J' s t)
    (hct : RelCT isa (Two (EAt H G P J')) c Q) :
    RelCT isa (Two fun a t => EAt H G P J a t ∧ isa.eval cond t = some b) c Q :=
  hct.mono (fun _ _ ⟨a, ⟨⟨s₁, S₁, j₁⟩, e₁⟩, ⟨⟨s₂, S₂, j₂⟩, e₂⟩⟩ =>
    ⟨a, ⟨s₁, S₁, h _ _ S₁.1 j₁ e₁⟩, ⟨s₂, S₂, h _ _ S₂.1 j₂ e₂⟩⟩) fun _ _ h => h

/-! ## The call -/

theorem entryBytes {s t : State} (he : EnvE s t) (rd wr : List Region)
    {p : Addr} {len : Nat} (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩)
    (hs : (scrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  have hfe : Frame [below (fb s) 16] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, he.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide) (by decide))
  have hfE : FrE s t.callEntry.mem :=
    he.fr.trans (hfe.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret_sub s⟩)
  rw [State.withRegions_mem]
  exact FrE.bytes hfE hk ho hs hl

theorem pw_sib {a s : State} (S : ESib H G P a s) (i : Nat) : pw s i = pw a i := by
  match i with
  | 0 => show off _ _ = off _ _; rw [S.arg (by decide)]
  | 1 => exact S.gpr (by decide)
  | 2 => show off _ _ = off _ _; rw [S.arg (by decide)]
  | _ + 3 => show _ - _ = _ - _; rw [S.arg (by decide)]

theorem e_entry_regs (t : State) (rd wr : List Region) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions rd wr).gpr =
      [t.gpr .rdi, t.gpr .rsi, t.gpr .rdx, t.gpr .rcx, t.gpr .r8, t.gpr .r9, t.gpr .rsp - 8] := by
  simp only [List.map_cons, List.map_nil, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]

/-! ## `encMain` -/

section
variable {TH TG : Spec.HashFns.Streaming} (hTH : StreamingOK TH H) (hTG : StreamingOK TG G) {kH kG : Nat}
  (sH : Spec.HashFns.streaming kH = some TH) (sG : Spec.HashFns.streaming kG = some TG)
  (eH : Spec.HashId.mgf1 kH = some H) (eG : Spec.HashId.mgf1 kG = some G)
  (hPH : ∀ a s, P a s → selH s = kH) (hPG : ∀ a s, P a s → selG s = kG)
  (hPr : ∀ a s, P a s → s.rd = a.rd ∧ s.wr = a.wr)

/-- In the frame, after the checks. -/
def EK (D : Nat) (s t : State) : Prop := EW s t ∧ 2 * D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat

/-- Before MGF1. -/
def EKM (D : Nat) (src srcLen dst dstLen : State → Nat) (s t : State) : Prop :=
  EWM s t (src s) (srcLen s) (dst s) (dstLen s) ∧ 2 * D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat

/-- The label's hash's public data. -/
def lq (a : State) : LQ := ⟨fb a, stackArg a 6, [outR a, scrR a], stackArg a 0, (stackArg a 1).toNat, a,
  tw a.mem (stackArg a 12) 0, tw a.mem (stackArg a 12) 1, tw a.mem (stackArg a 12) 2⟩

include hPH eH hTH in
/-- `hLen` of the label's hash function, in its slot. -/
theorem ESib.lenH {a s : State} (S : ESib H G P a s) : lenOf (selH s) = TH.S.digestBytes := by
  rw [hPH _ _ S.2.2]; exact (lenOf_eq hTH eH).symm

include hPG eG hTG in
theorem ESib.lenG {a s : State} (S : ESib H G P a s) : lenOf (selG s) = TG.S.digestBytes := by
  rw [hPG _ _ S.2.2]; exact (lenOf_eq hTG eG).symm

include hPH sH in
/-- The streaming functions of the label's hash function, in its table. -/
theorem ESib.fnsH {a s : State} (S : ESib H G P a s) : FnsOf s TH 12 := by
  have h := S.1.fH
  rw [hPH _ _ S.2.2] at h
  obtain ⟨T, _, sT, _, _, hF⟩ := fns_of_tab h
  rw [sH, Option.some.injEq] at sT
  subst sT
  exact hF

include hPG sG in
theorem ESib.fnsG {a s : State} (S : ESib H G P a s) : FnsOf s TG 13 := by
  have h := S.1.fG
  rw [hPG _ _ S.2.2] at h
  obtain ⟨T, _, sT, _, _, hF⟩ := fns_of_tab h
  rw [sG, Option.some.injEq] at sT
  subst sT
  exact hF

include hTH sH eH hPH hPr in
theorem encEm_ct : RelCT isa (Two (EAt H G P (EK TH.S.digestBytes))) encEm
    (Two (EAt H G P (EK TH.S.digestBytes))) := by
  have hz := sizes hTH
  unfold encEm seqs seqs seqs seqs
  refine RelCT.seq (e_post (J' := EK TH.S.digestBytes) (e_taintF (fun _ _ _ h => h.1) [] [14] (by decide) nopin
      ⟨_, by taint_decide⟩)
    fun _ s t _ h => WP.mono (ew_clearEm h.1) fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK TH.S.digestBytes) (e_taintF (fun _ _ _ h => h.1) [] [14, 31, 39] (by decide)
      nopin ⟨_, by taint_decide⟩)
    fun _ s t S h => WP.mono (ew_copySeed S.1 hTH.len (S.lenH hTH eH hPH) (by omega) (by omega) h.1)
      fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK TH.S.digestBytes) (two_map lq (fun a t ⟨s, S, e, _⟩ => by
      have hp := S.1
      obtain ⟨V, W, R, hW⟩ := e.rep
      obtain ⟨fn, -⟩ := hW.fn
      have hl := S.like (hPr _ _ S.2.2)
      have := (⟨e.he.frv hp, e.L, ⟨V, W, R, e.lab hp hW, fn⟩, ⟨s, e.he.here, S.fnsH sH hPH, hl⟩, hp.wL,
        fun x hx => hl.inR (hp.rdIn (r := ⟨stackArg s 0, (stackArg s 1).toNat⟩) (by simp [rdL]) x hx)⟩ :
        LW encStack TH 2 ⟨fb s, stackArg s 6, [outR s, scrR s], stackArg s 0, (stackArg s 1).toNat, a,
          tw s.mem (stackArg s 12) 0, tw s.mem (stackArg s 12) 1, tw s.mem (stackArg s 12) 2⟩ t)
      simp only [lq] at this ⊢
      rwa [S.tw (.inl rfl) (i := 0) (by decide), S.tw (.inl rfl) (i := 1) (by decide),
        S.tw (.inl rfl) (i := 2) (by decide), S.fb, S.out_eq, S.scr_eq, S.arg (i := 6) (by decide),
        S.arg (i := 0) (by decide), S.arg (i := 1) (by decide)] at this)
      (hashLabel_ct hTH 2 (.inl rfl) (Or.inl rfl)))
    fun _ s t S h => WP.mono (ew_hashLabel S.1 hTH (S.fnsH sH hPH) h.1) fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK TH.S.digestBytes) (e_taintF (fun _ _ _ h => h.1) [] [14, 39] (by decide) nopin
      ⟨_, by taint_decide⟩)
    fun _ s t S h => WP.mono (ew_copyLh (S.lenH hTH eH hPH) (by omega) (by omega) h.1) fun _ e => ⟨e, h.2⟩) ?_
  exact e_post (J' := EK TH.S.digestBytes) (e_taintF (fun _ _ _ h => h.1) [] [14, 23, 29, 30] (by decide) nopin
    ⟨_, by taint_decide⟩) fun _ s t S h => WP.mono (ew_putMsg S.1 h.2 h.1) fun _ e => ⟨e, h.2⟩

theorem fit_db {D : Nat} {s : State} {Hs : Spec.Mgf1.Hash} (hp : EPre Hs s)
    (hk : 2 * D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) :
    MFit (oEm + 1) D (oEm + 1 + D) ((s.gpr .rcx).toNat - (D + 1)) := by
  have := hp.k2
  exact ⟨by unfold oEm oSt; omega, by unfold oEm oSt; omega, by omega, by omega, by omega⟩

theorem fit_seed {D : Nat} {s : State} {Hs : Spec.Mgf1.Hash} (hp : EPre Hs s)
    (hk : 2 * D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) (hD : 0 < D) :
    MFit (oEm + 1 + D) ((s.gpr .rcx).toNat - (D + 1)) (oEm + 1) D := by
  have := hp.k2
  exact ⟨by unfold oEm oSt; omega, by unfold oEm oSt; omega, by omega, by omega, by omega⟩

include sG hPG hPr in
/-- Where MGF1 starts, for the anchor's public data. -/
theorem me_of {src srcLen dst dstLen : Nat → Nat} {a s t : State} (S : ESib H G P a s)
    (h43 : lenOf (selG s) = TG.S.digestBytes)
    (h : EWM s t (src (s.gpr .rcx).toNat) (srcLen (s.gpr .rcx).toNat) (dst (s.gpr .rcx).toNat)
      (dstLen (s.gpr .rcx).toNat))
    (hf : MFit (src (s.gpr .rcx).toNat) (srcLen (s.gpr .rcx).toNat) (dst (s.gpr .rcx).toNat)
      (dstLen (s.gpr .rcx).toNat)) :
    ME encStack TG 2 ⟨fb a, stackArg a 6, [outR a, scrR a], src (a.gpr .rcx).toNat, srcLen (a.gpr .rcx).toNat,
      dst (a.gpr .rcx).toNat, dstLen (a.gpr .rcx).toNat, a, tw a.mem (stackArg a 13) 0, tw a.mem (stackArg a 13) 1,
      tw a.mem (stackArg a 13) 2⟩ t := by
  have hp := S.1
  obtain ⟨V, W, R, hW, A⟩ := h.rep
  obtain ⟨-, -, -, -, -, -, w43⟩ := hW.sel
  obtain ⟨-, fn⟩ := hW.fn
  rw [h43] at w43
  have := (⟨h.he.frv hp, h.L, hf, ⟨V, W, R, A, fn, w43⟩, ⟨s, h.he.here, S.fnsG sG hPG, S.like (hPr _ _ S.2.2)⟩⟩ :
    ME encStack TG 2 ⟨fb s, stackArg s 6, [outR s, scrR s], src (s.gpr .rcx).toNat, srcLen (s.gpr .rcx).toNat,
      dst (s.gpr .rcx).toNat, dstLen (s.gpr .rcx).toNat, a, tw s.mem (stackArg s 13) 0, tw s.mem (stackArg s 13) 1,
      tw s.mem (stackArg s 13) 2⟩ t)
  rwa [S.tw (.inr rfl) (i := 0) (by decide), S.tw (.inr rfl) (i := 1) (by decide),
    S.tw (.inr rfl) (i := 2) (by decide), S.fb, S.out_eq, S.scr_eq, S.arg (i := 6) (by decide), S.k] at this

include hTH hTG sH sG eH eG hPH hPG hPr in
/-- `EM` built and masked, then `rest`, constant time if `rest` is. -/
theorem encMask_ct {rest : Prog isa}
    (hrest : RelCT isa (Two (EAt H G P (EK TH.S.digestBytes))) rest fun _ _ => True) :
    RelCT isa (Two (EAt H G P (EK TH.S.digestBytes))) (.seq encEm (.seq (.block dbArgs)
      (.seq (mgfXor lay) (.seq (.block seedArgs) (.seq (mgfXor lay) rest)))))
      fun _ _ => True := by
  have hz := sizes hTH
  have hD0 := hTH.pos
  refine RelCT.seq (encEm_ct hTH sH eH hPH hPr) ?_
  -- `DB` masked.
  refine RelCT.seq (e_post (J' := fun s t => EWM s t (oEm + 1) TH.S.digestBytes (oEm + 1 + TH.S.digestBytes)
      ((s.gpr .rcx).toNat - (TH.S.digestBytes + 1)) ∧
        2 * TH.S.digestBytes + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat)
    (e_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin ⟨_, by taint_decide⟩)
    fun _ s t S h => WP.mono (ew_dbArgs (S.lenH hTH eH hPH) (by have := h.2; omega) h.1) fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK TH.S.digestBytes) (two_map (fun a => (⟨fb a, stackArg a 6, [outR a, scrR a],
      oEm + 1, TH.S.digestBytes, oEm + 1 + TH.S.digestBytes, (a.gpr .rcx).toNat - (TH.S.digestBytes + 1), a,
      tw a.mem (stackArg a 13) 0, tw a.mem (stackArg a 13) 1, tw a.mem (stackArg a 13) 2⟩ : MQ))
      (fun a t ⟨s, S, e, hk⟩ => me_of sG hPG hPr (src := fun _ => oEm + 1) (srcLen := fun _ => TH.S.digestBytes)
        (dst := fun _ => oEm + 1 + TH.S.digestBytes) (dstLen := fun k => k - (TH.S.digestBytes + 1)) S
        (S.lenG hTG eG hPG) e (fit_db S.1 hk))
      (mgf_ct hTG 2 (Gs := G) (congrFun hTG.hash) hTG.len hTG.valid (.inl rfl)))
    fun _ s t S h => WP.mono (ew_mgf hTG (S.fnsG sG hPG) (by rw [hPG _ _ S.2.2]; exact eG) (fit_db S.1 h.2) h.1)
      fun _ e => ⟨e, h.2⟩) ?_
  -- The seed masked.
  refine RelCT.seq (e_post (J' := fun s t => EWM s t (oEm + 1 + TH.S.digestBytes)
      ((s.gpr .rcx).toNat - (TH.S.digestBytes + 1)) (oEm + 1) TH.S.digestBytes ∧
        2 * TH.S.digestBytes + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat)
    (e_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin ⟨_, by taint_decide⟩)
    fun _ s t S h => WP.mono (ew_seedArgs (S.lenH hTH eH hPH) (by have := h.2; omega) h.1) fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK TH.S.digestBytes) (two_map (fun a => (⟨fb a, stackArg a 6, [outR a, scrR a],
      oEm + 1 + TH.S.digestBytes, (a.gpr .rcx).toNat - (TH.S.digestBytes + 1), oEm + 1, TH.S.digestBytes, a,
      tw a.mem (stackArg a 13) 0, tw a.mem (stackArg a 13) 1, tw a.mem (stackArg a 13) 2⟩ : MQ))
      (fun a t ⟨s, S, e, hk⟩ => me_of sG hPG hPr (src := fun _ => oEm + 1 + TH.S.digestBytes)
        (srcLen := fun k => k - (TH.S.digestBytes + 1)) (dst := fun _ => oEm + 1)
        (dstLen := fun _ => TH.S.digestBytes) S (S.lenG hTG eG hPG) e (fit_seed S.1 hk hD0))
      (mgf_ct hTG 2 (Gs := G) (congrFun hTG.hash) hTG.len hTG.valid (.inl rfl)))
    fun _ s t S h => WP.mono (ew_mgf hTG (S.fnsG sG hPG) (by rw [hPG _ _ S.2.2]; exact eG) (fit_seed S.1 h.2 hD0)
      h.1) fun _ e => ⟨e, h.2⟩) ?_
  exact hrest

/-! ## The checks -/

omit hTH hTG sH sG eH eG hPH hPG hPr in
theorem zeroOut_ct : RelCT isa (Two (EAt H G P EW)) zeroOut fun _ _ => True :=
  e_taintF (fun _ _ _ h => h) [] [21, 23] (by decide) nopin ⟨_, by taint_decide⟩

/-- After the check of `k`. -/
def J2 (D : Nat) (s t : State) : Prop :=
  EW s t ∧ t.gpr .rax = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧ t.cf = some (decide ((s.gpr .rcx).toNat < 2 * D + 2))

/-- After the check of `k`, which passed. -/
def J2' (D : Nat) (s t : State) : Prop :=
  EW s t ∧ t.gpr .rax = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧ 2 * D + 2 ≤ (s.gpr .rcx).toNat

/-- After the check of the message's length. -/
def J3 (D : Nat) (s t : State) : Prop :=
  EW s t ∧ 2 * D + 2 ≤ (s.gpr .rcx).toNat ∧
    t.cf = some (decide ((s.gpr .rcx).toNat - (2 * D + 2) < (stackArg s 3).toNat))

theorem cf_false {t : State} {p : Prop} [Decidable p] (h : t.cf = some (decide p))
    (e : isa.eval .b t = some false) : ¬ p := by
  have e' : t.cf = some false := e
  rw [h] at e'
  simpa using e'

omit hTH hTG sH sG eH eG hPH hPG hPr in
theorem chkMsg_step {D : Nat} {s t : State} (hs : EPre H s) (hDl : lenOf (selH s) = D)
    (h : J2' D s t) : WP isa (.block chkMsg) t (J3 D s) := by
  have hp := hs
  have hk1 := hp.k1; have hk2 := hp.k2
  obtain ⟨e, hax, hk⟩ := h
  obtain ⟨V, W, R, hW⟩ := e.rep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, w30, -⟩ := hW.w
  obtain ⟨-, -, -, -, -, w42, -⟩ := hW.sel
  rw [hDl] at w42
  refine WP.mono (wp_good (block_good _ rfl rfl) (chkMsg_ok e.L R (k := (s.gpr .rcx).toNat)
    (mLen := (stackArg s 3).toNat) (by rw [w30, BitVec.ofNat_toNat, BitVec.setWidth_eq]) w42 hax (by omega)
    (by omega) (stackArg s 3).isLt))
    fun t3 ⟨⟨k3, hm3, hcf3⟩, sp3, mx3, f3⟩ => ⟨⟨e.he.step k3.2.1 k3.2.2 sp3 (keep_cs3 k3 (by decide)) mx3 f3,
      e.L.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3]), V, W, hm3 ▸ R, hW⟩, hk, hcf3⟩

/-- After the prologue. -/
def JA (s t : State) : Prop := t = allocState frameBytes s

theorem pro_taint : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block encPrologue) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chkK_taint : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block chkK) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chkMsg_taint : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block chkMsg) hc).isSome = true :=
  ⟨_, by taint_decide⟩

include hTH eH hPH hPG in
/-- The prologues and the checks, then `main`, constant time if `main` is. -/
theorem encBodyWith_ct (iH : kH ∈ Spec.RsaOaep.hashIds) (iG : kG ∈ Spec.RsaOaep.hashIds) {main : Prog isa}
    (hmain : RelCT isa (Two (EAt H G P (EK TH.S.digestBytes))) main fun _ _ => True) :
    RelCT isa (Two (EAt H G P JA)) (encBodyWith main) fun _ _ => True := by
  have hz := sizes hTH
  have hkm : ∀ {k : Nat}, k ∈ Spec.RsaOaep.hashIds → k ∈ lens.map (·.1) := fun h =>
    List.mem_map.mpr ⟨_, mem_lens h, rfl⟩
  unfold encBodyWith seqs seqs seqs seqs
  -- The prologue.
  refine RelCT.seq (e_post (J' := JP encPW) (two_taint [.rsp] (e_pins_rsp fun s t _ h => by rw [h]; rfl)
      pro_taint.choose_spec) fun _ s t S h => by subst h; exact pro_step S.1) ?_
  -- The selectors.
  have hsel : ∀ a t, EAt H G P (JP encPW) a t →
      SelPt fb (fun a => stackArg a 6) 10 11 (fun _ => kH) (fun _ => kG) (fun a => stackArg a 12)
        (fun a => stackArg a 13) a t := by
    rintro a t ⟨s, S, k1, L1, R1, f1, -⟩
    have hp := S.1
    have hrd := k1.2.1
    have i1 := hp.arg_in hrd (j := 10) (by decide)
    have i2 := hp.arg_in hrd (j := 11) (by decide)
    have ar : ∀ m', Frame [⟨fb s, frameBytes⟩] t.mem m' →
        m'.readW (off (fb s) (frameBytes + 8 + 8 * 10)) 64 = BitVec.ofNat 64 kH ∧
          m'.readW (off (fb s) (frameBytes + 8 + 8 * 11)) 64 = BitVec.ofNat 64 kG := fun m' hm => ⟨by
      rw [arg_read hp (f1.trans hm) (j := 10) (by decide), ← hPH _ _ S.2.2]; simp, by
      rw [arg_read hp (f1.trans hm) (j := 11) (by decide), ← hPG _ _ S.2.2]; simp⟩
    have tH := hp.tab hrd f1 (j := 12) (.inl rfl)
    have tG := hp.tab hrd f1 (j := 13) (.inr rfl)
    rw [S.fb, S.arg (i := 6) (by decide)] at L1 R1
    rw [S.fb] at i1 i2 ar
    rw [S.fb, S.arg (i := 12) (by decide)] at tH
    rw [S.fb, S.arg (i := 13) (by decide)] at tG
    exact ⟨L1, ⟨_, _, R1⟩, i1, i2, ar, ⟨_, _, _, tH⟩, ⟨_, _, _, tG⟩⟩
  refine RelCT.seq (e_post (J' := JP encW) (two_map id hsel
      (selPro_ct (F := fb) (S := fun a => stackArg a 6) (kH := fun _ => kH) (kG := fun _ => kG)
        (fun _ => hkm iH) (fun _ => hkm iG) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
        ⟨_, by taint_decide⟩))
    fun _ s t S h => sel_step S.1 (by rw [hPH _ _ S.2.2]; exact iH) (by rw [hPG _ _ S.2.2]; exact iG) h) ?_
  -- The check of `k`.
  refine RelCT.seq (e_post (J' := J2 TH.S.digestBytes) (two_taint [.rsp]
      (e_pins_rsp fun s t _ h => (h.1.gpr (by decide)).trans rfl) chkK_taint.choose_spec)
    fun _ s t S h => WP.mono (chk_step S.1 (S.lenH hTH eH hPH) (by omega) h)
      fun t2 ⟨he2, L2, R2, hax2, hcf2⟩ => ⟨⟨he2, L2, _, _, R2, fun _ _ => rfl⟩, hax2, hcf2⟩) ?_
  refine e_ite (fun s => some (decide ((s.gpr .rcx).toNat < 2 * TH.S.digestBytes + 2))) (fun s t h => h.2.2)
    (fun a s S => by rw [S.k]) (e_branch (J' := EW) (fun _ _ _ h _ => h.1) zeroOut_ct)
    (e_branch (J' := J2' TH.S.digestBytes) (fun s t _ h e => ⟨h.1, h.2.1, by have := cf_false h.2.2 e; omega⟩) ?_)
  refine RelCT.seq (e_post (J' := J3 TH.S.digestBytes) (two_taint [.rsp] (e_pins_rsp fun s t _ h => h.1.he.rsp)
      chkMsg_taint.choose_spec) fun _ s t S h => chkMsg_step S.1 (S.lenH hTH eH hPH) h) ?_
  refine e_ite (fun s => some (decide ((s.gpr .rcx).toNat - (2 * TH.S.digestBytes + 2) < (stackArg s 3).toNat)))
    (fun s t h => h.2.2) (fun a s S => by rw [S.k, S.arg (i := 3) (by decide)])
    (e_branch (J' := EW) (fun _ _ _ h _ => h.1) zeroOut_ct)
    (e_branch (J' := EK TH.S.digestBytes) (fun s t _ h e => ⟨h.1, by have := cf_false h.2.2 e; have := h.2.1; omega⟩) hmain)

/-! ## The frame -/

omit hTH hTG sH sG eH eG hPH hPG hPr in
theorem alloc_push {s s₁ : State} (h : isa.push (.alloc frameBytes) s = some s₁) :
    s₁ = allocState frameBytes s := by
  simp only [isa, push] at h
  split at h
  · cases h; rfl
  · cases h

omit hTH hTG sH sG eH eG hPH hPG hPr in
/-- A frame of `frameBytes` bytes leaks what its body does. -/
theorem relCT_alloc {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState frameBytes s₁ ∧ b = allocState frameBytes s₂)
      body R) :
    RelCT isa P (.frame (.alloc frameBytes) body (.free frameBytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := alloc_push p₁
      obtain rfl := alloc_push p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

end

end VG.Proof.RsaOaep.X86_64
