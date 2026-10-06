import VerifiedGarbage.Proof.RsaOaep.X86_64.EncSteps

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
The code with `hLen` as an immediate is checked for every `hLen` up to 64.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.RsaPkcs1Sig.X86_64 (pubChecked pubChk)

/-! ## The taint checks of the code with `hLen` as an immediate -/

theorem head_taint : ∀ d < 65, (taint.check (Taint.ofRegs [.rsp]) (.block (encPrologue ++ chkK (gD d)))
    (taint.hintOf (Taint.ofRegs [.rsp]) (.block (encPrologue ++ chkK (gD 0))))).isSome = true := by
  decide +kernel

theorem chkMsg_taint : ∀ d < 65, (taint.check (Taint.ofRegs [.rsp]) (.block (chkMsg (gD d)))
    (taint.hintOf (Taint.ofRegs [.rsp]) (.block (chkMsg (gD 0))))).isSome = true := by
  decide +kernel

theorem copySeed_taint : ∀ d < 65, (taint.check (frT [] [14, 31] 2) (copySeed (gD d))
    (taint.hintOf (frT [] [14, 31] 2) (copySeed (gD 0)))).isSome = true := by
  decide +kernel

theorem copyLh_taint : ∀ d < 65, (taint.check (frT [] [14] 2) (copyLh (gD d))
    (taint.hintOf (frT [] [14] 2) (copyLh (gD 0)))).isSome = true := by
  decide +kernel

theorem dbArgs_taint : ∀ d < 65, (taint.check (frT [] [] 2) (.block (dbArgs (gD d)))
    (taint.hintOf (frT [] [] 2) (.block (dbArgs (gD 0))))).isSome = true := by
  decide +kernel

theorem seedArgs_taint : ∀ d < 65, (taint.check (frT [] [] 2) (.block (seedArgs (gD d)))
    (taint.hintOf (frT [] [] 2) (.block (seedArgs (gD 0))))).isSome = true := by
  decide +kernel

/-! ## Entry states and the anchor -/

section
variable (H G : Spec.Mgf1.Hash)

/-- An entry state with the public data of the anchor `a`. -/
def ESib (a s : State) : Prop := (encK H G).pre s ∧ (encK H G).pub a s

/-- What `J` says of a run from an entry state with the anchor's public data. -/
def EAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, ESib H G a s ∧ J s t

theorem encPub_refl (s : State) : (encK H G).pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

end

variable {H G : Spec.Mgf1.Hash}

theorem ESib.gpr {a s : State} (h : ESib H G a s) {r : Reg}
    (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem ESib.arg {a s : State} (h : ESib H G a s) {i : Nat} (hi : i < 7) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.2.1) i (List.mem_range.mpr hi)).symm

theorem ESib.fb {a s : State} (h : ESib H G a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _; rw [h.gpr (r := .rsp) (by decide)]

theorem ESib.out_eq {a s : State} (h : ESib H G a s) : outR s = outR a := by
  unfold outR; rw [h.gpr (r := .rdi) (by decide), h.gpr (r := .rsi) (by decide)]

theorem ESib.scr_eq {a s : State} (h : ESib H G a s) : scrR s = scrR a := by
  unfold scrR; rw [h.arg (i := 5) (by decide), h.arg (i := 6) (by decide)]

theorem ESib.k {a s : State} (h : ESib H G a s) : (s.gpr .rcx).toNat = (a.gpr .rcx).toNat := by
  rw [h.gpr (r := .rcx) (by decide)]

theorem ESib.w_eq {a s : State} (h : ESib H G a s) {k : Nat} (hk : k ∈ encKs) : encW s k = encW a k := by
  simp only [encKs, List.mem_cons, List.not_mem_nil, or_false] at hk
  have hW : ∀ x : State, ArgsW x (encW x) := fun _ _ _ => rfl
  obtain ⟨a14, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31⟩ := (hW a).w
  obtain ⟨s14, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31⟩ := (hW s).w
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [s14, a14, h.arg (by decide)]
  · rw [s21, a21, h.gpr (by decide)]
  · rw [s22, a22, h.gpr (by decide)]
  · rw [s23, a23, h.gpr (by decide)]
  · rw [s24, a24, h.gpr (by decide)]
  · rw [s25, a25, h.gpr (by decide)]
  · rw [s26, a26, h.arg (by decide)]
  · rw [s27, a27, h.arg (by decide)]
  · rw [s28, a28, h.arg (by decide)]
  · rw [s29, a29, h.arg (by decide)]
  · rw [s30, a30, h.arg (by decide)]
  · rw [s31, a31, h.arg (by decide)]

/-! ## The pieces -/

/-- Code the taint analysis checks from the frame's argument slots `ks`. -/
theorem e_taintF {J : State → State → Prop} (hJ : ∀ s t, (encK H G).pre s → J s t → EW s t)
    (rs : List Reg) (ks : List Nat) (hks : ∀ k ∈ ks, k ∈ encKs) (hpin : Pins (EAt H G J) rs) {c : Prog isa}
    (h : ∃ hc, (taint.check (frT rs ks 2) c hc).isSome = true) :
    RelCT isa (Two (EAt H G J)) c fun _ _ => True :=
  two_taintF rs ks fb (fun a => [outR a, scrR a]) encW (fun a t ⟨s, S, j⟩ => by
      have e := hJ s t S.1 j
      rw [← S.fb, ← S.out_eq, ← S.scr_eq]
      exact ⟨e.he.frv (EPre.of H S.1), fun k hk => (e.words k (hks k hk)).trans (S.w_eq (hks k hk))⟩)
    hpin (fun k hk => encKs_lt k (hks k hk)) h

/-- What correctness says after a piece. -/
theorem e_post {J J' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Two (EAt H G J)) c fun _ _ => True)
    (hw : ∀ s t, (encK H G).pre s → J s t → WP isa c t (J' s)) :
    RelCT isa (Two (EAt H G J)) c (Two (EAt H G J')) :=
  two_post hct fun _ t ⟨s, S, j⟩ => WP.mono (hw s t S.1 j) fun _ j' => ⟨s, S, j'⟩

theorem e_pins_rsp {J : State → State → Prop} (hJ : ∀ s t, (encK H G).pre s → J s t → t.gpr .rsp = fb s) :
    Pins (EAt H G J) [.rsp] :=
  fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ r hr => by
    rw [List.mem_singleton.mp hr, hJ _ _ S₁.1 j₁, hJ _ _ S₂.1 j₂, S₁.fb, S₂.fb]

/-- A branch on a condition that the entry state's public data fixes. -/
theorem e_ite {J : State → State → Prop} {cond : isa.Cond} {th el : Prog isa} {Q : State → State → Prop}
    (f : State → Option Bool) (hf : ∀ s t, J s t → isa.eval cond t = f s) (hs : ∀ a s, ESib H G a s → f s = f a)
    (ht : RelCT isa (Two fun a t => EAt H G J a t ∧ isa.eval cond t = some true) th Q)
    (he : RelCT isa (Two fun a t => EAt H G J a t ∧ isa.eval cond t = some false) el Q) :
    RelCT isa (Two (EAt H G J)) (.ite cond th el) Q :=
  two_ite (fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ => by rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]) ht he

/-- In a branch, what its condition says of the entry state. -/
theorem e_branch {J J' : State → State → Prop} {cond : isa.Cond} {b : Bool} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ s t, (encK H G).pre s → J s t → isa.eval cond t = some b → J' s t)
    (hct : RelCT isa (Two (EAt H G J')) c Q) :
    RelCT isa (Two fun a t => EAt H G J a t ∧ isa.eval cond t = some b) c Q :=
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

theorem pw_sib {a s : State} (S : ESib H G a s) (i : Nat) : pw s i = pw a i := by
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

/-- What `vg_rsa_public_checked`'s contract makes public, from the anchor. -/
theorem pub_view {a s t : State} (S : ESib H G a s) (h : EWP s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (pubRd s) (pubWr s)).gpr =
      [a.gpr .rdi, a.gpr .rcx, a.gpr .rdx, a.gpr .rcx, a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    (∀ i < 4, stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) i = pw a i) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (pubRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .rdx)
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (pubRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .r8)
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  have hp := EPre.of H S.1
  have hF := fb_toNat hp
  refine ⟨?_, fun i hi => ?_, ?_, ?_⟩
  · rw [e_entry_regs, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.he.rsp, S.fb, S.gpr (r := .rdi) (by decide),
      S.gpr (r := .rdx) (by decide), S.gpr (r := .rcx) (by decide), S.gpr (r := .r8) (by decide),
      S.gpr (r := .r9) (by decide)]
  · rw [stackArg_entry h.he.rsp (by have := hp.sp1; unfold encStack frameBytes at *; omega) _ _
      (by have := hp.sp2; unfold frameBytes at *; omega), h.w i hi, pw_sib S]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), h.rdx, h.rcx]
    rw [entryBytes h.he _ _ hp.d_stk_n hp.d_out_n hp.d_n_scr.symm (by have := hp.wN; omega)]
    exact S.2.2.2.1.symm
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h.r8, h.r9]
    rw [entryBytes h.he _ _ hp.d_stk_e hp.d_out_e hp.d_e_scr.symm (by have := hp.wE; omega)]
    exact S.2.2.2.2.symm

theorem call_ct : RelCT isa (Two (EAt H G EWP)) (.call pubChecked.name pubChecked.code) fun _ _ => True := by
  refine RelCT.callEx (k := pubChk) pubChecked.ok pubChecked.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  have hp₁ := EPre.of H S₁.1
  have hp₂ := EPre.of H S₂.1
  obtain ⟨r₁, g₁, n₁, e₁⟩ := pub_view S₁ j₁
  obtain ⟨r₂, g₂, n₂, e₂⟩ := pub_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := pub_covers hp₁ j₁.he.rd j₁.he.wr
  obtain ⟨c₂, w₂⟩ := pub_covers hp₂ j₂.he.rd j₂.he.wr
  have p₁ := pub_pre hp₁ j₁.he.rsp (fb s₁) rfl (j₁.w 0 (by decide)) (j₁.w 1 (by decide)) (j₁.w 2 (by decide))
    (j₁.w 3 (by decide)) j₁.rdi j₁.rsi j₁.rdx j₁.rcx j₁.r8 j₁.r9
  have p₂ := pub_pre hp₂ j₂.he.rsp (fb s₂) rfl (j₂.w 0 (by decide)) (j₂.w 1 (by decide)) (j₂.w 2 (by decide))
    (j₂.w 3 (by decide)) j₂.rdi j₂.rsi j₂.rdx j₂.rcx j₂.r8 j₂.r9
  refine ⟨pubRd s₁, pubWr s₁, pubRd s₂, pubWr s₂, p₁, p₂, ⟨List.map_inj_left.mp (r₁.trans r₂.symm),
    (g₁ 0 (by decide)).trans (g₂ 0 (by decide)).symm, (g₁ 1 (by decide)).trans (g₂ 1 (by decide)).symm,
    (g₁ 2 (by decide)).trans (g₂ 2 (by decide)).symm, (g₁ 3 (by decide)).trans (g₂ 3 (by decide)).symm,
    n₁.trans n₂.symm, e₁.trans e₂.symm⟩, c₁, w₁, c₂, w₂, by rw [j₁.he.rsp, j₂.he.rsp, S₁.fb, S₂.fb]⟩

/-! ## `encMain` -/

section
variable {Hl Gm : Hash} (hH : HashOK Hl) (KH : Callees Hl) (hG : HashOK Gm) (KG : Callees Gm)
  (mH : MgfLink Hl hH) (mG : MgfLink Gm hG)

/-- In the frame, after the checks. -/
def EK (D : Nat) (s t : State) : Prop := EW s t ∧ 2 * D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat

/-- Before MGF1. -/
def EKM (D : Nat) (src srcLen dst dstLen : State → Nat) (s t : State) : Prop :=
  EWM s t (src s) (srcLen s) (dst s) (dstLen s) ∧ 2 * D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat

/-- The label's hash's public data. -/
def lq (a : State) : LQ := ⟨fb a, stackArg a 5, [outR a, scrR a], stackArg a 0, (stackArg a 1).toNat⟩

/-- MGF1's public data. -/
def mq (src srcLen dst dstLen : State → Nat) (a : State) : MQ :=
  ⟨fb a, stackArg a 5, [outR a, scrR a], src a, srcLen a, dst a, dstLen a⟩

include hH KH mH in
theorem encEm_ct : RelCT isa (Two (EAt mH.G mG.G (EK Hl.D))) (encEm Hl.stream) (Two (EAt mH.G mG.G (EK Hl.D))) := by
  have hz := sizes hH.stream
  have hsD : Hl.stream.D = Hl.D := rfl
  have hD65 : Hl.D < 65 := by omega
  unfold encEm seqs seqs seqs seqs
  refine RelCT.seq (e_post (J' := EK Hl.D) (e_taintF (fun _ _ _ h => h.1) [] [14] (by decide) nopin ⟨_, by taint_decide⟩)
    fun s t hs h => WP.mono (ew_clearEm h.1) fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK Hl.D) (e_taintF (fun _ _ _ h => h.1) [] [14, 31] (by decide) nopin
      ⟨_, copySeed_taint Hl.D hD65⟩)
    fun s t hs h => WP.mono (ew_copySeed (EPre.of _ hs) (Hm := Hl.stream) mH.len (by omega) (by omega) h.1)
      fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK Hl.D) (two_map lq (fun a t ⟨s, S, e, _⟩ => by
      have hp := EPre.of _ S.1
      obtain ⟨V, W, R, hW⟩ := e.rep
      have := (⟨e.he.frv hp, e.L, V, W, R, e.lab hp hW⟩ : LW 2 (lq s) t)
      simp only [lq] at this ⊢
      rwa [S.fb, S.out_eq, S.scr_eq, S.arg (i := 5) (by decide), S.arg (i := 0) (by decide),
        S.arg (i := 1) (by decide)] at this) (hashLabel_ct hH.stream 2 (.inl rfl) (Or.inl rfl)))
    fun s t hs h => WP.mono (ew_hashLabel (EPre.of _ hs) hH KH mH h.1) fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK Hl.D) (e_taintF (fun _ _ _ h => h.1) [] [14] (by decide) nopin
      ⟨_, copyLh_taint Hl.D hD65⟩)
    fun s t hs h => WP.mono (ew_copyLh (Hm := Hl.stream) (by omega) (by omega) h.1) fun _ e => ⟨e, h.2⟩) ?_
  exact e_post (J' := EK Hl.D) (e_taintF (fun _ _ _ h => h.1) [] [14, 23, 29, 30] (by decide) nopin ⟨_, by taint_decide⟩)
    fun s t hs h => WP.mono (ew_putMsg (EPre.of _ hs) h.2 h.1) fun _ e => ⟨e, h.2⟩


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

/-- Where MGF1 starts, for the anchor's public data. -/
theorem me_of {src srcLen dst dstLen : Nat → Nat} {a s t : State} (S : ESib H G a s)
    (h : EWM s t (src (s.gpr .rcx).toNat) (srcLen (s.gpr .rcx).toNat) (dst (s.gpr .rcx).toNat)
      (dstLen (s.gpr .rcx).toNat))
    (hf : MFit (src (s.gpr .rcx).toNat) (srcLen (s.gpr .rcx).toNat) (dst (s.gpr .rcx).toNat)
      (dstLen (s.gpr .rcx).toNat)) :
    ME 2 ⟨fb a, stackArg a 5, [outR a, scrR a], src (a.gpr .rcx).toNat, srcLen (a.gpr .rcx).toNat,
      dst (a.gpr .rcx).toNat, dstLen (a.gpr .rcx).toNat⟩ t := by
  have hp := EPre.of H S.1
  obtain ⟨V, W, R, _, A⟩ := h.rep
  have := (⟨h.he.frv hp, h.L, hf, V, W, R, A⟩ : ME 2 ⟨fb s, stackArg s 5, [outR s, scrR s],
    src (s.gpr .rcx).toNat, srcLen (s.gpr .rcx).toNat, dst (s.gpr .rcx).toNat, dstLen (s.gpr .rcx).toNat⟩ t)
  rwa [S.fb, S.out_eq, S.scr_eq, S.arg (i := 5) (by decide), S.k] at this

include hH KH hG KG mH mG in
theorem encMain_ct : RelCT isa (Two (EAt mH.G mG.G (EK Hl.D)))
    (encMain Hl.stream Gm.stream pubChecked.name pubChecked.code) fun _ _ => True := by
  have hz := sizes hH.stream
  have hsD : Hl.stream.D = Hl.D := rfl
  have hD65 : Hl.D < 65 := by omega
  have hD0 := hH.hD0
  unfold encMain seqs seqs seqs seqs seqs seqs
  refine RelCT.seq (encEm_ct (hH := hH) (KH := KH) (mH := mH) (mG := mG)) ?_
  -- `DB` masked.
  refine RelCT.seq (e_post (J' := fun s t => EWM s t (oEm + 1) Hl.D (oEm + 1 + Hl.D)
      ((s.gpr .rcx).toNat - (Hl.D + 1)) ∧ 2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat)
    (e_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin ⟨_, dbArgs_taint Hl.D hD65⟩)
    fun s t hs h => WP.mono (ew_dbArgs (Hm := Hl.stream) (by omega) (by have := h.2; omega) h.1) fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK Hl.D) (two_map (fun a => (⟨fb a, stackArg a 5, [outR a, scrR a], oEm + 1, Hl.D,
      oEm + 1 + Hl.D, (a.gpr .rcx).toNat - (Hl.D + 1)⟩ : MQ))
      (fun a t ⟨s, S, e, hk⟩ => me_of (src := fun _ => oEm + 1) (srcLen := fun _ => Hl.D)
        (dst := fun _ => oEm + 1 + Hl.D) (dstLen := fun k => k - (Hl.D + 1)) S e (fit_db (EPre.of _ S.1) hk))
      (mgf_ct hG.stream 2 mG.hash mG.len (valid_of_link hG mG) (.inl rfl)))
    fun s t hs h => WP.mono (ew_mgf hG KG mG (fit_db (EPre.of _ hs) h.2) h.1) fun _ e => ⟨e, h.2⟩) ?_
  -- The seed masked.
  refine RelCT.seq (e_post (J' := fun s t => EWM s t (oEm + 1 + Hl.D) ((s.gpr .rcx).toNat - (Hl.D + 1)) (oEm + 1)
      Hl.D ∧ 2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat)
    (e_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin ⟨_, seedArgs_taint Hl.D hD65⟩)
    fun s t hs h => WP.mono (ew_seedArgs (Hm := Hl.stream) (by omega) (by have := h.2; omega) h.1) fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK Hl.D) (two_map (fun a => (⟨fb a, stackArg a 5, [outR a, scrR a],
      oEm + 1 + Hl.D, (a.gpr .rcx).toNat - (Hl.D + 1), oEm + 1, Hl.D⟩ : MQ))
      (fun a t ⟨s, S, e, hk⟩ => me_of (src := fun _ => oEm + 1 + Hl.D) (srcLen := fun k => k - (Hl.D + 1))
        (dst := fun _ => oEm + 1) (dstLen := fun _ => Hl.D) S e (fit_seed (EPre.of _ S.1) hk hD0))
      (mgf_ct hG.stream 2 mG.hash mG.len (valid_of_link hG mG) (.inl rfl)))
    fun s t hs h => WP.mono (ew_mgf hG KG mG (fit_seed (EPre.of _ hs) h.2 hD0) h.1) fun _ e => ⟨e, h.2⟩) ?_
  -- The call.
  refine RelCT.seq (e_post (J' := EWP) (e_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin ⟨_, by taint_decide⟩)
    fun s t hs h => ew_pubArgs h.1) ?_
  exact call_ct


/-! ## The checks -/

omit hH KH hG KG mH mG in
theorem zeroOut_ct : RelCT isa (Two (EAt H G EW)) zeroOut fun _ _ => True :=
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

omit KH KG in
theorem chkMsg_step {s t : State} (hs : (encK mH.G mG.G).pre s) (h : J2' Hl.D s t) :
    WP isa (.block (chkMsg Hl.stream)) t (J3 Hl.D s) := by
  have hp := EPre.of _ hs
  have hk1 := hp.k1; have hk2 := hp.k2
  have hz := sizes hH.stream
  have hsD : Hl.stream.D = Hl.D := rfl
  obtain ⟨e, hax, hk⟩ := h
  obtain ⟨V, W, R, hW⟩ := e.rep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, w30, -⟩ := hW.w
  refine WP.mono (wp_good (block_good _ rfl) (chkMsg_ok (Hm := Hl.stream) e.L R (k := (s.gpr .rcx).toNat)
    (mLen := (stackArg s 3).toNat) (by rw [w30, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hax (by omega)
    (by omega) (stackArg s 3).isLt (by omega)))
    fun t3 ⟨⟨k3, hm3, hcf3⟩, sp3, mx3, f3⟩ => ⟨⟨e.he.step k3.2.1 k3.2.2 sp3 (keep_cs3 k3 (by decide)) mx3 f3,
      e.L.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3]), V, W, hm3 ▸ R, hW⟩, hk, by rw [hcf3, hsD]⟩

/-- After the prologue. -/
def JA (s t : State) : Prop := t = allocState frameBytes s

include hH KH hG KG mH mG in
theorem encBody_ct : RelCT isa (Two (EAt mH.G mG.G JA))
    (encBody Hl.stream Gm.stream pubChecked.name pubChecked.code) fun _ _ => True := by
  have hz := sizes hH.stream
  have hsD : Hl.stream.D = Hl.D := rfl
  have hD65 : Hl.D < 65 := by omega
  unfold encBody seqs seqs seqs
  refine RelCT.seq (e_post (J' := J2 Hl.D) (two_taint [.rsp] (e_pins_rsp fun s t _ h => by rw [h]; rfl)
      (head_taint Hl.D hD65))
    fun s t hs h => by
      subst h
      exact WP.mono (encHead_ok (Hm := Hl.stream) (EPre.of _ hs) (by omega))
        fun t2 ⟨he2, L2, R2, hax2, hcf2⟩ => ⟨⟨he2, L2, _, _, R2, fun _ _ => rfl⟩, hax2, hcf2⟩) ?_
  refine e_ite (fun s => some (decide ((s.gpr .rcx).toNat < 2 * Hl.D + 2))) (fun s t h => h.2.2)
    (fun a s S => by rw [S.k]) (e_branch (J' := EW) (fun _ _ _ h _ => h.1) zeroOut_ct)
    (e_branch (J' := J2' Hl.D) (fun s t _ h e => ⟨h.1, h.2.1, by have := cf_false h.2.2 e; omega⟩) ?_)
  refine RelCT.seq (e_post (J' := J3 Hl.D) (two_taint [.rsp] (e_pins_rsp fun s t _ h => h.1.he.rsp)
      (chkMsg_taint Hl.D hD65)) fun s t hs h => chkMsg_step (hH := hH) (hG := hG) (mH := mH) (mG := mG) hs h) ?_
  refine e_ite (fun s => some (decide ((s.gpr .rcx).toNat - (2 * Hl.D + 2) < (stackArg s 3).toNat)))
    (fun s t h => h.2.2) (fun a s S => by rw [S.k, S.arg (i := 3) (by decide)])
    (e_branch (J' := EW) (fun _ _ _ h _ => h.1) zeroOut_ct)
    (e_branch (J' := EK Hl.D) (fun s t _ h e => ⟨h.1, by have := cf_false h.2.2 e; have := h.2.1; omega⟩)
      (encMain_ct hH KH hG KG mH mG))

/-! ## The frame -/

omit hH KH hG KG mH mG in
theorem alloc_push {s s₁ : State} (h : isa.push (.alloc frameBytes) s = some s₁) :
    s₁ = allocState frameBytes s := by
  simp only [isa, push] at h
  split at h
  · cases h; rfl
  · cases h

omit hH KH hG KG mH mG in
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

include hH KH hG KG mH mG in
theorem enc_constantTime : ConstantTime isa (encK mH.G mG.G).pre (encK mH.G mG.G).pub
    (encrypt Hl.stream Gm.stream pubChecked.name pubChecked.code) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (relCT_alloc ((encBody_ct hH KH hG KG mH mG).mono ?_
    fun _ _ h => h))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, rfl, rfl⟩
  exact ⟨s₁, ⟨s₁, ⟨h₁, encPub_refl _ _ s₁⟩, rfl⟩, ⟨s₂, ⟨h₂, hpub⟩, rfl⟩⟩

include hH KH hG KG mH mG in
/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt` meets the shared contract. -/
theorem enc_verified (hsat : ∃ s, (Spec.RsaOaep.encryptContract mH.G mG.G abi encStack).pre s) :
    Verified target (encrypt Hl.stream Gm.stream pubChecked.name pubChecked.code)
      (Spec.RsaOaep.encryptContract mH.G mG.G abi encStack) :=
  Verified.of_correct (k := encK mH.G mG.G) (enc_correct hH KH hG KG mH mG)
    (enc_constantTime hH KH hG KG mH mG) (enc_implies mH.G mG.G hsat)

end

end VG.Proof.RsaOaep.X86_64
