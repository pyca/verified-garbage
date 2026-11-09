module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncSteps
public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelTCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCorrect
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Spec.RsaPkcs1Sig
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncSteps
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelTCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCorrect
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
meta import VerifiedGarbage.Spec.RsaPkcs1Sig
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCtx
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub

/-!
# RSAES-OAEP encryption on x86-64: constant time

Each point of the code is described, in each run, by what correctness says of
it from that run's entry state, which has the same public data as an anchor
(`EAt`, as in `Proof/RsaPkcs1Sig/X86_64/SignCT.lean`). The pieces between the
calls are checked by the taint analysis from the frame's public slots
(`e_taintF`); the branches are on `k` and the message's length, which are
public; MGF1 and the label's hash (`hashLabel_ct`) are constant time for the
same public data in both runs; and the call of
`vg_rsa_public_checked` is constant time for its contract, whose public data
(its registers, its stack arguments, `n` and `e`) are the same in both runs.
The code with `hLen` as an immediate is checked for every `hLen` up to 64.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.RsaPkcs1Sig.X86_64 (pubChecked pubChk)

/-! ## The taint checks of the code with `hLen` as an immediate -/

theorem pro_taint : (taint.check (Taint.ofRegs [.rsp]) (.block encPrologue)
    (taint.hintOf (Taint.ofRegs [.rsp]) (.block encPrologue))).isSome = true := by
  taint_decide

theorem chkK_taint : ∀ d < 65, (taint.check (Taint.ofRegs [.rsp]) (.block (chkK (gD d)))
    (taint.hintOf (Taint.ofRegs [.rsp]) (.block (chkK (gD 0))))).isSome = true := by
  decide +kernel

theorem etabSlot_taint : ∃ hc, (taint.check (frT [] [] 2) (.block (tabSlot 10)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem elenLoad_taint : ∃ hc, (taint.check (frT [] [35] 2) (.block lenLoad) hc).isSome = true :=
  ⟨_, by taint_decide⟩

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
variable (H G : Spec.Mgf1.Hash) (P : State → State → Prop)

/-- An entry state with the public data of the anchor `a`, and what `P`
relates them by: more public data, for a variant with more arguments
(`PcCT`). -/
def ESib (a s : State) : Prop := EPre H s ∧ (encK H G).pub a s ∧ P a s

/-- What `J` says of a run from an entry state with the anchor's public data. -/
def EAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, ESib H G P a s ∧ J s t

theorem encPub_refl (s : State) : (encK H G).pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

end

variable {H G : Spec.Mgf1.Hash} {P : State → State → Prop}

theorem ESib.gpr {a s : State} (h : ESib H G P a s) {r : Reg}
    (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r := (h.2.1.1 r hr).symm

theorem ESib.arg {a s : State} (h : ESib H G P a s) {i : Nat} (hi : i < 8) : stackArg s i = stackArg a i :=
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
theorem e_taintF {J : State → State → Prop} (hJ : ∀ s t, EPre H s → J s t → EW s t)
    (rs : List Reg) (ks : List Nat) (hks : ∀ k ∈ ks, k ∈ encKs) (hpin : Pins (EAt H G P J) rs) {c : Prog isa}
    (h : ∃ hc, (taint.check (frT rs ks 2) c hc).isSome = true) :
    RelCT isa (Two (EAt H G P J)) c fun _ _ => True :=
  two_taintF rs ks fb (fun a => [outR a, scrR a]) encW (fun a t ⟨s, S, j⟩ => by
      have e := hJ s t S.1 j
      rw [← S.fb, ← S.out_eq, ← S.scr_eq]
      exact ⟨e.he.frv S.1, fun k hk => (e.words k (hks k hk)).trans (S.w_eq (hks k hk))⟩)
    hpin (fun k hk => encKs_lt k (hks k hk)) h

/-- What correctness says after a piece, from what the entry state's
relation to the anchor says too. -/
theorem e_postS {J J' : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (EAt H G P J)) c fun _ _ => True)
    (hw : ∀ a s t, ESib H G P a s → J s t → WP isa c t (J' s)) :
    RelCT isa (Two (EAt H G P J)) c (Two (EAt H G P J')) :=
  two_post hct fun a t ⟨s, S, j⟩ => WP.mono (hw a s t S j) fun _ j' => ⟨s, S, j'⟩

/-- What correctness says after a piece. -/
theorem e_post {J J' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Two (EAt H G P J)) c fun _ _ => True)
    (hw : ∀ s t, EPre H s → J s t → WP isa c t (J' s)) :
    RelCT isa (Two (EAt H G P J)) c (Two (EAt H G P J')) :=
  two_post hct fun _ t ⟨s, S, j⟩ => WP.mono (hw s t S.1 j) fun _ j' => ⟨s, S, j'⟩

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
variable {Hl Gm : Hash} (hH : HashOK Hl) (KH : Callees Hl) (hG : HashOK Gm) (KG : Callees Gm)
  (mH : MgfLink Hl hH) (mG : MgfLink Gm hG)

/-- In the frame, after the checks, with the entry state's addresses of
statics. -/
def EK (D : Nat) (s t : State) : Prop :=
  EW s t ∧ 2 * D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat ∧ t.syms = s.syms

/-- The label's hash's public data. -/
def lq (a : State) : LQ := ⟨fb a, stackArg a 6, [outR a, scrR a], stackArg a 0, (stackArg a 1).toNat⟩

/-- The label's hash's public data with its table, the stack argument 10. -/
def lqtE (Hm : Hash) (a : State) : LQT :=
  ⟨lq a, stackArg a 10, a.syms Hm.initN, a.syms Hm.updN, a.syms Hm.finN⟩

omit hH KH hG KG mH mG in
/-- `EW` in a state with the flags of another. -/
theorem EW.after {s t t' : State} (h : EW s t) (k : Keep [] t t') (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) : EW s t' :=
  let ⟨V, W, R, hW⟩ := h.rep
  ⟨h.he.step k.2.1 k.2.2 (k.gpr (by simp)) (keep_cs3 k rfl) hmx (by rw [hm]; exact Frame.refl _ _),
    h.L.congr (k.gpr (by simp)) k.2.2 (by rw [hm]), V, W, hm ▸ R, hW⟩

omit hH KH hG KG mH mG in
/-- The table's address to its slot, from a state in the frame. -/
theorem ew_tabSlot {s t : State} {G' : Stream} {f : Impl.Mgf1.X86_64.Table.Fns} (h : EW s t)
    (T : Table.Tab G' f (fb s) (stackArg s 10) (frameBytes + 8 + 8 * 10) t) :
    WP isa (.block (tabSlot 10)) t fun t' => (EW s t' ∧ word t'.mem (fb s) (8 * 35) = stackArg s 10) ∧
      t'.syms = t.syms := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  exact WP.mono (wp_good (block_good _ rfl) (tabSlot_ok h.L R T)) fun t' ⟨⟨k, L', R', sy⟩, sp, mx, f'⟩ =>
    ⟨⟨⟨h.he.step k.2.1 k.2.2 sp (keep_cs3 k (by decide)) mx f', L', V, _, R', fun k hk => by
      simp only [upd]; rw [ifn (by omega)]; exact hW k hk⟩, by rw [R'.fr 35 (by decide)]; simp [upd]⟩, sy⟩

include hH mH in
/-- `EM` before masking, with the label's hash function that of the table at
the stack argument 10 (`hT`), whose address (`harg`) and functions'
addresses (`hsym`) the anchor's public data fixes. -/
theorem encEm_ct {f : Impl.Mgf1.X86_64.Table.Fns} (hgi : Table.FnsGood f.init) (hgu : Table.FnsGood f.upd)
    (hgf : Table.FnsGood f.fin)
    (hT : ∀ a s t, ESib mH.G mG.G P a s → EnvE s t → t.syms = s.syms →
      Table.Tab Hl.stream f (fb s) (stackArg s 10) (frameBytes + 8 + 8 * 10) t)
    (harg : ∀ a s, ESib mH.G mG.G P a s → stackArg s 10 = stackArg a 10)
    (hsym : ∀ a s, ESib mH.G mG.G P a s →
      s.syms Hl.initN = a.syms Hl.initN ∧ s.syms Hl.updN = a.syms Hl.updN ∧ s.syms Hl.finN = a.syms Hl.finN) :
    RelCT isa (Two (EAt mH.G mG.G P (EK Hl.D))) (encEm Hl.stream f) (Two (EAt mH.G mG.G P (EK Hl.D))) := by
  have hz := sizes hH.stream
  have hsD : Hl.stream.D = Hl.D := rfl
  have hD65 : Hl.D < 65 := by omega
  unfold encEm seqs seqs seqs seqs seqs
  refine RelCT.seq (e_post (J' := EK Hl.D) (e_taintF (fun _ _ _ h => h.1) [] [14] (by decide) nopin ⟨_, by taint_decide⟩)
    fun s t hs h => WP.mono_syms (ew_clearEm h.1) fun _ e sy => ⟨e, h.2.1, sy.trans h.2.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK Hl.D) (e_taintF (fun _ _ _ h => h.1) [] [14, 31] (by decide) nopin
      ⟨_, copySeed_taint Hl.D hD65⟩)
    fun s t hs h => WP.mono_syms (ew_copySeed hs (Hm := Hl.stream) mH.len (by omega) (by omega) h.1)
      fun _ e sy => ⟨e, h.2.1, sy.trans h.2.2⟩) ?_
  -- The table's address to its slot.
  refine RelCT.seq (e_postS (J' := fun s t => EK Hl.D s t ∧ word t.mem (fb s) (8 * 35) = stackArg s 10)
    (e_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin etabSlot_taint)
    fun a s t S h => WP.mono (ew_tabSlot h.1 (hT a s t S h.1.he h.2.2)) fun _ ⟨⟨e, h35⟩, sy⟩ =>
      ⟨⟨e, h.2.1, sy.trans h.2.2⟩, h35⟩) ?_
  -- The label's hash.
  refine RelCT.seq (e_postS (J' := EK Hl.D) (two_map (lqtE Hl) (fun a t ⟨s, S, ⟨e, _, sy⟩, h35⟩ => by
      have hp := S.1
      obtain ⟨V, W, R, hW⟩ := e.rep
      have := (⟨⟨e.he.frv hp, e.L, V, W, R, e.lab hp hW⟩, h35, ⟨t, _, hT a s t S e.he sy, Table.TJ.refl t _, rfl, rfl⟩,
        by rw [sy]; rfl, by rw [sy]; rfl, by rw [sy]; rfl⟩ : LWT Hl.stream f 2 (lqtE Hl s) t)
      obtain ⟨y1, y2, y3⟩ := hsym a s S
      simp only [lqtE, lq] at this ⊢
      rwa [S.fb, S.out_eq, S.scr_eq, S.arg (i := 6) (by decide), S.arg (i := 0) (by decide),
        S.arg (i := 1) (by decide), harg a s S, y1, y2, y3] at this)
      (hashLabelT_ct hH.stream hgi hgu (.inl rfl) (Or.inl rfl)))
    fun a s t S h => WP.mono_syms (ew_hashLabelT S.1 hH mH hgi hgu hgf h.1.1 h.2 (hT a s t S h.1.1.he h.1.2.2))
      fun _ e sy => ⟨e, h.1.2.1, sy.trans h.1.2.2⟩) ?_
  refine RelCT.seq (e_post (J' := EK Hl.D) (e_taintF (fun _ _ _ h => h.1) [] [14] (by decide) nopin
      ⟨_, copyLh_taint Hl.D hD65⟩)
    fun s t hs h => WP.mono_syms (ew_copyLh (Hm := Hl.stream) (by omega) (by omega) h.1)
      fun _ e sy => ⟨e, h.2.1, sy.trans h.2.2⟩) ?_
  exact e_post (J' := EK Hl.D) (e_taintF (fun _ _ _ h => h.1) [] [14, 23, 29, 30] (by decide) nopin ⟨_, by taint_decide⟩)
    fun s t hs h => WP.mono_syms (ew_putMsg hs h.2.1 h.1) fun _ e sy => ⟨e, h.2.1, sy.trans h.2.2⟩


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
theorem me_of {src srcLen dst dstLen : Nat → Nat} {a s t : State} (S : ESib H G P a s)
    (h : EWM s t (src (s.gpr .rcx).toNat) (srcLen (s.gpr .rcx).toNat) (dst (s.gpr .rcx).toNat)
      (dstLen (s.gpr .rcx).toNat))
    (hf : MFit (src (s.gpr .rcx).toNat) (srcLen (s.gpr .rcx).toNat) (dst (s.gpr .rcx).toNat)
      (dstLen (s.gpr .rcx).toNat)) :
    ME 2 ⟨fb a, stackArg a 6, [outR a, scrR a], src (a.gpr .rcx).toNat, srcLen (a.gpr .rcx).toNat,
      dst (a.gpr .rcx).toNat, dstLen (a.gpr .rcx).toNat⟩ t := by
  have hp := S.1
  obtain ⟨V, W, R, _, A⟩ := h.rep
  have := (⟨h.he.frv hp, h.L, hf, V, W, R, A⟩ : ME 2 ⟨fb s, stackArg s 6, [outR s, scrR s],
    src (s.gpr .rcx).toNat, srcLen (s.gpr .rcx).toNat, dst (s.gpr .rcx).toNat, dstLen (s.gpr .rcx).toNat⟩ t)
  rwa [S.fb, S.out_eq, S.scr_eq, S.arg (i := 6) (by decide), S.k] at this

/-! ## The checks -/

omit hH KH hG KG mH mG in
theorem zeroOut_ct : RelCT isa (Two (EAt H G P EW)) zeroOut fun _ _ => True :=
  e_taintF (fun _ _ _ h => h) [] [21, 23] (by decide) nopin ⟨_, by taint_decide⟩

/-- After the check of `k`. -/
def J2 (D : Nat) (s t : State) : Prop :=
  EW s t ∧ t.gpr .rax = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧ t.cf = some (decide ((s.gpr .rcx).toNat < 2 * D + 2)) ∧
    t.syms = s.syms

/-- After the check of `k`, which passed. -/
def J2' (D : Nat) (s t : State) : Prop :=
  EW s t ∧ t.gpr .rax = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧ 2 * D + 2 ≤ (s.gpr .rcx).toNat ∧ t.syms = s.syms

/-- After the check of the message's length. -/
def J3 (D : Nat) (s t : State) : Prop :=
  EW s t ∧ 2 * D + 2 ≤ (s.gpr .rcx).toNat ∧
    t.cf = some (decide ((s.gpr .rcx).toNat - (2 * D + 2) < (stackArg s 3).toNat)) ∧ t.syms = s.syms

theorem cf_false {t : State} {p : Prop} [Decidable p] (h : t.cf = some (decide p))
    (e : isa.eval .b t = some false) : ¬ p := by
  have e' : t.cf = some false := e
  rw [h] at e'
  simpa using e'

omit KH KG in
theorem chkMsg_step {s t : State} (hs : EPre mH.G s) (h : J2' Hl.D s t) :
    WP isa (.block (chkMsg Hl.stream)) t (J3 Hl.D s) := by
  have hp := hs
  have hk1 := hp.k1; have hk2 := hp.k2
  have hz := sizes hH.stream
  have hsD : Hl.stream.D = Hl.D := rfl
  obtain ⟨e, hax, hk, hsy⟩ := h
  obtain ⟨V, W, R, hW⟩ := e.rep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, w30, -⟩ := hW.w
  refine WP.mono_syms (wp_good (block_good _ rfl) (chkMsg_ok (Hm := Hl.stream) e.L R (k := (s.gpr .rcx).toNat)
    (mLen := (stackArg s 3).toNat) (by rw [w30, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hax (by omega)
    (by omega) (stackArg s 3).isLt (by omega)))
    fun t3 ⟨⟨k3, hm3, hcf3⟩, sp3, mx3, f3⟩ sy => ⟨⟨e.he.step k3.2.1 k3.2.2 sp3 (keep_cs3 k3 (by decide)) mx3 f3,
      e.L.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3]), V, W, hm3 ▸ R, hW⟩, hk, by rw [hcf3, hsD], sy.trans hsy⟩

/-- After the prologue. -/
def JA (s t : State) : Prop := t = allocState frameBytes s

include hH mH mG in
/-- The prologue, the branch on the digest length of the table at the stack
argument 10 (`hT`, `harg`) and the checks, then `main`, constant time if
`main` is. -/
theorem encBodyWith_ct {f : Impl.Mgf1.X86_64.Table.Fns} {main : Nat → Prog isa}
    (hT : ∀ a s t, ESib mH.G mG.G P a s → EnvE s t → t.syms = s.syms →
      Table.Tab Hl.stream f (fb s) (stackArg s 10) (frameBytes + 8 + 8 * 10) t)
    (harg : ∀ a s, ESib mH.G mG.G P a s → stackArg s 10 = stackArg a 10)
    (hmain : RelCT isa (Two (EAt mH.G mG.G P (EK Hl.D))) (main Hl.D) fun _ _ => True) :
    RelCT isa (Two (EAt mH.G mG.G P JA)) (encBodyWith main) fun _ _ => True := by
  have hz := sizes hH.stream
  have hsD : Hl.stream.D = Hl.D := rfl
  have hD65 : Hl.D < 65 := by omega
  have hDl : Hl.D ∈ lens := by rw [← mH.len]; exact mem_lens mH.mem
  unfold encBodyWith seqs seqs seqs
  -- The prologue.
  refine RelCT.seq (e_post (J' := fun s t => EW s t ∧ t.syms = s.syms)
    (two_taint [.rsp] (e_pins_rsp fun s t _ h => by rw [h]; rfl) pro_taint)
    fun s t hs h => by
      subst h
      exact WP.mono_syms (encHead_ok hs) fun t1 ⟨he1, L1, R1⟩ sy => ⟨⟨he1, L1, _, _, R1, fun _ _ => rfl⟩, sy⟩) ?_
  -- The table's address to its slot, and its digest length to `r11`.
  refine RelCT.seq (e_postS (J' := fun s t => (EW s t ∧ word t.mem (fb s) (8 * 35) = stackArg s 10) ∧
      t.syms = s.syms)
    (e_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin etabSlot_taint)
    fun a s t S h => WP.mono (ew_tabSlot h.1 (hT a s t S h.1.he h.2)) fun _ ⟨e, sy⟩ => ⟨e, sy.trans h.2⟩) ?_
  refine RelCT.seq (e_postS (J' := fun s t => EW s t ∧ t.syms = s.syms ∧ t.gpr .r11 = BitVec.ofNat 64 Hl.D)
    (two_taintF [] [35] fb (fun a => [outR a, scrR a]) (fun a _ => stackArg a 10)
      (fun a t ⟨s, S, ⟨⟨e, h35⟩, _⟩⟩ => by
        rw [← S.fb, ← S.out_eq, ← S.scr_eq, ← harg a s S]
        refine ⟨e.he.frv S.1, fun k hk => ?_⟩
        simp only [List.mem_singleton] at hk; subst hk
        exact h35)
      nopin (by decide) elenLoad_taint)
    fun a s t S h => by
      obtain ⟨⟨e, h35⟩, sy⟩ := h
      obtain ⟨V, W, R, hW⟩ := e.rep
      have T := hT a s t S e.he sy
      exact WP.mono (wp_good (block_good _ rfl) (lenLoad_ok e.L R ((R.fr 35 (by decide)).symm.trans h35) T.rdD
          (T.mem _ (Frame.refl _ _)).2.1))
        fun t' ⟨⟨k, h11, hm, sy'⟩, sp, mx, f'⟩ => ⟨⟨e.he.step k.2.1 k.2.2 sp (keep_cs3 k (by decide)) mx f',
          e.L.congr (k.gpr (by decide)) k.2.2 (by rw [hm]), V, W, hm ▸ R, hW⟩, sy'.trans sy, h11⟩) ?_
  -- The checks for that length.
  refine byLen_ct (fun _ => Hl.D) cmpLens_taint (fun a t ⟨_, _, ⟨_, _, h11⟩⟩ => ⟨h11, hDl, mem_lens_lt hDl⟩)
    fun d _ => ?_
  by_cases hdd : Hl.D = d
  swap
  · exact RelCT.of_false fun _ _ ⟨_, ⟨_, e⟩, _⟩ => hdd e
  subst hdd
  rw [encChecks_D (G := ofLen Hl.D) (G' := Hl.stream) rfl]
  refine (?_ : RelCT isa (Two (EAt mH.G mG.G P fun s t => EW s t ∧ t.syms = s.syms))
    (encChecks Hl.stream (main Hl.D)) _).mono (fun _ _ ⟨a, ⟨⟨t₁, ⟨s₁, S₁, j₁⟩, k₁, m₁, y₁, x₁⟩, _⟩,
      ⟨⟨t₂, ⟨s₂, S₂, j₂⟩, k₂, m₂, y₂, x₂⟩, _⟩⟩ =>
    ⟨a, ⟨s₁, S₁, j₁.1.after k₁ m₁ x₁, y₁.trans j₁.2.1⟩, ⟨s₂, S₂, j₂.1.after k₂ m₂ x₂, y₂.trans j₂.2.1⟩⟩)
    fun _ _ h => h
  unfold encChecks seqs seqs seqs
  refine RelCT.seq (e_post (J' := J2 Hl.D) (two_taint [.rsp] (e_pins_rsp fun s t _ h => h.1.he.rsp)
      (chkK_taint Hl.D hD65))
    fun s t hs h => by
      obtain ⟨e, sy⟩ := h
      obtain ⟨V, W, R, hW⟩ := e.rep
      obtain ⟨-, -, -, w23, -⟩ := hW.w
      have hk1 := hs.k1; have hk2 := hs.k2
      exact WP.mono_syms (wp_good (block_good _ rfl) (chkK_ok (Hm := Hl.stream) e.L R
          (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega) (by omega)))
        fun t2 ⟨⟨k2, hm2, hax2, hcf2⟩, sp2, mx2, f2⟩ sy2 => ⟨⟨e.he.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide))
          mx2 f2, e.L.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), V, W, hm2 ▸ R, hW⟩, hax2,
          by rw [hcf2, hsD], sy2.trans sy⟩) ?_
  refine e_ite (fun s => some (decide ((s.gpr .rcx).toNat < 2 * Hl.D + 2))) (fun s t h => h.2.2.1)
    (fun a s S => by rw [S.k]) (e_branch (J' := EW) (fun _ _ _ h _ => h.1) zeroOut_ct)
    (e_branch (J' := J2' Hl.D) (fun s t _ h e => ⟨h.1, h.2.1, by have := cf_false h.2.2.1 e; omega, h.2.2.2⟩) ?_)
  refine RelCT.seq (e_post (J' := J3 Hl.D) (two_taint [.rsp] (e_pins_rsp fun s t _ h => h.1.he.rsp)
      (chkMsg_taint Hl.D hD65)) fun s t hs h => chkMsg_step (hH := hH) (mH := mH) hs h) ?_
  refine e_ite (fun s => some (decide ((s.gpr .rcx).toNat - (2 * Hl.D + 2) < (stackArg s 3).toNat)))
    (fun s t h => h.2.2.1) (fun a s S => by rw [S.k, S.arg (i := 3) (by decide)])
    (e_branch (J' := EW) (fun _ _ _ h _ => h.1) zeroOut_ct)
    (e_branch (J' := EK Hl.D) (fun s t _ h e => ⟨h.1, by have := cf_false h.2.2.1 e; have := h.2.1; omega,
      h.2.2.2⟩) hmain)

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

end

end VG.Proof.RsaOaep.X86_64
