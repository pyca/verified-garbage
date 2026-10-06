import VerifiedGarbage.Proof.RsaOaep.X86_64.DecSteps
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT

/-!
# RSAES-OAEP decryption on x86-64: constant time

As for encryption (`EncCT.lean`), each point of the code is described, in
each run, by what correctness says of it from that run's entry state, which
has the same public data as an anchor (`DAt`). The pieces between the calls
are checked by the taint analysis from the frame's public slots
(`d_taintF`); the one branch is on `k`, which is public; MGF1 and the label's
hash are constant time for the same public data in both runs; and the call
of `vg_rsa_private_checked` is constant time for its contract, whose public
data (its registers, its stack arguments, `n` and `e`) are the same in both
runs. The private operation's result, the decoding's checks and the
message's length are secret: the code after the call computes masks from
them and never branches on them, which the taint analysis checks. The code
with `hLen` as an immediate is checked for every `hLen` up to 64.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.RsaPkcs1Enc.X86_64 (PrivImpl privK privStack)

/-! ## The taint checks -/

theorem dHead_taint : (taint.check (Taint.ofRegs [.rsp]) (.block (decPrologue ++ privArgs))
    (taint.hintOf (Taint.ofRegs [.rsp]) (.block (decPrologue ++ privArgs)))).isSome = true := by
  decide +kernel

theorem resK_taint : ∀ d < 65, (taint.check (frT [] [23] 3)
    (.block (([.mov32 .rax (.reg .rax), .store (sp sR) .rax] : List Instr) ++ chkK (gD d)))
    (taint.hintOf (frT [] [23] 3)
      (.block (([.mov32 .rax (.reg .rax), .store (sp sR) .rax] : List Instr) ++ chkK (gD 0))))).isSome = true := by
  decide +kernel

theorem dSeedArgs_taint : ∀ d < 65, (taint.check (frT [] [] 3) (.block (seedArgs (gD d)))
    (taint.hintOf (frT [] [] 3) (.block (seedArgs (gD 0))))).isSome = true := by
  decide +kernel

theorem dDbArgs_taint : ∀ d < 65, (taint.check (frT [] [] 3) (.block (dbArgs (gD d)))
    (taint.hintOf (frT [] [] 3) (.block (dbArgs (gD 0))))).isSome = true := by
  decide +kernel

theorem tail1_taint : ∀ d < 65, (taint.check (frT [] [14, 23] 3) (tail1 (gD d))
    (taint.hintOf (frT [] [14, 23] 3) (tail1 (gD 0)))).isSome = true := by
  decide +kernel

theorem decRet_taint : ∀ d < 65, (taint.check (frT [] [23, 29] 3) (.block (decRet (gD d)))
    (taint.hintOf (frT [] [23, 29] 3) (.block (decRet (gD 0))))).isSome = true := by
  decide +kernel

/-! ## Entry states and the anchor -/

section
variable (H G : Spec.Mgf1.Hash)

/-- An entry state with the public data of the anchor `a`. -/
def DSib (a s : State) : Prop := (decK H G).pre s ∧ (decK H G).pub a s

/-- What `J` says of a run from an entry state with the anchor's public data. -/
def DAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, DSib H G a s ∧ J s t

theorem decPub_refl (s : State) : (decK H G).pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

end

variable {H G : Spec.Mgf1.Hash}

theorem DSib.gpr {a s : State} (h : DSib H G a s) {r : Reg}
    (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem DSib.arg {a s : State} (h : DSib H G a s) {i : Nat} (hi : i < 17) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.2.1) i (List.mem_range.mpr hi)).symm

theorem DSib.fb {a s : State} (h : DSib H G a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _; rw [h.gpr (r := .rsp) (by decide)]

theorem DSib.out_eq {a s : State} (h : DSib H G a s) : outR s = outR a := by
  unfold outR; rw [h.gpr (r := .rdi) (by decide), h.gpr (r := .rsi) (by decide)]

theorem DSib.ml_eq {a s : State} (h : DSib H G a s) : mlR s = mlR a := by
  unfold mlR; rw [h.gpr (r := .rdx) (by decide)]

theorem DSib.scr_eq {a s : State} (h : DSib H G a s) : scrD s = scrD a := by
  unfold scrD; rw [h.arg (i := 15) (by decide), h.arg (i := 16) (by decide)]

theorem DSib.k {a s : State} (h : DSib H G a s) : (s.gpr .r8).toNat = (a.gpr .r8).toNat := by
  rw [h.gpr (r := .r8) (by decide)]

theorem DSib.w_eq {a s : State} (h : DSib H G a s) {k : Nat} (hk : k ∈ decKs) : decW s k = decW a k := by
  simp only [decKs, List.mem_cons, List.not_mem_nil, or_false] at hk
  have hW : ∀ x : State, ArgsD x (decW x) := fun _ _ _ => rfl
  obtain ⟨a14, a21, a22, a23, a24, a25, a26, a27, a28, a29⟩ := (hW a).w
  obtain ⟨s14, s21, s22, s23, s24, s25, s26, s27, s28, s29⟩ := (hW s).w
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [s14, a14, h.arg (by decide)]
  · rw [s21, a21, h.gpr (by decide)]
  · rw [s22, a22, h.gpr (by decide)]
  · rw [s23, a23, h.gpr (by decide)]
  · rw [s24, a24, h.gpr (by decide)]
  · rw [s25, a25, h.arg (by decide)]
  · rw [s26, a26, h.arg (by decide)]
  · rw [s27, a27, h.arg (by decide)]
  · rw [s28, a28, h.arg (by decide)]
  · rw [s29, a29, h.gpr (by decide)]

/-! ## The pieces -/

/-- Code the taint analysis checks from the frame's argument slots `ks`. -/
theorem d_taintF {J : State → State → Prop} (hJ : ∀ s t, (decK H G).pre s → J s t → DW s t)
    (rs : List Reg) (ks : List Nat) (hks : ∀ k ∈ ks, k ∈ decKs) (hpin : Pins (DAt H G J) rs) {c : Prog isa}
    (h : ∃ hc, (taint.check (frT rs ks 3) c hc).isSome = true) :
    RelCT isa (Two (DAt H G J)) c fun _ _ => True :=
  two_taintF rs ks fb (fun a => [outR a, mlR a, scrD a]) decW (fun a t ⟨s, S, j⟩ => by
      have e := hJ s t S.1 j
      rw [← S.fb, ← S.out_eq, ← S.ml_eq, ← S.scr_eq]
      exact ⟨e.he.frv (DPre.of H G S.1), fun k hk => (e.words k (hks k hk)).trans (S.w_eq (hks k hk))⟩)
    hpin (fun k hk => decKs_lt k (hks k hk)) h

/-- What correctness says after a piece. -/
theorem d_post {J J' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Two (DAt H G J)) c fun _ _ => True)
    (hw : ∀ s t, (decK H G).pre s → J s t → WP isa c t (J' s)) :
    RelCT isa (Two (DAt H G J)) c (Two (DAt H G J')) :=
  two_post hct fun _ t ⟨s, S, j⟩ => WP.mono (hw s t S.1 j) fun _ j' => ⟨s, S, j'⟩

theorem d_pins_rsp {J : State → State → Prop} (hJ : ∀ s t, (decK H G).pre s → J s t → t.gpr .rsp = fb s) :
    Pins (DAt H G J) [.rsp] :=
  fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ r hr => by
    rw [List.mem_singleton.mp hr, hJ _ _ S₁.1 j₁, hJ _ _ S₂.1 j₂, S₁.fb, S₂.fb]

/-- A branch on a condition that the entry state's public data fixes. -/
theorem d_ite {J : State → State → Prop} {cond : isa.Cond} {th el : Prog isa} {Q : State → State → Prop}
    (f : State → Option Bool) (hf : ∀ s t, J s t → isa.eval cond t = f s) (hs : ∀ a s, DSib H G a s → f s = f a)
    (ht : RelCT isa (Two fun a t => DAt H G J a t ∧ isa.eval cond t = some true) th Q)
    (he : RelCT isa (Two fun a t => DAt H G J a t ∧ isa.eval cond t = some false) el Q) :
    RelCT isa (Two (DAt H G J)) (.ite cond th el) Q :=
  two_ite (fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ => by rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]) ht he

/-- In a branch, what its condition says of the entry state. -/
theorem d_branch {J J' : State → State → Prop} {cond : isa.Cond} {b : Bool} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ s t, (decK H G).pre s → J s t → isa.eval cond t = some b → J' s t)
    (hct : RelCT isa (Two (DAt H G J')) c Q) :
    RelCT isa (Two fun a t => DAt H G J a t ∧ isa.eval cond t = some b) c Q :=
  hct.mono (fun _ _ ⟨a, ⟨⟨s₁, S₁, j₁⟩, e₁⟩, ⟨⟨s₂, S₂, j₂⟩, e₂⟩⟩ =>
    ⟨a, ⟨s₁, S₁, h _ _ S₁.1 j₁ e₁⟩, ⟨s₂, S₂, h _ _ S₂.1 j₂ e₂⟩⟩) fun _ _ h => h

/-! ## The call -/

/-- The private operation's stack arguments, by entry state. -/
theorem privW_eq (x : State) {i : Nat} (hi : i < 14) :
    privW x i = [stackArg x 13, x.gpr .r8, stackArg x 1, stackArg x 2, stackArg x 3, stackArg x 4,
      stackArg x 5, stackArg x 6, stackArg x 7, stackArg x 8, stackArg x 9, stackArg x 10,
      off (stackArg x 15) oRsa, stackArg x 16 - 1024].getD i 0 := by
  match i, hi with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl | 12, _ => rfl | 13, _ => rfl

theorem privW_sib {a s : State} (S : DSib H G a s) {i : Nat} (hi : i < 14) : privW s i = privW a i := by
  rw [privW_eq s hi, privW_eq a hi, S.gpr (r := .r8) (by decide), S.arg (i := 1) (by decide),
    S.arg (i := 2) (by decide), S.arg (i := 3) (by decide), S.arg (i := 4) (by decide),
    S.arg (i := 5) (by decide), S.arg (i := 6) (by decide), S.arg (i := 7) (by decide),
    S.arg (i := 8) (by decide), S.arg (i := 9) (by decide), S.arg (i := 10) (by decide),
    S.arg (i := 13) (by decide), S.arg (i := 15) (by decide), S.arg (i := 16) (by decide)]

/-- What `vg_rsa_private_checked`'s contract makes public, from the anchor. -/
theorem privD_view {a s t : State} (S : DSib H G a s) (h : DSet s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (privRdD s) (privWrD s)).gpr =
      [off (stackArg a 15) oEm, a.gpr .r8, a.gpr .rcx, a.gpr .r8, a.gpr .r9, stackArg a 0, fb a - 8] ∧
    (List.range 14).map (stackArg (t.callEntry.withRegions (privRdD s) (privWrD s))) =
      (List.range 14).map (privW a) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (privRdD s) (privWrD s)).mem
      ((t.callEntry.withRegions (privRdD s) (privWrD s)).gpr .rdx)
      ((t.callEntry.withRegions (privRdD s) (privWrD s)).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rcx) (a.gpr .r8).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (privRdD s) (privWrD s)).mem
      ((t.callEntry.withRegions (privRdD s) (privWrD s)).gpr .r8)
      ((t.callEntry.withRegions (privRdD s) (privWrD s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r9) (stackArg a 0).toNat := by
  have hp := DPre.of H G S.1
  have hfe : Frame [below (fb s) 16] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, h.he.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have hfE : FrD s t.callEntry.mem :=
    h.he.fr.trans (hfe.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., below_subD s (by decide)⟩)
  have g : ∀ {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions (privRdD s) (privWrD s)).gpr r = t.gpr r :=
    fun hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨?_, List.map_congr_left fun i hi => ?_, ?_, ?_⟩
  · rw [e_entry_regs, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.he.rsp, S.fb, S.arg (i := 15) (by decide),
      S.arg (i := 0) (by decide), S.gpr (r := .rcx) (by decide), S.gpr (r := .r8) (by decide),
      S.gpr (r := .r9) (by decide)]
  · have hi' := List.mem_range.mp hi
    rw [privD_args hp h _ _ hi', privW_sib S hi']
  · rw [g (by decide), g (by decide), h.rdx, h.rcx, State.withRegions_mem,
      FrD.bytes hfE hp.dKn hp.dOn hp.dMn hp.dns.symm (by have := hp.wN; omega)]
    exact S.2.2.2.1.symm
  · rw [g (by decide), g (by decide), h.r8, h.r9, State.withRegions_mem,
      FrD.bytes hfE hp.dKe hp.dOe hp.dMe hp.des.symm (by have := hp.wE; omega)]
    exact S.2.2.2.2.symm

theorem privD_ct (v : PrivImpl) : RelCT isa (Two (DAt H G DSet)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := privK) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  have hp₁ := DPre.of H G S₁.1
  have hp₂ := DPre.of H G S₂.1
  obtain ⟨r₁, g₁, n₁, e₁⟩ := privD_view S₁ j₁
  obtain ⟨r₂, g₂, n₂, e₂⟩ := privD_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := privD_covers hp₁ j₁
  obtain ⟨c₂, w₂⟩ := privD_covers hp₂ j₂
  exact ⟨privRdD s₁, privWrD s₁, privRdD s₂, privWrD s₂, privD_pre hp₁ j₁, privD_pre hp₂ j₂,
    ⟨List.map_inj_left.mp (r₁.trans r₂.symm), g₁.trans g₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩,
    c₁, w₁, c₂, w₂, by rw [j₁.he.rsp, j₂.he.rsp, S₁.fb, S₂.fb]⟩

/-! ## `decMain` -/

section
variable {Hl Gm : Hash} (hH : HashOK Hl) (KH : Callees Hl) (hG : HashOK Gm) (KG : Callees Gm)
  (mH : MgfLink Hl hH) (mG : MgfLink Gm hG)

/-- In the frame, after the check of `k`. -/
def DK (D : Nat) (s t : State) : Prop := DW s t ∧ 2 * D + 2 ≤ (s.gpr .r8).toNat

/-- The label's hash's public data. -/
def lqD (a : State) : LQ :=
  ⟨fb a, stackArg a 15, [outR a, mlR a, scrD a], stackArg a 11, (stackArg a 12).toNat⟩

/-- Where MGF1 starts, for the anchor's public data. -/
theorem dme_of {src srcLen dst dstLen : Nat → Nat} {a s t : State} (S : DSib H G a s)
    (h : DWM s t (src (s.gpr .r8).toNat) (srcLen (s.gpr .r8).toNat) (dst (s.gpr .r8).toNat)
      (dstLen (s.gpr .r8).toNat))
    (hf : MFit (src (s.gpr .r8).toNat) (srcLen (s.gpr .r8).toNat) (dst (s.gpr .r8).toNat)
      (dstLen (s.gpr .r8).toNat)) :
    ME 3 ⟨fb a, stackArg a 15, [outR a, mlR a, scrD a], src (a.gpr .r8).toNat, srcLen (a.gpr .r8).toNat,
      dst (a.gpr .r8).toNat, dstLen (a.gpr .r8).toNat⟩ t := by
  have hp := DPre.of H G S.1
  obtain ⟨V, W, R, _, A⟩ := h.rep
  have := (⟨h.he.frv hp, h.L, hf, V, W, R, A⟩ : ME 3 ⟨fb s, stackArg s 15, [outR s, mlR s, scrD s],
    src (s.gpr .r8).toNat, srcLen (s.gpr .r8).toNat, dst (s.gpr .r8).toNat, dstLen (s.gpr .r8).toNat⟩ t)
  rwa [S.fb, S.out_eq, S.ml_eq, S.scr_eq, S.arg (i := 15) (by decide), S.k] at this

theorem dfit_seed {D k : Nat} (hk : 2 * D + 2 ≤ k) (hk1 : k ≤ 1024) (hD : 0 < D) :
    MFit (oEm + 1 + D) (k - (D + 1)) (oEm + 1) D :=
  ⟨by unfold oEm oSt; omega, by unfold oEm oSt; omega, by omega, by omega, by omega⟩

theorem dfit_db {D k : Nat} (hk : 2 * D + 2 ≤ k) (hk1 : k ≤ 1024) :
    MFit (oEm + 1) D (oEm + 1 + D) (k - (D + 1)) :=
  ⟨by unfold oEm oSt; omega, by unfold oEm oSt; omega, by omega, by omega, by omega⟩

include hH KH hG KG mH mG in
theorem decMain_ct : RelCT isa (Two (DAt mH.G mG.G (DK Hl.D)))
    (decMain Hl.stream Gm.stream) fun _ _ => True := by
  have hz := sizes hH.stream
  have hsD : Hl.stream.D = Hl.D := rfl
  have hD65 : Hl.D < 65 := by omega
  have hD0 := hH.hD0
  have hk2 : ∀ {s : State}, (decK mH.G mG.G).pre s → (s.gpr .r8).toNat ≤ 1024 := fun hs =>
    (DPre.of _ _ hs).lv.2
  unfold decMain seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `lHash`.
  refine RelCT.seq (d_post (J' := DK Hl.D) (two_map lqD (fun a t ⟨s, S, e, _⟩ => by
      have hp := DPre.of _ _ S.1
      obtain ⟨V, W, R, hW⟩ := e.rep
      have := (⟨e.he.frv hp, e.L, V, W, R, e.lab hp hW⟩ : LW 3 (lqD s) t)
      simp only [lqD] at this ⊢
      rwa [S.fb, S.out_eq, S.ml_eq, S.scr_eq, S.arg (i := 15) (by decide), S.arg (i := 11) (by decide),
        S.arg (i := 12) (by decide)] at this) (hashLabel_ct hH.stream 3 (.inr rfl) (Or.inr rfl)))
    fun s t hs h => WP.mono (dw_hashLabel (DPre.of _ _ hs) hH KH mH h.1) fun _ e => ⟨e, h.2⟩) ?_
  -- The seed unmasked.
  refine RelCT.seq (d_post (J' := fun s t => DWM s t (oEm + 1 + Hl.D) ((s.gpr .r8).toNat - (Hl.D + 1)) (oEm + 1)
      Hl.D ∧ 2 * Hl.D + 2 ≤ (s.gpr .r8).toNat)
    (d_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin ⟨_, dSeedArgs_taint Hl.D hD65⟩)
    fun s t hs h => WP.mono (dw_seedArgs (Hm := Hl.stream) (by omega) (by have := h.2; omega) h.1)
      fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (d_post (J' := DK Hl.D) (two_map (fun a => (⟨fb a, stackArg a 15, [outR a, mlR a, scrD a],
      oEm + 1 + Hl.D, (a.gpr .r8).toNat - (Hl.D + 1), oEm + 1, Hl.D⟩ : MQ))
      (fun a t ⟨s, S, e, hk⟩ => dme_of (src := fun _ => oEm + 1 + Hl.D) (srcLen := fun k => k - (Hl.D + 1))
        (dst := fun _ => oEm + 1) (dstLen := fun _ => Hl.D) S e (dfit_seed hk (hk2 S.1) hD0))
      (mgf_ct hG.stream 3 mG.hash mG.len (valid_of_link hG mG) (.inr rfl)))
    fun s t hs h => WP.mono (dw_mgf hG KG mG (dfit_seed h.2 (hk2 hs) hD0) h.1) fun _ e => ⟨e, h.2⟩) ?_
  -- `DB` unmasked.
  refine RelCT.seq (d_post (J' := fun s t => DWM s t (oEm + 1) Hl.D (oEm + 1 + Hl.D)
      ((s.gpr .r8).toNat - (Hl.D + 1)) ∧ 2 * Hl.D + 2 ≤ (s.gpr .r8).toNat)
    (d_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin ⟨_, dDbArgs_taint Hl.D hD65⟩)
    fun s t hs h => WP.mono (dw_dbArgs (Hm := Hl.stream) (by omega) (by have := h.2; omega) h.1)
      fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (d_post (J' := DK Hl.D) (two_map (fun a => (⟨fb a, stackArg a 15, [outR a, mlR a, scrD a],
      oEm + 1, Hl.D, oEm + 1 + Hl.D, (a.gpr .r8).toNat - (Hl.D + 1)⟩ : MQ))
      (fun a t ⟨s, S, e, hk⟩ => dme_of (src := fun _ => oEm + 1) (srcLen := fun _ => Hl.D)
        (dst := fun _ => oEm + 1 + Hl.D) (dstLen := fun k => k - (Hl.D + 1)) S e (dfit_db hk (hk2 S.1)))
      (mgf_ct hG.stream 3 mG.hash mG.len (valid_of_link hG mG) (.inr rfl)))
    fun s t hs h => WP.mono (dw_mgf hG KG mG (dfit_db h.2 (hk2 hs)) h.1) fun _ e => ⟨e, h.2⟩) ?_
  -- The checks, and `T` shifted into the buffer.
  refine RelCT.assoc ?_
  refine RelCT.assoc ?_
  refine RelCT.assoc ?_
  refine RelCT.assoc ?_
  refine RelCT.seq (d_post (J' := DW) (c := tail1 Hl.stream)
    (d_taintF (fun _ _ _ h => h.1) [] [14, 23] (by decide) nopin ⟨_, tail1_taint Hl.D hD65⟩)
    fun s t hs h => dw_tail1 (DPre.of _ _ hs) (Hm := Hl.stream) hD0 (by omega) h.2 h.1) ?_
  -- `ok`, `out` and `*msg_len`.
  refine RelCT.assoc ?_
  refine RelCT.seq (d_post (J' := DW)
    (d_taintF (fun _ _ _ h => h) [] [14, 21, 23] (by decide) nopin ⟨_, by taint_decide⟩)
    fun s t hs h => dw_tail2 (DPre.of _ _ hs) h) ?_
  exact d_taintF (fun _ _ _ h => h) [] [23, 29] (by decide) nopin ⟨_, decRet_taint Hl.D hD65⟩

omit hH KH hG KG mH mG in
theorem decFail_ct : RelCT isa (Two (DAt H G DW)) decFail fun _ _ => True :=
  d_taintF (fun _ _ _ h => h) [] [21, 23, 29] (by decide) nopin ⟨_, by taint_decide⟩

/-- After the call. -/
def JC (s t : State) : Prop :=
  EnvD s t ∧ Lay t (fb s) (stackArg s 15) ∧ ∃ V, Rep t.mem (fb s) (stackArg s 15) V (privW s)

/-- After the check of `k`. -/
def JK (D : Nat) (s t : State) : Prop := DW s t ∧ t.cf = some (decide ((s.gpr .r8).toNat < 2 * D + 2))

include hH KH hG KG mH mG in
theorem decBody_ct (v : PrivImpl) : RelCT isa (Two (DAt mH.G mG.G JA))
    (decBody Hl.stream Gm.stream v.name v.code) fun _ _ => True := by
  have hz := sizes hH.stream
  have hsD : Hl.stream.D = Hl.D := rfl
  have hD65 : Hl.D < 65 := by omega
  unfold decBody seqs seqs seqs
  refine RelCT.seq (d_post (J' := DSet) (two_taint [.rsp] (d_pins_rsp fun s t _ h => by rw [h]; rfl) dHead_taint)
    fun s t hs h => by subst h; exact decHead_ok (DPre.of _ _ hs)) ?_
  refine RelCT.seq (d_post (J' := JC) (privD_ct v) fun s t hs h =>
    WP.mono (privD_call v (DPre.of _ _ hs) h) fun _ ⟨he, L, R, _⟩ => ⟨he, L, _, R⟩) ?_
  refine RelCT.seq (d_post (J' := JK Hl.D)
    (d_taintF (fun _ _ _ ⟨he, L, V, R⟩ => ⟨he, L, V, _, R, ArgsD_privW _⟩) [] [23] (by decide) nopin
      ⟨_, resK_taint Hl.D hD65⟩) fun s t hs h => ?_) ?_
  · obtain ⟨he, L, V, R⟩ := h
    have hp := DPre.of _ _ hs
    have hk1 := hp.lv.1; have hk2 := hp.lv.2
    obtain ⟨-, -, -, w23, -⟩ := (ArgsD_privW s).w
    exact WP.mono (wp_good (block_good _ rfl) (resK_ok (Hm := Hl.stream) L R (k := (s.gpr .r8).toNat)
      (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega) (by omega)))
      fun t2 ⟨⟨k2, L2, R2, hcf2⟩, sp2, mx2, f2⟩ => ⟨⟨he.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2,
        L2, _, _, R2, (ArgsD_privW s).of fun j hj => by
          simp only [upd]; rw [ifn (by have := decKs_iff hj; omega)]⟩, by rw [hcf2, hsD]⟩
  refine d_ite (fun s => some (decide ((s.gpr .r8).toNat < 2 * Hl.D + 2))) (fun s t h => h.2)
    (fun a s S => by rw [S.k]) (d_branch (J' := DW) (fun _ _ _ h _ => h.1) decFail_ct)
    (d_branch (J' := DK Hl.D) (fun s t _ h e => ⟨h.1, by have := cf_false h.2 e; omega⟩)
      (decMain_ct hH KH hG KG mH mG))

include hH KH hG KG mH mG in
theorem dec_constantTime (v : PrivImpl) : ConstantTime isa (decK mH.G mG.G).pre (decK mH.G mG.G).pub
    (decrypt Hl.stream Gm.stream v.name v.code) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (relCT_alloc ((decBody_ct hH KH hG KG mH mG v).mono ?_
    fun _ _ h => h))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, rfl, rfl⟩
  exact ⟨s₁, ⟨s₁, ⟨h₁, decPub_refl _ _ s₁⟩, rfl⟩, ⟨s₂, ⟨h₂, hpub⟩, rfl⟩⟩

include hH KH hG KG mH mG in
/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt` meets the shared contract. -/
theorem dec_verified (v : PrivImpl) :
    Verified target (decrypt Hl.stream Gm.stream v.name v.code)
      (Spec.RsaOaep.decryptContract mH.G mG.G abi decStack) :=
  Verified.of_correct (k := decK mH.G mG.G) (dec_correct hH KH hG KG mH mG v)
    (dec_constantTime hH KH hG KG mH mG v) (dec_implies mH.G mG.G)

end

end VG.Proof.RsaOaep.X86_64
