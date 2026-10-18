module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecSteps
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.DecSteps
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import Mathlib.Data.Int.ModEq
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall

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
them and never branches on them, which the taint analysis checks. The hash
functions are those the selectors name, the same in both runs, and so are
the tables' words: the calls of their streaming functions are of the same
addresses in both runs, from entries of the same program (`Like`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep ifn)
open VG.Proof.HashFns (StreamingOK)
open VG.Proof.RsaPkcs1Enc.X86_64 (PrivImpl privK privStack)

/-! ## The taint checks -/

theorem decPro_taint : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block decPrologue) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem privArgs_taint : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block privArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## Entry states and the anchor -/

section
variable (kH kG : Nat)

/-- An entry state with the public data and regions of the anchor `a`, and
the selectors `kH` and `kG`. -/
def DSib (a s : State) : Prop :=
  decK.pre s ∧ decK.pub a s ∧ dselH s = kH ∧ dselG s = kG ∧ s.rd = a.rd ∧ s.wr = a.wr

/-- What `J` says of a run from an entry state with the anchor's public data. -/
def DAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, DSib kH kG a s ∧ J s t

theorem decPub_refl (s : State) : decK.pub s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, by simp only [abi]; exact ⟨rfl, rfl, rfl⟩⟩

end

variable {kH kG : Nat}

theorem DSib.gpr {a s : State} (h : DSib kH kG a s) {r : Reg}
    (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r := (h.2.1.1 r hr).symm

theorem DSib.arg {a s : State} (h : DSib kH kG a s) {i : Nat} (hi : i < 21) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.1.2.1) i (List.mem_range.mpr hi)).symm

theorem DSib.fb {a s : State} (h : DSib kH kG a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _; rw [h.gpr (r := .rsp) (by decide)]

theorem DSib.out_eq {a s : State} (h : DSib kH kG a s) : outR s = outR a := by
  unfold outR; rw [h.gpr (r := .rdi) (by decide), h.gpr (r := .rsi) (by decide)]

theorem DSib.ml_eq {a s : State} (h : DSib kH kG a s) : mlR s = mlR a := by
  unfold mlR; rw [h.gpr (r := .rdx) (by decide)]

theorem DSib.scr_eq {a s : State} (h : DSib kH kG a s) : scrD s = scrD a := by
  unfold scrD; rw [h.arg (i := 15) (by decide), h.arg (i := 16) (by decide)]

theorem DSib.k {a s : State} (h : DSib kH kG a s) : (s.gpr .r8).toNat = (a.gpr .r8).toNat := by
  rw [h.gpr (r := .r8) (by decide)]

/-- The words of the tables, the stack arguments 19 and 20. -/
theorem DSib.tw {a s : State} (h : DSib kH kG a s) {j : Nat} (hj : j = 19 ∨ j = 20) {i : Nat} (hi : i < 3) :
    tw s.mem (stackArg s j) i = tw a.mem (stackArg a j) i := by
  rcases hj with rfl | rfl
  · exact (tw_eq h.2.1.2.2.2.2.1 hi).symm
  · exact (tw_eq h.2.1.2.2.2.2.2.1 hi).symm

/-- An entry with the anchor's public data and regions is like it. -/
theorem DSib.like {a s : State} (h : DSib kH kG a s) : Like a s := by
  obtain ⟨f, c, y⟩ := h.2.1.2.2.2.2.2.2
  simp only [abi, Option.elim] at y
  exact ⟨⟨f.symm, c.symm, by simp only [abi, Option.elim]; exact y.symm⟩, h.2.2.2.2.1, h.2.2.2.2.2,
    h.gpr (r := .rsp) (by decide)⟩

theorem DSib.w_eq {a s : State} (h : DSib kH kG a s) {k : Nat} (hk : k ∈ decKs) : decW s k = decW a k := by
  simp only [decKs, List.mem_cons, List.not_mem_nil, or_false] at hk
  have e : ∀ i < 19, stackArg s i = stackArg a i := fun i hi => h.arg (by omega)
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [decW, fnW, selW, decPW, upd, dselH, dselG, h.tw (.inl rfl) (i := 0) (by decide),
    h.tw (.inl rfl) (i := 1) (by decide), h.tw (.inl rfl) (i := 2) (by decide), h.tw (.inr rfl) (i := 0) (by decide),
    h.tw (.inr rfl) (i := 1) (by decide), h.tw (.inr rfl) (i := 2) (by decide), e 0 (by decide), e 11 (by decide), e 12 (by decide),
    e 15 (by decide), e 16 (by decide), e 17 (by decide), e 18 (by decide),
    h.gpr (r := .rdi) (by decide), h.gpr (r := .rdx) (by decide), h.gpr (r := .rcx) (by decide),
    h.gpr (r := .r8) (by decide), h.gpr (r := .r9) (by decide)]

/-! ## The pieces -/

/-- Code the taint analysis checks from the frame's argument slots `ks`. -/
theorem d_taintF {J : State → State → Prop} (hJ : ∀ s t, decK.pre s → J s t → DW s t)
    (rs : List Reg) (ks : List Nat) (hks : ∀ k ∈ ks, k ∈ decKs) (hpin : Pins (DAt kH kG J) rs) {c : Prog isa}
    (h : ∃ hc, (taint.check (frT rs ks 3) c hc).isSome = true) :
    RelCT isa (Two (DAt kH kG J)) c fun _ _ => True :=
  two_taintF rs ks fb (fun a => [outR a, mlR a, scrD a]) decW (fun a t ⟨s, S, j⟩ => by
      have e := hJ s t S.1 j
      rw [← S.fb, ← S.out_eq, ← S.ml_eq, ← S.scr_eq]
      exact ⟨e.he.frv (DPre.of S.1), fun k hk => (e.words k (hks k hk)).trans (S.w_eq (hks k hk))⟩)
    hpin (fun k hk => decKs_lt k (hks k hk)) h

/-- What correctness says after a piece. -/
theorem d_post {J J' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Two (DAt kH kG J)) c fun _ _ => True)
    (hw : ∀ a s t, DSib kH kG a s → J s t → WP isa c t (J' s)) :
    RelCT isa (Two (DAt kH kG J)) c (Two (DAt kH kG J')) :=
  two_post hct fun a t ⟨s, S, j⟩ => WP.mono (hw a s t S j) fun _ j' => ⟨s, S, j'⟩

theorem d_pins_rsp {J : State → State → Prop} (hJ : ∀ s t, decK.pre s → J s t → t.gpr .rsp = fb s) :
    Pins (DAt kH kG J) [.rsp] :=
  fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ r hr => by
    rw [List.mem_singleton.mp hr, hJ _ _ S₁.1 j₁, hJ _ _ S₂.1 j₂, S₁.fb, S₂.fb]

/-- A branch on a condition that the entry state's public data fixes. -/
theorem d_ite {J : State → State → Prop} {cond : isa.Cond} {th el : Prog isa} {Q : State → State → Prop}
    (f : State → Option Bool) (hf : ∀ s t, J s t → isa.eval cond t = f s) (hs : ∀ a s, DSib kH kG a s → f s = f a)
    (ht : RelCT isa (Two fun a t => DAt kH kG J a t ∧ isa.eval cond t = some true) th Q)
    (he : RelCT isa (Two fun a t => DAt kH kG J a t ∧ isa.eval cond t = some false) el Q) :
    RelCT isa (Two (DAt kH kG J)) (.ite cond th el) Q :=
  two_ite (fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ => by rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]) ht he

/-- In a branch, what its condition says of the entry state. -/
theorem d_branch {J J' : State → State → Prop} {cond : isa.Cond} {b : Bool} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ s t, decK.pre s → J s t → isa.eval cond t = some b → J' s t)
    (hct : RelCT isa (Two (DAt kH kG J')) c Q) :
    RelCT isa (Two fun a t => DAt kH kG J a t ∧ isa.eval cond t = some b) c Q :=
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

theorem privW_sib {a s : State} (S : DSib kH kG a s) {i : Nat} (hi : i < 14) : privW s i = privW a i := by
  rw [privW_eq s hi, privW_eq a hi, S.gpr (r := .r8) (by decide), S.arg (i := 1) (by decide),
    S.arg (i := 2) (by decide), S.arg (i := 3) (by decide), S.arg (i := 4) (by decide),
    S.arg (i := 5) (by decide), S.arg (i := 6) (by decide), S.arg (i := 7) (by decide),
    S.arg (i := 8) (by decide), S.arg (i := 9) (by decide), S.arg (i := 10) (by decide),
    S.arg (i := 13) (by decide), S.arg (i := 15) (by decide), S.arg (i := 16) (by decide)]

/-- What `vg_rsa_private_checked`'s contract makes public, from the anchor. -/
theorem privD_view {a s t : State} (S : DSib kH kG a s) (h : DSet s t) :
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
  have hp := DPre.of S.1
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
    exact S.2.1.2.2.1.symm
  · rw [g (by decide), g (by decide), h.r8, h.r9, State.withRegions_mem,
      FrD.bytes hfE hp.dKe hp.dOe hp.dMe hp.des.symm (by have := hp.wE; omega)]
    exact S.2.1.2.2.2.1.symm

theorem privD_ct (v : PrivImpl) : RelCT isa (Two (DAt kH kG DSet)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := privK) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  have hp₁ := DPre.of S₁.1
  have hp₂ := DPre.of S₂.1
  obtain ⟨r₁, g₁, n₁, e₁⟩ := privD_view S₁ j₁
  obtain ⟨r₂, g₂, n₂, e₂⟩ := privD_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := privD_covers hp₁ j₁
  obtain ⟨c₂, w₂⟩ := privD_covers hp₂ j₂
  exact ⟨privRdD s₁, privWrD s₁, privRdD s₂, privWrD s₂, privD_pre hp₁ j₁, privD_pre hp₂ j₂,
    ⟨List.map_inj_left.mp (r₁.trans r₂.symm), g₁.trans g₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩,
    c₁, w₁, c₂, w₂, by rw [j₁.he.rsp, j₂.he.rsp, S₁.fb, S₂.fb]⟩

/-! ## `decMain` -/

section
variable {TH TG : Spec.HashFns.Streaming} {Hh Gh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)
  (hTG : StreamingOK TG Gh) (sH : Spec.HashFns.streaming kH = some TH) (sG : Spec.HashFns.streaming kG = some TG)
  (eH : Spec.HashId.mgf1 kH = some Hh) (eG : Spec.HashId.mgf1 kG = some Gh)

/-- In the frame, after the check of `k`. -/
def DK (D : Nat) (s t : State) : Prop := DW s t ∧ 2 * D + 2 ≤ (s.gpr .r8).toNat

/-- The label's hash's public data. -/
def lqD (a : State) : LQ :=
  ⟨fb a, stackArg a 15, [outR a, mlR a, scrD a], stackArg a 11, (stackArg a 12).toNat, a,
    tw a.mem (stackArg a 19) 0, tw a.mem (stackArg a 19) 1, tw a.mem (stackArg a 19) 2⟩

include eH hTH in
theorem DSib.lenH {a s : State} (S : DSib kH kG a s) : lenOf (dselH s) = TH.S.digestBytes := by
  rw [S.2.2.1]; exact (lenOf_eq hTH eH).symm

include eG hTG in
theorem DSib.lenG {a s : State} (S : DSib kH kG a s) : lenOf (dselG s) = TG.S.digestBytes := by
  rw [S.2.2.2.1]; exact (lenOf_eq hTG eG).symm

include sH in
/-- The streaming functions of the label's hash function, in its table. -/
theorem DSib.fnsH {a s : State} (S : DSib kH kG a s) : FnsD s TH 19 := by
  have h := (DPre.of S.1).fH
  rw [S.2.2.1] at h
  obtain ⟨T, _, sT, _, _, hF⟩ := fns_of_tab h
  rw [sH, Option.some.injEq] at sT
  subst sT
  exact hF

include sG in
theorem DSib.fnsG {a s : State} (S : DSib kH kG a s) : FnsD s TG 20 := by
  have h := (DPre.of S.1).fG
  rw [S.2.2.2.1] at h
  obtain ⟨T, _, sT, _, _, hF⟩ := fns_of_tab h
  rw [sG, Option.some.injEq] at sT
  subst sT
  exact hF

include sG in
/-- Where MGF1 starts, for the anchor's public data. -/
theorem dme_of {src srcLen dst dstLen : Nat → Nat} {a s t : State} (S : DSib kH kG a s)
    (h43 : lenOf (dselG s) = TG.S.digestBytes)
    (h : DWM s t (src (s.gpr .r8).toNat) (srcLen (s.gpr .r8).toNat) (dst (s.gpr .r8).toNat)
      (dstLen (s.gpr .r8).toNat))
    (hf : MFit (src (s.gpr .r8).toNat) (srcLen (s.gpr .r8).toNat) (dst (s.gpr .r8).toNat)
      (dstLen (s.gpr .r8).toNat)) :
    ME decStack TG 3 ⟨fb a, stackArg a 15, [outR a, mlR a, scrD a], src (a.gpr .r8).toNat,
      srcLen (a.gpr .r8).toNat, dst (a.gpr .r8).toNat, dstLen (a.gpr .r8).toNat, a, tw a.mem (stackArg a 20) 0,
      tw a.mem (stackArg a 20) 1, tw a.mem (stackArg a 20) 2⟩ t := by
  have hp := DPre.of S.1
  obtain ⟨V, W, R, hW, A⟩ := h.rep
  obtain ⟨-, -, -, -, -, -, w43⟩ := hW.sel
  obtain ⟨-, fn⟩ := hW.fn
  rw [h43] at w43
  have := (⟨h.he.frv hp, h.L, hf, ⟨V, W, R, A, fn, w43⟩, ⟨s, h.he.here, S.fnsG sG, S.like⟩⟩ :
    ME decStack TG 3 ⟨fb s, stackArg s 15, [outR s, mlR s, scrD s], src (s.gpr .r8).toNat,
      srcLen (s.gpr .r8).toNat, dst (s.gpr .r8).toNat, dstLen (s.gpr .r8).toNat, a, tw s.mem (stackArg s 20) 0,
      tw s.mem (stackArg s 20) 1, tw s.mem (stackArg s 20) 2⟩ t)
  rwa [S.tw (.inr rfl) (i := 0) (by decide), S.tw (.inr rfl) (i := 1) (by decide),
    S.tw (.inr rfl) (i := 2) (by decide), S.fb, S.out_eq, S.ml_eq, S.scr_eq, S.arg (i := 15) (by decide),
    S.k] at this

theorem dfit_seed {D k : Nat} (hk : 2 * D + 2 ≤ k) (hk1 : k ≤ 1024) (hD : 0 < D) :
    MFit (oEm + 1 + D) (k - (D + 1)) (oEm + 1) D :=
  ⟨by unfold oEm oSt; omega, by unfold oEm oSt; omega, by omega, by omega, by omega⟩

theorem dfit_db {D k : Nat} (hk : 2 * D + 2 ≤ k) (hk1 : k ≤ 1024) :
    MFit (oEm + 1) D (oEm + 1 + D) (k - (D + 1)) :=
  ⟨by unfold oEm oSt; omega, by unfold oEm oSt; omega, by omega, by omega, by omega⟩

include hTH hTG sH sG eH eG in
theorem decMain_ct : RelCT isa (Two (DAt kH kG (DK TH.S.digestBytes))) decMain fun _ _ => True := by
  have hz := sizes hTH
  have hD0 := hTH.pos
  have hD64 : TH.S.digestBytes ≤ 64 := Nat.le_trans hTH.digest hTH.out
  have hk2 : ∀ {s : State}, decK.pre s → (s.gpr .r8).toNat ≤ 1024 := fun hs => (DPre.of hs).lv.2
  unfold decMain seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `lHash`.
  refine RelCT.seq (d_post (J' := DK TH.S.digestBytes) (two_map lqD (fun a t ⟨s, S, e, _⟩ => by
      have hp := DPre.of S.1
      obtain ⟨V, W, R, hW⟩ := e.rep
      obtain ⟨fn, -⟩ := hW.fn
      have hl := S.like
      have := (⟨e.he.frv hp, e.L, ⟨V, W, R, e.lab hp hW, fn⟩, ⟨s, e.he.here, S.fnsH sH, hl⟩, hp.wL,
        fun x hx => hl.inR (rdIn_entry (r := ⟨stackArg s 11, (stackArg s 12).toNat⟩) (by rw [hp.hrd]; simp) x hx)⟩ :
        LW decStack TH 3 ⟨fb s, stackArg s 15, [outR s, mlR s, scrD s], stackArg s 11, (stackArg s 12).toNat, a,
          tw s.mem (stackArg s 19) 0, tw s.mem (stackArg s 19) 1, tw s.mem (stackArg s 19) 2⟩ t)
      simp only [lqD] at this ⊢
      rwa [S.tw (.inl rfl) (i := 0) (by decide), S.tw (.inl rfl) (i := 1) (by decide),
        S.tw (.inl rfl) (i := 2) (by decide), S.fb, S.out_eq, S.ml_eq, S.scr_eq, S.arg (i := 15) (by decide),
        S.arg (i := 11) (by decide), S.arg (i := 12) (by decide)] at this)
      (hashLabel_ct hTH 3 (.inr rfl) (Or.inr rfl)))
    fun _ s t S h => WP.mono (dw_hashLabel (DPre.of S.1) hTH (S.fnsH sH) h.1) fun _ e => ⟨e, h.2⟩) ?_
  -- The seed unmasked.
  refine RelCT.seq (d_post (J' := fun s t => DWM s t (oEm + 1 + TH.S.digestBytes)
      ((s.gpr .r8).toNat - (TH.S.digestBytes + 1)) (oEm + 1) TH.S.digestBytes ∧
        2 * TH.S.digestBytes + 2 ≤ (s.gpr .r8).toNat)
    (d_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin ⟨_, by taint_decide⟩)
    fun _ s t S h => WP.mono (dw_seedArgs (S.lenH hTH eH) (by have := h.2; omega) h.1)
      fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (d_post (J' := DK TH.S.digestBytes) (two_map (fun a => (⟨fb a, stackArg a 15,
      [outR a, mlR a, scrD a], oEm + 1 + TH.S.digestBytes, (a.gpr .r8).toNat - (TH.S.digestBytes + 1), oEm + 1,
      TH.S.digestBytes, a, tw a.mem (stackArg a 20) 0, tw a.mem (stackArg a 20) 1, tw a.mem (stackArg a 20) 2⟩ : MQ))
      (fun a t ⟨s, S, e, hk⟩ => dme_of sG (src := fun _ => oEm + 1 + TH.S.digestBytes)
        (srcLen := fun k => k - (TH.S.digestBytes + 1)) (dst := fun _ => oEm + 1)
        (dstLen := fun _ => TH.S.digestBytes) S (S.lenG hTG eG) e (dfit_seed hk (hk2 S.1) hD0))
      (mgf_ct hTG 3 (Gs := Gh) (congrFun hTG.hash) hTG.len hTG.valid (.inr (.inl rfl))))
    fun _ s t S h => WP.mono (dw_mgf hTG (S.fnsG sG) (by rw [S.2.2.2.1]; exact eG) (dfit_seed h.2 (hk2 S.1) hD0)
      h.1) fun _ e => ⟨e, h.2⟩) ?_
  -- `DB` unmasked.
  refine RelCT.seq (d_post (J' := fun s t => DWM s t (oEm + 1) TH.S.digestBytes (oEm + 1 + TH.S.digestBytes)
      ((s.gpr .r8).toNat - (TH.S.digestBytes + 1)) ∧ 2 * TH.S.digestBytes + 2 ≤ (s.gpr .r8).toNat)
    (d_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin ⟨_, by taint_decide⟩)
    fun _ s t S h => WP.mono (dw_dbArgs (S.lenH hTH eH) (by have := h.2; omega) h.1)
      fun _ e => ⟨e, h.2⟩) ?_
  refine RelCT.seq (d_post (J' := DK TH.S.digestBytes) (two_map (fun a => (⟨fb a, stackArg a 15,
      [outR a, mlR a, scrD a], oEm + 1, TH.S.digestBytes, oEm + 1 + TH.S.digestBytes,
      (a.gpr .r8).toNat - (TH.S.digestBytes + 1), a, tw a.mem (stackArg a 20) 0, tw a.mem (stackArg a 20) 1,
      tw a.mem (stackArg a 20) 2⟩ : MQ))
      (fun a t ⟨s, S, e, hk⟩ => dme_of sG (src := fun _ => oEm + 1) (srcLen := fun _ => TH.S.digestBytes)
        (dst := fun _ => oEm + 1 + TH.S.digestBytes) (dstLen := fun k => k - (TH.S.digestBytes + 1)) S
        (S.lenG hTG eG) e (dfit_db hk (hk2 S.1)))
      (mgf_ct hTG 3 (Gs := Gh) (congrFun hTG.hash) hTG.len hTG.valid (.inr (.inl rfl))))
    fun _ s t S h => WP.mono (dw_mgf hTG (S.fnsG sG) (by rw [S.2.2.2.1]; exact eG) (dfit_db h.2 (hk2 S.1)) h.1)
      fun _ e => ⟨e, h.2⟩) ?_
  -- The checks, and `T` shifted into the buffer.
  refine RelCT.assoc ?_
  refine RelCT.assoc ?_
  refine RelCT.assoc ?_
  refine RelCT.assoc ?_
  refine RelCT.seq (d_post (J' := DW) (c := tail1)
    (d_taintF (fun _ _ _ h => h.1) [] [14, 23, 39, 41] (by decide) nopin ⟨_, by taint_decide⟩)
    fun _ s t S h => dw_tail1 (DPre.of S.1) (S.lenH hTH eH) hD0 hD64 h.2 h.1) ?_
  -- `ok`, `out` and `*msg_len`.
  refine RelCT.assoc ?_
  refine RelCT.seq (d_post (J' := DW)
    (d_taintF (fun _ _ _ h => h) [] [14, 21, 23] (by decide) nopin ⟨_, by taint_decide⟩)
    fun _ s t S h => dw_tail2 (DPre.of S.1) h) ?_
  exact d_taintF (fun _ _ _ h => h) [] [23, 29] (by decide) nopin ⟨_, by taint_decide⟩

omit hTH hTG sH sG eH eG in
theorem decFail_ct : RelCT isa (Two (DAt kH kG DW)) decFail fun _ _ => True :=
  d_taintF (fun _ _ _ h => h) [] [21, 23, 29] (by decide) nopin ⟨_, by taint_decide⟩

/-- After the call. -/
def JC (s t : State) : Prop :=
  EnvD s t ∧ Lay t (fb s) (stackArg s 15) ∧ ∃ V, Rep t.mem (fb s) (stackArg s 15) V (privW s)

/-- After the check of `k`. -/
def JK (D : Nat) (s t : State) : Prop := DW s t ∧ t.cf = some (decide ((s.gpr .r8).toNat < 2 * D + 2))

include hTH hTG sH sG eH eG in
theorem decBody_ct (iH : kH ∈ Spec.RsaOaep.hashIds) (iG : kG ∈ Spec.RsaOaep.hashIds) (v : PrivImpl) :
    RelCT isa (Two (DAt kH kG JA)) (decBody v.name v.code) fun _ _ => True := by
  have hz := sizes hTH
  have hD64 : TH.S.digestBytes ≤ 64 := Nat.le_trans hTH.digest hTH.out
  have hkm : ∀ {k : Nat}, k ∈ Spec.RsaOaep.hashIds → k ∈ lens.map (·.1) := fun h =>
    List.mem_map.mpr ⟨_, mem_lens h, rfl⟩
  unfold decBody seqs seqs seqs seqs seqs
  -- The prologue.
  refine RelCT.seq (d_post (J' := JPD decPW) (two_taint [.rsp] (d_pins_rsp fun s t _ h => by rw [h]; rfl)
      decPro_taint.choose_spec) fun _ s t S h => by subst h; exact decPro_step (DPre.of S.1)) ?_
  -- The selectors.
  have hsel : ∀ a t, DAt kH kG (JPD decPW) a t →
      SelPt fb (fun a => stackArg a 15) 17 18 (fun _ => kH) (fun _ => kG) (fun a => stackArg a 19)
        (fun a => stackArg a 20) a t := by
    rintro a t ⟨s, S, k1, L1, R1, f1, -⟩
    have hp := DPre.of S.1
    have hrd := k1.2.1
    have i1 := hp.arg_in hrd (j := 17) (by decide)
    have i2 := hp.arg_in hrd (j := 18) (by decide)
    have ar : ∀ m', Frame [⟨fb s, frameBytes⟩] t.mem m' →
        m'.readW (off (fb s) (frameBytes + 8 + 8 * 17)) 64 = BitVec.ofNat 64 kH ∧
          m'.readW (off (fb s) (frameBytes + 8 + 8 * 18)) 64 = BitVec.ofNat 64 kG := fun m' hm => ⟨by
      rw [arg_readD hp (f1.trans hm) (j := 17) (by decide), ← S.2.2.1]; simp, by
      rw [arg_readD hp (f1.trans hm) (j := 18) (by decide), ← S.2.2.2.1]; simp⟩
    have tH := hp.tab hrd f1 (j := 19) (.inl rfl)
    have tG := hp.tab hrd f1 (j := 20) (.inr rfl)
    rw [S.fb, S.arg (i := 15) (by decide)] at L1 R1
    rw [S.fb] at i1 i2 ar
    rw [S.fb, S.arg (i := 19) (by decide)] at tH
    rw [S.fb, S.arg (i := 20) (by decide)] at tG
    exact ⟨L1, ⟨_, _, R1⟩, i1, i2, ar, ⟨_, _, _, tH⟩, ⟨_, _, _, tG⟩⟩
  refine RelCT.seq (d_post (J' := JPD decW) (two_map id hsel
      (selPro_ct (F := fb) (S := fun a => stackArg a 15) (kH := fun _ => kH) (kG := fun _ => kG)
        (fun _ => hkm iH) (fun _ => hkm iG) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
        ⟨_, by taint_decide⟩))
    fun _ s t S h => decSel_step (DPre.of S.1) h) ?_
  -- The private-key operation's arguments, and its call.
  refine RelCT.seq (d_post (J' := DSet) (two_taint [.rsp]
      (d_pins_rsp fun s t _ h => (h.1.gpr (by decide)).trans rfl) privArgs_taint.choose_spec)
    fun _ s t S h => privArgs_step (DPre.of S.1) h) ?_
  refine RelCT.seq (d_post (J' := JC) (privD_ct v) fun _ s t S h =>
    WP.mono (privD_call v (DPre.of S.1) h) fun _ ⟨he, L, R, _⟩ => ⟨he, L, _, R⟩) ?_
  refine RelCT.seq (d_post (J' := JK TH.S.digestBytes)
    (d_taintF (fun _ _ _ ⟨he, L, V, R⟩ => ⟨he, L, V, _, R, ArgsD_privW _⟩) [] [23] (by decide) nopin
      ⟨_, by taint_decide⟩) fun _ s t S h => ?_) ?_
  · obtain ⟨he, L, V, R⟩ := h
    have hp := DPre.of S.1
    have hk1 := hp.lv.1; have hk2 := hp.lv.2
    obtain ⟨-, -, -, w23, -⟩ := (ArgsD_privW s).w
    obtain ⟨-, -, -, -, -, w42, -⟩ := (ArgsD_privW s).sel
    rw [S.lenH hTH eH] at w42
    exact WP.mono (wp_good (block_good _ rfl rfl) (resK_ok L R (k := (s.gpr .r8).toNat)
      (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega) w42 (by omega)))
      fun t2 ⟨⟨k2, L2, R2, hcf2⟩, sp2, mx2, f2⟩ => ⟨⟨he.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2,
        L2, _, _, R2, (ArgsD_privW s).of fun j hj => by
          simp only [upd]; rw [ifn (by have := decKs_iff hj; omega)]⟩, hcf2⟩
  refine d_ite (fun s => some (decide ((s.gpr .r8).toNat < 2 * TH.S.digestBytes + 2))) (fun s t h => h.2)
    (fun a s S => by rw [S.k]) (d_branch (J' := DW) (fun _ _ _ h _ => h.1) decFail_ct)
    (d_branch (J' := DK TH.S.digestBytes) (fun s t _ h e => ⟨h.1, by have := cf_false h.2 e; omega⟩)
      (decMain_ct hTH hTG sH sG eH eG))

end

theorem dec_constantTime (v : PrivImpl) :
    ConstantTime isa decK.pre decK.pub (decrypt v.name v.code) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (relCT_alloc (R := fun _ _ => True) ?_)
  rintro _ _ t₁ t₂ s₁' s₂' ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, rfl, rfl⟩ e₁ e₂
  have hp₁ := DPre.of h₁
  have hp₂ := DPre.of h₂
  obtain ⟨TH, TG, Hh, Gh, sH, sG, eH, eG, oH, oG, -, -⟩ := dsel_of hp₁
  have a : ∀ i < 21, stackArg s₁ i = stackArg s₂ i := fun i hi =>
    (List.map_inj_left.mp hpub.2.1) i (List.mem_range.mpr hi)
  have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r := hpub.1
  have eH' : dselH s₂ = dselH s₁ := by simp only [dselH, a 17 (by decide)]
  have eG' : dselG s₂ = dselG s₁ := by simp only [dselG, a 18 (by decide)]
  have rd₂ : s₂.rd = s₁.rd := by
    rw [hp₂.hrd, hp₁.hrd]
    simp only [dtabH, dtabG, stackArgAddr, a 0 (by decide), a 1 (by decide), a 2 (by decide),
      a 3 (by decide), a 4 (by decide), a 5 (by decide), a 6 (by decide), a 7 (by decide), a 8 (by decide),
      a 9 (by decide), a 10 (by decide), a 11 (by decide), a 12 (by decide), a 13 (by decide), a 14 (by decide),
      a 19 (by decide), a 20 (by decide), r .rcx (by simp), r .r8 (by simp), r .r9 (by simp), r .rsp (by simp)]
  have wr₂ : s₂.wr = s₁.wr := by
    rw [hp₂.hwr, hp₁.hwr]
    simp only [a 15 (by decide), a 16 (by decide), r .rdi (by simp), r .rsi (by simp), r .rdx (by simp)]
  exact decBody_ct oH oG sH sG eH eG hp₁.iH hp₁.iG v _ _ _ _ _ _
    ⟨s₁, ⟨s₁, ⟨h₁, decPub_refl s₁, rfl, rfl, rfl, rfl⟩, rfl⟩, ⟨s₂, ⟨h₂, hpub, eH', eG', rd₂, wr₂⟩, rfl⟩⟩ e₁ e₂

/-- `vg_rsa_oaep_decrypt`, calling `v`, meets the shared contract. -/
theorem dec_verified (v : PrivImpl) :
    Verified target (decrypt v.name v.code) (Spec.RsaOaep.decryptAnyContract abi decStack) :=
  Verified.of_correct (k := decK) (dec_correct v) (dec_constantTime v) dec_implies

end VG.Proof.RsaOaep.X86_64
