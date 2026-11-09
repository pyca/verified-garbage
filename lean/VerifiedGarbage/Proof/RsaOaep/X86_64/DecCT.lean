module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecSteps
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecPriv
import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCorrect
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Spec.RsaPkcs1Sig
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfTCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelTCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecTab
public import VerifiedGarbage.Proof.HashTable.X86_64
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.DecSteps
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelTCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.DecPriv
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCorrect
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Spec.RsaPkcs1Sig

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

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.RsaPkcs1Enc.X86_64 (PrivImpl privK privStack)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Proof.HashTable.X86_64 (tableOf tables fnsOf names Coh tabOK_of held_tableOf hashAt_tableOf fnsGood_of
  mem_names)

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
variable (ts : List FnTable)

/-- An entry state with the public data of the anchor `a`. -/
def DSib (a s : State) : Prop := (decK ts).pre s ∧ (decK ts).pub a s

/-- What `J` says of a run from an entry state with the anchor's public data. -/
def DAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, DSib ts a s ∧ J s t

theorem decPub_refl (s : State) : (decK ts).pub s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

end

/-- MGF1's table `T` at the entry state's stack argument 18, and the entry
state's addresses of statics. -/
def HS (T : FnTable) (s t : State) : Prop :=
  Abi.tableHeld 64 s.mem (stackArg s 18) (FnTable.words isa s T) ∧ t.syms = s.syms

/-- The table `T` of the label's hash function at the entry state's stack
argument 17. -/
def HL (T : FnTable) (s : State) : Prop := Abi.tableHeld 64 s.mem (stackArg s 17) (FnTable.words isa s T)

variable {ts : List FnTable}

theorem DSib.gpr {a s : State} (h : DSib ts a s) {r : Reg}
    (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem DSib.arg {a s : State} (h : DSib ts a s) {i : Nat} (hi : i < 19) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.2.1) i (List.mem_range.mpr hi)).symm

theorem DSib.syms {a s : State} (h : DSib ts a s) {n : String} (hn : n ∈ tabFns ts) : s.syms n = a.syms n :=
  (h.2.2.2.2.2.1 n hn).symm

theorem DSib.fb {a s : State} (h : DSib ts a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _; rw [h.gpr (r := .rsp) (by decide)]

theorem DSib.out_eq {a s : State} (h : DSib ts a s) : outR s = outR a := by
  unfold outR; rw [h.gpr (r := .rdi) (by decide), h.gpr (r := .rsi) (by decide)]

theorem DSib.ml_eq {a s : State} (h : DSib ts a s) : mlR s = mlR a := by
  unfold mlR; rw [h.gpr (r := .rdx) (by decide)]

theorem DSib.scr_eq {a s : State} (h : DSib ts a s) : scrD s = scrD a := by
  unfold scrD; rw [h.arg (i := 15) (by decide), h.arg (i := 16) (by decide)]

theorem DSib.k {a s : State} (h : DSib ts a s) : (s.gpr .r8).toNat = (a.gpr .r8).toNat := by
  rw [h.gpr (r := .r8) (by decide)]

theorem DSib.w_eq {a s : State} (h : DSib ts a s) {k : Nat} (hk : k ∈ decKs) : decW s k = decW a k := by
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
theorem d_taintF {J : State → State → Prop} (hJ : ∀ s t, (decK ts).pre s → J s t → DW s t)
    (rs : List Reg) (ks : List Nat) (hks : ∀ k ∈ ks, k ∈ decKs) (hpin : Pins (DAt ts J) rs) {c : Prog isa}
    (h : ∃ hc, (taint.check (frT rs ks 3) c hc).isSome = true) :
    RelCT isa (Two (DAt ts J)) c fun _ _ => True :=
  two_taintF rs ks fb (fun a => [outR a, mlR a, scrD a]) decW (fun a t ⟨s, S, j⟩ => by
      have e := hJ s t S.1 j
      rw [← S.fb, ← S.out_eq, ← S.ml_eq, ← S.scr_eq]
      exact ⟨e.he.frv (DPre.of ts S.1), fun k hk => (e.words k (hks k hk)).trans (S.w_eq (hks k hk))⟩)
    hpin (fun k hk => decKs_lt k (hks k hk)) h

/-- What correctness says after a piece. -/
theorem d_post {J J' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Two (DAt ts J)) c fun _ _ => True)
    (hw : ∀ s t, (decK ts).pre s → J s t → WP isa c t (J' s)) :
    RelCT isa (Two (DAt ts J)) c (Two (DAt ts J')) :=
  two_post hct fun _ t ⟨s, S, j⟩ => WP.mono (hw s t S.1 j) fun _ j' => ⟨s, S, j'⟩

theorem d_pins_rsp {J : State → State → Prop} (hJ : ∀ s t, (decK ts).pre s → J s t → t.gpr .rsp = fb s) :
    Pins (DAt ts J) [.rsp] :=
  fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ r hr => by
    rw [List.mem_singleton.mp hr, hJ _ _ S₁.1 j₁, hJ _ _ S₂.1 j₂, S₁.fb, S₂.fb]

/-- A branch on a condition that the entry state's public data fixes. -/
theorem d_ite {J : State → State → Prop} {cond : isa.Cond} {th el : Prog isa} {Q : State → State → Prop}
    (f : State → Option Bool) (hf : ∀ s t, J s t → isa.eval cond t = f s) (hs : ∀ a s, DSib ts a s → f s = f a)
    (ht : RelCT isa (Two fun a t => DAt ts J a t ∧ isa.eval cond t = some true) th Q)
    (he : RelCT isa (Two fun a t => DAt ts J a t ∧ isa.eval cond t = some false) el Q) :
    RelCT isa (Two (DAt ts J)) (.ite cond th el) Q :=
  two_ite (fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ => by rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]) ht he

/-- In a branch, what its condition says of the entry state. -/
theorem d_branch {J J' : State → State → Prop} {cond : isa.Cond} {b : Bool} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ s t, (decK ts).pre s → J s t → isa.eval cond t = some b → J' s t)
    (hct : RelCT isa (Two (DAt ts J')) c Q) :
    RelCT isa (Two fun a t => DAt ts J a t ∧ isa.eval cond t = some b) c Q :=
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

theorem privW_sib {a s : State} (S : DSib ts a s) {i : Nat} (hi : i < 14) : privW s i = privW a i := by
  rw [privW_eq s hi, privW_eq a hi, S.gpr (r := .r8) (by decide), S.arg (i := 1) (by decide),
    S.arg (i := 2) (by decide), S.arg (i := 3) (by decide), S.arg (i := 4) (by decide),
    S.arg (i := 5) (by decide), S.arg (i := 6) (by decide), S.arg (i := 7) (by decide),
    S.arg (i := 8) (by decide), S.arg (i := 9) (by decide), S.arg (i := 10) (by decide),
    S.arg (i := 13) (by decide), S.arg (i := 15) (by decide), S.arg (i := 16) (by decide)]

/-- What `vg_rsa_private_checked`'s contract makes public, from the anchor. -/
theorem privD_view {a s t : State} (S : DSib ts a s) (h : DSet s t) :
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
  have hp := DPre.of ts S.1
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
    exact S.2.2.2.2.1.symm

theorem privD_ct (v : PrivImpl) : RelCT isa (Two (DAt ts DSet)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := privK) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  have hp₁ := DPre.of ts S₁.1
  have hp₂ := DPre.of ts S₂.1
  obtain ⟨r₁, g₁, n₁, e₁⟩ := privD_view S₁ j₁
  obtain ⟨r₂, g₂, n₂, e₂⟩ := privD_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := privD_covers hp₁ j₁
  obtain ⟨c₂, w₂⟩ := privD_covers hp₂ j₂
  exact ⟨privRdD s₁, privWrD s₁, privRdD s₂, privWrD s₂, privD_pre hp₁ j₁, privD_pre hp₂ j₂,
    ⟨List.map_inj_left.mp (r₁.trans r₂.symm), g₁.trans g₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩,
    c₁, w₁, c₂, w₂, by rw [j₁.he.rsp, j₂.he.rsp, S₁.fb, S₂.fb]⟩

/-! ## `decMain` -/

section
variable {vs : List MdHash} (hc : Coh vs)

/-- In the frame, after the check of `k`. -/
def DK (D : Nat) (s t : State) : Prop := DW s t ∧ 2 * D + 2 ≤ (s.gpr .r8).toNat

/-- The label's hash's public data. -/
def lqD (a : State) : LQ :=
  ⟨fb a, stackArg a 15, [outR a, mlR a, scrD a], stackArg a 11, (stackArg a 12).toNat⟩

/-- The label's hash's public data with its table, that of `w₁`. -/
def lqtD (w₁ : MdHash) (a : State) : LQT :=
  ⟨lqD a, stackArg a 17, a.syms w₁.H.initN, a.syms w₁.H.updN, a.syms w₁.H.finN⟩

theorem lqtD_sib {w₁ : MdHash} (hw₁ : w₁ ∈ vs) {a s : State} (S : DSib (tables vs) a s) :
    lqtD w₁ s = lqtD w₁ a := by
  have hn := mem_names hw₁
  simp only [lqtD, lqD]
  rw [S.fb, S.out_eq, S.ml_eq, S.scr_eq, S.arg (i := 15) (by decide), S.arg (i := 11) (by decide),
    S.arg (i := 12) (by decide), S.arg (i := 17) (by decide), S.syms hn.1, S.syms hn.2.1, S.syms hn.2.2]

/-- Where MGF1 starts, for the anchor's public data. -/
theorem dme_of {src srcLen dst dstLen : Nat → Nat} {a s t : State} (S : DSib ts a s)
    (h : DWM s t (src (s.gpr .r8).toNat) (srcLen (s.gpr .r8).toNat) (dst (s.gpr .r8).toNat)
      (dstLen (s.gpr .r8).toNat))
    (hf : MFit (src (s.gpr .r8).toNat) (srcLen (s.gpr .r8).toNat) (dst (s.gpr .r8).toNat)
      (dstLen (s.gpr .r8).toNat)) :
    ME 3 ⟨fb a, stackArg a 15, [outR a, mlR a, scrD a], src (a.gpr .r8).toNat, srcLen (a.gpr .r8).toNat,
      dst (a.gpr .r8).toNat, dstLen (a.gpr .r8).toNat⟩ t := by
  have hp := DPre.of ts S.1
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

/-- MGF1's public data from the anchor's: its `MQ`, the table, and the
addresses of `w`'s functions. -/
def mqtD (w : MdHash) (q : MQ) (a : State) : Table.MQT :=
  ⟨q, stackArg a 18, a.syms w.H.initN, a.syms w.H.updN, a.syms w.H.finN⟩

include hc in
/-- Where MGF1 starts, with its table, for the anchor's public data. -/
theorem dmet_of {w : MdHash} (hw : w ∈ vs) {src srcLen dst dstLen : Nat → Nat} {a s t : State}
    (S : DSib (tables vs) a s) (hs : HS (tableOf w) s t)
    (h : DWM s t (src (s.gpr .r8).toNat) (srcLen (s.gpr .r8).toNat) (dst (s.gpr .r8).toNat)
      (dstLen (s.gpr .r8).toNat))
    (hf : MFit (src (s.gpr .r8).toNat) (srcLen (s.gpr .r8).toNat) (dst (s.gpr .r8).toNat)
      (dstLen (s.gpr .r8).toNat)) :
    Table.MET w.H.stream (fnsOf vs) 3 (frameBytes + 8 + 8 * 18)
      (mqtD w ⟨fb a, stackArg a 15, [outR a, mlR a, scrD a], src (a.gpr .r8).toNat, srcLen (a.gpr .r8).toNat,
        dst (a.gpr .r8).toNat, dstLen (a.gpr .r8).toNat⟩ a) t := by
  have hp := DPre.of _ S.1
  obtain ⟨-, -, hd⟩ := DPre.tab _ S.1
  obtain ⟨hm, -, hDm⟩ := held_tableOf hs.1
  have T := dtab hp h.he hs.2 (tabOK_of hc hd hw) hm hDm
  have hn := mem_names hw
  refine ⟨dme_of S h hf, ?_, ?_, ?_, ?_⟩
  · simp only [mqtD]; rw [← S.fb, ← S.arg (i := 18) (by decide)]; exact T
  · simp only [mqtD]; rw [hs.2]; exact S.syms hn.1
  · simp only [mqtD]; rw [hs.2]; exact S.syms hn.2.1
  · simp only [mqtD]; rw [hs.2]; exact S.syms hn.2.2

theorem dtabArg_taint : ∃ hc, (taint.check (frT [] [] 3)
    (.block (Impl.Mgf1.X86_64.Table.tabArg (frameBytes + 8 + 8 * 18) sTab)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

include hc in
theorem decMain_ct {w₁ w : MdHash} (hw₁ : w₁ ∈ vs) (hw : w ∈ vs) :
    RelCT isa (Two (DAt (tables vs) fun s t => (DK w₁.H.D s t ∧ HS (tableOf w) s t) ∧ HL (tableOf w₁) s ∧
        word t.mem (fb s) (8 * 35) = stackArg s 17))
      (decMain w₁.H.stream (fnsOf vs)) fun _ _ => True := by
  have hz := sizes w₁.ok.stream
  have hsD : w₁.H.stream.D = w₁.H.D := rfl
  have hD65 : w₁.H.D < 65 := by omega
  have hD0 := w₁.ok.hD0
  obtain ⟨hgi, hgu, hgf⟩ := fnsGood_of vs
  have hk2 : ∀ {s : State}, (decK (tables vs)).pre s → (s.gpr .r8).toNat ≤ 1024 := fun hs =>
    (DPre.of _ hs).lv.2
  unfold decMain seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `lHash`.
  refine RelCT.seq (d_post (J' := fun s t => DK w₁.H.D s t ∧ HS (tableOf w) s t) (two_map (lqtD w₁)
      (fun a t ⟨s, S, ⟨⟨e, _⟩, hs⟩, hl, h35⟩ => by
        have hp := DPre.of _ S.1
        obtain ⟨V, W, R, hW⟩ := e.rep
        obtain ⟨-, -, hd⟩ := DPre.tab _ S.1
        obtain ⟨hmL, -, hDmL⟩ := held_tableOf hl
        have T := dtabL hp e.he hs.2 (tabOK_of hc hd hw₁) hmL hDmL
        have := (⟨⟨e.he.frv hp, e.L, V, W, R, e.lab hp hW⟩, h35, ⟨t, _, T, Table.TJ.refl t _, rfl, rfl⟩,
          by rw [hs.2]; rfl, by rw [hs.2]; rfl, by rw [hs.2]; rfl⟩ : LWT w₁.H.stream (fnsOf vs) 3 (lqtD w₁ s) t)
        rwa [lqtD_sib hw₁ S] at this)
      (hashLabelT_ct w₁.ok.stream hgi hgu (.inr rfl) (Or.inr rfl)))
    fun s t hs h => by
      have hp := DPre.of _ hs
      obtain ⟨-, -, hd⟩ := DPre.tab _ hs
      obtain ⟨hmL, -, hDmL⟩ := held_tableOf h.2.1
      exact WP.mono_syms (dw_hashLabelT hp w₁.ok w₁.mgf hgi hgu hgf h.1.1.1 h.2.2
        (dtabL hp h.1.1.1.he h.1.2.2 (tabOK_of hc hd hw₁) hmL hDmL))
        fun _ e sy => ⟨⟨e, h.1.1.2⟩, h.1.2.1, sy.trans h.1.2.2⟩) ?_
  -- The seed unmasked.
  refine RelCT.seq (d_post (J' := fun s t => (DWM s t (oEm + 1 + w₁.H.D) ((s.gpr .r8).toNat - (w₁.H.D + 1)) (oEm + 1)
      w₁.H.D ∧ 2 * w₁.H.D + 2 ≤ (s.gpr .r8).toNat) ∧ HS (tableOf w) s t)
    (d_taintF (fun _ _ _ h => h.1.1) [] [] (by decide) nopin ⟨_, dSeedArgs_taint w₁.H.D hD65⟩)
    fun s t hs h => WP.mono_syms (dw_seedArgs (Hm := w₁.H.stream) (by omega) (by have := h.1.2; omega) h.1.1)
      fun _ e sy => ⟨⟨e, h.1.2⟩, h.2.1, sy.trans h.2.2⟩) ?_
  refine RelCT.seq (d_post (J' := fun s t => DK w₁.H.D s t ∧ HS (tableOf w) s t)
      (two_map (fun a => mqtD w ⟨fb a, stackArg a 15, [outR a, mlR a, scrD a],
      oEm + 1 + w₁.H.D, (a.gpr .r8).toNat - (w₁.H.D + 1), oEm + 1, w₁.H.D⟩ a)
      (fun a t ⟨s, S, ⟨e, hk⟩, hs⟩ => dmet_of hc hw (src := fun _ => oEm + 1 + w₁.H.D)
        (srcLen := fun k => k - (w₁.H.D + 1)) (dst := fun _ => oEm + 1) (dstLen := fun _ => w₁.H.D) S hs e
        (dfit_seed hk (hk2 S.1) hD0))
      (Table.mgfT_ct w.ok.stream hgi hgu hgf w.mgf.hash w.mgf.len (valid_of_link w.ok w.mgf) (.inr rfl)
        dtabArg_taint))
    fun s t hs h => by
      have hp := DPre.of _ hs
      obtain ⟨-, -, hd⟩ := DPre.tab _ hs
      obtain ⟨hm, -, hDm⟩ := held_tableOf h.2.1
      exact WP.mono_syms (dw_mgfT w.ok w.mgf hgi hgu hgf (dfit_seed h.1.2 (hk2 hs) hD0) h.1.1
        (dtab hp h.1.1.he h.2.2 (tabOK_of hc hd hw) hm hDm)) fun _ e sy => ⟨⟨e, h.1.2⟩, h.2.1, sy.trans h.2.2⟩) ?_
  -- `DB` unmasked.
  refine RelCT.seq (d_post (J' := fun s t => (DWM s t (oEm + 1) w₁.H.D (oEm + 1 + w₁.H.D)
      ((s.gpr .r8).toNat - (w₁.H.D + 1)) ∧ 2 * w₁.H.D + 2 ≤ (s.gpr .r8).toNat) ∧ HS (tableOf w) s t)
    (d_taintF (fun _ _ _ h => h.1.1) [] [] (by decide) nopin ⟨_, dDbArgs_taint w₁.H.D hD65⟩)
    fun s t hs h => WP.mono_syms (dw_dbArgs (Hm := w₁.H.stream) (by omega) (by have := h.1.2; omega) h.1.1)
      fun _ e sy => ⟨⟨e, h.1.2⟩, h.2.1, sy.trans h.2.2⟩) ?_
  refine RelCT.seq (d_post (J' := DK w₁.H.D) (two_map (fun a => mqtD w ⟨fb a, stackArg a 15,
      [outR a, mlR a, scrD a], oEm + 1, w₁.H.D, oEm + 1 + w₁.H.D, (a.gpr .r8).toNat - (w₁.H.D + 1)⟩ a)
      (fun a t ⟨s, S, ⟨e, hk⟩, hs⟩ => dmet_of hc hw (src := fun _ => oEm + 1) (srcLen := fun _ => w₁.H.D)
        (dst := fun _ => oEm + 1 + w₁.H.D) (dstLen := fun k => k - (w₁.H.D + 1)) S hs e (dfit_db hk (hk2 S.1)))
      (Table.mgfT_ct w.ok.stream hgi hgu hgf w.mgf.hash w.mgf.len (valid_of_link w.ok w.mgf) (.inr rfl)
        dtabArg_taint))
    fun s t hs h => by
      have hp := DPre.of _ hs
      obtain ⟨-, -, hd⟩ := DPre.tab _ hs
      obtain ⟨hm, -, hDm⟩ := held_tableOf h.2.1
      exact WP.mono (dw_mgfT w.ok w.mgf hgi hgu hgf (dfit_db h.1.2 (hk2 hs)) h.1.1
        (dtab hp h.1.1.he h.2.2 (tabOK_of hc hd hw) hm hDm)) fun _ e => ⟨e, h.1.2⟩) ?_
  -- The checks, and `T` shifted into the buffer.
  refine RelCT.assoc ?_
  refine RelCT.assoc ?_
  refine RelCT.assoc ?_
  refine RelCT.assoc ?_
  refine RelCT.seq (d_post (J' := DW) (c := tail1 w₁.H.stream)
    (d_taintF (fun _ _ _ h => h.1) [] [14, 23] (by decide) nopin ⟨_, tail1_taint w₁.H.D hD65⟩)
    fun s t hs h => dw_tail1 (DPre.of _ hs) (Hm := w₁.H.stream) hD0 (by omega) h.2 h.1) ?_
  -- `ok`, `out` and `*msg_len`.
  refine RelCT.assoc ?_
  refine RelCT.seq (d_post (J' := DW)
    (d_taintF (fun _ _ _ h => h) [] [14, 21, 23] (by decide) nopin ⟨_, by taint_decide⟩)
    fun s t hs h => dw_tail2 (DPre.of _ hs) h) ?_
  exact d_taintF (fun _ _ _ h => h) [] [23, 29] (by decide) nopin ⟨_, decRet_taint w₁.H.D hD65⟩

omit hc in
theorem decFail_ct : RelCT isa (Two (DAt ts DW)) decFail fun _ _ => True :=
  d_taintF (fun _ _ _ h => h) [] [21, 23, 29] (by decide) nopin ⟨_, by taint_decide⟩

/-- After the call. -/
def JC (s t : State) : Prop :=
  EnvD s t ∧ Lay t (fb s) (stackArg s 15) ∧ ∃ V, Rep t.mem (fb s) (stackArg s 15) V (privW s)

/-- After the address of the table of the label's hash function to its slot. -/
def JS (s t : State) : Prop :=
  EnvD s t ∧ Lay t (fb s) (stackArg s 15) ∧
    ∃ V, Rep t.mem (fb s) (stackArg s 15) V (upd (privW s) 35 (stackArg s 17))

/-- After the check of `k`. -/
def JK (D : Nat) (s t : State) : Prop := DW s t ∧ t.cf = some (decide ((s.gpr .r8).toNat < 2 * D + 2))

omit hc in
theorem ArgsD_privW35 (s : State) : ArgsD s (upd (privW s) 35 (stackArg s 17)) :=
  (ArgsD_privW s).of fun j hj => by have := decKs_iff hj; simp only [upd]; rw [ifn (by omega)]

omit hc in
theorem JS.dw {s t : State} (h : JS s t) : DW s t :=
  let ⟨V, R⟩ := h.2.2; ⟨h.1, h.2.1, V, _, R, ArgsD_privW35 s⟩

omit hc in
/-- `JS` in a state with the flags of another. -/
theorem JS.after {s t t' : State} (h : JS s t) (k : Keep [] t t') (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) : JS s t' :=
  let ⟨V, R⟩ := h.2.2
  ⟨h.1.step k.2.1 k.2.2 (k.gpr (by simp)) (keep_cs3 k rfl) hmx (by rw [hm]; exact Frame.refl _ _),
    h.2.1.congr (k.gpr (by simp)) k.2.2 (by rw [hm]), V, hm ▸ R⟩

theorem dtabSlot_taint : ∃ hc, (taint.check (frT [] [] 3) (.block (tabSlot 17)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dlenLoad_taint : ∃ hc, (taint.check (frT [] [35] 3) (.block lenLoad) hc).isSome = true :=
  ⟨_, by taint_decide⟩

include hc in
theorem decBody_ct (v : PrivImpl) {w₁ w : MdHash} (hw₁ : w₁ ∈ vs) (hw : w ∈ vs) :
    RelCT isa (Two (DAt (tables vs) fun s t => (JA s t ∧ HS (tableOf w) s t) ∧ HL (tableOf w₁) s))
      (decBody (fnsOf vs) v.name v.code) fun _ _ => True := by
  have hz := sizes w₁.ok.stream
  have hsD : w₁.H.stream.D = w₁.H.D := rfl
  have hD65 : w₁.H.D < 65 := by omega
  unfold decBody seqs seqs seqs seqs
  refine RelCT.seq (d_post (J' := fun s t => (DSet s t ∧ HS (tableOf w) s t) ∧ HL (tableOf w₁) s)
    (two_taint [.rsp] (d_pins_rsp fun s t _ h => by rw [h.1.1]; rfl) dHead_taint)
    fun s t hs h => by
      obtain ⟨⟨rfl, hs'⟩, hl⟩ := h
      exact WP.mono_syms (decHead_ok (DPre.of _ hs)) fun _ e sy => ⟨⟨e, hs'.1, sy.trans hs'.2⟩, hl⟩) ?_
  refine RelCT.seq (d_post (J' := fun s t => (JC s t ∧ HS (tableOf w) s t) ∧ HL (tableOf w₁) s)
    ((privD_ct v).mono (fun _ _ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ⟨a, ⟨s₁, S₁, j₁.1.1⟩, ⟨s₂, S₂, j₂.1.1⟩⟩)
      fun _ _ h => h) fun s t hs h =>
    WP.mono_syms (privD_call v (DPre.of _ hs) h.1.1) fun _ ⟨he, L, R, _⟩ sy => ⟨⟨⟨he, L, _, R⟩, h.1.2.1,
      sy.trans h.1.2.2⟩, h.2⟩) ?_
  -- The address of the table of the label's hash function to its slot.
  refine RelCT.seq (d_post (J' := fun s t => (JS s t ∧ HS (tableOf w) s t) ∧ HL (tableOf w₁) s)
    (d_taintF (fun _ _ _ ⟨⟨⟨he, L, V, R⟩, _⟩, _⟩ => ⟨he, L, V, _, R, ArgsD_privW _⟩) [] [] (by decide) nopin
      dtabSlot_taint) fun s t hs h => ?_) ?_
  · obtain ⟨⟨⟨he, L, V, R⟩, hs'⟩, hl⟩ := h
    have hp := DPre.of _ hs
    obtain ⟨-, -, hd⟩ := DPre.tab _ hs
    obtain ⟨hmL, -, hDmL⟩ := held_tableOf hl
    exact WP.mono_syms (wp_good (block_good _ rfl) (tabSlot_ok L R (dtabL hp he hs'.2 (tabOK_of hc hd hw₁) hmL hDmL)))
      fun t' ⟨⟨k, L', R', _⟩, sp, mx, f⟩ sy => ⟨⟨⟨he.step k.2.1 k.2.2 sp (keep_cs3 k (by decide)) mx f, L', V, R'⟩,
        hs'.1, sy.trans hs'.2⟩, hl⟩
  -- Its digest length to `r11`.
  refine RelCT.seq (d_post (J' := fun s t => ((JS s t ∧ t.gpr .r11 = BitVec.ofNat 64 w₁.H.D) ∧
      HS (tableOf w) s t) ∧ HL (tableOf w₁) s)
    (two_taintF [] [35] fb (fun a => [outR a, mlR a, scrD a]) (fun a _ => stackArg a 17)
      (fun a t ⟨s, S, ⟨⟨⟨he, L, V, R⟩, _⟩, _⟩⟩ => by
        rw [← S.fb, ← S.out_eq, ← S.ml_eq, ← S.scr_eq, ← S.arg (i := 17) (by decide)]
        refine ⟨he.frv (DPre.of _ S.1), fun k hk => ?_⟩
        simp only [List.mem_singleton] at hk; subst hk
        rw [R.fr 35 (by decide)]; simp [upd])
      nopin (by decide) dlenLoad_taint)
    fun s t hs h => ?_) ?_
  · obtain ⟨⟨⟨he, L, V, R⟩, hs'⟩, hl⟩ := h
    have hp := DPre.of _ hs
    obtain ⟨-, -, hd⟩ := DPre.tab _ hs
    obtain ⟨hmL, -, hDmL⟩ := held_tableOf hl
    have T := dtabL hp he hs'.2 (tabOK_of hc hd hw₁) hmL hDmL
    exact WP.mono_syms (wp_good (block_good _ rfl) (lenLoad_ok L R (by simp [upd]) T.rdD
        (T.mem _ (Frame.refl _ _)).2.1))
      fun t' ⟨⟨k, h11, hm, _⟩, sp, mx, f⟩ sy => ⟨⟨⟨⟨he.step k.2.1 k.2.2 sp (keep_cs3 k (by decide)) mx f,
        L.congr (k.gpr (by decide)) k.2.2 (by rw [hm]), V, hm ▸ R⟩, h11⟩, hs'.1, sy.trans hs'.2⟩, hl⟩
  -- The tail for that length.
  have hDl : w₁.H.D ∈ lens := by rw [← w₁.mgf.len]; exact mem_lens w₁.mgf.mem
  refine byLen_ct (fun _ => w₁.H.D) cmpLens_taint (fun a t ⟨_, _, ⟨⟨⟨_, h11⟩, _⟩, _⟩⟩ =>
    ⟨h11, hDl, mem_lens_lt hDl⟩) fun d _ => ?_
  by_cases hdd : w₁.H.D = d
  swap
  · exact RelCT.of_false fun _ _ ⟨_, ⟨_, e⟩, _⟩ => hdd e
  subst hdd
  dsimp only
  rw [decTail_D (G := ofLen w₁.H.D) (G' := w₁.H.stream) rfl]
  refine (?_ : RelCT isa (Two (DAt (tables vs) fun s t => (JS s t ∧ HS (tableOf w) s t) ∧ HL (tableOf w₁) s))
    (decTail w₁.H.stream (fnsOf vs)) _).mono (fun _ _ ⟨a, ⟨⟨t₁, ⟨s₁, S₁, j₁⟩, k₁, m₁, y₁, x₁⟩, _⟩,
      ⟨⟨t₂, ⟨s₂, S₂, j₂⟩, k₂, m₂, y₂, x₂⟩, _⟩⟩ =>
    ⟨a, ⟨s₁, S₁, ⟨j₁.1.1.1.after k₁ m₁ x₁, j₁.1.2.1, y₁.trans j₁.1.2.2⟩, j₁.2⟩,
      ⟨s₂, S₂, ⟨j₂.1.1.1.after k₂ m₂ x₂, j₂.1.2.1, y₂.trans j₂.1.2.2⟩, j₂.2⟩⟩) fun _ _ h => h
  unfold decTail seqs
  refine RelCT.seq (d_post (J' := fun s t => ((JK w₁.H.D s t ∧ word t.mem (fb s) (8 * 35) = stackArg s 17) ∧
      HS (tableOf w) s t) ∧ HL (tableOf w₁) s)
    (d_taintF (fun _ _ _ h => h.1.1.dw) [] [23] (by decide) nopin ⟨_, resK_taint w₁.H.D hD65⟩)
    fun s t hs h => ?_) ?_
  · obtain ⟨⟨⟨he, L, V, R⟩, hs'⟩, hl⟩ := h
    have hp := DPre.of _ hs
    have hk1 := hp.lv.1; have hk2 := hp.lv.2
    obtain ⟨-, -, -, w23, -⟩ := (ArgsD_privW35 s).w
    exact WP.mono_syms (wp_good (block_good _ rfl) (resK_ok (Hm := w₁.H.stream) L R (k := (s.gpr .r8).toNat)
      (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega) (by omega)))
      fun t2 ⟨⟨k2, L2, R2, hcf2⟩, sp2, mx2, f2⟩ sy => ⟨⟨⟨⟨⟨he.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2,
        L2, _, _, R2, (ArgsD_privW35 s).of fun j hj => by
          simp only [upd]; rw [ifn (by have := decKs_iff hj; omega)]⟩, by rw [hcf2, hsD]⟩,
        by rw [R2.fr 35 (by decide)]; simp [upd]⟩, hs'.1, sy.trans hs'.2⟩, hl⟩
  refine d_ite (fun s => some (decide ((s.gpr .r8).toNat < 2 * w₁.H.D + 2))) (fun s t h => h.1.1.1.2)
    (fun a s S => by rw [S.k]) (d_branch (J' := DW) (fun _ _ _ h _ => h.1.1.1.1) decFail_ct)
    (d_branch (J' := fun s t => (DK w₁.H.D s t ∧ HS (tableOf w) s t) ∧ HL (tableOf w₁) s ∧
        word t.mem (fb s) (8 * 35) = stackArg s 17)
      (fun s t _ h e => ⟨⟨⟨h.1.1.1.1, by have := cf_false h.1.1.1.2 e; omega⟩, h.1.2⟩, h.2, h.1.1.2⟩)
      (decMain_ct hc hw₁ hw))

include hc in
theorem dec_constantTime (v : PrivImpl) :
    ConstantTime isa (decK (tables vs)).pre (decK (tables vs)).pub (decrypt (fnsOf vs) v.name v.code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨⟨T₁, hT₁, hheld₁⟩, ⟨T, hT, hheld⟩, -⟩ := DPre.tab _ h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have key := relCT_alloc (P := fun x y => (decK (tables vs)).pre x ∧ (decK (tables vs)).pre y ∧
      (decK (tables vs)).pub x y ∧ Abi.tableHeld 64 x.mem (stackArg x 17) (FnTable.words isa x (tableOf w₁)) ∧
      Abi.tableHeld 64 x.mem (stackArg x 18) (FnTable.words isa x (tableOf w)))
    ((decBody_ct hc v hw₁ hw).mono (fun _ _ ⟨x, y, ⟨hx, hy, hxy, hh₁, hh⟩, ex, ey⟩ =>
      ⟨x, ⟨x, ⟨hx, decPub_refl _ x⟩, ⟨ex, hh, by rw [ex]; rfl⟩, hh₁⟩,
        ⟨y, ⟨hy, hxy⟩, ⟨ey, (hxy.2.2.2.2.2.2 _ (List.mem_map_of_mem hw)).mp hh, by rw [ey]; rfl⟩,
          (hxy.2.2.2.2.2.1 _ (List.mem_map_of_mem hw₁)).mp hh₁⟩⟩) fun _ _ h => h)
  exact (key _ _ _ _ _ _ ⟨h₁, h₂, hpub, hheld₁, hheld⟩ e₁ e₂).1

include hc in
/-- `vg_rsa_oaep_decrypt` meets the shared contract, with the tables of `vs`
for both of its hash functions. -/
theorem dec_verified (v : PrivImpl) (hsat : ∃ s, (decC (tables vs)).pre s) :
    Verified target (decrypt (fnsOf vs) v.name v.code) (decC (tables vs)) :=
  Verified.of_correct (k := decK (tables vs)) (dec_correct hc v) (dec_constantTime hc v)
    (dec_implies (tables vs) hsat)

end

end VG.Proof.RsaOaep.X86_64
