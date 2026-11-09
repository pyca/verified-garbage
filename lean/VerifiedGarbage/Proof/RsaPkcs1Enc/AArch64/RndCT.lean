module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndCTScan
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcVerified
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndCTScan
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndBody
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndInvoke
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndCall
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndBody
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndInvoke
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndCall

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: constant time, and `Verified`

After the scan (`RndCTScan`), both runs have kept as many octets, so they
take the same branch on whether `PS` is full. With `PS` full: the call's
arguments by the taint analysis, with `tape` public; the call of
`vg_rsa_pkcs1_encrypt_precomputed`, constant time for its contract, whose
public data both runs share; and the status and the wipe, whose length is a
constant. Otherwise `reject`, which branches only on `n_len` and constants,
by the taint analysis with `out`, `tape` and `n_len` public.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random
open VG.Proof.Bignum.AArch64 (Two two_post two_taint two_piece two_ite)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)

variable {P : Nat}

/-- On entry to the frames' body. -/
def AllocPt (P : Nat) (a t : State) : Prop := ∃ s, PR P a s ∧ t = entered s

theorem setup_two : RelCT isa (Two (AllocPt P)) (.block setup) (Two (ScanPt P)) :=
  two_piece [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
    fun a t ⟨s, S, e⟩ => by subst e; exact WP.mono (setup_ok S.pre) fun u B => ⟨s, S, B⟩

/-- The registers both runs share, from the entry. -/
theorem keepS {s t₀ u : State} (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u) {r : Reg}
    (hr : r ∉ [Reg.x9, .x11, .x12, .x14, .x15, .x16, .x17]) : u.gpr r = s.gpr r :=
  ((hb.keep.trans hI.keep).mono (by decide)) r hr

/-! ## `PS` full -/

def AccPt (P : Nat) (a u : State) : Prop :=
  ∃ s t₀, PR P a s ∧ Before s t₀ ∧ At s t₀ (N a) u ∧ (kept s (N a)).length = psLen s

def ArgsPt (P : Nat) (a w : State) : Prop := ∃ s, PR P a s ∧ Args s w (N a) (kept s (N a))

def AfterPt (P : Nat) (a u : State) : Prop := ∃ s, PR P a s ∧ AfterCall P s u (N a) (kept s (N a))

theorem args_two : RelCT isa (Two (AccPt P)) (.block callArgs) (Two (ArgsPt P)) :=
  two_piece [.x2] (fun a u₁ u₂ ⟨s₁, t₁, S₁, B₁, I₁, _⟩ ⟨s₂, t₂, S₂, B₂, I₂, _⟩ r hr => by
      rw [List.mem_singleton.mp hr, keepS B₁ I₁ (by decide), keepS B₂ I₂ (by decide),
        S₁.gprEq (by decide), S₂.gprEq (by decide)]) (by taint_decide)
    fun a u ⟨s, t₀, S, B, I, hf⟩ => WP.mono (args_ok S.pre (ready_of S.pre B I hf)) fun w h => ⟨s, S, h⟩

theorem entry_gpr (w : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (w.callEntry.withRegions rd wr).gpr r = w.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem call_ct (c : PdChecked) :
    RelCT isa (Two (ArgsPt c.stack)) (.call (encName c) (encCode c)) fun _ _ => True := by
  refine RelCT.callEx (k := Enc.Pc.contract c.stack)
    (fun _ h => by obtain ⟨t, s', he, hq⟩ := Enc.Pc.code_ok c h; exact ⟨t, s', he, hq⟩)
    (Enc.Pc.code_constantTime c) fun w₁ w₂ ⟨a, ⟨s₁, S₁, A₁⟩, ⟨s₂, S₂, A₂⟩, hsp⟩ => ?_
  obtain ⟨c₁, w₁'⟩ := call_covers S₁.pre A₁
  obtain ⟨c₂, w₂'⟩ := call_covers S₂.pre A₂
  obtain ⟨n₁, e₁, -, q₁⟩ := args_read S₁.pre A₁
  obtain ⟨n₂, e₂, -, q₂⟩ := args_read S₂.pre A₂
  have g₁ : ∀ {r : Reg}, r ∉ linkRegs → _ := fun {r} h => entry_gpr w₁ (callRd s₁) (callWr s₁) (r := r) h
  have g₂ : ∀ {r : Reg}, r ∉ linkRegs → _ := fun {r} h => entry_gpr w₂ (callRd s₂) (callWr s₂) (r := r) h
  have ga : ∀ j < 6, stackArg (w₁.callEntry.withRegions (callRd s₁) (callWr s₁)) j =
      stackArg (w₂.callEntry.withRegions (callRd s₂) (callWr s₂)) j := fun j hj => by
    rw [stackArg_call A₁ _ _ hj, stackArg_call A₂ _ _ hj]
    match j, hj with
    | 0, _ => show off (Q s₁) oBuf = off (Q s₂) oBuf; rw [S₁.QEq, S₂.QEq]
    | 1, _ => show BitVec.ofNat 64 (psLen s₁) = BitVec.ofNat 64 (psLen s₂); rw [S₁.psEq, S₂.psEq]
    | 2, _ => show stackArg s₁ 3 = stackArg s₂ 3; rw [S₁.argEq (by decide), S₂.argEq (by decide)]
    | 3, _ => show stackArg s₁ 4 = stackArg s₂ 4; rw [S₁.argEq (by decide), S₂.argEq (by decide)]
    | 4, _ => show stackArg s₁ 5 = stackArg s₂ 5; rw [S₁.argEq (by decide), S₂.argEq (by decide)]
    | 5, _ => show stackArg s₁ 6 = stackArg s₂ 6; rw [S₁.argEq (by decide), S₂.argEq (by decide)]
  have rg : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], s₁.gpr r = s₂.gpr r := fun r hr =>
    (S₁.gprEq hr).trans (S₂.gprEq hr).symm
  have hx' : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], r ∉ linkRegs := by decide
  have hx : ∀ {r : Reg}, r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] → r ∉ linkRegs := fun h => hx' _ h
  refine ⟨callRd s₁, callWr s₁, callRd s₂, callWr s₂, call_pre S₁.pre A₁, call_pre S₂.pre A₂, ?_, c₁.append_left
    w₁'.right, w₁', c₂.append_left w₂'.right, w₂'⟩
  refine ⟨⟨by simp only [State.withRegions_sp, State.callEntry_sp, A₁.sp, A₂.sp, S₁.QEq, S₂.QEq], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ga 0 (by decide), ga 1 (by decide), ga 2 (by decide), ga 3 (by decide), ?_, ?_⟩,
    ga 4 (by decide), ga 5 (by decide), ?_⟩
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x0, A₂.x0]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x1, A₂.x1]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x2, A₂.x2]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x3, A₂.x3]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x4, A₂.x4]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x5, A₂.x5]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x6, A₂.x6]; exact rg _ (by simp)
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x7, A₂.x7, S₁.argEq (by decide), S₂.argEq (by decide)]
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x2, A₂.x2, A₁.x3, A₂.x3,
      State.withRegions_mem, State.withRegions_mem, State.callEntry_mem, State.callEntry_mem, n₁, n₂,
      S₁.2.2.2.2.1.symm.trans S₂.2.2.2.2.1]
  · rw [g₁ (hx (by simp)), g₂ (hx (by simp)), g₁ (hx (by simp)), g₂ (hx (by simp)), A₁.x4, A₂.x4, A₁.x5, A₂.x5,
      State.withRegions_mem, State.withRegions_mem, State.callEntry_mem, State.callEntry_mem, e₁, e₂,
      S₁.2.2.2.2.2.1.symm.trans S₂.2.2.2.2.2.1]
  · rw [stackArg_call A₁ _ _ (j := 4) (by decide), stackArg_call A₂ _ _ (j := 4) (by decide),
      stackArg_call A₁ _ _ (j := 5) (by decide), stackArg_call A₂ _ _ (j := 5) (by decide),
      State.withRegions_mem, State.withRegions_mem, State.callEntry_mem, State.callEntry_mem]
    show Spec.Rsa.wordsAt w₁.mem (stackArg s₁ 5) (stackArg s₁ 6).toNat = Spec.Rsa.wordsAt w₂.mem (stackArg s₂ 5)
      (stackArg s₂ 6).toNat
    rw [q₁, q₂, S₁.2.2.2.2.2.2.1.symm.trans S₂.2.2.2.2.2.2.1]

theorem call_two (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s) :
    RelCT isa (Two (ArgsPt c.stack)) (.call (encName c) (encCode c)) (Two (AfterPt c.stack)) :=
  two_post (call_ct c) fun _ _ ⟨s, S, A⟩ => WP.mono (call_ok c hsat S.pre A) fun _ h => ⟨s, S, h⟩

theorem tail_two : RelCT isa (Two (AfterPt P)) (.seq (.block status) wipe) fun _ _ => True :=
  two_taint [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)

theorem accept_ct (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s) :
    RelCT isa (Two (AccPt c.stack)) (accept (encName c) (encCode c)) fun _ _ => True :=
  RelCT.seq args_two (RelCT.seq (call_two c hsat) tail_two)

/-! ## `PS` not full -/

def RejPt (P : Nat) (a u : State) : Prop := ∃ s t₀, PR P a s ∧ Before s t₀ ∧ At s t₀ (N a) u

theorem reject_ct : RelCT isa (Two (RejPt P)) reject fun _ _ => True :=
  two_taint [.x0, .x2, .x4] (fun a u₁ u₂ ⟨s₁, t₁, S₁, B₁, I₁⟩ ⟨s₂, t₂, S₂, B₂, I₂⟩ r hr => by
    rw [keepS B₁ I₁ (by revert hr; revert r; decide), keepS B₂ I₂ (by revert hr; revert r; decide),
      S₁.gprEq (by revert hr; revert r; decide), S₂.gprEq (by revert hr; revert r; decide)]) (by taint_decide)

/-! ## The body -/

theorem x16_eq {a s t₀ u : State} (S : PR P a s) (I : At s t₀ (N a) u) :
    u.gpr .x16 = BitVec.ofNat 64 (psLen a - (kept a (N a)).length) := by
  rw [I.x16, S.psEq, S.keptEq (Nat.le_refl _)]

theorem body_ct (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s) :
    RelCT isa (Two (AllocPt c.stack)) (body (encName c) (encCode c)) fun _ _ => True := by
  refine RelCT.seq setup_two (RelCT.seq scan_two (two_ite
    (fun a w₁ w₂ ⟨s₁, t₁, S₁, _, I₁⟩ ⟨s₂, t₂, S₂, _, I₂⟩ => by
      rw [eval_zero, eval_zero, x16_eq S₁ I₁, x16_eq S₂ I₂])
    ((accept_ct c hsat).mono (fun w₁ w₂ ⟨a, ⟨⟨s₁, t₁, S₁, B₁, I₁⟩, e₁⟩, ⟨⟨s₂, t₂, S₂, B₂, I₂⟩, e₂⟩, hsp⟩ => ?_)
      fun _ _ h => h)
    (reject_ct.mono (fun w₁ w₂ ⟨a, ⟨⟨s₁, t₁, S₁, B₁, I₁⟩, _⟩, ⟨⟨s₂, t₂, S₂, B₂, I₂⟩, _⟩, hsp⟩ =>
      ⟨a, ⟨s₁, t₁, S₁, B₁, I₁⟩, ⟨s₂, t₂, S₂, B₂, I₂⟩, hsp⟩) fun _ _ h => h)))
  have full : ∀ {s t₀ w : State}, PR c.stack a s → At s t₀ (N a) w → isa.eval (.zero .x .x16) w = some true →
      (kept s (N a)).length = psLen s := fun {s t₀ w} S I e => by
    rw [eval_zero, I.x16] at e
    have hc := I.hc
    have hP : psLen s < 2 ^ 64 := by have := S.pre.ps; omega
    have h0 : BitVec.ofNat 64 (psLen s - (kept s (N a)).length) = 0 := by
      simpa using e
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    simp at this; omega
  exact ⟨a, ⟨s₁, t₁, S₁, B₁, I₁, full S₁ I₁ e₁⟩, ⟨s₂, t₂, S₂, B₂, I₂, full S₂ I₂ e₂⟩, hsp⟩

theorem pub_refl (s : State) : pub s s :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem code_constantTime (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s) :
    ConstantTime isa (contract c.stack).pre (contract c.stack).pub (code (encName c) (encCode c)) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => h.2.2.1) (RelCT.alloc (R := fun _ _ => True)
    ((body_ct c hsat).mono ?_ fun _ _ h => h)))
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  refine ⟨s₁, ⟨s₁, ⟨h₁, pub_refl s₁⟩, rfl⟩, ⟨s₂, ⟨h₂, hp⟩, rfl⟩, ?_⟩
  show (entered s₁).sp = (entered s₂).sp
  rw [entered_sp, entered_sp]
  show s₁.sp - _ = s₂.sp - _
  rw [hp.1]

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_encrypt_random`, calling `vg_rsa_pkcs1_encrypt_precomputed` with the
precomputed public operation `c`, meets the shared contract with `c.stack + 2192`
bytes of stack. -/
theorem code_verified (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s)
    (hsat' : ∃ s, (Spec.RsaPkcs1Enc.encryptRandomContract AArch64.abi (rndStack c.stack)).pre s) :
    Verified AArch64.target (code (encName c) (encCode c))
      (Spec.RsaPkcs1Enc.encryptRandomContract AArch64.abi (rndStack c.stack)) :=
  Verified.of_correct (k := contract c.stack) (fun _ h => by
    obtain ⟨t, s', he, hq⟩ := code_ok c hsat (pre_of h)
    exact ⟨t, s', he, hq⟩) (code_constantTime c hsat) (implies c.stack hsat')

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd
