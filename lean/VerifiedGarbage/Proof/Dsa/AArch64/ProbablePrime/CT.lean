module

public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Body
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrimeCT
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT -- shake: keep (pairs with its `public meta import` for `taint_decide`)
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public meta import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Body
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CheckPrimeCT
public meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # The probable-prime test's timing depends only on its public inputs -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.ProbablePrime VG.Impl.Dsa.Generation.Layout VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Dsa.AArch64.Generation (PrimeParams PrimeCallPublic PrimeBytesPublic PrimeFramePublic
  PrimeFrameInputs CheckPrimeBefore allocState)
open VG.Impl.Bignum.AArch64 (ldh)

/-- What the contract makes public: the arguments, the stack pointer, the
candidate and the tape. -/
structure View where
  x0 : Addr
  x1 : Addr
  x2 : Addr
  x3 : Addr
  x4 : Addr
  sp : Addr
  N : Nat
  rand : List Byte

def view (bits : Nat) (s : State) : View :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.sp, candidateOf bits s,
    Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat⟩

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem view_of_pub {bits : Nat} {s₁ s₂ : State} (h : (contract bits).pub s₁ s₂) :
    view bits s₁ = view bits s₂ := by
  sig_pub [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4⟩ := h
  obtain ⟨hN, hr⟩ := List.cons.inj hl
  have hr' := map_toNat_inj hr
  unfold view candidateOf
  rw [hN, hr', hsp, h0, h1, h2, h3, h4]

/-- Big-endian octet strings of one length are equal if their values are. -/
theorem os2ip_inj : ∀ {l₁ l₂ : List Byte}, l₁.length = l₂.length →
    Spec.Rsa.os2ip l₁ = Spec.Rsa.os2ip l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | a :: l₁, b :: l₂, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [os2ip_cons, os2ip_cons, hl] at h
    have h₁ := os2ip_lt l₁
    have h₂ := os2ip_lt l₂
    rw [hl] at h₁
    have hd : (a.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₁) / 256 ^ l₂.length =
        (b.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₂) / 256 ^ l₂.length := by rw [h]
    have hm : (a.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₁) % 256 ^ l₂.length =
        (b.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₂) % 256 ^ l₂.length := by rw [h]
    have hp : 0 < 256 ^ l₂.length := Nat.pow_pos (by decide)
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h₁, Nat.zero_add,
      Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h₂, Nat.zero_add] at hd
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₁,
      Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₂] at hm
    rw [BitVec.eq_of_toNat_eq hd, os2ip_inj hl hm]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem params_ext {P Q : PrimeParams} (hB : P.B = Q.B) (hp : P.p = Q.p) (hrp : P.rp = Q.rp)
    (hZ : P.Z = Q.Z) (hw : P.w = Q.w) (hN : P.N = Q.N) (hlen : P.len = Q.len)
    (hd : P.drawBytes = Q.drawBytes) (hc : P.checks = Q.checks) (hr : P.rand = Q.rand) : P = Q := by
  cases P; cases Q
  simp only at hB hp hrp hZ hw hN hlen hd hc hr
  subst hB hp hrp hZ hw hN hlen hd hc hr
  rfl

/-- The test's public parameters, as the generation's timing lemmas take them. -/
def callPublic {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) : PrimeCallPublic where
  draw := ⟨params hb A, 0⟩
  arena := s.gpr .x0
  base := rfl
  width := by change words bits ≤ 48; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  tab := by
    change Bignum.slot (words bits) aTab + 2048 ≤ arithmeticBytes
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  large := by
    change 8161 < candidateOf bits s
    have hlow := ((bitLength_iff_bounds (by have := hb.le; omega)).mp A.bits).1
    have h2 : 2 ^ 159 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by have := hb.le; omega)
    have : (8161 : Nat) < 2 ^ 159 := by decide
    exact Nat.lt_of_lt_of_le this (Nat.le_trans h2 hlow)
  policy := by
    change 1024 < Spec.Dsa.bitLength (candidateOf bits s) ↔ 16 < words bits
    rw [A.bits]; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide

def bytesPublic {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) : PrimeBytesPublic where
  call := callPublic hb A
  source := off (s.gpr .x0) (candidate bits)
  bytes := Spec.Rsa.bytesAt s.mem (off (s.gpr .x0) (candidate bits)) (len bits)
  length := bytesAt_length _ _ _
  value := rfl

def framePublic {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) : PrimeFramePublic where
  bytes := bytesPublic hb A
  F := frameBase s
  candidate := candidate bits
  candidateBound := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  checksBound := by change checks bits < _; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  checks := by
    change checks bits = Spec.Dsa.primeChecks (Spec.Dsa.bitLength (candidateOf bits s))
    rw [A.bits]; rfl
  source := rfl
  witness := rfl
  separate := by
    intro k hk j hj
    have D0 : Region.Disjoint ⟨frameBase s, 272⟩ ⟨off (s.gpr .x0) arithmetic, arithmeticBytes⟩ :=
      (A.stackWs.sub_left (frame_sub s)).sub_right (ws_sub A (by decide))
    exact D0.sep (frame_contains s (by omega))
      (Offset.contains_base _ (by change 8 * j + 8 ≤ arithmeticBytes; unfold arithmeticBytes; omega) (by omega))
  outside := by
    intro k hk i hi
    have D0 : Region.Disjoint ⟨frameBase s, 272⟩ ⟨off (s.gpr .x0) arithmetic, arithmeticBytes⟩ :=
      (A.stackWs.sub_left (frame_sub s)).sub_right (ws_sub A (by decide))
    rw [off_off]
    exact out_scr D0 (frame_contains s (by omega))

theorem framePublic_eq {bits : Nat} (hb : Supported bits) {s₁ s₂ : State} (A₁ : PrimeABI bits s₁)
    (A₂ : PrimeABI bits s₂) (hv : view bits s₁ = view bits s₂) : framePublic hb A₁ = framePublic hb A₂ := by
  simp only [view, View.mk.injEq] at hv
  obtain ⟨h0, -, h2, -, -, hsp, hN, hr⟩ := hv
  have hP : params hb A₁ = params hb A₂ :=
    params_ext (by simp only [params, h0]) (by simp only [params, h0]) h2 rfl rfl hN rfl rfl rfl hr
  have hbytes : Spec.Rsa.bytesAt s₁.mem (off (s₁.gpr .x0) (candidate bits)) (len bits) =
      Spec.Rsa.bytesAt s₂.mem (off (s₂.gpr .x0) (candidate bits)) (len bits) :=
    os2ip_inj (by rw [bytesAt_length, bytesAt_length]) hN
  rw [h0] at hbytes
  have hF : frameBase s₁ = frameBase s₂ := by simp only [frameBase, hsp]
  unfold framePublic bytesPublic callPublic
  simp only [hP, hbytes, h0, hF]

theorem before_of_prepared {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {u : State}
    (P : Prepared hb A u) :
    CheckPrimeBefore (words bits) (candidate bits) (len bits) (draw bits) (checks bits) (framePublic hb A) u := by
  have hws : wsRegion s ∈ s.wr := by rw [A.wr]; exact List.mem_cons_self
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨⟨P.sp, fun k hk => ⟨_, List.mem_append_right _ (by rw [P.wr]; exact List.mem_cons_self),
      frame_contains s (by omega)⟩, P.arena, P.tapePtr, ?_,
      by change word u.mem (frameBase s) 128 = BitVec.ofNat 64 0; rw [P.used]; rfl, P.tape, P.source,
      fun i hi => ?_, Nat.zero_le _⟩, P.scr, P.x0, rfl, rfl, rfl, rfl, rfl⟩
  · change word u.mem (frameBase s) 120 =
      BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat).length
    rw [P.tapeLength]
    rw [bytesAt_length, ofNat_toNat64]
  · refine ⟨_, by rw [P.wr]; exact List.mem_cons_of_mem _ hws, ?_⟩
    change (wsRegion s).Contains (off (off (s.gpr .x0) witness) i) 1
    change i < len bits at hi
    rw [off_off]
    exact Offset.contains_base _ (by have := A.size; have : witness + 384 ≤ domainCheck := (by decide); omega)
      (by have : witness + 384 < 2 ^ 64 := (by decide); omega)

/-! ## The stages, each with the public view of the arguments -/

def Entered (bits : Nat) (v : View) (u : State) : Prop :=
  ∃ s, ∃ _ : PrimeABI bits s, view bits s = v ∧ u = allocState 272 s

def PreparedAt {bits : Nat} (hb : Supported bits) (v : View) (u : State) : Prop :=
  ∃ s, ∃ A : PrimeABI bits s, view bits s = v ∧ Prepared hb A u

def TestedAt {bits : Nat} (hb : Supported bits) (v : View) (u : State) : Prop :=
  ∃ s, ∃ A : PrimeABI bits s, view bits s = v ∧ Tested hb A u

/-- The workspace and `used` in their registers. -/
def Loaded (v : View) (u : State) : Prop :=
  u.gpr .x0 = off v.x0 arithmetic ∧ u.gpr .x4 = v.x4

theorem post_of_exec {c : Prog isa} {s t : State} {trace : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (he : Exec isa c s trace t) : Q t := by
  obtain ⟨_, u, hu, hq⟩ := h
  obtain ⟨_, heq⟩ := Exec.det he hu
  rw [heq]
  exact hq

theorem entry_ct {bits : Nat} (hb : Supported bits) :
    RelCT isa (Two (Entered bits)) (.block entry) (Two (PreparedAt hb)) :=
  two_piece [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) fun v u ⟨s, A, hv, hu⟩ => by
    subst hu
    exact WP.mono (entry_ok (s := allocState 272 s) (F := frameBase s) rfl
      (fun d hd => ⟨_, List.mem_cons_self, frame_contains s hd⟩))
      fun t ⟨m, x, k⟩ => ⟨s, A, hv, prepared hb A m x k⟩

theorem test_ct (M : Mont) (K : Kernel) {bits : Nat} (hb : Supported bits) :
    RelCT isa (Two (PreparedAt hb)) (test bits M.mm K.run) (Two (TestedAt hb)) := by
  have hct : RelCT isa (Two (CheckPrimeBefore (words bits) (candidate bits) (len bits) (draw bits) (checks bits)))
      (test bits M.mm K.run) fun _ _ => True := by
    unfold test
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      exact VG.Proof.Dsa.AArch64.Generation.checkPrime_ct M K _ _ _ _ _
        (by unfold VG.Proof.Dsa.AArch64.Generation.PrimeWidths; decide +kernel) (by taint_decide) (by taint_decide)
  intro u₁ u₂ t₁ t₂ u₁' u₂' ⟨v, ⟨s₁, A₁, hv₁, P₁⟩, ⟨s₂, A₂, hv₂, P₂⟩, hsp⟩ e₁ e₂
  have hp₂ : CheckPrimeBefore (words bits) (candidate bits) (len bits) (draw bits) (checks bits)
      (framePublic hb A₁) u₂ := by
    rw [framePublic_eq hb A₁ A₂ (hv₁.trans hv₂.symm)]; exact before_of_prepared hb A₂ P₂
  refine ⟨(hct _ _ _ _ _ _ ⟨_, before_of_prepared hb A₁ P₁, hp₂, hsp⟩ e₁ e₂).1, v,
    ⟨s₁, A₁, hv₁, post_of_exec (test_ok M K hb A₁ P₁) e₁⟩,
    ⟨s₂, A₂, hv₂, post_of_exec (test_ok M K hb A₂ P₂) e₂⟩, ?_⟩
  rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hsp]

/-- The exit's loads of the workspace's word and of `used`. -/
abbrev exitLoad : List Instr := [ldh .x3 kUsed, .ldrSp .x4 usedSlot]

abbrev exitStatus : List Instr := [.str .x .x3 .x4 0, ldh .x0 kStat, .lsr .x .x3 .x0 1, .sub .x .x0 .x0 .x3]

theorem load_ok {bits : Nat} {hb : Supported bits} {v : View} {u : State} (h : TestedAt hb v u) :
    WP isa (.block exitLoad) u (Loaded v) := by
  obtain ⟨s, A, rfl, T⟩ := h
  obtain ⟨⟨_, inp, _⟩, hsp, hwr, _, _, _, _, hU⟩ := T
  have hx0 := inp.ws.x0
  have h216 := inp.ws.scr.ld (d := 216) (by have := inp.ws.h256; omega)
  have h136 : InRegions (u.rd ++ u.wr) (off (frameBase s) usedSlot) 8 :=
    ⟨_, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_self), frame_contains s (by decide)⟩
  have run : WP isa (.block exitLoad) u fun t => t.gpr .x4 = s.gpr .x4 := by
    simp only [word, off, usedSlot] at hU h136 h216
    rw [← hsp] at hU h136
    rw [← hx0] at h216
    brun [State.write, exec_ldrSp (by decide : 136 % 8 = 0 ∧ 136 < 32768), h216, h136, hU, kUsed,
      VG.Impl.Bignum.sFn, usedSlot]
  exact WP.mono (WP.keep [.x3, .x4] run (by decide)) fun t ⟨h4, k⟩ =>
    ⟨(k.gpr .x0 (by decide)).trans hx0, h4⟩

theorem exit_ct {bits : Nat} (hb : Supported bits) :
    RelCT isa (Two (TestedAt hb)) (.block exit) fun _ _ => True := by
  have pins : Pins (TestedAt hb) [.x0] := by
    rintro v u₁ u₂ ⟨s₁, A₁, rfl, T₁⟩ ⟨s₂, A₂, h₂, T₂⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨⟨_, inp₁, _⟩, _⟩ := T₁
    obtain ⟨⟨_, inp₂, _⟩, _⟩ := T₂
    rw [inp₁.ws.x0, inp₂.ws.x0]
    simp only [view, View.mk.injEq] at h₂
    change off (s₁.gpr .x0) arithmetic = off (s₂.gpr .x0) arithmetic
    rw [h₂.1]
  change RelCT isa _ (.block (exitLoad ++ exitStatus)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.x0] pins (by taint_decide) fun v u h => load_ok h) ?_)
  intro s t xs ys u w hp es et
  have pl : Pins Loaded [.x0, .x4] := by
    rintro v a b ⟨a0, a4⟩ ⟨b0, b4⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a0, b0]
    · rw [a4, b4]
  exact two_taint [.x0, .x4] pl (by taint_decide) _ _ _ _ _ _ hp es et

theorem code_ct (M : Mont) (K : Kernel) {bits : Nat} (hb : Supported bits) :
    ConstantTime isa (contract bits).pre (contract bits).pub (code bits M.mm K.run) := by
  intro s t xs ys u v hs ht hp es et
  have ct : RelCT isa (fun s t => (contract bits).pre s ∧ (contract bits).pre t ∧ (contract bits).pub s t)
      (code bits M.mm K.run) (fun _ _ => True) := by
    apply RelCT.alloc
    refine RelCT.mono (RelCT.seq (entry_ct hb) (RelCT.seq (test_ct M K hb) (exit_ct hb))) ?_ fun _ _ h => h
    rintro a b ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩
    have hv := view_of_pub hp
    refine ⟨view bits s₁, ⟨s₁, primeABI_of h₁, rfl, rfl⟩, ⟨s₂, primeABI_of h₂, hv.symm, rfl⟩, ?_⟩
    simp only [view, View.mk.injEq] at hv
    change s₁.sp - _ = s₂.sp - _
    rw [hv.2.2.2.2.2.1]
  exact (ct _ _ _ _ _ _ ⟨hs, ht, hp⟩ es et).1

end VG.Proof.Dsa.AArch64.ProbablePrime
