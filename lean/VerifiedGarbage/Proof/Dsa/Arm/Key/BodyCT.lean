module

import VerifiedGarbage.Proof.Dsa.Arm.Key.CallCT
public import VerifiedGarbage.Proof.Dsa.Arm.Key.FinishCT
public import VerifiedGarbage.Proof.Dsa.Arm.Key.SampleCT
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Body
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.Arm.Key.PrepareCT
import VerifiedGarbage.Proof.Dsa.Arm.Key.Scan
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.CallCT
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.FinishCT
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.SampleCT
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Body
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.PrepareCT
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Scan
meta import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.Arm.Key.Sample
meta import VerifiedGarbage.Proof.Dsa.Arm.Key.Sample
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Call
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Two

/-!
# Key generation's body leaks only its public data (32-bit ARM)

The domain is public, so whether it passes the check is (`pub_checked`).
The sampling trace is the generation trace without the derivation's last
entry, 5 or 6, which no sampling trace has (`spl_trace`); it fixes whether
x is found (`BodyPub.ok`), and the generation's status is the derivation's.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.GenerateKey
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm eval_eq eval_ne)

/-! ## What two runs share -/

/-- A sampling trace has no entry above 4. -/
theorem sample_trace_le (q fuel : Nat) (rand : List Byte) :
    ∀ x ∈ (Spec.Dsa.Random.sample q fuel rand).trace, x ≤ 4 := by
  induction fuel generalizing rand with
  | zero => simp [Spec.Dsa.Random.sample]
  | succ fuel ih =>
    rw [Spec.Dsa.Random.sample]
    split
    · simp
    · dsimp only
      split
      · simp
      · split
        · simp
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · decide
          · exact ih _ x hx

/-- The public data of two runs of the body: the entry's, the domain, and
the generation's status and trace. -/
structure BodyPub where
  pub : Pub
  key : List Byte
  status : Nat
  tr : List Nat

structure BodyFacts (b : BodyPub) (s₀ : State) : Prop where
  key : (rInput s₀).key = b.key
  status : (rResult s₀).status = b.status
  tr : (rResult s₀).trace = b.tr

/-- The sampling trace: the trace without the derivation's entry. -/
def BodyPub.splTr (b : BodyPub) : List Nat := if b.tr.getLast?.any (4 < ·) then b.tr.dropLast else b.tr

/-- Whether sampling finds x. -/
def BodyPub.ok (b : BodyPub) : Bool := b.splTr.getLast? == some 1

theorem pub_checked {s₁ s₂ : State} (e : pubOf s₁ = pubOf s₂) (hk : (rInput s₁).key = (rInput s₂).key) :
    rChecked s₁ = rChecked s₂ := by
  have hp : (rInput s₁).pLen = (rInput s₂).pLen := congrArg BitVec.toNat (pub_arg e 1 (by decide))
  have hq : (rInput s₁).qLen = (rInput s₂).qLen := congrArg BitVec.toNat (pub_arg e 2 (by decide))
  unfold rChecked; rw [hp, hq, hk]

theorem splTr_append (tr : List Nat) {c : Nat} (hc : 4 < c) :
    (if (tr ++ [c]).getLast?.any (4 < ·) then (tr ++ [c]).dropLast else tr ++ [c]) = tr := by
  simp [hc]

theorem spl_trace {b : BodyPub} {s₀ : State} (A : KeyABI s₀) (F : BodyFacts b s₀) (hc : rChecked s₀ = true) :
    (spl s₀ 128 0).trace = b.splTr := by
  have hR := rResult_eq A
  rw [ite_eq_left hc] at hR
  have ht := F.tr
  unfold BodyPub.splTr
  rw [← ht, hR]
  cases hk : (spl s₀ 128 0).scalar with
  | none =>
    dsimp only
    have h4 : (spl s₀ 128 0).trace.getLast?.any (4 < ·) = false := by
      cases hl : (spl s₀ 128 0).trace.getLast? with
      | none => rfl
      | some x =>
        have := sample_trace_le _ _ _ x (List.mem_of_getLast? hl)
        simp only [Option.any_some, decide_eq_false_iff_not]; omega
    rw [h4]; rfl
  | some x =>
    dsimp only
    exact (splTr_append _ (by split <;> decide)).symm

theorem spl_ok {b : BodyPub} {s₀ : State} (A : KeyABI s₀) (F : BodyFacts b s₀) (hc : rChecked s₀ = true) :
    decide (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 0) = 1) = b.ok := by
  unfold BodyPub.ok
  have hs : (spl s₀ 128 0).scalar.isSome = ((spl s₀ 128 0).trace.getLast? == some 1) :=
    (VG.Proof.Dsa.Random.sample_trace_result _ _ _).2
  rw [← spl_trace A F hc, ← hs]
  cases hk : (spl s₀ 128 0).scalar with
  | none => rw [decide_eq_false (sampleStatus_none hk)]; rfl
  | some k => rw [decide_eq_true (sampleStatus_some hk)]; rfl

/-! ## The entry -/

/-- The body's entry, after the frame's allocation. -/
def BodyEntry (b : BodyPub) (s₀ t : State) : Prop := BodyFacts b s₀ ∧ t = allocated frameBytes s₀

/-- After the entry's first instruction, which puts the frame's base in `r12`. -/
def entryBase (s₀ : State) : State :=
  (allocated frameBytes s₀).setReg .r12 ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)

def Based (b : BodyPub) (s₀ t : State) : Prop := BodyFacts b s₀ ∧ t = entryBase s₀

/-- Between the calls: the saved words, and the counts. -/
structure Kept (b : BodyPub) (s₀ t : State) : Prop where
  facts : BodyFacts b s₀
  ready : RReady s₀ t
  saved : Saved s₀ t.mem
  used : slot t.mem (rBase s₀) oUsed = 0
  status : slot t.mem (rBase s₀) oStatus = 0

theorem Kept.fupd {b : BodyPub} {s₀ t u : State} (h : Kept b s₀ t) (f : Fupd t u) : Kept b s₀ u := by
  have hm : u.mem = t.mem := f.mem
  exact ⟨h.facts, h.ready.fupd f, by rw [hm]; exact h.saved, by rw [hm]; exact h.used, by rw [hm]; exact h.status⟩

theorem exec_entryBase (s₀ : State) : isa.exec (.addSp .r12 0) (allocated frameBytes s₀) = some (entryBase s₀) := by
  simp [exec, entryBase]

theorem entryRest_ok {s₀ : State} (A : KeyABI s₀) :
    WP isa (.block entry.tail) (entryBase s₀) fun u => RReady s₀ u ∧ Saved s₀ u.mem ∧
      slot u.mem (rBase s₀) oUsed = 0 ∧ slot u.mem (rBase s₀) oStatus = 0 := by
  have h := entry_ok A
  rw [show entry = .addSp .r12 0 :: entry.tail from rfl, WP.block_cons_iff] at h
  obtain ⟨s', hs, W⟩ := h
  rw [exec_entryBase, Option.some.injEq] at hs
  subst hs
  exact WP.mono W fun u ⟨a, b, c, d, _⟩ => ⟨a, b, c, d⟩

theorem entryBase_r12 (s₀ : State) : (entryBase s₀).gpr .r12 = s₀.sp - BitVec.ofNat 32 frameBytes := by
  simp [entryBase, State.setReg, allocated]

theorem entry_ct : RelCT isa (Two fun b => At (BodyEntry b) b.pub) (.block entry) (Two fun b => At (Kept b) b.pub) := by
  rw [show entry = [.addSp .r12 0] ++ entry.tail from rfl]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun b => At (Based b) b.pub) []
    (fun _ _ _ _ _ _ h => by cases h) (by taint_decide) fun b t ⟨s₀, A, e, Fb, ht⟩ => ?_)
    (two_piece [.r12] (fun b t₁ t₂ ⟨s₁, _, e₁, _, h₁⟩ ⟨s₂, _, e₂, _, h₂⟩ r hr => ?_) (by taint_decide)
      fun b t ⟨s₀, A, e, Fb, ht⟩ => ?_))
  · subst ht
    exact VG.Proof.X25519.Arm.WP.cons (exec_entryBase s₀) (WP.block_nil ⟨s₀, A, e, Fb, rfl⟩)
  · rw [List.mem_singleton] at hr; subst hr h₁ h₂
    rw [entryBase_r12, entryBase_r12, pub_sp (e₁.trans e₂.symm)]
  · subst ht
    exact WP.mono (entryRest_ok A) fun u ⟨h, sv, us, st⟩ => ⟨s₀, A, e, Fb, h, sv, us, st⟩

/-! ## The domain check -/

def CheckIn (b : BodyPub) (s₀ t : State) : Prop := Kept b s₀ t ∧ CheckRegs s₀ t

/-- After the check. -/
def Checked (b : BodyPub) (s₀ t : State) : Prop :=
  Kept b s₀ t ∧ t.gpr .r0 = if rChecked s₀ then 1 else 0

theorem checked_ok (name : String) {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (C : CheckIn b s₀ t) :
    WP isa (callWith name Generate.checkParameters) t (Checked b s₀) := by
  obtain ⟨K, R⟩ := C
  refine WP.mono (callCheck_ok A K.ready R name) fun u ⟨h, f, _, r0⟩ => ?_
  have sl : ∀ d, d + 4 ≤ frameBytes → slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    slot_keep f (check_keeps A) hd
  have hck : checkResult s₀ t = rChecked s₀ := by
    unfold checkResult; rw [key_bytes A K.ready]; rfl
  rw [hck] at r0
  exact ⟨⟨K.facts, h, K.saved.of_slots fun d _ hd => sl d hd, by rw [sl _ (by decide)]; exact K.used,
    by rw [sl _ (by decide)]; exact K.status⟩, r0⟩

/-- After the test of the check. -/
def Tested (b : BodyPub) (s₀ t : State) : Prop := Kept b s₀ t ∧ t.z = !rChecked s₀

/-- An unchecked domain: the end. -/
theorem unchecked_fin {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (T : Tested b s₀ t) (hc : rChecked s₀ = false) :
    RFin s₀ t ∧ (rResult s₀).status = b.status := by
  obtain ⟨K, _⟩ := T
  have hR := rResult_unchecked A hc
  exact ⟨⟨K.ready, by rw [K.used, hR]; rfl, by rw [K.status, hR]; rfl, fun e => by rw [hR] at e; exact absurd e (by decide),
    K.saved⟩, K.facts.status⟩

/-! ## Sampling -/

/-- After `prepare`. -/
def Prepped (b : BodyPub) (s₀ t : State) : Prop :=
  BodyFacts b s₀ ∧ rChecked s₀ = true ∧ Smp s₀ 0 (slot t.mem (rBase s₀) oDraws).toNat t ∧ Saved s₀ t.mem

theorem prepped_ok {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (T : Tested b s₀ t) (hc : rChecked s₀ = true) :
    WP isa prepare t (Prepped b s₀) := by
  obtain ⟨K, _⟩ := T
  have hq := rq_of_checked A hc
  have hql := rQBytes_le A
  have hfit := rWidth_le s₀
  refine WP.mono (prepare_ok A K.ready K.saved.2.2.2.2) fun t₅ ⟨_, P₅, h₅, o₅, _⟩ => ?_
  have P := P₅ hq
  have lo₅ : ∀ d, d + 4 ≤ oQ → slot t₅.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    outs_low o₅ (by decide) hd (by unfold oQ at hd; omega)
  have us₅ : slot t₅.mem (rBase s₀) oUsed = BitVec.ofNat 32 0 := by
    rw [lo₅ _ (by decide)]; exact K.used
  exact ⟨K.facts, hc, ⟨h₅, P.q, P.width, P.mask, us₅, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
    fun i hi => P.nonce i (by omega), Nat.zero_le _⟩, K.saved.of_outs o₅ (by decide)⟩

/-- After sampling. -/
structure Sampled (b : BodyPub) (s₀ t : State) : Prop where
  facts : BodyFacts b s₀
  checked : rChecked s₀ = true
  out : SampleOut s₀ 0 (spl s₀ 128 0) t
  r0 : t.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 0))
  ready : RReady s₀ t
  saved : Saved s₀ t.mem

theorem sampled_ok {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (P : Prepped b s₀ t) :
    WP isa KeyRandom.sample t (Sampled b s₀) := by
  obtain ⟨F, hc, S, sv⟩ := P
  exact WP.mono (sample_ok A S (rq_of_checked A hc)) fun u ⟨O, r0, h, o, _⟩ =>
    ⟨F, hc, O, r0, h, sv.of_outs o (by decide)⟩

/-- After the test of the sampling's status. -/
def SampleTested (b : BodyPub) (s₀ t : State) : Prop := Sampled b s₀ t ∧ t.z = b.ok

theorem Sampled.fupd {b : BodyPub} {s₀ t u : State} (A : KeyABI s₀) (h : Sampled b s₀ t) (f : Fupd t u) :
    Sampled b s₀ u :=
  ⟨h.facts, h.checked, h.out.mem A (h.ready.fupd f) f.mem, by rw [f.gpr]; exact h.r0, h.ready.fupd f,
    by rw [f.mem]; exact h.saved⟩

/-- No x: the end. -/
theorem rejected_fin {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (T : SampleTested b s₀ t) (hb : b.ok = false) :
    RFin s₀ t ∧ (rResult s₀).status = b.status := by
  obtain ⟨S, _⟩ := T
  have hR := rResult_eq A
  simp only [S.checked, ↓reduceIte] at hR
  have hn : VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 0) ≠ 1 := by
    have := spl_ok A S.facts S.checked; rw [hb] at this; simpa using this
  cases hk : (spl s₀ 128 0).scalar with
  | some k => exact absurd (sampleStatus_some hk) hn
  | none =>
    simp only [hk] at hR
    obtain ⟨d, Sm⟩ := S.out.smp
    refine ⟨⟨S.ready, ?_, ?_, fun e => by rw [hR] at e; exact absurd e hn, S.saved⟩, S.facts.status⟩
    · rw [Sm.usedW, hR]; simp
    · rw [S.out.status, hR]

/-! ## The derivation -/

/-- With x, before the derivation's call. -/
structure DeriveIn (b : BodyPub) (s₀ t : State) : Prop where
  facts : BodyFacts b s₀
  checked : rChecked s₀ = true
  ready : RReady s₀ t
  regs : DeriveRegs s₀ t
  x : ∃ k, (spl s₀ 128 0).scalar = some k ∧ deriveResult s₀ t =
    Spec.Dsa.deriveKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key (Spec.Dsa.encodeBE (rInput s₀).qLen k)
  used : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 (spl s₀ 128 0).used
  saved : Saved s₀ t.mem

theorem deriveIn_ok {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (T : SampleTested b s₀ t) (hb : b.ok = true) :
    WP isa (.block deriveArgs) t (DeriveIn b s₀) := by
  obtain ⟨S, _⟩ := T
  have hqn := rQBytes_length A
  have h1 : VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 0) = 1 := by
    have := spl_ok A S.facts S.checked; rw [hb] at this; simpa using this
  obtain ⟨k, hk⟩ : ∃ k, (spl s₀ 128 0).scalar = some k := by
    cases hk : (spl s₀ 128 0).scalar with
    | none => exact absurd h1 (sampleStatus_none hk)
    | some k => exact ⟨k, rfl⟩
  obtain ⟨d, Sm⟩ := S.out.smp
  refine WP.mono (deriveArgs_ok A S.ready S.saved) fun u ⟨h, m, C, _⟩ => ⟨S.facts, S.checked, h, C, ⟨k, hk, ?_⟩,
    by rw [m, Sm.usedW, Nat.zero_add], by rw [m]; exact S.saved⟩
  unfold deriveResult
  rw [key_bytes A h, m, ← hqn, S.out.nonce k hk, hqn]
  rfl

theorem DeriveIn.status {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (D : DeriveIn b s₀ t) :
    Spec.Dsa.signStatus (deriveResult s₀ t) = b.status := by
  obtain ⟨k, hk, hr⟩ := D.x
  have hR := rResult_eq A
  simp only [D.checked, ↓reduceIte, hk] at hR
  rw [hr, ← D.facts.status, hR]

/-- After the derivation's call. -/
structure Derived (b : BodyPub) (s₀ t : State) : Prop where
  facts : BodyFacts b s₀
  ready : RReady s₀ t
  r0 : t.gpr .r0 = BitVec.ofNat 32 (rResult s₀).status
  out : Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    (rResult s₀).key.getD (List.replicate (s₀.gpr .r1).toNat 0)
  used : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 (rResult s₀).used
  saved : Saved s₀ t.mem

theorem derived_ok (name : String) {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (D : DeriveIn b s₀ t) :
    WP isa (callWith name Generate.deriveKey) t (Derived b s₀) := by
  obtain ⟨k, hk, hres⟩ := D.x
  have hR := rResult_eq A
  simp only [D.checked, ↓reduceIte, hk] at hR
  refine WP.mono (callDerive_ok A D.ready D.regs name) fun u ⟨h, f, _, r0, out⟩ => ?_
  rw [hres] at r0 out
  have sl : ∀ d, d + 4 ≤ frameBytes → slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    slot_keep f (derive_keeps A) hd
  exact ⟨D.facts, h, by rw [r0, hR], by rw [out, hR], by rw [sl _ (by decide), D.used, hR],
    D.saved.of_slots fun d _ hd => sl d hd⟩

theorem stored_fin {b : BodyPub} {s₀ t : State} (A : KeyABI s₀) (D : Derived b s₀ t) :
    WP isa (.block [st .r0 oStatus]) t fun u => RFin s₀ u ∧ (rResult s₀).status = b.status := by
  refine wp_st D.ready (by decide) fun u mm hu => WP.block_nil ?_
  have mem : u.mem = t.mem.writeW (off (rBase s₀) oStatus) (t.gpr .r0) := mm.mem
  refine ⟨⟨hu, ?_, ?_, fun _ => ?_, ?_⟩, D.facts.status⟩
  · rw [mem, slot_write_ne _ _ _ (by decide) (by decide) (by decide), D.used]
  · rw [mem, slot_write_self, D.r0]
  · rw [mem, rBytes_frame (frame_store s₀ t.mem (by decide) _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact A.stackOut.symm)
      (by have := (s₀.gpr .r1).isLt; omega), D.out]
  · exact D.saved.of_slots fun d hd hd' => by
      rw [mem, slot_write_ne _ _ _ (by unfold oStatus; omega) (by omega) (by decide)]

/-! ## The pieces' constant time -/

/-- The end of a branch, with its status. -/
theorem fin_two {Φ : BodyPub → State → Prop} {c : Prog isa}
    (h : RelCT isa (Two Φ) c (Two fun (b : BodyPub) => At (fun s₀ t => RFin s₀ t ∧ (rResult s₀).status = b.status) b.pub)) :
    RelCT isa (Two Φ) c (Two FinAt) :=
  h.mono (fun _ _ h => h) fun _ _ ⟨(b : BodyPub), h₁, h₂⟩ => ⟨(b.pub, b.status), h₁, h₂⟩

theorem derived_ct (name : String) :
    RelCT isa (Two fun b s => At (SampleTested b) b.pub s ∧ isa.eval .eq s = some true)
      (.seq (.block deriveArgs) (.seq (callWith name Generate.deriveKey) (.block [st .r0 oStatus])))
      (Two FinAt) := by
  refine RelCT.seq (two_piece (Ψ := fun b => At (DeriveIn b) b.pub) [.r11]
    (pins_at' BodyPub.pub fun _ _ _ h => h.1.ready) (by taint_decide)
    fun b t ⟨⟨s₀, A, e, T⟩, hb⟩ => WP.mono (deriveIn_ok A T (by
      rw [eval_eq, T.2, Option.some.injEq] at hb; exact hb)) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun b => At (Derived b) b.pub)
    ((deriveCall_ct name).mono (fun t₁ t₂ ⟨_, ⟨s₁, A₁, e₁, D₁⟩, ⟨s₂, A₂, e₂, D₂⟩⟩ =>
      ⟨s₁, s₂, A₁, A₂, e₁.trans e₂.symm, D₁.facts.key.trans D₂.facts.key.symm, D₁.ready, D₂.ready,
        D₁.regs, D₂.regs, by rw [D₁.status A₁, D₂.status A₂]⟩) fun _ _ h => h)
    fun b t ⟨s₀, A, e, D⟩ => WP.mono (derived_ok name A D) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  exact fin_two (two_piece [.r11] (pins_at BodyPub.pub fun _ _ _ h => h.ready) (by taint_decide)
    fun b t ⟨s₀, A, e, D⟩ => WP.mono (stored_fin A D) fun u hu => ⟨s₀, A, e, hu⟩)

theorem rejected_ct : RelCT isa (Two fun b s => At (SampleTested b) b.pub s ∧ isa.eval .eq s = some false)
    (.block []) (Two FinAt) :=
  fin_two (two_post (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide))
    fun b t ⟨⟨s₀, A, e, T⟩, hb⟩ => WP.block_nil ⟨s₀, A, e, rejected_fin A T (by
      rw [eval_eq, T.2, Option.some.injEq] at hb; exact hb)⟩)

theorem generate_ct (name : String) :
    RelCT isa (Two fun b s => At (Tested b) b.pub s ∧ isa.eval .eq s = some false)
      (generate name Generate.deriveKey) (Two FinAt) := by
  unfold generate derived
  refine RelCT.seq (two_post (Ψ := fun b => At (Prepped b) b.pub)
    (two_map BodyPub.pub (fun b t ⟨⟨s₀, A, e, K, _⟩, _⟩ => ⟨s₀, A, e, K.ready, K.saved.2.2.2.2⟩) prepare_ct)
    fun b t ⟨⟨s₀, A, e, T⟩, hb⟩ => WP.mono (prepped_ok A T (by
      rw [eval_eq, T.2, Option.some.injEq] at hb; simpa using hb)) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun b => At (Sampled b) b.pub)
    (two_map (fun b => (⟨b.pub, 0, b.splTr⟩ : SmpPub))
      (fun b t ⟨s₀, A, e, F, hc, S, _⟩ => ⟨s₀, A, e, ⟨_, S⟩, rq_of_checked A hc, spl_trace A F hc⟩) sample_ct)
    fun b t ⟨s₀, A, e, P⟩ => WP.mono (sampled_ok A P) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun b => At (SampleTested b) b.pub) []
    (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)
    fun b t ⟨s₀, A, e, S⟩ => wp_cmp (op2_imm (by decide)) fun u fu z =>
      WP.block_nil ⟨s₀, A, e, S.fupd A fu, ?_⟩) ?_
  · have hle := sampleStatus_le (spl s₀ 128 0)
    rw [z, S.r0, one_beq (by omega), spl_ok A S.facts S.checked]
  exact two_ite (fun b t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by rw [eval_eq, eval_eq, z₁, z₂])
    (derived_ct name) rejected_ct

theorem body_ct (check derive : String) :
    RelCT isa (Two fun b => At (BodyEntry b) b.pub)
      (body check derive Generate.checkParameters Generate.deriveKey) fun _ _ => True := by
  unfold body
  refine RelCT.seq entry_ct ?_
  refine RelCT.seq (two_piece (Ψ := fun b => At (CheckIn b) b.pub) [.r11]
    (pins_at BodyPub.pub fun _ _ _ h => h.ready) (by taint_decide)
    fun b t ⟨s₀, A, e, K⟩ => WP.mono (checkArgs_ok A K.ready K.saved) fun u ⟨h, m, C, _⟩ =>
      ⟨s₀, A, e, ⟨K.facts, h, by rw [m]; exact K.saved, by rw [m]; exact K.used, by rw [m]; exact K.status⟩,
        C⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun b => At (Checked b) b.pub)
    ((checkCall_ct check).mono (fun t₁ t₂ ⟨_, ⟨s₁, A₁, e₁, K₁, C₁⟩, ⟨s₂, A₂, e₂, K₂, C₂⟩⟩ =>
      ⟨s₁, s₂, A₁, A₂, e₁.trans e₂.symm, K₁.facts.key.trans K₂.facts.key.symm, K₁.ready, K₂.ready, C₁, C₂⟩)
      fun _ _ h => h)
    fun b t ⟨s₀, A, e, C⟩ => WP.mono (checked_ok check A C) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun b => At (Tested b) b.pub) []
    (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)
    fun b t ⟨s₀, A, e, K, r0⟩ => wp_cmp0 fun u f z => WP.block_nil ⟨s₀, A, e, K.fupd f, ?_⟩) ?_
  · rw [z, r0]; cases rChecked s₀ <;> rfl
  refine RelCT.seq (R := Two FinAt) (two_ite (fun b t₁ t₂ ⟨s₁, _, e₁, K₁, z₁⟩ ⟨s₂, _, e₂, K₂, z₂⟩ => by
    rw [eval_eq, eval_eq, z₁, z₂, pub_checked (e₁.trans e₂.symm) (K₁.facts.key.trans K₂.facts.key.symm)])
    ?_ (generate_ct derive)) finish_ct
  exact fin_two (two_post (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide))
    fun b t ⟨⟨s₀, A, e, T⟩, hb⟩ => WP.block_nil ⟨s₀, A, e, unchecked_fin A T (by
      rw [eval_eq, T.2, Option.some.injEq] at hb; simpa using hb)⟩)

end VG.Proof.Dsa.Arm.Key
