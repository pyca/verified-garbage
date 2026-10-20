module
public import VerifiedGarbage.Proof.Dsa.Arm.RandomAttempt
public import VerifiedGarbage.Proof.Dsa.Arm.RandomTwo

import VerifiedGarbage.Proof.Dsa.Arm.RandomCallCT
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Dsa.Arm.RandomSampleCT
import VerifiedGarbage.Proof.Dsa.Arm.RandomSample
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomAttempt
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomTwo
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomCallCT
meta import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomSampleCT
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomSample
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# An attempt leaks only its trace (32-bit ARM)

The rest of the specification's signing (`randomSignRemaining`) has a trace
that records the attempt's sampling (`randomSamplingTrace`), whether it
found a nonce (`AttPub.ok`) and whether signing with it succeeded
(`AttPub.signed`). Two runs with the same public data, consumption,
attempts and trace take the same branches.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm eval_eq eval_ne)
open VG.Proof.Dsa (randomSignRemaining randomSamplingTrace randomSigningTrace)

/-- What two runs share before an attempt. -/
structure AttPub where
  pub : Pub
  leak : List Nat
  used : Nat
  fuel : Nat
  tr : List Nat
  /-- The overall status. -/
  status : Nat

/-- Whether the attempt's sampling finds a nonce. -/
def AttPub.ok (a : AttPub) : Bool := (randomSamplingTrace a.tr).getLast? == some 1

/-- Whether signing with it succeeds. -/
def AttPub.signed (a : AttPub) : Bool := randomSigningTrace a.tr == [5]

/-- What the attempt keeps of its entry. -/
structure AttFacts (a : AttPub) (s₀ : State) : Prop where
  q : 1 < rq s₀
  pos : 1 ≤ a.fuel
  le : a.fuel ≤ 8
  leak : keyLeak s₀ = a.leak
  tr : (randomSignRemaining (rInput s₀) a.used a.fuel).trace = a.tr

/-- Before an attempt. -/
def AttAt (a : AttPub) (s₀ t : State) : Prop := AttFacts a s₀ ∧ Att s₀ a.used a.fuel t

theorem AttFacts.spl_trace {a : AttPub} {s₀ : State} (F : AttFacts a s₀) :
    (spl s₀ 128 a.used).trace = randomSamplingTrace a.tr := by
  obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := F.pos; omega⟩
  rw [← F.tr, hf]
  exact (VG.Proof.Dsa.random_sign_trace_draw _ _ _).symm

theorem AttFacts.ok {a : AttPub} {s₀ : State} (F : AttFacts a s₀) :
    (spl s₀ 128 a.used).scalar.isSome = a.ok := by
  rw [(VG.Proof.Dsa.Random.sample_trace_result _ _ _).2, F.spl_trace]; rfl

theorem AttFacts.status {a : AttPub} {s₀ : State} (F : AttFacts a s₀) :
    decide (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 a.used) = 1) = a.ok := by
  rw [← F.ok]
  unfold VG.Proof.Dsa.Random.sampleStatus
  split
  · next h => simp [h]
  · next h => simp only [h, Option.isSome_none]; split <;> decide

theorem AttFacts.signed {a : AttPub} {s₀ : State} (F : AttFacts a s₀) {k : Nat}
    (hk : (spl s₀ 128 a.used).scalar = some k) :
    (Spec.Dsa.signBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
      (Spec.Dsa.encodeBE (rInput s₀).qLen k) (rInput s₀).digest).isSome = a.signed := by
  obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := F.pos; omega⟩
  have htr := F.tr
  rw [hf] at htr
  unfold AttPub.signed
  rw [← htr]
  cases hs : Spec.Dsa.signBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
      (Spec.Dsa.encodeBE (rInput s₀).qLen k) (rInput s₀).digest with
  | some sig => rw [VG.Proof.Dsa.random_sign_trace_success _ _ _ _ hk hs]; rfl
  | none => rw [VG.Proof.Dsa.random_sign_trace_retry _ _ _ _ hk hs]; simp

/-- After sampling. -/
structure Sampled (a : AttPub) (s₀ t : State) : Prop where
  facts : AttFacts a s₀
  out : SampleOut s₀ a.used (spl s₀ 128 a.used) t
  ready : RReady s₀ t
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel
  saved : Saved s₀ t.mem

theorem sample_sampled {a : AttPub} {s₀ t : State} (A : RandomABI s₀) (h : AttAt a s₀ t) :
    WP isa sample t fun u => Sampled a s₀ u ∧
      u.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 a.used)) := by
  obtain ⟨F, T⟩ := h
  obtain ⟨d₀, Sm⟩ := T.smp
  exact WP.mono (sample_ok A Sm F.q) fun u₁ ⟨O, r0₁, h₁, o₁, _⟩ =>
    ⟨⟨F, O, h₁, (slot_outs o₁ (by decide) (by decide)).trans T.attempts, T.saved.of_outs o₁ (by decide)⟩, r0₁⟩

/-- After the test of the sampling's status. -/
def Tested (a : AttPub) (s₀ t : State) : Prop := Sampled a s₀ t ∧ t.z = a.ok

/-- After loading the signer's arguments. -/
structure Args (a : AttPub) (s₀ t : State) : Prop where
  facts : AttFacts a s₀
  ready : RReady s₀ t
  regs : CallRegs s₀ t
  nonce : ∃ k, (spl s₀ 128 a.used).scalar = some k ∧
    Spec.Rsa.bytesAt t.mem (off (rBase s₀) oNonce) (rQBytes s₀).length = Spec.Dsa.encodeBE (rQBytes s₀).length k
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel

theorem args_ok {a : AttPub} {s₀ t : State} (A : RandomABI s₀) (h : Tested a s₀ t)
    (hok : a.ok = true) : WP isa (.block callArgs) t (Args a s₀) := by
  obtain ⟨S, -⟩ := h
  obtain ⟨k, hk⟩ : ∃ k, (spl s₀ 128 a.used).scalar = some k := by
    have := S.facts.ok
    rw [hok] at this
    exact Option.isSome_iff_exists.mp this
  exact WP.mono (callArgs_ok A S.ready S.saved) fun u₃ ⟨h₃, m₃, C₃, _⟩ =>
    ⟨S.facts, h₃, C₃, ⟨k, hk, by rw [m₃]; exact S.out.nonce k hk⟩, by rw [m₃]; exact S.attempts⟩

/-- After the call. -/
structure Called (a : AttPub) (s₀ t : State) : Prop where
  pos : 1 ≤ a.fuel
  le : a.fuel ≤ 8
  ready : RReady s₀ t
  r0 : t.gpr .r0 = BitVec.ofNat 32 (if a.signed then 1 else 0)
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel

theorem Args.status {a : AttPub} {s₀ t : State} (A : RandomABI s₀) (h : Args a s₀ t) :
    Spec.Dsa.signStatus (callResult s₀ t) = if a.signed then 1 else 0 := by
  obtain ⟨k, hk, hn⟩ := h.nonce
  rw [callResult_eq A h.ready hn, Spec.Dsa.signStatus, h.facts.signed hk]

theorem call_called (name : String) {a : AttPub} {s₀ t : State} (A : RandomABI s₀) (h : Args a s₀ t) :
    WP isa (callSigner name (Entry.operation true)) t (Called a s₀) :=
  WP.mono (callSigner_ok A h.ready h.regs name) fun u ⟨h₄, f₄, _, r0₄, _⟩ =>
    ⟨h.facts.pos, h.facts.le, h₄, by rw [r0₄, h.status A],
      by rw [call_frame_slot A f₄ (by decide)]; exact h.attempts⟩

/-- After recording the signer's status. -/
def Recorded (a : AttPub) (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.z = !a.signed ∧ slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel ∧
    1 ≤ a.fuel ∧ a.fuel ≤ 8

/-- After spending an attempt. -/
def Spent' (a : AttPub) (s₀ t : State) : Prop := RReady s₀ t ∧ t.z = decide (a.fuel - 1 = 0)

theorem callFinish_ct : RelCT isa (Two fun a => At (Called a) a.pub) callFinish fun _ _ => True := by
  unfold callFinish
  refine RelCT.seq (two_piece (Ψ := fun a => At (Recorded a) a.pub) [.r11]
    (pins_at AttPub.pub fun _ _ _ h => h.ready) (by taint_decide) fun a t ⟨s₀, A, e, C⟩ => ?_) ?_
  · refine WP.mono (finHead_ok C.ready (k := if a.signed then 1 else 0) (by split <;> decide) C.r0)
      fun u ⟨h, _, m, z⟩ => ⟨s₀, A, e, h, ?_, ?_, C.pos, C.le⟩
    · rw [z]; cases a.signed <;> rfl
    · rw [m, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact C.attempts
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁, _⟩ ⟨_, _, _, _, z₂, _⟩ => by rw [eval_eq, eval_eq, z₁, z₂]) ?_ ?_
  · refine RelCT.seq (two_piece (Ψ := fun a => At (Spent' a) a.pub) [.r11]
      (pins_at' AttPub.pub fun _ _ _ h => h.1) (by taint_decide)
      fun a t ⟨⟨s₀, A, e, h, _, ha, hp, hl⟩, _⟩ => ?_) ?_
    · obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by omega⟩
      rw [hf] at ha hl
      refine WP.mono (finDec_ok h ha hl) fun u ⟨h', _, _, z⟩ => ⟨s₀, A, e, h', ?_⟩
      rw [z, hf, Nat.add_sub_cancel]
    · refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by rw [eval_ne, eval_ne, z₁, z₂]) ?_ ?_
      · exact two_taint [.r11] (pins_at' AttPub.pub fun _ _ _ h => h.1) (by taint_decide)
      · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

theorem signerCall_ct (name : String) :
    RelCT isa (Two fun a => At (Args a) a.pub) (callSigner name (Entry.operation true)) fun _ _ => True :=
  (callSigner_ct name).mono (fun t₁ t₂ ⟨a, ⟨s₁, A₁, e₁, h₁⟩, ⟨s₂, A₂, e₂, h₂⟩⟩ =>
    ⟨s₁, s₂, A₁, A₂, e₁.trans e₂.symm, h₁.facts.leak.trans h₂.facts.leak.symm, h₁.ready, h₂.ready,
      h₁.regs, h₂.regs, by rw [h₁.status A₁, h₂.status A₂]⟩) fun _ _ h => h

theorem attempt_ct (name : String) :
    RelCT isa (Two fun a => At (AttAt a) a.pub) (attempt name (Entry.operation true)) fun _ _ => True := by
  unfold attempt
  refine RelCT.seq (two_post (Ψ := fun a => At (fun s₀ t => Sampled a s₀ t ∧
      t.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 a.used))) a.pub)
    (two_map (fun a => (⟨a.pub, a.used, randomSamplingTrace a.tr⟩ : SmpPub))
      (fun a t ⟨s₀, A, e, F, T⟩ => ⟨s₀, A, e, T.smp, F.q, F.spl_trace⟩) sample_ct)
    fun a t ⟨s₀, A, e, h⟩ => WP.mono (sample_sampled A h) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun a => At (Tested a) a.pub) []
    (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)
    fun a t ⟨s₀, A, e, S, r0⟩ => wp_cmp (op2_imm (by decide)) fun u fu z => WP.block_nil ⟨s₀, A, e, ?_, ?_⟩) ?_
  · exact ⟨S.facts, ⟨let ⟨d, Sd⟩ := S.out.smp; ⟨d, Sd.mem A (S.ready.fupd fu) fu.mem⟩,
      by rw [fu.mem]; exact S.out.status, by rw [fu.mem]; exact S.out.nonce⟩, S.ready.fupd fu,
      by rw [fu.mem]; exact S.attempts, by rw [fu.mem]; exact S.saved⟩
  · have hle := sampleStatus_le (spl s₀ 128 a.used)
    rw [z, r0, one_beq (by omega), S.facts.status]
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by rw [eval_eq, eval_eq, z₁, z₂]) ?_ ?_
  · refine RelCT.seq (two_piece (Ψ := fun a => At (Args a) a.pub) [.r11]
      (pins_at' AttPub.pub fun _ _ _ h => h.1.ready) (by taint_decide)
      fun a t ⟨⟨s₀, A, e, h⟩, hb⟩ => WP.mono (args_ok A h (by
        rw [eval_eq, h.2, Option.some.injEq] at hb; exact hb)) fun u hu => ⟨s₀, A, e, hu⟩) ?_
    exact RelCT.seq (two_post (Ψ := fun a => At (Called a) a.pub) (signerCall_ct name)
      fun a t ⟨s₀, A, e, h⟩ => WP.mono (call_called name A h) fun u hu => ⟨s₀, A, e, hu⟩) callFinish_ct
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

end VG.Proof.Dsa.Arm
