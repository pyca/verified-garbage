module

public import VerifiedGarbage.Proof.Dsa.X86.RandomCallCT
public import VerifiedGarbage.Impl.Dsa.X86.RandomSign
public import VerifiedGarbage.Proof.Dsa.RandomSignTrace
public import VerifiedGarbage.Proof.Dsa.X86.RandomAttemptState
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Dsa.X86.RandomCallCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86.RandomSampleCT
import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
import VerifiedGarbage.Proof.Dsa.X86.RandomCallArgs
import VerifiedGarbage.Proof.Dsa.X86.RandomSample
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.FetchByte
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.LoadSlot
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.RandomBody
import VerifiedGarbage.Proof.Dsa.X86.RandomCT
import VerifiedGarbage.Proof.Dsa.X86.RandomPrepare
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.Dsa.X86.Reduce
import VerifiedGarbage.Proof.Dsa.X86.RunBytes
import VerifiedGarbage.Proof.Dsa.X86.SaveArgument
import VerifiedGarbage.Proof.Dsa.X86.StackArgument
import VerifiedGarbage.Proof.Dsa.X86.StageFrame
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.DynamicSelect
import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
import VerifiedGarbage.Proof.Mont.X86.ExponentLoop
import VerifiedGarbage.Proof.Mont.X86.ExponentMask
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.ExponentStep
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Mont.X86.Exponentiate
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.PowerLoop
import VerifiedGarbage.Proof.Mont.X86.PowerTwo
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.RowW
import VerifiedGarbage.Proof.Mont.X86.SparseShift
import VerifiedGarbage.Proof.Mont.X86.SparseStep
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Random
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding
meta import VerifiedGarbage.Proof.Dsa.RandomSign
meta import VerifiedGarbage.Proof.Dsa.RandomSignResult
meta import VerifiedGarbage.Proof.Dsa.RandomTrace
meta import VerifiedGarbage.Proof.Dsa.X86.Bytes
meta import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
meta import VerifiedGarbage.Proof.Dsa.X86.EntrySave
meta import VerifiedGarbage.Proof.Dsa.X86.FetchByte
meta import VerifiedGarbage.Proof.Dsa.X86.Layout
meta import VerifiedGarbage.Proof.Dsa.X86.LoadSlot
meta import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
meta import VerifiedGarbage.Proof.Dsa.X86.Moduli
meta import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
meta import VerifiedGarbage.Proof.Dsa.X86.RandomBody
meta import VerifiedGarbage.Proof.Dsa.X86.RandomCT
meta import VerifiedGarbage.Proof.Dsa.X86.RandomCallArgs
meta import VerifiedGarbage.Proof.Dsa.X86.RandomPrepare
meta import VerifiedGarbage.Proof.Dsa.X86.RandomSample
meta import VerifiedGarbage.Proof.Dsa.X86.RandomSampleCT
meta import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
meta import VerifiedGarbage.Proof.Dsa.X86.Reduce
meta import VerifiedGarbage.Proof.Dsa.X86.RunBytes
meta import VerifiedGarbage.Proof.Dsa.X86.SaveArgument
meta import VerifiedGarbage.Proof.Dsa.X86.StackArgument
meta import VerifiedGarbage.Proof.Dsa.X86.StageFrame
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Mont.X86.Chain
meta import VerifiedGarbage.Proof.Mont.X86.ContextLayout
meta import VerifiedGarbage.Proof.Mont.X86.ContextMath
meta import VerifiedGarbage.Proof.Mont.X86.ContextMul
meta import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
meta import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
meta import VerifiedGarbage.Proof.Mont.X86.DynamicSelect
meta import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
meta import VerifiedGarbage.Proof.Mont.X86.ExponentLoop
meta import VerifiedGarbage.Proof.Mont.X86.ExponentMask
meta import VerifiedGarbage.Proof.Mont.X86.ExponentShift
meta import VerifiedGarbage.Proof.Mont.X86.ExponentStep
meta import VerifiedGarbage.Proof.Mont.X86.ExponentWord
meta import VerifiedGarbage.Proof.Mont.X86.Exponentiate
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Mont.X86.Inverse
meta import VerifiedGarbage.Proof.Mont.X86.P256Red
meta import VerifiedGarbage.Proof.Mont.X86.PowerInit
meta import VerifiedGarbage.Proof.Mont.X86.PowerLoop
meta import VerifiedGarbage.Proof.Mont.X86.PowerTwo
meta import VerifiedGarbage.Proof.Mont.X86.RedRow
meta import VerifiedGarbage.Proof.Mont.X86.Row
meta import VerifiedGarbage.Proof.Mont.X86.RowW
meta import VerifiedGarbage.Proof.Mont.X86.SparseShift
meta import VerifiedGarbage.Proof.Mont.X86.SparseStep
meta import VerifiedGarbage.Proof.Mont.X86.Step
meta import VerifiedGarbage.Proof.Mont.X86.WordOps
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Weierstrass.Words
meta import VerifiedGarbage.Proof.Weierstrass.Words32
meta import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
meta import VerifiedGarbage.Proof.Weierstrass.X86.Copy
meta import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontRed

/-!
# An attempt leaks only its public trace (x86)

The rest of the specification's signing (`randomSignRemaining`) has a trace
that records the attempt's sampling (`randomSamplingTrace`), whether it
found a nonce (`AttPub.ok`) and whether signing with it succeeded
(`AttPub.signed`). Two runs with the same public data, consumption,
attempts and trace take the same branches.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random VG.Impl.Dsa.X86.RandomSign
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
  ready : Ready s₀ t
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel

theorem sample_sampled {a : AttPub} {s₀ t : State} (A : RandomSignABI s₀) (h : AttAt a s₀ t) :
    WP isa sample t fun u => Sampled a s₀ u ∧
      u.gpr .eax = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 a.used)) := by
  obtain ⟨F, T⟩ := h
  obtain ⟨d₀, Sm⟩ := T.smp
  exact WP.mono (sample_ok A Sm F.q) fun u₁ ⟨O, eax₁, h₁, o₁, _⟩ =>
    ⟨⟨F, O, h₁, (slot_outs o₁ (by decide) (by decide)).trans T.attempts⟩, eax₁⟩

/-- After the test of the sampling's status. -/
def Tested (a : AttPub) (s₀ t : State) : Prop := Sampled a s₀ t ∧ t.zf = some a.ok

/-- After storing the signer's arguments. -/
structure Args (a : AttPub) (s₀ t : State) : Prop where
  facts : AttFacts a s₀
  ready : Ready s₀ t
  slots : CallSlots s₀ t
  nonce : ∃ k, (spl s₀ 128 a.used).scalar = some k ∧
    Spec.Rsa.bytesAt t.mem (off (rBase s₀) oNonce) (rQBytes s₀).length = Spec.Dsa.encodeBE (rQBytes s₀).length k
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel

theorem args_ok {a : AttPub} {s₀ t : State} (A : RandomSignABI s₀) (h : Tested a s₀ t)
    (hok : a.ok = true) : WP isa (.block callArgs) t (Args a s₀) := by
  obtain ⟨S, -⟩ := h
  have hql := rQBytes_le A
  obtain ⟨k, hk⟩ : ∃ k, (spl s₀ 128 a.used).scalar = some k := by
    have := S.facts.ok
    rw [hok] at this
    exact Option.isSome_iff_exists.mp this
  refine (callArgs_ok (is := []) A S.ready fun u₃ h₃ m₃ k₃ => WP.block_nil ?_ :
    WP isa (.block (callArgs ++ [])) t _)
  have o₃ := argsMem_outs s₀ t.mem (t.gpr .esp)
  rw [← m₃] at o₃
  refine ⟨S.facts, h₃, fun i hi => ?_, ⟨k, hk, ?_⟩, ?_⟩
  · rw [m₃, k₃.1 .esp (by decide)]; exact argsMem_slots s₀ _ _ i hi
  · rw [outs_frame_bytes o₃ (by decide) (by unfold oNonce; omega)]; exact S.out.nonce k hk
  · rw [outs_high o₃ (e := 44) (by decide) (by decide) (by decide)]; exact S.attempts

/-- After the call. -/
structure Called (a : AttPub) (s₀ t : State) : Prop where
  pos : 1 ≤ a.fuel
  le : a.fuel ≤ 8
  ready : Ready s₀ t
  eax : t.gpr .eax = BitVec.ofNat 32 (if a.signed then 1 else 0)
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel

theorem Args.status {a : AttPub} {s₀ t : State} (A : RandomSignABI s₀) (h : Args a s₀ t) :
    Spec.Dsa.signStatus (callResult s₀ t) = if a.signed then 1 else 0 := by
  obtain ⟨k, hk, hn⟩ := h.nonce
  rw [callResult_eq A h.ready hn, Spec.Dsa.signStatus, h.facts.signed hk]

theorem call_called (F : SignFn) {a : AttPub} {s₀ t : State} (A : RandomSignABI s₀) (h : Args a s₀ t) :
    WP isa (.call F.name F.code) t (Called a s₀) :=
  WP.mono (call_ok F A h.ready h.slots) fun u ⟨h₄, f₄, _, eax₄, _⟩ =>
    ⟨h.facts.pos, h.facts.le, h₄, by rw [eax₄, h.status A],
      by rw [call_frame_slot A f₄ (by decide) (by decide)]; exact h.attempts⟩

/-- After recording the signer's status. -/
def Recorded (a : AttPub) (s₀ t : State) : Prop :=
  Ready s₀ t ∧ t.zf = some (!a.signed) ∧ slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 a.fuel ∧
    1 ≤ a.fuel ∧ a.fuel ≤ 8

/-- After spending an attempt. -/
def Spent' (a : AttPub) (s₀ t : State) : Prop := Ready s₀ t ∧ t.zf = some (decide (a.fuel - 1 = 0))

theorem callFinish_ct : RelCT isa (Two fun a => At (Called a) a.pub) callFinish fun _ _ => True := by
  unfold callFinish
  refine RelCT.seq (two_piece (Ψ := fun a => At (Recorded a) a.pub) [.esp]
    (pins_at AttPub.pub fun _ _ _ h => h.ready) (by taint_decide) fun a t ⟨s₀, A, e, C⟩ => ?_) ?_
  · refine WP.mono (finHead_ok C.ready (st := if a.signed then 1 else 0) (by split <;> decide) C.eax)
      fun u ⟨h, _, m, z⟩ => ⟨s₀, A, e, h, ?_, ?_, C.pos, C.le⟩
    · rw [z]; cases a.signed <;> rfl
    · rw [m, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact C.attempts
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁, _⟩ ⟨_, _, _, _, z₂, _⟩ => by simp only [eval, z₁, z₂]) ?_ ?_
  · refine RelCT.seq (two_piece (Ψ := fun a => At (Spent' a) a.pub) [.esp]
      (pins_at' AttPub.pub fun _ _ _ h => h.1) (by taint_decide)
      fun a t ⟨⟨s₀, A, e, h, _, ha, hp, hl⟩, _⟩ => ?_) ?_
    · obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by omega⟩
      rw [hf] at ha hl
      refine WP.mono (finDec_ok h ha hl) fun u ⟨h', _, _, z⟩ => ⟨s₀, A, e, h', ?_⟩
      rw [z, hf, Nat.add_sub_cancel]
    · refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by simp only [eval, z₁, z₂]) ?_ ?_
      · exact two_taint [.esp] (pins_at' AttPub.pub fun _ _ _ h => h.1) (by taint_decide)
      · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

theorem signerCall_ct (F : SignFn) : RelCT isa (Two fun a => At (Args a) a.pub) (.call F.name F.code)
    fun _ _ => True :=
  (call_ct F).mono (fun t₁ t₂ ⟨a, ⟨s₁, A₁, e₁, h₁⟩, ⟨s₂, A₂, e₂, h₂⟩⟩ =>
    ⟨s₁, s₂, A₁, A₂, e₁.trans e₂.symm, h₁.facts.leak.trans h₂.facts.leak.symm, h₁.ready, h₂.ready,
      h₁.slots, h₂.slots, by rw [h₁.status A₁, h₂.status A₂]⟩) fun _ _ h => h

theorem attempt_ct (F : SignFn) :
    RelCT isa (Two fun a => At (AttAt a) a.pub) (attempt F.name F.code) fun _ _ => True := by
  unfold attempt
  refine RelCT.seq (two_post (Ψ := fun a => At (fun s₀ t => Sampled a s₀ t ∧
      t.gpr .eax = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 a.used))) a.pub)
    (two_map (fun a => (⟨a.pub, a.used, randomSamplingTrace a.tr⟩ : SmpPub))
      (fun a t ⟨s₀, A, e, F, T⟩ => ⟨s₀, A, e, T.smp, F.q, F.spl_trace⟩) sample_ct)
    fun a t ⟨s₀, A, e, h⟩ => WP.mono (sample_sampled A h) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun a => At (Tested a) a.pub) [.esp]
    (pins_at AttPub.pub fun _ _ _ h => h.1.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, S, eax⟩ => wp_cmpi fun u fu _ z => WP.block_nil ⟨s₀, A, e, ?_, ?_⟩) ?_
  · exact ⟨S.facts, ⟨let ⟨d, Sd⟩ := S.out.smp; ⟨d, Sd.mem A (S.ready.fupd fu) fu.mem⟩,
      by rw [fu.mem]; exact S.out.status, by rw [fu.mem]; exact S.out.nonce⟩, S.ready.fupd fu,
      by rw [fu.mem]; exact S.attempts⟩
  · have hle := sampleStatus_le (spl s₀ 128 a.used)
    rw [z, eax, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide),
      S.facts.status]
  refine two_ite (fun a t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by simp only [eval, z₁, z₂]) ?_ ?_
  · refine RelCT.seq (two_piece (Ψ := fun a => At (Args a) a.pub) [.esp]
      (pins_at' AttPub.pub fun _ _ _ h => h.1.ready) (by taint_decide)
      fun a t ⟨⟨s₀, A, e, h⟩, hb⟩ => WP.mono (args_ok A h (by
        simpa only [eval, h.2, Option.some.injEq] using hb)) fun u hu => ⟨s₀, A, e, hu⟩) ?_
    exact RelCT.seq (two_post (Ψ := fun a => At (Called a) a.pub) (signerCall_ct F)
      fun a t ⟨s₀, A, e, h⟩ => WP.mono (call_called F A h) fun u hu => ⟨s₀, A, e, hu⟩) callFinish_ct
  · exact two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)

end VG.Proof.Dsa.X86
