module

public import VerifiedGarbage.Proof.Dsa.Arm.RandomAttemptCT
public import VerifiedGarbage.Proof.Dsa.Arm.RandomFinish
public import VerifiedGarbage.Proof.Dsa.Arm.RandomSampleCT
import VerifiedGarbage.Proof.Dsa.Arm.RandomPrepareCT
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomAttemptCT
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomPrepareCT
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomSignCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.RandomBody
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Arm.ArithCall
import VerifiedGarbage.Proof.Dsa.Arm.BodyTrace
import VerifiedGarbage.Proof.Dsa.Arm.Bytes
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
import VerifiedGarbage.Proof.Dsa.Arm.Doubling
import VerifiedGarbage.Proof.Dsa.Arm.OpTrace
import VerifiedGarbage.Proof.Dsa.Arm.PowCall
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationBody
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCall
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCorrect
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationTrace
import VerifiedGarbage.Proof.Dsa.Arm.RandomCallCT
import VerifiedGarbage.Proof.Dsa.Arm.RandomSample
import VerifiedGarbage.Proof.Dsa.Arm.RandomSignCorrect
import VerifiedGarbage.Proof.Dsa.Arm.ScheduleTrace
import VerifiedGarbage.Proof.Dsa.Arm.ShapeTrace
import VerifiedGarbage.Proof.Dsa.Arm.SignCT
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.Arm.ValidateTrace
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.StreamBytes
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Digit
import VerifiedGarbage.Proof.Mont.Arm.Dyn.DigitRow
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
import VerifiedGarbage.Proof.Mont.Arm.Dyn.MulRow
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ops
import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Select
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Mont.Arm.Row
import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog
import VerifiedGarbage.Proof.Weierstrass.BytesLen32
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.Words32
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.Arm.ArithCall
meta import VerifiedGarbage.Proof.Dsa.Arm.BodyTrace
meta import VerifiedGarbage.Proof.Dsa.Arm.Bytes
meta import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
meta import VerifiedGarbage.Proof.Dsa.Arm.Doubling
meta import VerifiedGarbage.Proof.Dsa.Arm.OpTrace
meta import VerifiedGarbage.Proof.Dsa.Arm.PowCall
meta import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationBody
meta import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCall
meta import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCorrect
meta import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationTrace
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomBody
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomCallCT
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomSample
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomSampleCT
meta import VerifiedGarbage.Proof.Dsa.Arm.ScheduleTrace
meta import VerifiedGarbage.Proof.Dsa.Arm.ShapeTrace
meta import VerifiedGarbage.Proof.Dsa.Arm.SignCT
meta import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
meta import VerifiedGarbage.Proof.Dsa.Arm.ValidateTrace
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Frame
meta import VerifiedGarbage.Proof.Dsa.OutputBytes
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Dsa.Random
meta import VerifiedGarbage.Proof.Dsa.RandomEncoding
meta import VerifiedGarbage.Proof.Dsa.RandomSign
meta import VerifiedGarbage.Proof.Dsa.RandomSignResult
meta import VerifiedGarbage.Proof.Dsa.RandomTrace
meta import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Dsa.SignVerify
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.StreamBytes
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Mont.Arm.Csub
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Digit
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.DigitRow
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.MulRow
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ops
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Select
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
meta import VerifiedGarbage.Proof.Mont.Arm.Row
meta import VerifiedGarbage.Proof.Mont.Arm.Step
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Const
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog
meta import VerifiedGarbage.Proof.Weierstrass.BytesLen32
meta import VerifiedGarbage.Proof.Weierstrass.Words
meta import VerifiedGarbage.Proof.Weierstrass.Words32

/-!
# The randomized signer's body leaks only its public data (32-bit ARM)

The entry computes the frame's base from `sp` (`entry_ct`). The attempts
continue after a retry with attempts left, which the signing trace records
(`AttPub.cont`); the next attempt's trace is the rest of it. `finish`
branches on the overall status, and writes through the public `out` and
`used` pointers.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm eval_eq eval_ne)
open VG.Proof.Dsa (randomSignRemaining randomSamplingTrace randomSigningTrace)

/-! ## The attempts -/

/-- Whether another attempt follows: a retry, with attempts left. -/
def AttPub.cont (a : AttPub) : Bool := ((randomSigningTrace a.tr).head? == some 6) && decide (2 ≤ a.fuel)

def AttPub.next (a : AttPub) : AttPub :=
  ⟨a.pub, a.leak, a.used + a.pub.width * (randomSamplingTrace a.tr).countP (· ≤ 1), a.fuel - 1,
    (randomSigningTrace a.tr).tail, a.status⟩

/-- The test of the attempt's status. -/
abbrev attTest : Prog isa := .block [ld .r0 oStatus, .cmp .r0 (.imm 4)]

theorem AttemptOut.ready {s₀ u : State} {used f : Nat} (h : AttemptOut s₀ used f u) : RReady s₀ u := by
  rcases h with ⟨_, _, T, _⟩ | ⟨_, D, _⟩
  · obtain ⟨_, S⟩ := T.smp; exact S.ready
  · obtain ⟨_, S⟩ := D.smp; exact S.ready

/-- After an attempt and its test. -/
def AStep (a : AttPub) (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.z = a.cont ∧ (a.cont = true → AttAt a.next s₀ t) ∧ (a.cont = false → RFin s₀ t)

theorem astep_ok (name : String) {a : AttPub} {s₀ t : State} (A : RandomABI s₀) (e : pubOf s₀ = a.pub)
    (L : AttAt a s₀ t) : WP isa (.seq (attempt name (Entry.operation true)) attTest) t (AStep a s₀) := by
  obtain ⟨Fa, T⟩ := L
  obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := Fa.pos; omega⟩
  have hf8 : f + 1 ≤ 8 := hf ▸ Fa.le
  rw [hf] at T
  refine WP.seq (WP.mono (attempt_ok name A T hf8 Fa.q) fun v hv => ?_)
  have hrv := hv.ready
  refine wp_ld hrv (by decide) fun v₁ uv₁ => wp_cmp (op2_imm (by decide)) fun v₂ fv₂ zv₂ => WP.block_nil ?_
  have hv₂ := (hrv.upd uv₁).fupd fv₂
  have mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
  rw [uv₁.gpr] at zv₂
  have htr := Fa.tr
  rw [hf] at htr
  rcases hv with ⟨st, h1f, T', hs⟩ | ⟨st, D, hh⟩
  · have hc : a.cont = true := by
      simp only [AttPub.cont, ← htr, hs, List.head?_cons, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
      omega
    refine ⟨hv₂, by rw [zv₂, st, hc]; rfl, fun _ => ?_, fun h => Bool.noConfusion (hc.symm.trans h)⟩
    have hu : a.pub.width * (randomSamplingTrace a.tr).countP (· ≤ 1) = (spl s₀ 128 a.used).used := by
      rw [(VG.Proof.Dsa.Random.sample_trace_result _ _ _).1, Fa.spl_trace, pub_width e, rWidth_eq]
    refine ⟨⟨Fa.q, by show 1 ≤ a.fuel - 1; omega, by show a.fuel - 1 ≤ 8; omega, Fa.leak, ?_⟩, ?_⟩
    · show (randomSignRemaining (rInput s₀) (a.used + a.pub.width * _) (a.fuel - 1)).trace =
        (randomSigningTrace a.tr).tail
      rw [hu, hf, Nat.add_sub_cancel, ← htr, hs]; rfl
    · show Att s₀ (a.used + a.pub.width * _) (a.fuel - 1) v₂
      rw [hu, hf, Nat.add_sub_cancel]; exact T'.mem A hv₂ mv₂
  · have hc : a.cont = false := by
      simp only [AttPub.cont, ← htr, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
        decide_eq_false_iff_not]
      by_cases h6 : (randomSigningTrace (randomSignRemaining (rInput s₀) a.used (f + 1)).trace).head? = some 6
      · exact .inr fun h2 => hh ⟨h6, by omega⟩
      · exact .inl h6
    exact ⟨hv₂, by rw [zv₂, sub_four_ne st, hc], fun h => Bool.noConfusion (hc.symm.trans h),
      fun _ => (D.mem A hv₂ mv₂).rfin⟩

/-- At the end: the frame's slots, and the overall status `p.2`. -/
def FinAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => RFin s₀ t ∧ (rResult s₀).status = p.2) p.1

/-- Before an attempt, with the overall status. -/
def LoopAt' (a : AttPub) : State → Prop := At (fun s₀ t => AttAt a s₀ t ∧ (rResult s₀).status = a.status) a.pub

theorem attemptLoop_ct (name : String) (n : Nat) :
    RelCT isa (Two fun a t => a.fuel = n ∧ LoopAt' a t)
      (.loop (.seq (attempt name (Entry.operation true)) attTest) .eq) (Two FinAt) := by
  refine RelCT.loop (M := isa) (fun n => Two fun a t => a.fuel = n ∧ LoopAt' a t) (fun n => ?_) n
  have hct : RelCT isa (Two fun a t => a.fuel = n ∧ LoopAt' a t)
      (.seq (attempt name (Entry.operation true)) attTest) fun _ _ => True := by
    refine RelCT.seq (two_post (Ψ := fun a => At (fun s₀ t => RReady s₀ t) a.pub)
      (two_map id (fun a t ⟨_, s₀, A, e, L, _⟩ => ⟨s₀, A, e, L⟩) (attempt_ct name))
      (fun a t ⟨_, s₀, A, e, ⟨Fa, T⟩, _⟩ => ?_)) ?_
    · obtain ⟨f, hf⟩ : ∃ f, a.fuel = f + 1 := ⟨a.fuel - 1, by have := Fa.pos; omega⟩
      have hf8 : f + 1 ≤ 8 := hf ▸ Fa.le
      rw [hf] at T
      exact WP.mono (attempt_ok name A T hf8 Fa.q) fun u h => ⟨s₀, A, e, h.ready⟩
    · exact two_taint [.r11] (pins_at (P := fun _ s₀ t => RReady s₀ t) AttPub.pub fun _ _ _ h => h)
        (by taint_decide)
  have hp := two_post (Ψ := fun a t => a.fuel = n ∧ At (fun s₀ t => AStep a s₀ t ∧
      (rResult s₀).status = a.status) a.pub t) hct
    fun a t ⟨hn, s₀, A, e, L, st⟩ => WP.mono (astep_ok name A e L) fun u h => ⟨hn, s₀, A, e, h, st⟩
  refine hp.mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨a, ⟨hn, s₁, A₁, e₁, ⟨r₁, z₁, c₁, d₁⟩, st₁⟩, ⟨_, s₂, A₂, e₂, ⟨r₂, z₂, c₂, d₂⟩, st₂⟩⟩
  refine ⟨by rw [eval_eq, eval_eq, z₁, z₂], fun hc => ?_, fun hc => ?_⟩
  · have hc' : a.cont = false := by rw [eval_eq, z₁, Option.some.injEq] at hc; exact hc
    exact ⟨(a.pub, a.status), ⟨s₁, A₁, e₁, d₁ hc', st₁⟩, ⟨s₂, A₂, e₂, d₂ hc', st₂⟩⟩
  · have hc' : a.cont = true := by rw [eval_eq, z₁, Option.some.injEq] at hc; exact hc
    have h2 : 2 ≤ a.fuel := by
      simp only [AttPub.cont, Bool.and_eq_true, decide_eq_true_eq] at hc'; exact hc'.2
    exact ⟨n - 1, by omega, a.next, ⟨by show a.fuel - 1 = n - 1; omega, s₁, A₁, e₁, c₁ hc', st₁⟩,
      ⟨by show a.fuel - 1 = n - 1; omega, s₂, A₂, e₂, c₂ hc', st₂⟩⟩

/-! ## The end -/

/-- Test the overall status. -/
theorem finTest_ok {s₀ t : State} (A : RandomABI s₀) (F : RFin s₀ t) :
    WP isa (.block [ld .r0 oStatus, .cmp .r0 (.imm 1)]) t fun u =>
      RReady s₀ u ∧ Saved s₀ u.mem ∧ u.z = decide ((rResult s₀).status = 1) := by
  have hR := rResult_status_le A
  refine wp_ld F.ready (by decide) fun t₁ u₁ => wp_cmp (op2_imm (by decide)) fun t₂ f₂ z₂ => WP.block_nil ?_
  rw [u₁.gpr, F.status, one_beq (by omega)] at z₂
  exact ⟨(F.ready.upd u₁).fupd f₂, by rw [f₂.mem, u₁.mem]; exact F.saved, z₂⟩

/-- Ready, with public data `p.1`. -/
def ReadyAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => RReady s₀ t ∧ Saved s₀ t.mem) p.1

/-- The output's address and length. -/
theorem zeroHead_ok {s₀ t : State} (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa (.block [ld .r1 oOut, ld .r2 oOutLen, .mov .r0 (.imm 0)]) t fun u =>
      u.gpr .r1 = s₀.gpr .r0 ∧ u.gpr .r2 = s₀.gpr .r1 := by
  refine wp_ld h (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    VG.Proof.X25519.Arm.wp_mov (op2_imm (by decide)) fun t₃ u₃ => WP.block_nil ⟨?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, sv.2.1]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, sv.2.2.1]

theorem zeroOut_ct : RelCT isa (Two fun p s => ReadyAt p s ∧ isa.eval .ne s = some true) zeroOut
    fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => t.gpr .r1 = s₀.gpr .r0 ∧ t.gpr .r2 = s₀.gpr .r1) p.1)
    [.r11] (pins_at' (P := fun _ s₀ t => RReady s₀ t ∧ Saved s₀ t.mem) Prod.fst fun _ _ _ h => h.1)
    (by taint_decide) fun p t ⟨⟨s₀, A, e, h, sv⟩, _⟩ => WP.mono (zeroHead_ok h sv) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.r1, .r2] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, x₁, c₁⟩ := h₁
  obtain ⟨s₂, _, e₂, x₂, c₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [x₁, x₂, pub_r0 e]
  · rw [c₁, c₂, pub_r1 e]

/-- The nonce cleared, and the address of `used`. -/
theorem finPrefix_ok {s₀ t : State} (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa (.block (clearNonce ++ ([ld .r4 oUsedPtr] : List Instr))) t fun u =>
      RReady s₀ u ∧ u.gpr .r4 = s₀.gpr .r2 := by
  refine clearNonce_ok h fun t₁ h₁ m₁ _ _ => ?_
  have o₁ : Outs (rBase s₀) [(oNonce, 32)] t.mem t₁.mem := by
    rw [m₁]; exact Outs.of_outside (clearMem_outside _ _ 8 (by decide)) (List.mem_singleton_self _)
  have sv₁ : Saved s₀ t₁.mem := sv.of_outs o₁ (by decide)
  exact wp_ld h₁ (by decide) fun t₂ u₂ => WP.block_nil ⟨h₁.upd u₂, by rw [u₂.gpr]; exact sv₁.2.2.2.1⟩

theorem finalBlock_ct : RelCT isa (Two ReadyAt) (.block (clearNonce ++ finalList)) fun _ _ => True := by
  show RelCT isa _ (.block ((clearNonce ++ [ld .r4 oUsedPtr]) ++
    [ld .r0 oUsed, .str .r0 .r4 0, .mov .r0 (.imm 0), .str .r0 .r4 4, ld .r0 oStatus,
      ld .r4 0, ld .r5 4, ld .r6 8, ld .r7 12, ld .r8 16, ld .r9 20, ld .r10 24, ld .lr 32, ld .r11 28])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => RReady s₀ t ∧ t.gpr .r4 = s₀.gpr .r2) p.1)
    [.r11] (pins_at (P := fun _ s₀ t => RReady s₀ t ∧ Saved s₀ t.mem) Prod.fst fun _ _ _ h => h.1)
    (by taint_decide) fun p t ⟨s₀, A, e, h, sv⟩ => WP.mono (finPrefix_ok h sv) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.r11, .r4] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, r₁, d₁⟩ := h₁
  obtain ⟨s₂, _, e₂, r₂, d₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact r11_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
  · rw [d₁, d₂, pub_r2 e]

theorem finish_ct : RelCT isa (Two FinAt) finish fun _ _ => True := by
  unfold finish
  rw [finishBlock_eq]
  refine RelCT.seq (two_piece (Ψ := fun (p : Pub × Nat) => At (fun s₀ t => RReady s₀ t ∧ Saved s₀ t.mem ∧
      t.z = decide (p.2 = 1)) p.1) [.r11]
    (pins_at (P := fun p s₀ t => RFin s₀ t ∧ (rResult s₀).status = p.2) Prod.fst fun _ _ _ h => h.1.ready)
    (by taint_decide) fun p t ⟨s₀, A, e, Fi, st⟩ => WP.mono (finTest_ok A Fi)
      fun u ⟨h, sv, z⟩ => ⟨s₀, A, e, h, sv, by rw [z, st]⟩) ?_
  refine RelCT.seq (R := Two ReadyAt) (two_ite (fun p t₁ t₂ ⟨s₁, _, e₁, _, _, z₁⟩ ⟨s₂, _, e₂, _, _, z₂⟩ => by
    rw [eval_ne, eval_ne, z₁, z₂]) ?_ ?_) finalBlock_ct
  · exact two_post (Ψ := ReadyAt) (two_map id (fun p t ⟨⟨s₀, A, e, h, sv, _⟩, hb⟩ => ⟨⟨s₀, A, e, h, sv⟩, hb⟩)
      zeroOut_ct) fun p t ⟨⟨s₀, A, e, h, sv, _⟩, _⟩ => WP.mono (zeroOut_ok A h sv)
        fun u ⟨hv, fv, _, _⟩ => ⟨s₀, A, e, hv, sv.of_slots fun d _ hd => apart_slot fv A.stackOut hd⟩
  · exact two_post (Ψ := ReadyAt) (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide))
      fun p t ⟨⟨s₀, A, e, h, sv, _⟩, _⟩ => WP.block_nil ⟨s₀, A, e, h, sv⟩

/-! ## The body -/

/-- What two runs of the body share: the public data and key bytes, and
the overall status and trace. -/
structure BodyPub where
  pub : Pub
  leak : List Nat
  status : Nat
  tr : List Nat

structure BodyFacts (b : BodyPub) (s₀ : State) : Prop where
  leak : keyLeak s₀ = b.leak
  status : (rResult s₀).status = b.status
  tr : (rResult s₀).trace = b.tr

/-- The body's entry, after the frame's allocation. -/
def BodyEntry (b : BodyPub) (s₀ t : State) : Prop := BodyFacts b s₀ ∧ t = allocated frameBytes s₀

/-- After the entry's first instruction, which puts the frame's base in `r12`. -/
def entryBase (s₀ : State) : State :=
  (allocated frameBytes s₀).setReg .r12 ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)

def Based (b : BodyPub) (s₀ t : State) : Prop := BodyFacts b s₀ ∧ t = entryBase s₀

/-- After the entry block. -/
def Entered (b : BodyPub) (s₀ t : State) : Prop :=
  BodyFacts b s₀ ∧ RReady s₀ t ∧ Saved s₀ t.mem ∧ slot t.mem (rBase s₀) oUsed = 0 ∧
    slot t.mem (rBase s₀) oAttempts = 8

theorem exec_entryBase (s₀ : State) : isa.exec (.addSp .r12 0) (allocated frameBytes s₀) = some (entryBase s₀) := by
  simp [exec, entryBase]

theorem entryRest_ok {s₀ : State} (A : RandomABI s₀) :
    WP isa (.block entry.tail) (entryBase s₀) fun u => RReady s₀ u ∧ Saved s₀ u.mem ∧
      slot u.mem (rBase s₀) oUsed = 0 ∧ slot u.mem (rBase s₀) oAttempts = 8 := by
  have h := entry_ok A
  rw [show entry = .addSp .r12 0 :: entry.tail from rfl, WP.block_cons_iff] at h
  obtain ⟨s', hs, W⟩ := h
  rw [exec_entryBase, Option.some.injEq] at hs
  subst hs
  exact WP.mono W fun u ⟨a, b, c, d, _⟩ => ⟨a, b, c, d⟩

theorem entryBase_r12 (s₀ : State) : (entryBase s₀).gpr .r12 = s₀.sp - BitVec.ofNat 32 frameBytes := by
  simp [entryBase, State.setReg, allocated]

theorem entry_ct : RelCT isa (Two fun b => At (BodyEntry b) b.pub) (.block entry) (Two fun b => At (Entered b) b.pub) := by
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
    exact WP.mono (entryRest_ok A) fun u ⟨h, sv, us, at₁⟩ => ⟨s₀, A, e, Fb, h, sv, us, at₁⟩

/-- After `prepare`. -/
structure Prepped (b : BodyPub) (s₀ t : State) : Prop where
  facts : BodyFacts b s₀
  ready : RReady s₀ t
  r0 : t.gpr .r0 = if 1 < rq s₀ then 1 else 0
  prep : 1 < rq s₀ → Prepared s₀ t
  saved : Saved s₀ t.mem
  used : slot t.mem (rBase s₀) oUsed = 0
  attempts : slot t.mem (rBase s₀) oAttempts = 8

theorem Prepped.fupd {b : BodyPub} {s₀ t u : State} (h : Prepped b s₀ t) (f : Fupd t u) : Prepped b s₀ u := by
  have hr := h.ready.fupd f
  have hm : u.mem = t.mem := f.mem
  refine ⟨h.facts, hr, by rw [f.gpr]; exact h.r0, fun hq => ?_, by rw [hm]; exact h.saved,
    by rw [hm]; exact h.used, by rw [hm]; exact h.attempts⟩
  have P := h.prep hq
  exact ⟨hr, by rw [hm]; exact P.q, by rw [hm]; exact P.width, by rw [hm]; exact P.mask,
    by rw [hm]; exact P.nonce⟩

theorem prepped_ok {b : BodyPub} {s₀ t : State} (A : RandomABI s₀) (E : Entered b s₀ t) :
    WP isa prepare t (Prepped b s₀) := by
  obtain ⟨Fb, h₁, sv₁, us₁, at₁⟩ := E
  refine WP.mono (prepare_ok A h₁ sv₁.2.2.2.2) fun t₂ ⟨ax₂, P₂, h₂, o₂, _⟩ => ?_
  have lo₂ : ∀ d, d + 4 ≤ oQ → slot t₂.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    outs_low o₂ (by decide) hd (by unfold oQ at hd; omega)
  exact ⟨Fb, h₂, ax₂, P₂, sv₁.of_outs o₂ (by decide), by rw [lo₂ _ (by decide)]; exact us₁,
    by rw [lo₂ _ (by decide)]; exact at₁⟩

/-- After the test of q. -/
def Checked (b : BodyPub) (s₀ t : State) : Prop := Prepped b s₀ t ∧ t.z = !decide (1 < rq s₀)

/-- q ≤ 1: the status, and the end. -/
theorem small_fin {b : BodyPub} {s₀ t : State} (A : RandomABI s₀) (C : Checked b s₀ t) (hq : ¬ 1 < rq s₀) :
    WP isa (.block [st .r0 oStatus]) t fun u => RFin s₀ u ∧ (rResult s₀).status = b.status := by
  obtain ⟨Pp, _⟩ := C
  have hR := rResult_small A hq
  have r0 : t.gpr .r0 = BitVec.ofNat 32 (rResult s₀).status := by
    rw [Pp.r0, hR]; simp only [hq, ↓reduceIte]; rfl
  refine wp_st Pp.ready (by decide) fun t₄ m₄ h₄ => WP.block_nil ?_
  rw [r0] at m₄
  refine ⟨⟨h₄, ?_, by rw [m₄.mem, slot_write_self], fun e => by rw [hR] at e; exact absurd e (by decide),
    Pp.saved.of_slots fun d hd _ => by rw [m₄.mem, slot_write_ne _ _ _ (by unfold oStatus; omega) (by omega)
      (by decide)]⟩, Pp.facts.status⟩
  rw [m₄.mem, slot_write_ne _ _ _ (by decide) (by decide) (by decide), Pp.used, hR]; rfl

theorem body_ct (name : String) :
    RelCT isa (Two fun b => At (BodyEntry b) b.pub) (body name (Entry.operation true)) fun _ _ => True := by
  unfold body
  refine RelCT.seq entry_ct ?_
  refine RelCT.seq (two_post (Ψ := fun b => At (Prepped b) b.pub)
    (two_map BodyPub.pub (fun b t ⟨s₀, A, e, E⟩ => ⟨s₀, A, e, E.2.1, E.2.2.1.2.2.2.2⟩) prepare_ct)
    fun b t ⟨s₀, A, e, E⟩ => WP.mono (prepped_ok A E) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine RelCT.seq (two_piece (Ψ := fun b => At (Checked b) b.pub) []
    (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)
    fun b t ⟨s₀, A, e, Pp⟩ => wp_cmp0 fun u f z => WP.block_nil ⟨s₀, A, e, Pp.fupd f, ?_⟩) ?_
  · rw [z, Pp.r0]
    by_cases hq : 1 < rq s₀ <;> simp [hq]
  refine RelCT.seq (R := Two FinAt) (two_ite (fun b t₁ t₂ ⟨s₁, _, e₁, _, z₁⟩ ⟨s₂, _, e₂, _, z₂⟩ => by
    rw [eval_eq, eval_eq, z₁, z₂, pub_rq (e₁.trans e₂.symm)]) ?_ ?_) finish_ct
  · refine (two_post (Ψ := fun (b : BodyPub) => At (fun s₀ t => RFin s₀ t ∧ (rResult s₀).status = b.status) b.pub)
      (two_taint [.r11] (pins_at' BodyPub.pub fun _ _ _ h => h.1.ready) (by taint_decide))
      fun b t ⟨⟨s₀, A, e, C⟩, hb⟩ => WP.mono (small_fin A C (by
        rw [eval_eq, C.2, Option.some.injEq] at hb
        simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using hb)) fun u hu => ⟨s₀, A, e, hu⟩).mono
      (fun _ _ h => h) fun _ _ ⟨b, h₁, h₂⟩ => ⟨(b.pub, b.status), h₁, h₂⟩
  · refine two_map (fun b => (⟨b.pub, b.leak, 0, 8, b.tr, b.status⟩ : AttPub))
      (fun b t ⟨⟨s₀, A, e, Pp, z⟩, hb⟩ => ⟨rfl, s₀, A, e, ?_, Pp.facts.status⟩) (attemptLoop_ct name 8)
    have hq : 1 < rq s₀ := by
      rw [eval_eq, z, Option.some.injEq] at hb
      simpa only [Bool.not_eq_false', decide_eq_true_eq] using hb
    have P := Pp.prep hq
    have hql := rQBytes_le A
    have hfit := rWidth_le s₀
    have er : randomSignRemaining (rInput s₀) 0 8 = rResult s₀ := by rw [rResult_loop A]; rfl
    refine ⟨⟨hq, (by decide : 1 ≤ 8), (by decide : 8 ≤ 8), Pp.facts.leak, by
      show (randomSignRemaining (rInput s₀) 0 8).trace = b.tr; rw [er]; exact Pp.facts.tr⟩, ?_⟩
    refine ⟨⟨(slot t.mem (rBase s₀) oDraws).toNat, ⟨Pp.ready, P.q, P.width, P.mask, Pp.used,
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], fun i hi => P.nonce i (by omega), Nat.zero_le _⟩⟩,
      Pp.attempts, Pp.saved, ?_⟩
    exact ⟨by rw [er], by rw [er], by rw [er]⟩

end VG.Proof.Dsa.Arm
