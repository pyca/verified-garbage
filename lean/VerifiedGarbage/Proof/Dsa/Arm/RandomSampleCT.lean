module

public import VerifiedGarbage.Proof.Dsa.Arm.RandomDrawCT
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomDrawCT
import VerifiedGarbage.Proof.Dsa.RandomTrace
meta import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.RandomSample
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Arm.ArithCall
import VerifiedGarbage.Proof.Dsa.Arm.Bytes
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
import VerifiedGarbage.Proof.Dsa.Arm.Doubling
import VerifiedGarbage.Proof.Dsa.Arm.PowCall
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationBody
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCall
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCorrect
import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationTrace
import VerifiedGarbage.Proof.Dsa.Arm.RandomBody
import VerifiedGarbage.Proof.Dsa.Arm.RandomPrepareCT
import VerifiedGarbage.Proof.Dsa.Arm.RandomSignCorrect
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
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.StreamBytes
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
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
meta import VerifiedGarbage.Proof.Dsa.Arm.Bytes
meta import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
meta import VerifiedGarbage.Proof.Dsa.Arm.Doubling
meta import VerifiedGarbage.Proof.Dsa.Arm.PowCall
meta import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationBody
meta import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCall
meta import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationCorrect
meta import VerifiedGarbage.Proof.Dsa.Arm.PublicValidationTrace
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomBody
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomPrepareCT
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomSample
meta import VerifiedGarbage.Proof.Dsa.Arm.RandomSignCorrect
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
# Sampling leaks only its trace (32-bit ARM)

Two runs of the sampler whose specification traces agree draw alike: each
draw's decision is the trace's head (`LoopAt.drawPre`), so they take the
same branches; after a rejection the rest of the trace is the next draw's.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm eval_eq eval_ne)

/-- The width of q's significant bytes. -/
def Pub.width (a : Pub) : Nat := (VG.Proof.Dsa.significant a.qBytes).1

theorem pub_width {s₀ : State} {a : Pub} (e : pubOf s₀ = a) : a.width = rWidth s₀ := by
  rw [← e]; rfl

/-- What two runs share before a draw of the sampling loop. -/
structure LoopPub where
  pub : Pub
  used : Nat
  draws : Nat
  tr : List Nat

/-- Before a draw of the sampling loop, whose trace is `tr`. -/
structure LoopAt (a : LoopPub) (s₀ t : State) : Prop where
  smp : Smp s₀ a.used a.draws t
  status : slot t.mem (rBase s₀) oStatus = 4
  pos : 1 ≤ a.draws
  le : a.draws ≤ 128
  q : 1 < rq s₀
  tr : (spl s₀ a.draws a.used).trace = a.tr

/-- Whether the loop draws again: a rejection, and draws left. -/
def LoopPub.cont (a : LoopPub) : Bool := (a.tr.head? == some 0) && decide (2 ≤ a.draws)

def LoopPub.next (a : LoopPub) : LoopPub := ⟨a.pub, a.used + a.pub.width, a.draws - 1, a.tr.tail⟩

/-- The draw's decision is the trace's. -/
theorem LoopAt.drawPre {a : LoopPub} {s₀ t : State} (L : LoopAt a s₀ t) :
    DrawPre ⟨a.pub, a.used, a.draws, a.tr.head? == some 1⟩ s₀ t := by
  refine ⟨L.smp, L.pos, L.le, L.q, fun hfull => ?_⟩
  dsimp only at hfull
  obtain ⟨d', hd'⟩ : ∃ d', a.draws = d' + 1 := ⟨a.draws - 1, by have := L.pos; omega⟩
  have hdw : Spec.Dsa.Random.drawBytes (rq s₀) = rWidth s₀ := rWidth_eq s₀
  have hdl : (drawBytes s₀ a.used).length = rWidth s₀ := drawBytes_length hfull
  have htr := L.tr
  rw [hd'] at htr
  show accepts s₀ (drawCand s₀ a.used) = (a.tr.head? == some 1)
  rw [accepts_candidate hdl (width_pos L.q), ← htr, spl,
    VG.Proof.Dsa.Random.sample_trace_head _ _ _ L.q (by rw [hdw, List.length_drop]; omega), hdw]

def sampleBody : Prog isa := .seq draw (.block [ld .r0 oStatus, .cmp .r0 (.imm 4)])

/-- After a draw and the loop's test. -/
def StepPost (a : LoopPub) (s₀ t : State) : Prop :=
  RReady s₀ t ∧ t.z = a.cont ∧ (a.cont = true → LoopAt a.next s₀ t)

theorem sub_four_ne {x : BitVec 32} (h : x ≠ 4) : (x - 4 == 0) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro h'
  apply h
  calc x = x - 4 + 4 := (BitVec.sub_add_cancel x 4).symm
    _ = 4 := by rw [h']; rfl

theorem step_ok {a : LoopPub} {s₀ t : State} (A : RandomABI s₀) (e : pubOf s₀ = a.pub) (L : LoopAt a s₀ t) :
    WP isa sampleBody t (StepPost a s₀) := by
  unfold sampleBody
  refine WP.seq (WP.mono (draw_ok A L.smp L.pos L.le L.q L.status) fun v ⟨hv, _, _, hcase⟩ => ?_)
  refine wp_ld hv (by decide) fun v₁ uv₁ => wp_cmp (op2_imm (by decide)) fun v₂ fv₂ zv₂ => WP.block_nil ?_
  have hv₂ : RReady s₀ v₂ := (hv.upd uv₁).fupd fv₂
  have mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
  have htr := L.tr
  rcases hcase with ⟨stv, h2, Sv, _, hspl⟩ | ⟨stv, _, hh⟩
  · have hc : a.cont = true := by
      simp only [LoopPub.cont, ← htr, hspl, List.head?_cons, beq_self_eq_true, Bool.true_and,
        decide_eq_true_eq]
      exact h2
    refine ⟨hv₂, by rw [zv₂, uv₁.gpr, stv, hc]; rfl, fun _ => ⟨?_, by rw [mv₂]; exact stv,
      by show 1 ≤ a.draws - 1; omega, by show a.draws - 1 ≤ 128; have := L.le; omega, L.q, ?_⟩⟩
    · show Smp s₀ (a.used + a.pub.width) (a.draws - 1) v₂
      rw [pub_width e]; exact Sv.mem A hv₂ mv₂
    · show (spl s₀ (a.draws - 1) (a.used + a.pub.width)).trace = a.tr.tail
      rw [pub_width e, ← htr, hspl]; rfl
  · have hc : a.cont = false := by
      simp only [LoopPub.cont, ← htr, Bool.and_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
      rcases hh with hh | hh
      · exact .inl hh
      · exact .inr (by omega)
    refine ⟨hv₂, by rw [zv₂, uv₁.gpr, sub_four_ne stv, hc], fun h => by rw [hc] at h; cases h⟩

theorem sampleLoop_ct (n : Nat) :
    RelCT isa (Two fun a t => a.draws = n ∧ At (LoopAt a) a.pub t) (.loop sampleBody .eq)
      (Two fun (a : Pub) => At (fun s₀ t => RReady s₀ t) a) := by
  refine RelCT.loop (M := isa) (fun n => Two fun a t => a.draws = n ∧ At (LoopAt a) a.pub t) (fun n => ?_) n
  have hct : RelCT isa (Two fun a t => a.draws = n ∧ At (LoopAt a) a.pub t) sampleBody fun _ _ => True := by
    unfold sampleBody
    refine RelCT.seq (two_post (Ψ := fun a => At (fun s₀ t => RReady s₀ t) a.pub)
      (two_map (fun a => (⟨a.pub, a.used, a.draws, a.tr.head? == some 1⟩ : DrawPub))
        (fun a t ⟨_, s₀, A, e, L⟩ => ⟨s₀, A, e, L.drawPre⟩) draw_ct)
      (fun a t ⟨_, s₀, A, e, L⟩ => WP.mono (draw_ok A L.smp L.pos L.le L.q L.status)
        fun u h => ⟨s₀, A, e, h.1⟩)) ?_
    exact two_taint [.r11] (pins_at (P := fun _ s₀ t => RReady s₀ t) LoopPub.pub fun _ _ _ h => h)
      (by taint_decide)
  have hp := two_post (Ψ := fun a t => a.draws = n ∧ At (StepPost a) a.pub t) hct
    fun a t ⟨hn, s₀, A, e, L⟩ => WP.mono (step_ok A e L) fun u h => ⟨hn, s₀, A, e, h⟩
  refine hp.mono (fun _ _ h => h) ?_
  rintro t₁ t₂ ⟨a, ⟨hn, s₁, A₁, e₁, r₁, z₁, c₁⟩, ⟨_, s₂, A₂, e₂, r₂, z₂, c₂⟩⟩
  refine ⟨by rw [eval_eq, eval_eq, z₁, z₂], fun _ => ⟨a.pub, ⟨s₁, A₁, e₁, r₁⟩, ⟨s₂, A₂, e₂, r₂⟩⟩, fun hc => ?_⟩
  have hc' : a.cont = true := by rw [eval_eq, z₁, Option.some.injEq] at hc; exact hc
  have h2 : 2 ≤ a.draws := by
    simp only [LoopPub.cont, Bool.and_eq_true, decide_eq_true_eq] at hc'; exact hc'.2
  exact ⟨n - 1, by omega, a.next, ⟨by show a.draws - 1 = n - 1; omega, s₁, A₁, e₁, c₁ hc'⟩,
    ⟨by show a.draws - 1 = n - 1; omega, s₂, A₂, e₂, c₂ hc'⟩⟩

/-- What two runs of the sampler share. -/
structure SmpPub where
  pub : Pub
  used : Nat
  tr : List Nat

/-- The sampler's entry. -/
def SamplePre (a : SmpPub) (s₀ t : State) : Prop :=
  (∃ d, Smp s₀ a.used d t) ∧ 1 < rq s₀ ∧ (spl s₀ 128 a.used).trace = a.tr

theorem sample_ct : RelCT isa (Two fun a => At (SamplePre a) a.pub) sample fun _ _ => True := by
  unfold sample
  refine RelCT.seq (two_piece (Ψ := fun a => At (LoopAt ⟨a.pub, a.used, 128, a.tr⟩) a.pub) [.r11]
    (pins_at SmpPub.pub fun _ _ _ h => h.1.choose_spec.ready) (by taint_decide)
    fun a t ⟨s₀, A, e, ⟨d, S⟩, hq, htr⟩ => WP.mono (sampleInit_ok A S)
      fun u ⟨S', st, _, _⟩ => ⟨s₀, A, e, S', st, (by decide : 1 ≤ 128), (by decide : 128 ≤ 128), hq, htr⟩) ?_
  refine RelCT.seq (two_map (fun a => (⟨a.pub, a.used, 128, a.tr⟩ : LoopPub)) (fun _ _ h => ⟨rfl, h⟩)
    (sampleLoop_ct 128)) ?_
  exact two_taint [.r11] (pins_at (P := fun _ s₀ t => RReady s₀ t) id fun _ _ _ h => h) (by taint_decide)

end VG.Proof.Dsa.Arm
