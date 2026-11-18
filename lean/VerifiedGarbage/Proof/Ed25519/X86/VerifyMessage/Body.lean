module

public import VerifiedGarbage.Proof.Ed25519.X86.Whole.Setup
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre
import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
public import VerifiedGarbage.Impl.Ed25519.X86.VerifyMessage
public import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTLit
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyContract
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyLit
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Reduce
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Count
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyDecode
import VerifiedGarbage.Proof.Ed25519.X86.VerifyScalar
import VerifiedGarbage.Proof.Ed25519.X86.VerifyFinish
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTBytes
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTInputs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.X86.WindowCT
import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyDecode
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyScalar
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyFinish
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTBytes
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTInputs
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Ed25519.Group.Decode
meta import VerifiedGarbage.Proof.Ed25519.X86.WindowCT
meta import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyLit
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Ed25519.Group.Double
import VerifiedGarbage.Proof.Ed25519.X86.VerifyPoints
import VerifiedGarbage.Proof.Framework.X86.TaintSym
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTLit
meta import VerifiedGarbage.Proof.Ed25519.Group.Double
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyPoints
meta import VerifiedGarbage.Proof.Framework.X86.TaintSym
meta import VerifiedGarbage.Proof.Ed25519.Window
meta import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTLit
public import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
meta import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Lit

/-! ### `Ed25519.X86.VerifyVerified`, which this module and modules that import it used -/

section

/-! ### `Ed25519.X86.VerifyCTEquation`, which only this module used -/

section

/-!
# Verification's equation: what its traces depend on

The windows' traces depend only on the public scalars (`windowMultiply_ct`), and the projective
comparison's on whether the points represented are equal (`pointEqualRep_ct`), the same in both
runs.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

private theorem ctEqualOps_eval (e : Env) :
    evalOps pointEqualOps e 8 = e 0 * e 6 ∧ evalOps pointEqualOps e 9 = e 4 * e 2 ∧
    evalOps pointEqualOps e 10 = e 1 * e 6 ∧ evalOps pointEqualOps e 11 = e 5 * e 2 := ⟨rfl, rfl, rfl, rfl⟩

/-- Two points representing `P` and `Q` in slots 0–3 and 4–7. -/
def EqRepPre (base : BitVec 32) (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) (s : State) : Prop :=
  Ctx base s ∧ VG.Proof.Ed25519.RepP (point (env s.mem base) 0 1 2 3) P ∧
    VG.Proof.Ed25519.RepP (point (env s.mem base) 4 5 6 7) Q

/-- Before pass `n` of `equalStep`: slots 8 and 9 are equal exactly when `P` and `Q` agree in `x`
(`n = 2`, with slots 10 and 11 for `y`) or in `y` (`n = 1`). -/
def EqLoopCT (base : BitVec 32) (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) (n : Nat) (s : State) : Prop :=
  Ctx base s ∧ s.gpr .esi = BitVec.ofNat 32 n ∧
    ((n = 2 ∧ (env s.mem base 8 = env s.mem base 9 ↔ P.x = Q.x) ∧
        (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) ∨
      (n = 1 ∧ (env s.mem base 8 = env s.mem base 9 ↔ P.y = Q.y)))

/-- The condition pass `n` compares. -/
abbrev eqCond (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) (n : Nat) : Prop := if n = 2 then P.x = Q.x else P.y = Q.y

theorem EqLoopCT.cond {base : BitVec 32} {P Q : Edwards.EPoint VG.Proof.Ed25519.dZ} {n : Nat} {s : State}
    (h : EqLoopCT base P Q n s) : env s.mem base 8 = env s.mem base 9 ↔ eqCond P Q n := by
  rcases h.2.2 with ⟨rfl, e, _⟩ | ⟨rfl, e⟩
  · exact e
  · exact e

/-- One pass: its trace depends only on the comparison, which is the same in both runs. -/
theorem equalStep_ct (base : BitVec 32) (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) (n : Nat) :
    RelCT isa (fun s t => EqLoopCT base P Q n s ∧ EqLoopCT base P Q n t) equalStep (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => EqLoopCT base P Q n s ∧ EqLoopCT base P Q n t)
      (.block (fieldEqual 8 9)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : EqLoopCT base P Q n s) :
      WP isa (.block (fieldEqual 8 9)) s fun t => Ctx base t ∧ t.zf = some (decide (eqCond P Q n)) :=
    WP.mono (fieldEqual_ok h.1 8 9) fun t k => ⟨k.1.ctx h.1, by
      rw [k.2.2]; exact congrArg some (decide_eq_decide.mpr h.cond)⟩
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [equalStep]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
    exact fun _ _ h => edi_agree h.1.2.1.1.edi h.1.2.2.1.edi
  · apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by native_taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)

/-- The comparison branches on whether the points represented are equal. -/
theorem pointEqualRep_ct (base : BitVec 32) (P Q : Edwards.EPoint VG.Proof.Ed25519.dZ) :
    RelCT isa (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      Impl.Ed25519.X86.pointEqual (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      (.block (fieldCode pointEqualOps ++ [.mov .esi (.imm 2)])) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : EqRepPre base P Q s) :
      WP isa (.block (fieldCode pointEqualOps ++ [.mov .esi (.imm 2)])) s (EqLoopCT base P Q 2) := by
    rw [WP.block_append_iff]
    refine WP.mono (fieldCode_ok pointEqualOps h.1) fun a ⟨ka, ea⟩ => Wp.wp_movi fun t u => WP.block_nil ?_
    have ev := ctEqualOps_eval (env s.mem base)
    refine ⟨(IKeep.of_counter u).ctx (ka.ctx h.1), u.gpr, .inl ⟨rfl, ?_, ?_⟩⟩
    · rw [u.mem, ea, ev.1, ev.2.1]; exact VG.Proof.Ed25519.repP_cross_x h.2.1 h.2.2
    · rw [u.mem, ea, ev.2.2.1, ev.2.2.2]; exact VG.Proof.Ed25519.repP_cross_y h.2.1 h.2.2
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [Impl.Ed25519.X86.pointEqual]
  refine VG.RelCT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (VG.RelCT.loop (M := isa) (body := equalStep) (c := .ne) (Q := fun _ _ => True) (fun (n : Nat) (s t : State) => EqLoopCT base P Q n s ∧ EqLoopCT base P Q n t)
      (fun n => ?_) 2)
  -- One pass: the same branch in both runs, and the next pass's facts.
  have step (s : State) (h : EqLoopCT base P Q n s) : WP isa equalStep s fun t =>
      isa.eval .ne t = some (decide (eqCond P Q n ∧ n - 1 ≠ 0)) ∧
      (eqCond P Q n ∧ n - 1 ≠ 0 → EqLoopCT base P Q (n - 1) t) := by
    have hn : 1 ≤ n ∧ n ≤ 2 := by rcases h.2.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
    refine WP.mono (equalStep_ok h.1 hn.1 hn.2 h.2.1) fun t ⟨k, yes, no⟩ => ?_
    by_cases c : eqCond P Q n
    · obtain ⟨_, ri, rz, r8, r9⟩ := yes (h.cond.mpr c)
      refine ⟨by rw [rz]; simp [c], fun ⟨_, hn1⟩ => ⟨k.ctx h.1, ri, ?_⟩⟩
      rcases h.2.2 with ⟨rfl, _, ey⟩ | ⟨rfl, _⟩
      · exact .inr ⟨rfl, by rw [r8, r9]; exact ey⟩
      · exact absurd rfl hn1
    · obtain ⟨_, rz⟩ := no (fun e => c (h.cond.mp e))
      exact ⟨by rw [rz]; simp [c], fun ⟨c', _⟩ => absurd c' c⟩
  refine (VG.RelCT.wp (equalStep_ct base P Q n) fun s t h => ⟨step s h.1, step t h.2⟩).mono
    (fun _ _ h => h) fun s t ⟨_, ⟨es, ns⟩, ⟨et, nt⟩⟩ => ⟨es.trans et.symm, fun _ => trivial, fun e => ?_⟩
  rw [es] at e
  have c := of_decide_eq_true (Option.some.inj e)
  exact ⟨n - 1, by omega, ns c, nt c⟩

end VG.Proof.Ed25519.X86

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards

/-- Before the equation's points: the saved state, `A` at byte 7680, `R` at byte 7808, and the
static's address. -/
def PointsCTPre (s₀ : State) (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  Saved s₀ (arg s₀ 3) s ∧ tablePoint s.mem (arg s₀ 3) 7680 = a ∧ tablePoint s.mem (arg s₀ 3) 7808 = r ∧
    s.syms = s₀.syms

/-- The copy of the static: its addresses are the static's, public, and the working space's. -/
theorem bTable_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a r : Spec.Ed25519.Point) :
    RelCT isa (fun s t => PointsCTPre s₀ a r s ∧ PointsCTPre t₀ a r t) bTable (fun _ _ => True) :=
  VG.RelCT.taint (A := taintSym [bSym]) callTaint₀
    (fun _ _ hh => ⟨callTaint₀_agree (h.callPre hh.1.1 hh.2.1), fun n hn => by
      rw [List.mem_singleton.mp hn, hh.1.2.2.2, hh.2.2.2.2]; exact h.sym⟩) (by native_taint_decide)

/-- The windows, `-R`, and the comparison: the windows' traces depend only on the public
scalars, and the comparison's on whether the points represented are equal. -/
theorem verifyEquationPoints_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (a r : Spec.Ed25519.Point)
    {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    RelCT isa (fun s t => PointsCTPre s₀ a r s ∧ PointsCTPre t₀ a r t) verifyEquationPoints
      (fun _ _ => True) := by
  have bw (u x : State) (hu : VerifyPre u) (hx : PointsCTPre u a r x) : WP isa bTable x (EquationCTPre u a r) :=
    WP.mono (bTable_stage hu hx.1 hx.2.2.2) fun _ ⟨sb, ab, rb, tb⟩ =>
      ⟨sb, ab.trans hx.2.1, rb.trans hx.2.2.1, tb⟩
  have ww (u x : State) (hu : VerifyPre u) (hx : EquationCTPre u a r x) :=
    windowMultiply_ok hu hx.1 hA hx.2.1 hx.2.2.1 hx.2.2.2
  have nw (u x : State) (hx : WinCtx u Aa r x ∧ Rep (point (env x.mem (arg u 3)) 0 1 2 3)
      (verificationChallenge u • Aa + verificationScalar u • (-baseAff))) :
      WP isa (.block negR) x
        (EqRepPre (arg u 3) (verificationChallenge u • Aa + verificationScalar u • (-baseAff)) (-Ra)) :=
    WP.mono (negR_ok hx.1.ctx) fun t ⟨kt, qt, pt⟩ =>
      ⟨kt.ctx hx.1.ctx, by rw [pt]; exact hx.2.proj, by rw [qt, hx.1.r]; exact hR.neg.proj⟩
  rw [verifyEquationPoints]
  refine seq_runs (bTable_ct h a r) (fun x hx => bw s₀ x (verify_pre h.left) hx)
    (fun y hy => bw t₀ y (verify_pre h.right) hy) ?_
  refine seq_runs (windowMultiply_ct h hA) (fun x hx => ww s₀ x (verify_pre h.left) hx)
    (fun y hy => ww t₀ y (verify_pre h.right) hy) ?_
  refine seq_runs (VG.RelCT.taint (A := taint) (regsTaint [.edi])
    (fun _ _ hh => agree_one (saved_edi h hh.1.1.saved hh.2.1.saved)) (by native_taint_decide))
    (fun x hx => nw s₀ x hx) (fun y hy => nw t₀ y hy) ?_
  refine (pointEqualRep_ct (arg s₀ 3) (verificationChallenge s₀ • Aa + verificationScalar s₀ • (-baseAff))
    (-Ra)).mono (fun x y hh => ⟨hh.1, ?_⟩) (fun _ _ h => h)
  rw [h.args 3 (by decide), h.challengeNat, h.scalarNat]
  exact hh.2

end VG.Proof.Ed25519.X86

end

end

/-! Merged from `Proof.Ed25519.X86.VerifyMain`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verificationScalar_num {s : State} (hp : VerifyPre s) :
    verificationScalar s = fe s.mem (arg s 1 + 32) 0 := by
  rw [verificationScalar, ← addr_zero (arg s 1 + BitVec.ofNat 32 32)]
  exact decode_words s.mem 8 (by have := hp.scalar.fit; omega_using [this])

private theorem verification_order (pk sig ch : List Byte)
    (hp : pk.length = 32) (hs : sig.length = 64) (hc : ch.length = 64) :
    Spec.Ed25519.verifyEquation pk sig ch =
      (decide (Spec.Ed25519.decodeLE (sig.drop 32) < Spec.Ed25519.L) &&
        (match Spec.Ed25519.decodePoint pk with
        | none => false
        | some a => match Spec.Ed25519.decodePoint (sig.take 32) with
          | none => false
          | some r => Spec.Ed25519.pointEqual
            (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (sig.drop 32)) Spec.Ed25519.basePoint)
            (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE ch) a)))) := by
  rw [Spec.Ed25519.verifyEquation, hp, hs, hc]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  cases Spec.Ed25519.decodePoint pk <;> cases Spec.Ed25519.decodePoint (sig.take 32) <;>
    simp only [Bool.and_false]

theorem verifyEquation_result {s : State} (hp : VerifyPre s) :
    Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64)
      (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 64) =
      (decide (verificationScalar s < Spec.Ed25519.L) && decodeResult s) := by
  have address : (arg s 1 + BitVec.ofNat 32 32).setWidth 64 = (arg s 1).setWidth 64 + BitVec.ofNat 64 32 :=
    addr_eq (by have hf := hp.signature_fit; omega_using [hf])
  rw [verification_order _ _ _
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    (by simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]),
    signatureBytes_take, signatureBytes_drop, ← address]
  have zero (i : Nat) : arg s i + BitVec.ofNat 32 0 = arg s i := BitVec.add_zero _
  simp only [decodeResult, decodeRResult, inputPoint, equationResult, verificationScalar,
    verificationChallenge, zero]
  cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32) <;>
    cases Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) <;> rfl

theorem verifyBody_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s)
    (hy : s.syms = s₀.syms) :
    WP isa (.seq (.block verifyScalar) (.ite .e verifyDecode recoverInvalid)) s fun t =>
      Saved s₀ (arg s₀ 3) t ∧ t.gpr .eax = signWord
        (decide (verificationScalar s₀ < Spec.Ed25519.L) && decodeResult s₀) := by
  refine WP.seq (WP.mono_syms (verifyScalar_ok hp.scratch hp.scalar hs) fun a ⟨ha, za⟩ ya => ?_)
  rw [← verificationScalar_num hp] at za
  apply WP.ite (decide (verificationScalar s₀ < Spec.Ed25519.L)) za
  · intro hh
    refine WP.mono (verifyDecode_ok hp ha (ya.trans hy)) fun t ⟨ht, vt⟩ => ⟨ht, ?_⟩
    rw [hh, Bool.true_and]
    exact vt
  · intro hh
    refine WP.mono (recoverInvalid_ok a (arg s₀ 3)) fun t ⟨kt, rt⟩ => ?_
    exact ⟨ha.ikeep hp.scratch.fit (IKeep.of_field kt), by rw [hh, Bool.false_and]; exact rt⟩

theorem verify_correct {s : State} (h : verifyLocal.pre s) :
    WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  have hp := verify_pre h
  refine WP.seq (WP.mono_syms (abiSave_ok hp.scratch) fun a ha ya => ?_)
  refine WP.seq (WP.mono (verifyBody_ok hp ha ya) fun b ⟨hb, vb⟩ => ?_)
  refine WP.mono (verifyFinish_ok hp.scratch hb) fun t ⟨abi_t, vt, _⟩ => ⟨abi_t, ?_⟩
  change t.gpr .eax = _
  rw [vt, vb, verifyEquation_result hp]

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.VerifyCT`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyCTDecode`. -/
section
/-! Merged from `Proof.Ed25519.X86.DecodedThenCT`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyCTDecodeInput`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem VerifyCTFacts.inputBytes {s t : State} (h : VerifyCTFacts s t) {k : Nat} (hk : k < 2) :
    Spec.Ed25519.bytesAt s.mem ((arg s k + BitVec.ofNat 32 0).setWidth 64) 32 =
      Spec.Ed25519.bytesAt t.mem ((arg t k + BitVec.ofNat 32 0).setWidth 64) 32 := by
  rcases (by omega_using [hk] : k = 0 ∨ k = 1) with rfl | rfl
  exacts [h.pkBytes, h.rBytes]

theorem VerifyPre.input {s : State} (hp : VerifyPre s) {k : Nat} (hk : k < 2) :
    SlicePre s 3 (arg s k + BitVec.ofNat 32 0) 32 := by
  rcases (by omega_using [hk] : k = 0 ∨ k = 1) with rfl | rfl
  exacts [hp.pk, hp.r]

theorem VerifyCTFacts.inputA {s t : State} (h : VerifyCTFacts s t) : inputPoint s 0 = inputPoint t 0 :=
  congrArg Spec.Ed25519.decodePoint h.pkBytes

theorem VerifyCTFacts.inputR {s t : State} (h : VerifyCTFacts s t) : inputPoint s 1 = inputPoint t 1 :=
  congrArg Spec.Ed25519.decodePoint h.rBytes

theorem VerifyCTFacts.decOk {s t : State} (h : VerifyCTFacts s t) : decOk s 2 = decOk t 2 := by
  rw [decOk_two, decOk_two, h.inputA, h.inputR]

/-! ## Constant time of the decodings' loop -/

theorem VerifyCTFacts.edi {s₀ t₀ x y : State} (h : VerifyCTFacts s₀ t₀) (hx : Saved s₀ (arg s₀ 3) x)
    (hy : Saved t₀ (arg t₀ 3) y) : x.gpr .edi = y.gpr .edi :=
  hx.edi.trans ((h.args 3 (by decide)).trans hy.edi.symm)

theorem decodeStart_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (VerifySaved s₀ t₀) (.block decodeStart) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esp]) _ (by native_taint_decide)
  intro s t hp
  apply regsTaint_agree
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.edi hp.1 hp.2
  · exact hp.1.esp.trans (h.pub.1.trans hp.2.esp.symm)

/-- After the copy of the input `k`: its number in slot 3. -/
def LoadedAt (u : State) (k : Nat) (x : State) : Prop :=
  Saved u (arg u 3) x ∧ fe x.mem (arg u 3) 96 = Spec.Ed25519.decodeLE
      (Spec.Ed25519.bytesAt u.mem ((arg u k + BitVec.ofNat 32 0).setWidth 64) 32) ∧
    wd x.mem (arg u 3) DTAB = BitVec.ofNat 32 (7680 + 128 * k)

/-- After its decoding. -/
def DecodedAt (u : State) (k : Nat) (x : State) : Prop :=
  Saved u (arg u 3) x ∧ wd x.mem (arg u 3) DTAB = BitVec.ofNat 32 (7680 + 128 * k)

theorem decodeLoad_at {u x : State} (hu : VerifyPre u) {k : Nat} (hk : k < 2) (hx : DecAt u k x) :
    WP isa (.block decodeLoad) x (LoadedAt u k) := by
  have hi := hu.input hk
  refine WP.mono (decodeLoad_ok hu hi hx.saved (hx.ptr hk)) fun t ⟨ht, wt, ft⟩ => ⟨ht, ?_, ?_⟩
  · rw [← addr_zero (arg u k + BitVec.ofNat 32 0), decode_words u.mem 8 (by have := hi.fit; omega_using [this])]
    apply num_congr
    intro j hj
    simp only [Nat.zero_add]
    exact congrArg BitVec.toNat (wt j hj)
  · rw [wd_frame1 ft hu.scratch.fit (by decide) (by decide) (Or.inr (by decide))]
    exact hx.tab

theorem pointDecode_at {u x : State} (hu : VerifyPre u) {k : Nat} (hx : LoadedAt u k x) :
    WP isa pointDecode x (DecodedAt u k) := by
  have cx := hx.1.ctx hu.scratch.fit hu.scratch.wr hu.scratch.stk
  refine WP.mono (pointDecode_ok cx) fun t ht => ?_
  refine ⟨hx.1.mulkeep hu.scratch.fit ht.1, ?_⟩
  rw [wd_frame1s cx ht.1.frame (by decide) (by decide) (Or.inr (by decide))]
  exact hx.2.2

theorem decodeLoad_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {k : Nat} (hk : k < 2) :
    RelCT isa (fun x y => DecAt s₀ k x ∧ DecAt t₀ k y) (.block decodeLoad) (fun _ _ => True) := by
  have hc : RelCT isa (fun x y => DecAt s₀ k x ∧ DecAt t₀ k y)
      (.block [.mov .esi (.mem (Impl.X25519.X86.sc DPTR))]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
    intro x y hp
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h.edi hp.1.saved hp.2.saved)
  have hw (u x : State) (hu : VerifyPre u) (hx : DecAt u k x) :
      WP isa (.block [.mov .esi (.mem (Impl.X25519.X86.sc DPTR))]) x fun z =>
        z.gpr .edi = arg u 3 ∧ z.gpr .esi = arg u k :=
    loadWd_ok hu hx.saved (d := DPTR) (by decide) .esi (by decide) fun z hz ez _ _ =>
      WP.block_nil ⟨hz.edi, ez.trans (hx.ptr hk)⟩
  have hh := ctWithRuns hc (fun x y hp => ⟨hw s₀ x (verify_pre h.left) hp.1, hw t₀ y (verify_pre h.right) hp.2⟩)
  have hl : RelCT isa (fun x y => DecAt s₀ k x ∧ DecAt t₀ k y)
      (.block [.mov .esi (.mem (Impl.X25519.X86.sc DPTR))])
      (fun x y => x.gpr .edi = y.gpr .edi ∧ x.gpr .esi = y.gpr .esi) :=
    hh.mono (fun _ _ h => h) fun (x y : State) ⟨_, _, _, _, hx, hy⟩ =>
      ⟨hx.1.trans ((h.args 3 (by decide)).trans hy.1.symm), hx.2.trans ((h.args k (by omega_using [hk])).trans hy.2.symm)⟩
  show RelCT isa _ (.block ([.mov .esi (.mem (Impl.X25519.X86.sc DPTR))] ++ copyWords 96 8)) _
  exact ctBlockAppend hl copyWords96_ct

theorem decodeNext1_ok {u x : State} (hu : VerifyPre u) {k : Nat} (hx : DecodedAt u k x) :
    WP isa (.block ([.mov .ecx (.reg .eax), .mov .edx (.mem (Impl.X25519.X86.sc DTAB)),
      .alu .add .edx (.reg .edi)] : List Instr)) x fun t =>
      t.gpr .edi = arg u 3 ∧ t.gpr .edx = arg u 3 + BitVec.ofNat 32 (7680 + 128 * k) := by
  refine Wp.wp_mov fun u1 h1 => ?_
  have hs1 := hx.1.upd h1
  refine loadWd_ok hu hs1 (d := DTAB) (by decide) .edx (by decide) fun u2 hs2 e2 g2 _ => ?_
  refine Wp.wp_add fun u3 h3 _ => WP.block_nil ⟨(hs2.upd h3).edi, ?_⟩
  rw [h3.gpr, e2, h1.mem, hx.2, hs2.edi, BitVec.add_comm]

theorem decodeNext_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {k : Nat} :
    RelCT isa (fun x y => DecodedAt s₀ k x ∧ DecodedAt t₀ k y) (.block decodeNext) (fun _ _ => True) := by
  rw [decodeNext_eq]
  have hc : RelCT isa (fun x y => DecodedAt s₀ k x ∧ DecodedAt t₀ k y)
      (.block ([.mov .ecx (.reg .eax), .mov .edx (.mem (Impl.X25519.X86.sc DTAB)),
        .alu .add .edx (.reg .edi)] : List Instr)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
    intro x y hp
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h.edi hp.1.1 hp.2.1)
  have hh := ctWithRuns hc (fun x y hp => ⟨decodeNext1_ok (verify_pre h.left) hp.1,
    decodeNext1_ok (verify_pre h.right) hp.2⟩)
  have h1 : RelCT isa (fun x y => DecodedAt s₀ k x ∧ DecodedAt t₀ k y)
      (.block ([.mov .ecx (.reg .eax), .mov .edx (.mem (Impl.X25519.X86.sc DTAB)),
        .alu .add .edx (.reg .edi)] : List Instr))
      (fun x y => x.gpr .edi = y.gpr .edi ∧ x.gpr .edx = y.gpr .edx) :=
    hh.mono (fun _ _ h => h) fun (x y : State) ⟨_, _, _, _, hx, hy⟩ =>
      ⟨by rw [hx.1, hy.1, h.args 3 (by decide)], by rw [hx.2, hy.2, h.args 3 (by decide)]⟩
  refine ctBlockAppend h1 ?_
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .edx]) _ (by native_taint_decide)
  intro x y hp
  apply regsTaint_agree
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [hp.1, hp.2]

theorem decodeBody_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) {k : Nat} (hk : k < 2) :
    RelCT isa (fun x y => DecAt s₀ k x ∧ DecAt t₀ k y) decodeBody (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  have hb := h.inputBytes hk
  rw [decodeBody]
  refine seq_runs (decodeLoad_ct h hk) (fun x hx => decodeLoad_at ps hk hx) (fun y hy => decodeLoad_at pt hk hy) ?_
  refine seq_runs ?_ (fun x hx => pointDecode_at ps hx) (fun y hy => pointDecode_at pt hy) (decodeNext_ct h)
  refine (pointDecode_ct (arg s₀ 3) (s₀.gpr .esp) s₀.wr (Spec.Ed25519.decodeLE
    (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ k + BitVec.ofNat 32 0).setWidth 64) 32))).mono ?_ (fun _ _ h => h)
  intro x y ⟨hx, hy⟩
  have e3 := h.args 3 (by decide)
  have cy := verify_pointCTCtx h.right hy.1
  rw [← e3] at cy
  refine ⟨⟨⟨verify_pointCTCtx h.left hx.1, hx.1.esp, hx.1.wr⟩, hx.2.1⟩,
    ⟨⟨cy, hy.1.esp.trans h.pub.1.symm, hy.1.wr.trans ?_⟩, ?_⟩⟩
  · rw [h.right.2.1, h.left.2.1, e3]
  · rw [e3, hy.2.1, hb]

theorem decodeLoop_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (fun x y => DecAt s₀ 0 x ∧ DecAt t₀ 0 y) (.loop decodeBody .ne)
      (fun x y => DecAt s₀ 2 x ∧ DecAt t₀ 2 y) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  refine (VG.RelCT.loop (I := fun m x y => ∃ k, k + m = 2 ∧ k < 2 ∧ DecAt s₀ k x ∧ DecAt t₀ k y) ?_ 2).mono
    (fun x y hh => ⟨0, rfl, by decide, hh.1, hh.2⟩) (fun _ _ h => h)
  intro m
  have step (k : Nat) (hk : k < 2) := ((decodeBody_ct h hk).wp fun x y hh =>
    ⟨decodeBody_ok ps hk hh.1, decodeBody_ok pt hk hh.2⟩)
  rcases m with _ | _ | _ | m
  · exact VG.RelCT.of_false fun _ _ ⟨k, hkm, hk, _⟩ => by omega_using [hkm, hk]
  · refine ((step 1 (by decide)).mono (fun x y ⟨k, hkm, _, hx, hy⟩ => by
      obtain rfl : k = 1 := by omega_using [hkm]
      exact ⟨hx, hy⟩) (fun _ _ h => h)).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨hx, zx⟩, ⟨hy, zy⟩⟩
    refine ⟨?_, fun _ => ⟨hx, hy⟩, fun he => ?_⟩
    · show x.zf.map (!·) = y.zf.map (!·); rw [zx, zy]
    · have : x.zf.map (!·) = some true := he
      rw [zx] at this; cases this
  · refine ((step 0 (by decide)).mono (fun x y ⟨k, hkm, _, hx, hy⟩ => by
      obtain rfl : k = 0 := by omega_using [hkm]
      exact ⟨hx, hy⟩) (fun _ _ h => h)).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨hx, zx⟩, ⟨hy, zy⟩⟩
    refine ⟨?_, fun he => ?_, fun _ => ⟨1, by omega_using [], 1, rfl, by decide, hx, hy⟩⟩
    · show x.zf.map (!·) = y.zf.map (!·); rw [zx, zy]
    · have : x.zf.map (!·) = some false := he
      rw [zx] at this; cases this
  · exact VG.RelCT.of_false fun _ _ ⟨k, hkm, hk, _⟩ => by omega_using [hkm]

/-- The test of `DOK`. -/
theorem okTest_ok {u x : State} (hu : VerifyPre u) (hx : DecAt u 2 x) :
    WP isa (.block [.mov .eax (.mem (Impl.X25519.X86.sc DOK)), .alu .test .eax (.reg .eax)]) x fun t =>
      Saved u (arg u 3) t ∧ t.mem = x.mem ∧ t.zf.map (!·) = some (decOk u 2) :=
  loadWd_ok hu hx.saved (d := DOK) (by decide) .eax (by decide) fun b hb eb _ mb =>
    Wp.wp_test fun c hc zc => WP.block_nil ⟨⟨by rw [hc.gpr]; exact hb.edi, by rw [hc.gpr]; exact hb.esp,
      hc.rd.trans hb.rd, hc.wr.trans hb.wr, by rw [hc.mem]; exact hb.frame, by rw [hc.mem]; exact hb.saved, hb.stk⟩,
      hc.mem.trans mb, by rw [zc, eb, hx.ok, BitVec.and_self]; cases decOk u 2 <;> rfl⟩

/-- Runs keep their statics' addresses: a relational fact carries them. -/
theorem relCT_syms {P Q : State → State → Prop} {c : Prog isa} (h : RelCT isa P c Q)
    (A B : String → BitVec 32) :
    RelCT isa (fun x y => P x y ∧ x.syms = A ∧ y.syms = B) c
      (fun x y => Q x y ∧ x.syms = A ∧ y.syms = B) :=
  fun _ _ _ _ _ _ hp e₁ e₂ =>
    let ⟨ht, hq⟩ := h _ _ _ _ _ _ hp.1 e₁ e₂
    ⟨ht, hq, (VG.X86.Exec.syms e₁).trans hp.2.1, (VG.X86.Exec.syms e₂).trans hp.2.2⟩

theorem verifyDecode_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (fun x y => VerifySaved s₀ t₀ x y ∧ x.syms = s₀.syms ∧ y.syms = t₀.syms) verifyDecode
      (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  rw [verifyDecode, decodeBoth]
  refine VG.RelCT.seq (M := isa)
    (R := fun (x y : State) => (DecAt s₀ 2 x ∧ x.syms = s₀.syms) ∧ (DecAt t₀ 2 y ∧ y.syms = t₀.syms)) ?_ ?_
  · exact (relCT_syms (seq_runs (decodeStart_ct h) (fun x hx => decodeStart_ok ps hx)
      (fun y hy => decodeStart_ok pt hy) (decodeLoop_ct h)) s₀.syms t₀.syms).mono (fun _ _ hh => hh)
      fun _ _ hh => ⟨⟨hh.1.1, hh.2.1⟩, hh.1.2, hh.2.2⟩
  have ht : RelCT isa (fun x y => (DecAt s₀ 2 x ∧ x.syms = s₀.syms) ∧ (DecAt t₀ 2 y ∧ y.syms = t₀.syms))
      (.block [.mov .eax (.mem (Impl.X25519.X86.sc DOK)), .alu .test .eax (.reg .eax)]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by native_taint_decide)
    intro x y hp
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h.edi hp.1.1.saved hp.2.1.saved)
  refine seq_runs ht (F₁ := fun t => ∃ x, DecAt s₀ 2 x ∧ Saved s₀ (arg s₀ 3) t ∧ t.mem = x.mem ∧
      t.zf.map (!·) = some (decOk s₀ 2) ∧ t.syms = s₀.syms)
    (F₂ := fun t => ∃ y, DecAt t₀ 2 y ∧ Saved t₀ (arg t₀ 3) t ∧ t.mem = y.mem ∧
      t.zf.map (!·) = some (decOk t₀ 2) ∧ t.syms = t₀.syms)
    (fun x hx => WP.mono_syms (okTest_ok ps hx.1) fun t ⟨a, b, c⟩ yt => ⟨x, hx.1, a, b, c, yt.trans hx.2⟩)
    (fun y hy => WP.mono_syms (okTest_ok pt hy.1) fun t ⟨a, b, c⟩ yt => ⟨y, hy.1, a, b, c, yt.trans hy.2⟩) ?_
  refine VG.RelCT.ite (M := isa) ?_ ?_ ?_
  · intro x y ⟨⟨_, _, _, _, zx, _⟩, ⟨_, _, _, _, zy, _⟩⟩
    show x.zf.map (!·) = y.zf.map (!·)
    rw [zx, zy, h.decOk]
  · cases ha : inputPoint s₀ 0 with
    | none =>
      exact VG.RelCT.of_false fun x y hh => by
        obtain ⟨⟨_, _, _, _, zx, _⟩, _⟩ := hh.1
        have e := hh.2
        change x.zf.map (!·) = some true at e
        rw [zx, decOk_two, ha] at e; cases e
    | some a =>
      cases hr : inputPoint s₀ 1 with
      | none =>
        exact VG.RelCT.of_false fun x y hh => by
          obtain ⟨⟨_, _, _, _, zx, _⟩, _⟩ := hh.1
          have e := hh.2
          change x.zf.map (!·) = some true at e
          rw [zx, decOk_two, ha, hr] at e; cases e
      | some r =>
        obtain ⟨Aa, hAa⟩ := VG.Proof.Ed25519.decodePoint_rep ha
        obtain ⟨Ra, hRa⟩ := VG.Proof.Ed25519.decodePoint_rep hr
        refine (verifyEquationPoints_ct h a r hAa hRa).mono ?_ (fun _ _ h => h)
        intro x y ⟨⟨⟨x', hx', sx, mx, _, yx⟩, ⟨y', hy', sy, my, _, yy⟩⟩, _⟩
        refine ⟨⟨sx, by rw [mx]; exact hx'.pts 0 (by decide) a ha, by rw [mx]; exact hx'.pts 1 (by decide) r hr,
            yx⟩,
          ⟨sy, by rw [my]; exact hy'.pts 0 (by decide) a (h.inputA ▸ ha),
            by rw [my]; exact hy'.pts 1 (by decide) r (h.inputR ▸ hr), yy⟩⟩
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86
end
end
end

/-! Merged from `Proof.Ed25519.X86.VerifyCTSetup`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def verifyEntryTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 20 }

theorem verifyEntryTaint_wf {s : State} (h : verifyLocal.pre s) : VG.X86.Taint.Wf verifyEntryTaint s := by
  have hp := (verify_pre h).scratch
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (by cases h),
    fun _ h => (by cases h), fun _ => ⟨?_, ?_⟩, fun _ h => (by cases h)⟩
  · exact hp.sp_fit
  · intro r hr
    rw [h.2.1] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro a _ ha
      change _ + 1 ≤ 0 at ha
      omega_using [ha]
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.sp_fit; omega_using [this]) hp.ret_sc hp.args_sc

theorem verifyEntryTaint_agree {s t : State} (h : VerifyCTFacts s t) : VG.X86.Taint.Agree verifyEntryTaint s t := by
  refine ⟨⟨?_, fun h => (by cases h)⟩, fun h => absurd rfl h,
    verifyEntryTaint_wf h.left, verifyEntryTaint_wf h.right,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => h.pub.1, ?_⟩
  · intro r hr
    simp only [verifyEntryTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r
    exact h.pub.1
  · intro k h4 hk
    change k < 20 at hk
    rw [show VG.X86.Taint.depth verifyEntryTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (verify_pre h.left).scratch.sp_fit h4 hk,
      VG.X86.Taint.argByte_eq (verify_pre h.right).scratch.sp_fit h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (h.args ((k - 4) / 4) (by omega_using [hk, h4]))

theorem verifyStart_ct : RelCT isa
    (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
    (.block (abiSave 3)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) verifyEntryTaint _ (by native_taint_decide)
  exact fun _ _ h => verifyEntryTaint_agree ⟨h.1, h.2.1, h.2.2⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem verifyBody_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (fun x y => VerifySaved s₀ t₀ x y ∧ x.syms = s₀.syms ∧ y.syms = t₀.syms)
      (.seq (.block verifyScalar) (.ite .e verifyDecode recoverInvalid)) (fun _ _ => True) := by
  have ps := verify_pre h.left
  have pt := verify_pre h.right
  have hs0 : RelCT isa (fun x y => VerifySaved s₀ t₀ x y ∧ x.syms = s₀.syms ∧ y.syms = t₀.syms)
      (.block verifyScalar) (fun _ _ => True) :=
    (verifyScalar_ct h).mono (fun _ _ hp => hp.1) (fun _ _ h => h)
  have hh := hs0.wp
    (F₁ := fun (t : State) => (Saved s₀ (arg s₀ 3) t ∧
      t.zf = some (decide (fe s₀.mem (arg s₀ 1 + 32) 0 < Spec.Ed25519.L))) ∧ t.syms = s₀.syms)
    (F₂ := fun (t : State) => (Saved t₀ (arg t₀ 3) t ∧
      t.zf = some (decide (fe t₀.mem (arg t₀ 1 + 32) 0 < Spec.Ed25519.L))) ∧ t.syms = t₀.syms)
    (fun _ _ hp =>
    ⟨WP.mono_syms (verifyScalar_ok ps.scratch ps.scalar hp.1.1) fun _ ht yt => ⟨ht, yt.trans hp.2.1⟩,
      WP.mono_syms (verifyScalar_ok pt.scratch pt.scalar hp.1.2) fun _ ht yt => ⟨ht, yt.trans hp.2.2⟩⟩)
  refine VG.RelCT.seq hh (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t hp
    change s.zf = t.zf
    rw [hp.2.1.1.2, hp.2.2.1.2, h.scalarFe]
  · exact (verifyDecode_ct h).mono (fun _ _ hp => ⟨⟨hp.1.2.1.1.1, hp.1.2.2.1.1⟩, hp.1.2.1.2, hp.1.2.2.2⟩)
      (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem verifyTail_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (fun x y => VerifySaved s₀ t₀ x y ∧ x.syms = s₀.syms ∧ y.syms = t₀.syms)
      (.seq (.seq (.block verifyScalar) (.ite .e verifyDecode recoverInvalid)) (.block verifyFinish))
      (fun _ _ => True) := by
  have hh := (verifyBody_ct h).wp (fun _ _ hp =>
    ⟨verifyBody_ok (verify_pre h.left) hp.1.1 hp.2.1, verifyBody_ok (verify_pre h.right) hp.1.2 hp.2.2⟩)
  refine VG.RelCT.seq (hh.mono (fun _ _ h => h) ?_) verifyFinish_ct
  intro s t hp
  exact hp.2.1.1.edi.trans ((h.args 3 (by decide)).trans hp.2.2.1.edi.symm)

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  have start := ctWithRuns verifyStart_ct (F₁ := fun u x => Saved u (arg u 3) x ∧ x.syms = u.syms)
    (F₂ := fun u x => Saved u (arg u 3) x ∧ x.syms = u.syms) (fun _ _ h =>
    ⟨WP.mono_syms (abiSave_ok (verify_pre h.1).scratch) fun _ ha ya => ⟨ha, ya⟩,
      WP.mono_syms (abiSave_ok (verify_pre h.2.1).scratch) fun _ ha ya => ⟨ha, ya⟩⟩)
  rw [verifyEquation]
  refine VG.RelCT.seq start ?_
  intro s t ts tt s' t' ⟨_, u, v, hp, hu, hv⟩ es et
  exact verifyTail_ct ⟨hp.1, hp.2.1, hp.2.2⟩ _ _ _ _ _ _ ⟨⟨hu.1, hv.1⟩, hu.2, hv.2⟩ es et

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.VerifyNarrow`. -/

/-! Transfer the verifier from its framed local contract to the reviewed ABI. -/

end

end

/-! ### `Ed25519.X86.VerifyMessage.Args`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Layout`. -/

@[expose] public section

section
/-! Buffer geometry of complete Ed25519 verification on x86. -/
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86

structure Lay where
  pk : BitVec 32
  msg : BitVec 32
  len : BitVec 32
  sig : BitVec 32
  scr : BitVec 32
  E : BitVec 32
  /-- The address of the static of `-[1]B … -[15]B`, which the equation reads. -/
  tbl : BitVec 32

namespace Lay
variable (L : Lay)
abbrev PK : Region := ⟨L.pk.setWidth 64, 32⟩
abbrev MSG : Region := ⟨L.msg.setWidth 64, L.len.toNat⟩
abbrev SIG : Region := ⟨L.sig.setWidth 64, 64⟩
abbrev SCR : Region := ⟨L.scr.setWidth 64, 8192⟩
abbrev ARGS : Region := ⟨L.E.setWidth 64 + 260, 20⟩
abbrev RET : Region := ⟨L.E.setWidth 64 + 256, 4⟩
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := Whole.STK L.E
abbrev TBL : Region := ⟨L.tbl.setWidth 64, 1920⟩
def inputs : List Region := [L.PK, L.MSG, L.SIG, L.ARGS, L.TBL]
def outputs : List Region := [L.SCR]
def value (j : Nat) : BitVec 32 :=
  match j with | 0 => L.pk | 1 => L.msg | 2 => L.len | 3 => L.sig | _ => L.scr

structure Ok : Prop where
  below : 24 ≤ L.E.toNat
  top : L.E.toNat + 280 ≤ 2 ^ 32
  sc : ∀ r ∈ L.inputs, r.Disjoint L.SCR
  ks : ∀ r ∈ L.inputs, L.STK.Disjoint r
  rs : ∀ r ∈ L.inputs, L.RET.Disjoint r
  kc : L.STK.Disjoint L.SCR
  rc : L.RET.Disjoint L.SCR
  np : L.pk.toNat + 32 ≤ 2 ^ 32
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 32
  ns : L.sig.toNat + 64 ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
  nt : L.tbl.toNat + 1920 ≤ 2 ^ 32
end Lay

abbrev Ctx (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

namespace Ctx
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem input_bytes (hc : Ctx L g m₀ t) (hL : L.Ok)
    {r : Region} (hr : r ∈ L.inputs) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.mem r.base r.len = Spec.Ed25519.bytesAt m₀ r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine Frame.bytes hc.frame ?_ hn (List.mem_range.mp hi)
  intro R hR
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl
  · exact hL.sc r hr
  · exact (hL.ks r hr).symm

theorem arg_word (hc : Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 5) :
    t.mem.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 =
      m₀.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 := by
  refine hc.frame.readW (r := L.ARGS) ?_ ?_ (by decide)
  · exact Offset.contains _ (e := 260) (k := 20) (by omega_using []) (by omega_using [hj]) (by decide)
  · intro R hR
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hR
    obtain ha : L.ARGS ∈ L.inputs := by simp [Lay.inputs]
    rcases hR with rfl | rfl
    · exact hL.sc _ ha
    · exact (hL.ks _ ha).symm

end Ctx
end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

def Arguments (L : Lay) (m : Mem) : Prop :=
  ∀ j < 5, m.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 = L.value j

def value (L : Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

def OutArgs (L : Lay) (vs : List Value) (s : State) : Prop :=
  ∀ j (hj : j < vs.length), s.mem.readW (addr L.E (4 * j)) 32 = value L (vs[j]'hj)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem Ctx.value (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {v : Value} (hv : Whole.valid 5 v) : Whole.value L.E s.mem v = value L v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    change j < 5 at hv
    simp only [Whole.value, VerifyMessage.value]
    rw [addr_eq (by have := hL.top; omega_using [hv, this]), hc.arg_word hL hv, ha j hv]

theorem args_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {vs : List Value} (hlen : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 5 v) :
    WP isa (.block (setup 0 vs)) s fun t => Ctx L g m₀ t ∧
      Frame [⟨L.E.setWidth 64, 24⟩] s.mem t.mem ∧ OutArgs L vs t := by
  refine WP.mono (Whole.Ctx.setup hc (by simpa using hL.top) ?_ (by omega_using [hlen]) hv)
    fun t ⟨ht, hf, hvals⟩ => ⟨ht, hf, fun j hj => ?_⟩
  · intro j hj
    refine ⟨L.ARGS, ?_, ?_⟩
    · rw [hc.rd]; exact List.mem_append_left _ (by simp [Lay.inputs])
    · rw [addr_eq (by have := hL.top; omega_using [hj, this])]
      exact Offset.contains _ (e := 260) (k := 20) (by omega_using []) (by omega_using [hj]) (by decide)
  · simpa only [Nat.zero_add, hc.value hL ha (hv _ (List.getElem_mem _))] using hvals j hj

end VG.Proof.Ed25519.X86.VerifyMessage

end

end


/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Hash`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.PublicKey (callWith)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashSpace (h : L.Ok) : Whole.HashSpace L.E L.scr :=
  ⟨h.below, by have := h.top; omega_using [this], h.nc, h.kc⟩

theorem shaWithin (L : Lay) : Whole.Within (Whole.SHA L.scr) L.SCR :=
  ⟨0, by simp, by change 0 + 192 ≤ 8192; decide⟩

theorem workWithin (h : L.Ok) : Whole.Within (Whole.WORK L.scr) L.SCR :=
  ⟨192, (hashSpace h).work_addr, by change 192 + 272 ≤ 8192; decide⟩

theorem argsWithin (L : Lay) {n : Nat} (hn : n ≤ 256) :
    Whole.Within (Whole.ARGS L.E n) L.FR := ⟨0, by simp, by simpa using hn⟩

theorem hash_covers {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R) :
    Covers rs (L.inputs ++ L.FR :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases h r hr with h | ⟨R, hR, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨R, by simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using Or.inr hR, h⟩

theorem hash_writes {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ Whole.Within r L.SCR) :
    ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rcases h r hr with h | h
  · exact .inl h
  · exact .inr ⟨_, by simp [Lay.outputs], h⟩

theorem scratch_covered {r : Region} (h : Whole.Within r L.SCR) :
    Whole.Within r L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  .inr ⟨_, by simp [Lay.outputs], h⟩

def hashWrites (L : Lay) : List Region :=
  [L.SCR, ⟨L.E.setWidth 64, 24⟩, below L.E 24, ⟨L.E.setWidth 64 + 192, 64⟩]

theorem setup_frame {m m' : Mem} (h : Frame [⟨L.E.setWidth 64, 24⟩] m m') : Frame (hashWrites L) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp [hashWrites], fun _ h => h⟩

theorem hash_frame {m m' : Mem} {wr : List Region}
    (h : Frame (wr ++ [below L.E 24]) m m')
    (hw : ∀ r ∈ wr, Whole.Within r L.SCR ∨ Whole.Within r ⟨L.E.setWidth 64 + 192, 64⟩) :
    Frame (hashWrites L) m m' := by
  refine h.sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with h | h
    · exact ⟨_, by simp [hashWrites], h.sub⟩
    · exact ⟨_, by simp [hashWrites], h.sub⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp [hashWrites], fun _ h => h⟩

theorem setup_repr (hL : L.Ok) {u : State}
    (hf : Frame [⟨L.E.setWidth 64, 24⟩] s.mem u.mem) {msg : List Byte}
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (L.scr.setWidth 64) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := s.mem) ?_ hr
  intro i hi
  exact hf.bytes (R := Whole.SHA L.scr) (by
    rintro r hr; rw [List.mem_singleton.mp hr]
    exact ((hashSpace hL).args_sha (n := 24) (by decide)).symm) (by change 192 ≤ 2 ^ 64; decide) hi

theorem OutArgs.slot {vs : List Value} {t : State} (h : OutArgs L vs t) (hL : L.Ok)
    {j : Nat} (hj : j < vs.length) (hlen : vs.length ≤ 6) :
    Whole.slots L.E t j = value L (vs[j]'hj) := by
  obtain e := h j hj
  rw [addr_eq (by have := hL.top; omega_using [hj, hlen, this])] at e
  exact e

theorem init_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa Impl.Ed25519.X86.VerifyMessage.init s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64) [] := by
  refine WP.seq (WP.mono (args_ok hc hL ha (vs := [.caller 4 0]) (by decide) (Whole.valid_all (by decide)))
    fun u ⟨hu, hf, hs⟩ => ?_)
  obtain a0 : Whole.slots L.E u 0 = L.scr := by
    obtain hh := hs.slot hL (j := 0) (by decide) (by decide)
    change Whole.slots L.E u 0 = L.scr + BitVec.ofNat 32 0 at hh
    simpa only [BitVec.add_zero] using hh
  obtain H := hashSpace hL
  obtain cov := hash_covers (L := L) (rs := Whole.initRd L.E ++ Whole.initWr L.scr) (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L))
  obtain ws := hash_writes (L := L) (rs := Whole.initWr L.scr) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (shaWithin L))
  refine WP.mono (Whole.init_call hu H.below (Whole.init_pre hu.esp H a0) cov ws
    ((Whole.call_arg hu.esp H.below H.frameFit (by decide)).trans a0)) fun t ⟨ht, hft, hr⟩ =>
    ⟨ht, (setup_frame hf).trans (hash_frame hft ?_), hr⟩
  intro r hr; rw [List.mem_singleton.mp hr]; exact .inl (shaWithin L)

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Equation`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def challenge (L : Lay) : Region := ⟨(L.E + 128).setWidth 64, 64⟩
def equationRd (L : Lay) : List Region := [L.PK, L.SIG, challenge L, ⟨L.E.setWidth 64, 16⟩, L.TBL]
def equationWr (L : Lay) : List Region := [⟨L.scr.setWidth 64, 0⟩, L.SCR]
def EqArgs (L : Lay) (s : State) : Prop := Whole.slots L.E s 0 = L.pk ∧
  Whole.slots L.E s 1 = L.sig ∧ Whole.slots L.E s 2 = L.E + 128 ∧ Whole.slots L.E s 3 = L.scr

theorem equation_nosp : NoSp verifyEquation := NoSp.of_all (by lit_decide)
theorem equation_stack : stackUse verifyEquation = 8 := by lit_decide

theorem challengeWithin (hL : L.Ok) : Whole.Within (challenge L) L.FR :=
  ⟨128, Whole.frame_addr (hashSpace hL).frameFit (by decide), by change 128 + 64 ≤ 256; decide⟩

/-- The static of `-[1]B … -[15]B` at `L.tbl` in `m`. -/
def TblAt (L : Lay) (m : Mem) : Prop :=
  ∀ i < 240, m.readW (L.tbl.setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0

/-- The static survives what the function writes. -/
theorem Ctx.tbl (hc : Ctx L g m₀ s) (hL : L.Ok) (ht : TblAt L m₀) : TblAt L s.mem := fun i hi => by
  obtain tin : L.TBL ∈ L.inputs := by simp [Lay.inputs]
  obtain hcon : L.TBL.Contains (L.tbl.setWidth 64 + BitVec.ofNat 64 (8 * i)) (64 / 8) :=
    Offset.contains_base _ (d := 8 * i) (n := 8) (k := 1920) (by omega_using [hi]) (by have := hL.nt; omega_using [hi])
  rw [hc.frame.readW hcon (fun R hR => by
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hR
    rcases hR with rfl | rfl
    · exact hL.sc _ tin
    · exact (hL.ks _ tin).symm) (by decide)]
  exact ht i hi

/-- The static, as the equation's contract states it at its call. -/
theorem equation_tbl (hc : Ctx L g m₀ s) (hL : L.Ok) (ht : TblAt L s.mem) (hy : s.syms bSym = L.tbl)
    (rd wr : List Region) :
    BHeld (s.callEntry.withRegions rd wr) [L.SCR, below (L.E - 4) 8] := by
  obtain tin : L.TBL ∈ L.inputs := by simp [Lay.inputs]
  have hy' : (s.callEntry.withRegions rd wr).syms bSym = L.tbl := hy
  refine ⟨fun i hi => ?_, by rw [hy']; exact hL.nt, fun r hr => ?_⟩
  · rw [hy']
    obtain hcon : L.TBL.Contains (L.tbl.setWidth 64 + BitVec.ofNat 64 (8 * i)) (64 / 8) :=
      Offset.contains_base _ (d := 8 * i) (n := 8) (k := 1920) (by omega_using [hi]) (by have := hL.nt; omega_using [hi])
    change (s.callEntry.mem).readW _ 64 = _
    rw [Frame.readW (Whole.callEntry_frame s) hcon (fun R hR => by
        rw [List.mem_singleton.mp hR, hc.esp]
        exact (hL.ks _ tin).symm.sub_right (Whole.below_sub_stack hL.below (by decide))) (by decide)]
    exact ht i hi
  · rw [hy']
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.sc _ tin
    · exact (hL.ks _ tin).symm.sub_right (Whole.inner_sub_stack hL.below)

theorem equation_pre (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : EqArgs L s) (ht : TblAt L s.mem)
    (hy : s.syms bSym = L.tbl) :
    verifyLocal.pre (s.callEntry.withRegions (equationRd L) (equationWr L)) := by
  obtain hb := equation_tbl hc hL ht hy (equationRd L) (equationWr L)
  have hy' : (s.callEntry.withRegions (equationRd L) (equationWr L)).syms bSym = L.tbl := hy
  obtain H := hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  obtain ⟨a0, a1, a2, a3⟩ := ha
  obtain e0 := (ca (j := 0) (by decide)).trans a0
  obtain e1 := (ca (j := 1) (by decide)).trans a1
  obtain e2 := (ca (j := 2) (by decide)).trans a2
  obtain e3 := (ca (j := 3) (by decide)).trans a3
  obtain ab := Whole.arg_base hc.esp (equationRd L) (equationWr L)
  obtain stk := Whole.inner_sub_stack hL.below
  obtain hf : L.E.toNat + 256 ≤ 2 ^ 32 := by have := hL.top; omega_using [this]
  obtain cs : callStk (s.callEntry.withRegions (equationRd L) (equationWr L)) =
      below (L.E - BitVec.ofNat 32 4) 8 := by
    simp only [callStk, State.withRegions_gpr, State.callEntry_esp, hc.esp]; rfl
  simp only [verifyLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, e0, e1, e2, e3, ab, cs,
    sub, addr_zero, scR, hy']
  refine ⟨rfl, rfl, hL.sc _ (by simp [Lay.inputs]), hL.sc _ (by simp [Lay.inputs]),
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((challengeWithin hL).sub p hp)),
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p (Region.sub_prefix (by decide) p hp)),
    hL.kc.sub_left (Whole.below_sub_stack hL.below (by decide)), hL.np, hL.ns,
    Whole.frame_fit H.frameFit (by decide : 128 < 256) (by decide : 128 + 64 ≤ 256), hL.nc, ?_, ?_,
    hL.kc.sub_left stk, (hL.ks _ (by simp [Lay.inputs])).sub_left stk,
    (hL.ks _ (by simp [Lay.inputs])).sub_left stk,
    Whole.inner_frame hL.below hf (d := 128) (n := 64) (by decide) (by decide), hb⟩
  all_goals
    obtain e : (L.E - 4).toNat = L.E.toNat - 4 := sub_toNat (k := 4) (by have := hL.below; omega_using [this])
    rw [e]
    have := hL.top; have := hL.below; omega_arith

theorem equation_correct_result (s : State) (h : verifyLocal.pre s) :
    ∃ tr t, Exec isa verifyEquation s tr t ∧ abiPreserved s t ∧ verifyLocal.post s t := verify_correct h

theorem equation_call (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : EqArgs L s) (ht : TblAt L m₀)
    (hy : s.syms bSym = L.tbl) :
    WP isa (.call "vg_ed25519_verify_equation" verifyEquation) s fun t => Ctx L g m₀ t ∧
      t.gpr .eax = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem (L.pk.setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem (L.sig.setWidth 64) 64)
        (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64)) := by
  obtain H := hashSpace hL
  obtain wz : Whole.Within ⟨L.scr.setWidth 64, 0⟩ L.SCR := ⟨0, by simp, by change 0 ≤ 8192; decide⟩
  obtain wsc : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩
  obtain cov : Covers (equationRd L ++ equationWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply hash_covers
    simp only [equationRd, equationWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inr ⟨L.PK, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inr ⟨L.SIG, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inl (challengeWithin hL)
    · exact .inl (argsWithin L (by decide))
    · exact .inr ⟨L.TBL, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact scratch_covered wz
    · exact scratch_covered wsc
  obtain ws : ∀ r ∈ equationWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
    hash_writes (by
      simp only [equationWr, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact .inr wz
      · exact .inr wsc)
  with_reducible
    refine Whole.call_ok hc hL.below equation_correct_result equation_nosp (by rw [equation_stack]; decide)
      (equation_pre hc hL ha (hc.tbl hL ht) hy) cov ws fun t ht _ _ post => ⟨ht, ?_⟩
  obtain ⟨t₂, hm, hg, hp⟩ := post
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  obtain ⟨a0, a1, a2, _⟩ := ha
  change t₂.gpr .eax = signWord (Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 0).setWidth 64) 32)
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 1).setWidth 64) 64)
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 2).setWidth 64) 64)) at hp
  rw [hg .eax (by decide), (ca (j := 0) (by decide)).trans a0,
    (ca (j := 1) (by decide)).trans a1, (ca (j := 2) (by decide)).trans a2] at hp
  obtain pk : Spec.Ed25519.bytesAt s.callEntry.mem (L.pk.setWidth 64) 32 =
      Spec.Ed25519.bytesAt s.mem (L.pk.setWidth 64) 32 := by
    apply Whole.callEntry_bytes (r := L.PK) ?_ (by change 32 ≤ 2 ^ 64; decide)
    rw [hc.esp]
    exact ((hL.ks _ (by simp [Lay.inputs])).sub_left (Whole.below_sub_stack hL.below (by decide))).symm
  obtain sg : Spec.Ed25519.bytesAt s.callEntry.mem (L.sig.setWidth 64) 64 =
      Spec.Ed25519.bytesAt s.mem (L.sig.setWidth 64) 64 := by
    apply Whole.callEntry_bytes (r := L.SIG) ?_ (by change 64 ≤ 2 ^ 64; decide)
    rw [hc.esp]
    exact ((hL.ks _ (by simp [Lay.inputs])).sub_left (Whole.below_sub_stack hL.below (by decide))).symm
  obtain ch : Spec.Ed25519.bytesAt s.callEntry.mem ((L.E + 128).setWidth 64) 64 =
      Spec.Ed25519.bytesAt s.mem ((L.E + 128).setWidth 64) 64 := by
    apply Whole.callEntry_bytes (r := challenge L) ?_ (by change 64 ≤ 2 ^ 64; decide)
    rw [hc.esp]
    exact (Whole.frame_below hL.below H.frameFit (by decide : 128 < 256) (by decide : 128 + 64 ≤ 256)).symm
  obtain ce : (L.E + 128).setWidth 64 = L.E.setWidth 64 + 128 := Whole.frame_addr H.frameFit (by decide : 128 < 256)
  rw [pk, sg, ch, ce] at hp
  exact hp

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.HashFinalize`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.FinalizeArgs`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole VG.Impl.Ed25519.X86.VerifyMessage

def FinArgs (L : Lay) (count : BitVec 64) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.scr ∧ Whole.slots L.E t 3 = L.E + 192 ∧
    Whole.slots L.E t 4 = L.scr + 192 ∧
    Whole.slots L.E t 2 ++ Whole.slots L.E t 1 = count

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem count_keep {t u : State} (hf : Frame [⟨L.E.setWidth 64 + 4, 8⟩] t.mem u.mem)
    {j : Nat} (hj : j = 0 ∨ j = 3 ∨ j = 4) : Whole.slots L.E u j = Whole.slots L.E t j := by
  refine hf.readW (Region.contains_self _ _) ?_ (by decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  apply Offset.disjoint (e := 4) (k := 8)
  · rcases hj with rfl | rfl | rfl <;> decide
  · rcases hj with rfl | rfl | rfl <;> decide
  · decide

theorem count_frame {m m' : Mem} (hf : Frame [⟨L.E.setWidth 64 + 4, 8⟩] m m') :
    Frame [⟨L.E.setWidth 64, 24⟩] m m' :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (d := 4) (by decide)⟩

theorem finalizeArgs_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    :
    WP isa (.block finalizeArgs) s fun t => Ctx L g m₀ t ∧
      Frame [⟨L.E.setWidth 64, 24⟩] s.mem t.mem ∧
      FinArgs L (BitVec.ofNat 64 (L.len.toNat + 64)) t := by
  rw [finalizeArgs, WP.block_append_iff]
  refine WP.mono (args_ok hc hL ha (vs := [.caller 4 0, .const 0, .const 0, .frame 192, .caller 4 192])
    (by decide) (Whole.valid_all (by decide))) fun u ⟨hu, hf, hs⟩ => ?_
  obtain aa := hs.slot hL (j := 0) (by decide) (by decide)
  obtain ab := hs.slot hL (j := 1) (by decide) (by decide)
  obtain ac := hs.slot hL (j := 2) (by decide) (by decide)
  obtain ad := hs.slot hL (j := 3) (by decide) (by decide)
  obtain ae := hs.slot hL (j := 4) (by decide) (by decide)
  change Whole.slots L.E u 0 = L.scr + 0#32 at aa
  rw [BitVec.add_zero] at aa
  change Whole.slots L.E u 1 = 0#32 at ab
  change Whole.slots L.E u 2 = 0#32 at ac
  change Whole.slots L.E u 3 = L.E + 192 at ad
  change Whole.slots L.E u 4 = L.scr + 192 at ae
  obtain hr : InRegions (u.rd ++ u.wr) (addr L.E 268) 4 := by
    refine ⟨L.ARGS, ?_, ?_⟩
    · rw [hu.rd]; simp [Lay.inputs]
    · rw [addr_eq (by have := hL.top; omega_using [this])]
      exact Offset.contains _ (e := 260) (k := 20) (d := 268) (n := 4) (by decide) (by decide) (by decide)
  obtain hx : u.mem.readW (addr L.E 268) 32 = L.len := by
    rw [addr_eq (by have := hL.top; omega_using [this])]
    exact (hu.arg_word hL (j := 2) (by decide)).trans (ha 2 (by decide))
  refine WP.mono (Whole.Ctx.count hu (index := 2) (n := 64) (by have := hL.top; omega_using [this]) hr hx)
    fun t ⟨ht, hft, hlo, hhi⟩ => ⟨ht, hf.trans (count_frame hft),
      (count_keep hft (.inl rfl)).trans aa,
      (count_keep hft (.inr (.inl rfl))).trans ad,
      (count_keep hft (.inr (.inr rfl))).trans ae, ?_⟩
  show (t.mem.readW (L.E.setWidth 64 + 8#64) 32 ++ t.mem.readW (L.E.setWidth 64 + 4#64) 32) = BitVec.ofNat 64 (L.len.toNat + 64)
  change t.mem.readW (L.E.setWidth 64 + 8#64) 32 = _ at hhi
  change t.mem.readW (L.E.setWidth 64 + 4#64) 32 = _ at hlo
  rw [hhi, hlo]
  exact Whole.count_pair L.len 64 (by decide)

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem digest_addr (hL : L.Ok) : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 :=
  addr_eq (x := L.E) (k := 192) (by have := hL.top; omega_using [this])

theorem digestWithin (hL : L.Ok) : Whole.Within ⟨(L.E + 192).setWidth 64, 64⟩ L.FR :=
  ⟨192, digest_addr hL, by change 192 + 64 ≤ 256; decide⟩

theorem digest_below (hL : L.Ok) : (below L.E 24).Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ := by
  change Region.Disjoint ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
  rw [Taint.sub_setWidth hL.below, digest_addr hL]
  exact Offset.disjoint_below_above _ (m := 24) (a := 192) (l := 64) (by decide)

theorem finalize_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {msg : List Byte}
    (hlen : msg.length < 2 ^ 64) (hcount : L.len.toNat + 64 = msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) msg) :
    WP isa (VG.Impl.Ed25519.X86.PublicKey.callWith finalizeArgs "vg_sha512_finalize_scratch" Impl.Sha512.X86.Stream.finalize) s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = Spec.Sha512.sha512 msg := by
  refine WP.seq (WP.mono (finalizeArgs_ok hc hL ha) fun u ⟨hu, hf, a0, a3, a4, ac⟩ => ?_)
  obtain H := hashSpace hL
  obtain fit : (L.E + 192).toNat + 64 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega_using [this])]
    have := hL.top; omega_using [this]
  obtain hd : Region.Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ L.SCR :=
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((digestWithin hL).sub p hp))
  obtain hp := Whole.finalize_pre hu.esp H a0 a3 a4 hd (digest_below hL) (by
    rw [digest_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)) fit
  obtain cov := hash_covers (L := L)
    (rs := Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact scratch_covered (workWithin hL))
  obtain ws := hash_writes (L := L) (rs := Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact .inr (workWithin hL))
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hu.esp H.below H.frameFit hj
  obtain cnt : Proof.Sha512.countX86 u.callEntry = BitVec.ofNat 64 msg.length := by
    unfold Proof.Sha512.countX86
    rw [ca (j := 2) (by decide), ca (j := 1) (by decide), ac, hcount]
  obtain hbsha : (Whole.SHA L.scr).Disjoint (below (u.gpr .esp) 4) := by
    rw [hu.esp]; exact (H.below_sha (by decide)).symm
  refine WP.mono (Whole.finalize_call hu H.below hp cov ws (ca (by decide) |>.trans a0)
    (ca (by decide) |>.trans a3) cnt hbsha (setup_repr hL hf hr) hlen)
    fun t ⟨ht, hft, hdigest⟩ => ⟨ht, ?_, ?_⟩
  · refine (setup_frame hf).trans (hash_frame hft ?_)
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (shaWithin L)
    · exact .inr ⟨0, by rw [digest_addr hL]; simp, by change 0 + 64 ≤ 64; decide⟩
    · exact .inl (workWithin hL)
  · rw [digest_addr hL] at hdigest
    exact hdigest

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.HashInputs`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.HashUpdate`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

structure Input (L : Lay) (p n : BitVec 32) : Prop where
  cover : Whole.Within ⟨p.setWidth 64, n.toNat⟩ L.FR ∨
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨p.setWidth 64, n.toNat⟩ R
  scratch : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ L.SCR
  below : (below L.E 24).Disjoint ⟨p.setWidth 64, n.toNat⟩
  args : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ ⟨L.E.setWidth 64, 24⟩
  fit : p.toNat + n.toNat ≤ 2 ^ 32

def UpdateArgs (L : Lay) (c p n : BitVec 32) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.scr ∧ Whole.slots L.E t 1 = c ∧ Whole.slots L.E t 2 = 0 ∧
    Whole.slots L.E t 3 = p ∧ Whole.slots L.E t 4 = n ∧ Whole.slots L.E t 5 = L.scr + 192

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem count_zero_high (x : BitVec 32) : (0#32) ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat]
  change 0 * 2 ^ 32 + x.toNat = x.toNat % 2 ^ 64
  omega_using []

theorem update_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {vs : List Value} (hlen : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 5 v)
    {c p n : BitVec 32} (hargs : ∀ t, OutArgs L vs t → UpdateArgs L c p n t)
    (hi : Input L p n) {prev : List Byte} (hcount : c.toNat = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (Impl.Ed25519.X86.VerifyMessage.update (setup 0 vs)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem (p.setWidth 64) n.toNat) := by
  refine WP.seq (WP.mono (args_ok hc hL ha hlen hv) fun u ⟨hu, hf, hs⟩ => ?_)
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hargs u hs
  obtain H := hashSpace hL
  obtain hp := Whole.update_pre hu.esp H a0 a3 a4 a5 hi.scratch hi.below hi.fit
  obtain cov := hash_covers (L := L) (rs := Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hi.cover
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact scratch_covered (workWithin hL))
  obtain ws := hash_writes (L := L) (rs := Whole.hashWr L.scr) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inr (workWithin hL))
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hu.esp H.below H.frameFit hj
  obtain cnt : Proof.Sha512.countX86 u.callEntry = BitVec.ofNat 64 prev.length := by
    unfold Proof.Sha512.countX86
    rw [ca (j := 2) (by decide), ca (j := 1) (by decide), a1, a2]
    exact (count_zero_high c).trans (congrArg (BitVec.ofNat 64) hcount)
  obtain hb : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ (below (u.gpr .esp) 4) := by
    rw [hu.esp]
    exact (hi.below.sub_left (below_sub (by decide) H.below)).symm
  obtain hbsha : (Whole.SHA L.scr).Disjoint (below (u.gpr .esp) 4) := by
    rw [hu.esp]; exact (H.below_sha (by decide)).symm
  refine WP.mono (Whole.update_call hu H.below hp cov ws (ca (by decide) |>.trans a0)
    (ca (by decide) |>.trans a3) (ca (by decide) |>.trans a4) cnt hbsha hb
    (setup_repr hL hf hr)) fun t ⟨ht, hft, hrepr⟩ => ⟨ht, ?_, ?_⟩
  · refine (setup_frame hf).trans (hash_frame hft ?_)
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (shaWithin L)
    · exact .inl (workWithin hL)
  · have same : Spec.Ed25519.bytesAt u.mem (p.setWidth 64) n.toNat =
        Spec.Ed25519.bytesAt s.mem (p.setWidth 64) n.toNat := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi' => ?_
      exact hf.bytes (R := ⟨p.setWidth 64, n.toNat⟩)
        (by rintro r hr; rw [List.mem_singleton.mp hr]; exact hi.args)
        (by have := n.isLt; change n.toNat ≤ 2 ^ 64; omega_using []) (List.mem_range.mp hi')
    rw [same] at hrepr
    exact hrepr

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem input_geometry (hL : L.Ok) {p n : BitVec 32} {R : Region}
    (hr : R ∈ L.inputs) (hw : Whole.Within ⟨p.setWidth 64, n.toNat⟩ R)
    (hf : p.toNat + n.toNat ≤ 2 ^ 32) : Input L p n := by
  refine ⟨.inr ⟨R, List.mem_append_left _ hr, hw⟩, (hL.sc _ hr).sub_left hw.sub,
    ((hL.ks _ hr).sub_left (Whole.below_sub_stack hL.below (by simp))).sub_right hw.sub, ?_, hf⟩
  exact ((hL.ks _ hr).sub_left (fun p hp => Whole.frame_sub L.E p
    ((argsWithin L (n := 24) (by simp)).sub p hp))).symm.sub_left hw.sub

theorem input_pk (hL : L.Ok) : Input L L.pk 32 :=
  input_geometry hL (R := L.PK) (by simp [Lay.inputs]) ⟨0, by simp, by change 0 + 32 ≤ 32; decide⟩ hL.np

theorem input_sig (hL : L.Ok) : Input L L.sig 32 :=
  input_geometry hL (R := L.SIG) (by simp [Lay.inputs]) ⟨0, by simp, by change 0 + 32 ≤ 64; decide⟩
    (by change L.sig.toNat + 32 ≤ 2 ^ 32; have := hL.ns; omega_using [this])

theorem input_msg (hL : L.Ok) : Input L L.msg L.len :=
  input_geometry hL (R := L.MSG) (by simp [Lay.inputs]) ⟨0, by simp, by simp⟩ hL.nm

theorem prefix_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {source count : Nat} (hs : source < 5) {prev : List Byte}
    (hlen : prev.length = count) (hcount : count < 2 ^ 32)
    (hi : Input L (L.value source) 32)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (Impl.Ed25519.X86.VerifyMessage.update (Impl.Ed25519.X86.VerifyMessage.prefixArgs source count)) s
      fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem ((L.value source).setWidth 64) 32) := by
  apply update_step hc hL ha (vs := [.caller 4 0, .const count, .const 0,
    .caller source 0, .const 32, .caller 4 192]) (by simp)
    (by simp [Whole.valid, hs]) (c := BitVec.ofNat 32 count) (p := L.value source) (n := 32)
    ?_ hi (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcount] using hlen.symm) hr
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ht.slot hL (j := 0) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 1) (by simp) (by simp)
  · exact ht.slot hL (j := 2) (by simp) (by simp)
  · exact (ht.slot hL (j := 3) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 4) (by simp) (by simp)
  · exact ht.slot hL (j := 5) (by simp) (by simp)

theorem message_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {prev : List Byte} (hlen : prev.length = 64)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (Impl.Ed25519.X86.VerifyMessage.update Impl.Ed25519.X86.VerifyMessage.messageArgs) s
      fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem (L.msg.setWidth 64) L.len.toNat) := by
  apply update_step hc hL ha (vs := [.caller 4 0, .const 64, .const 0,
    .caller 1 0, .caller 2 0, .caller 4 192]) (by simp)
    (Whole.valid_all (by decide)) (c := 64) (p := L.msg) (n := L.len)
    ?_ (input_msg hL) hlen.symm hr
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ht.slot hL (j := 0) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 1) (by simp) (by simp)
  · exact ht.slot hL (j := 2) (by simp) (by simp)
  · exact (ht.slot hL (j := 3) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact (ht.slot hL (j := 4) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 5) (by simp) (by simp)

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Challenge`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.HashPipeline`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def hashInput (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 32 ++
    Spec.Ed25519.bytesAt m (L.pk.setWidth 64) 32 ++
    Spec.Ed25519.bytesAt m (L.msg.setWidth 64) L.len.toNat

theorem bytes_length (m : Mem) (p : BitVec 64) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

theorem sig_prefix_same (hc : Ctx L g m₀ s) (hL : L.Ok) :
    Spec.Ed25519.bytesAt s.mem (L.sig.setWidth 64) 32 = Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hc.frame.bytes (R := L.SIG) (by
    intro r hr
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.sc _ (by simp [Lay.inputs])
    · exact (hL.ks _ (by simp [Lay.inputs])).symm)
    (by change 64 ≤ 2 ^ 64; decide) (by change i < 64; have := List.mem_range.mp hi; omega_using [this])

theorem hash_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hash s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = Spec.Sha512.sha512 (hashInput L m₀) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun t ⟨ht, _, hinit⟩ => ?_)
  refine WP.seq (WP.mono (prefix_step ht hL ha (source := 3) (count := 0)
    (by decide) rfl (by decide) (input_sig hL) hinit) fun u ⟨hu, _, hsig⟩ => ?_)
  change Spec.Sha512.Repr _ u.mem _ ([] ++ Spec.Ed25519.bytesAt t.mem (L.sig.setWidth 64) 32) at hsig
  rw [List.nil_append, sig_prefix_same ht hL] at hsig
  refine WP.seq (WP.mono (prefix_step hu hL ha (source := 0) (count := 32)
    (by decide) (bytes_length _ _ _) (by decide) (input_pk hL) hsig) fun v ⟨hv, _, hpk⟩ => ?_)
  change Spec.Sha512.Repr _ v.mem _ (_ ++ Spec.Ed25519.bytesAt u.mem (L.pk.setWidth 64) 32) at hpk
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)] at hpk
  obtain hpkl : (Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 32 ++
      Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32).length = 64 := by
    rw [List.length_append, bytes_length, bytes_length]
  refine WP.seq (WP.mono (message_step hv hL ha hpkl hpk) fun w ⟨hw, _, hmsg⟩ => ?_)
  rw [hv.input_bytes hL (r := L.MSG) (by simp [Lay.inputs])
    (by have := L.len.isLt; change L.len.toNat ≤ 2 ^ 64; omega_using [])] at hmsg
  obtain hlen : (hashInput L m₀).length = L.len.toNat + 64 := by
    simp only [hashInput, List.length_append, bytes_length]
    omega_using []
  refine WP.mono (finalize_step hw hL ha (msg := hashInput L m₀)
    (by rw [hlen]; have := L.len.isLt; omega_using []) hlen.symm hmsg) fun t ⟨ht, _, hd⟩ => ⟨ht, hd⟩

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduced_challenge (digest : List Byte) :
    Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) =
      Spec.Ed25519.scalarReduce digest ++ Spec.Ed25519.encodeLE 32 0 := by
  simp only [Spec.Ed25519.scalarReduce, Proof.Ed25519.X86.encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  obtain hL : Spec.Ed25519.L ≤ 256 ^ 32 := by decide
  obtain hpos : 0 < Spec.Ed25519.L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

theorem setup_bytes {u : State} {d n : Nat}
    (hf : Frame [⟨L.E.setWidth 64, 24⟩] s.mem u.mem) (hd : 24 ≤ d) (hn : d + n ≤ 256) :
    Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + BitVec.ofNat 64 d) n := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩) (by
    rintro r hr; rw [List.mem_singleton.mp hr]
    exact (Offset.base_disjoint _ hd (by omega_using [hn])).symm) (by change n ≤ 2 ^ 64; omega_using [hn]) (List.mem_range.mp hi)

theorem reduce_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.X86.PublicKey.callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce) s
      fun t => Ctx L g m₀ t ∧ Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64) := by
  refine WP.seq (WP.mono (args_ok hc hL ha (vs := [.frame 128, .frame 192, .caller 4 0])
    (by decide) (Whole.valid_all (by decide))) fun u ⟨hu, hf, hs⟩ => ?_)
  obtain a0 := hs.slot hL (j := 0) (by decide) (by decide)
  obtain a1 := hs.slot hL (j := 1) (by decide) (by decide)
  obtain a2 := (hs.slot hL (j := 2) (by decide) (by decide)).trans (BitVec.add_zero _)
  obtain H := hashSpace hL
  refine WP.mono (Whole.reduce_call hu H (by simp [Lay.outputs]) (d := 128)
    (by decide) (by decide) a0 a1 a2) fun t ⟨ht, _, hd⟩ => ⟨ht, ?_⟩
  obtain e128 : (L.E + 128).setWidth 64 = L.E.setWidth 64 + 128 := Whole.frame_addr H.frameFit (by decide : 128 < 256)
  obtain e192 : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 := Whole.frame_addr H.frameFit (by decide : 192 < 256)
  change Spec.Ed25519.bytesAt t.mem ((L.E + 128).setWidth 64) 32 = _ at hd
  obtain same : Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + 192) 64 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64 :=
    setup_bytes hf (by decide : 24 ≤ 192) (by decide : 192 + 64 ≤ 256)
  rw [e128, e192, same] at hd
  exact hd

theorem extend_step (hc : Ctx L g m₀ s) (hL : L.Ok) {digest : List Byte}
    (hd : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 32 = Spec.Ed25519.scalarReduce digest) :
    WP isa (.block extendChallenge) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 40) (count := 8)
    (hashSpace hL).frameFit (by decide)) fun t ⟨ht, hf, hz⟩ => ⟨ht, ?_⟩
  obtain low : Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (R := ⟨L.E.setWidth 64 + 128, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  obtain high : Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 160) 32 = Spec.Ed25519.encodeLE 32 0 := by
    rw [Proof.Ed25519.X86.encodeLE_eq]
    apply Proof.X25519.bytesAt_leBytes_words32
    intro j hj
    obtain z := hz j hj
    rw [addr_eq (by have := hL.top; omega_using [hj, this])] at z
    obtain e : L.E.setWidth 64 + BitVec.ofNat 64 (4 * (40 + j)) =
        L.E.setWidth 64 + 160 + BitVec.ofNat 64 (4 * j) := by
      rw [show 4 * (40 + j) = 160 + 4 * j by omega_using [], BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [e] at z
    rw [z]
    simp
  change Spec.X25519.bytesAt t.mem (L.E.setWidth 64 + 128) (32 + 32) = _
  rw [Proof.X25519.bytesAt_add]
  change Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 ++
    Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128 + 32) 32 = _
  rw [show L.E.setWidth 64 + 128 + 32 = L.E.setWidth 64 + 160 by rw [BitVec.add_assoc]; rfl,
    low, hd, high, reduced_challenge]

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashInput_eq (L : Lay) (m : Mem) : hashInput L m =
    (Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 64).take 32 ++
      Spec.Ed25519.bytesAt m (L.pk.setWidth 64) 32 ++
      Spec.Ed25519.bytesAt m (L.msg.setWidth 64) L.len.toNat := by
  obtain e : (Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 64).take 32 =
      Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 32 := by
    unfold Spec.Ed25519.bytesAt
    rw [← List.map_take, List.take_range]
    rfl
  rw [e]
  rfl

theorem equation_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (ht : TblAt L m₀)
    (hy : s.syms Impl.Ed25519.X86.bSym = L.tbl) {challenge : List Byte}
    (hh : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 = challenge) :
    WP isa (VG.Impl.Ed25519.X86.PublicKey.callWith equationArgs "vg_ed25519_verify_equation" Impl.Ed25519.X86.verifyEquation) s
      fun t => Ctx L g m₀ t ∧ t.gpr .eax = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32)
        (Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 64) challenge) := by
  refine WP.seq (WP.mono_syms (args_ok hc hL ha
    (vs := [.caller 0 0, .caller 3 0, .frame 128, .caller 4 0])
    (by decide) (Whole.valid_all (by decide))) fun u ⟨hu, hf, hs⟩ yu => ?_)
  obtain a0 := (hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _)
  obtain a1 := (hs.slot hL (j := 1) (by decide) (by decide)).trans (BitVec.add_zero _)
  obtain a2 := hs.slot hL (j := 2) (by decide) (by decide)
  obtain a3 := (hs.slot hL (j := 3) (by decide) (by decide)).trans (BitVec.add_zero _)
  obtain he : Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + 128) 64 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 :=
    setup_bytes hf (by decide : 24 ≤ 128) (by decide : 128 + 64 ≤ 256)
  refine WP.mono (equation_call hu hL ⟨a0, a1, a2, a3⟩ ht (by rw [yu, hy])) fun t ⟨ht, eq⟩ => ⟨ht, ?_⟩
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide),
    hu.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide), he, hh] at eq
  exact eq

theorem body_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (ht : TblAt L m₀)
    (hy : s.syms Impl.Ed25519.X86.bSym = L.tbl) :
    WP isa body s fun t => Ctx L g m₀ t ∧ t.gpr .eax = signWord (Spec.Ed25519.verify
      (Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32)
      (Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat)
      (Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 64)) := by
  refine WP.seq (WP.mono_syms (hash_ok hc hL ha) fun t ⟨hs, hh⟩ yt => ?_)
  refine WP.seq (WP.mono_syms (reduce_step hs hL ha) fun u ⟨hu, hr⟩ yu => ?_)
  rw [hh] at hr
  refine WP.seq (WP.mono_syms (extend_step hu hL hr) fun v ⟨hv, he⟩ yv => ?_)
  rw [hashInput_eq] at he
  exact equation_step hv hL ha ht (by rw [yv, yu, yt, hy]) he

end VG.Proof.Ed25519.X86.VerifyMessage
