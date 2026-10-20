module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerPhase
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrograms
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyTailLaw
import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallTailCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerAtCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhase
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhaseCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain

/-! # The shared Montgomery backend supplies key generation's exponentiation law -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyGenerate
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

def arithmetic (b : MontBackend) (base sp : BitVec 32) (len w : Nat) :=
  TwoExp.sharedMontgomery base sp len w b.name b.mul
    (fun _ _ _ ho ha hb s h => b.correct s h ho ha hb) b.stackOk

theorem timing (b : MontBackend) (base sp : BitVec 32) (len w : Nat) :
    TwoExp.MontgomeryTiming (arithmetic b base sp len w) :=
  TwoExp.sharedMontgomeryTiming base sp len w b.name b.mul
    (fun _ _ _ ho ha hb s h => b.correct s h ho ha hb) b.stackOk
    (fun _ _ _ ho ha hb => b.rawCT ho ha hb)

def fallback {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming A)
    (fits : arrAt w 16 ≤ 8 * len) : KeyPower.Fallback base len w P regions where
  code := VG.Impl.Bignum.Arm.SharedWindow.phase A.op
  correct := by
    intro s ep M x eb h
    exact sharedWindowExpPhase_ok A s h.phase h.persistent fits h.separate
  ct := by
    intro ep M1 M2 x eb1 eb2 positive length s t tr1 tr2 u v h e1 e2
    exact SharedWindow.phase_ct A ct fits positive length h.1.separate s t tr1 tr2 u v
      ⟨⟨h.1.phase, h.1.persistent⟩, ⟨h.2.1.phase, h.2.1.persistent⟩, h.2.2⟩ e1 e2

private theorem powerLaw (b : MontBackend) : KeyPowerLaw
    (VG.Impl.Ffdh.Arm.KeyPower.powerAt
      (VG.Impl.Ffdh.Arm.KeyPower.twoPhase (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul))
      (VG.Impl.Bignum.Arm.SharedWindow.phase (VG.Impl.Bignum.Arm.MontCall.op b.name b.mul)) 56 16 20) := by
  constructor
  · intro s p slots eb context calls stable h56 h16 h20 h32 ready modulus odd r2 significant size
    let A := arithmetic b p.base s.sp p.len p.w
    let F := fallback A (timing b p.base s.sp p.len p.w) p.width.2.2.1
    have input : KeyPower.ArgsInput p slots 56 16 p.P (TwoExp.CallReady p.base s.sp p.len)
        [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] ((p.dom.drop p.k).take p.k) eb s := by
      refine ⟨⟨context, ready, modulus, r2, context.gBytes, significant⟩, ⟨calls.stack, rfl⟩, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact significant.separate
      · change Region.Disjoint ⟨State.addr p.scalarStart, eb.length⟩ _
        rw [size]; exact calls.significant_below
    refine WP.mono (KeyPower.powerAt_ok s A F stable h56 h16 h20 h32 p.gLength
      (by rw [size]; exact p.scalarWidthBounds.1)
      (by rw [size]; have := p.scalarWidthBounds; have := p.maxLength; omega)
      (by change BitVec.ofNat 32 p.scalarWidth = _; rw [size]) odd input calls) ?_
    rintro t ⟨ctx, rd, value, m, rr, one, _, frame, rest⟩
    exact ⟨ctx, rd, value, m, rr, one, frame, rest⟩
  · intro p slots eb1 eb2 stable h56 h16 h20 h32 size1 size2 odd s t tr1 tr2 u v h e1 e2
    let A := arithmetic b p.base s.sp p.len p.w
    let F := fallback A (timing b p.base s.sp p.len p.w) p.width.2.2.1
    have mkInput (z : State) (eb : List Byte) (hz : KeyPowerInput p slots eb z)
        (calls : KeyCallMemory p z) (sp : z.sp = s.sp) (size : eb.length = p.scalarWidth) :
        KeyPower.ArgsInput p slots 56 16 p.P (TwoExp.CallReady p.base s.sp p.len)
          [⟨State.addr p.base, 8 * p.len⟩, belowA s.sp 48] ((p.dom.drop p.k).take p.k) eb z := by
      refine ⟨hz.toPowerAtInput, ⟨calls.stack, sp⟩, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hz.exponent.separate
      · change Region.Disjoint ⟨State.addr p.scalarStart, eb.length⟩ _
        rw [size, ← sp]; exact calls.significant_below
    exact KeyPower.powerAt_ct A (timing b p.base s.sp p.len p.w) F stable h56 h16 h20 h32 p.gLength
      (by rw [size1]; exact p.scalarWidthBounds.1)
      (by rw [size1]; have := p.scalarWidthBounds; have := p.maxLength; omega)
      (by change BitVec.ofNat 32 p.scalarWidth = _; rw [size1]) (size1.trans size2.symm) odd
      s t tr1 tr2 u v ⟨mkInput s eb1 h.1.1 h.1.2 rfl size1,
        mkInput t eb2 h.2.1.1 h.2.1.2 h.2.2.symm size2, h.2.2⟩ e1 e2

theorem tailLaw (b : MontBackend) : KeyTailLaw (tail b) :=
  keyCallTail_law (powerLaw b)

end VG.Proof.Ffdh.Arm.KeyGenerate
