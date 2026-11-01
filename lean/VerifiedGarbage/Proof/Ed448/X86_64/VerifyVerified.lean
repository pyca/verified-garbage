module

public import VerifiedGarbage.Proof.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Timing
public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyPrefix
public import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Joint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed448.X86_64.PointSums
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Timing
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyPrefix
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
meta import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Joint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ed448.X86_64.PointSums
meta import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-!
# Ed448 verification's equation on x86-64: `Verified`

Correctness and ABI preservation for both field backends, together with a
relational timing proof. Decoding uses fixed addresses. The joint multiplication
indexes its projective table using public challenge digits, whose values follow
from correctness of scalar decoding. The reviewed contract already makes every
verification input public; no signing or secret-scalar contract changes.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64
set_option exponentiation.threshold 1024

open VG VG.X86_64 VG.Impl.Ed448.X86_64

def verifyEquationSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 114⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x4000, 8192⟩]

/-- The arguments are public; the working space is writable region 0, at `rcx`. -/
def verifyEquationτ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false, lens := [8192], bases := [(.rcx, 0, 0)] }

theorem verifyEquation_agree {s₁ s₂ : State} (h₁ : verifyEquationLocal.pre s₁)
    (h₂ : verifyEquationLocal.pre s₂) (hpub : verifyEquationLocal.pub s₁ s₂) :
    X86_64.Taint.Agree verifyEquationτ s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3, p4, _, _⟩ := hpub
  have wf : ∀ s, verifyEquationLocal.pre s → X86_64.Taint.Wf verifyEquationτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, -, d⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, verifyEquationτ], by simp [hw], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [verifyEquationτ, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [verifyEquationτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [p1, p2, p3, p4, p0]
  · rw [h₁.2.1, h₂.2.1, p4]
  · intro sl h; simp [verifyEquationτ] at h
  · intro sl h; simp [verifyEquationτ] at h

theorem verifyEquation_okI (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) (s : State)
    (hs : verifyEquationLocal.pre s) :
    ∃ t s', Exec isa verifyEquation.inline s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verifyEquation_correct_inline hR hE hs
  exact ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; lit_decide) he h.1, h.2⟩

/-- The postcondition reads registers only. -/
theorem verifyEquation_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (_ : verifyEquationLocal.pre s)
    (_ : Clear (hole (s.gpr .rsp)) s) (hp : verifyEquationLocal.post s b) :
    verifyEquationLocal.post s (b.patch (hole (s.gpr .rsp)) hv u) := hp

/-- The code's correctness, for callers. -/
theorem verifyEquation_ok (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) :
    ∀ s, verifyEquationLocal.clear.pre s →
      ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' :=
  ok_of_inline verifyEquation_inlineOk (verifyEquation_okI hR hE) verifyEquation_patch

/-! ## Public-input timing, with decoding summaries -/

/-- What the code needs public after the entry, and the registers `rs` (the
encoding's address `rsi`, for the decoding). -/
def verifySumτ (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.rdi, .rsp]), flags := false, lens := [8192], bases := [(.rdi, 0, 0)],
    slots := [(0, PPK, 8), (0, PSIG, 8), (0, PCUR, 8), (0, CNT, 8)] }

taint_summary verifyRootInlineSum : taintS (verifySumτ [])
    (rootCallFor .scalar).inline
taint_summary verifyDecodeInlineSum : taintS (verifySumτ [.rsi])
    (decode Impl.X448.X86_64.baseline 6 7 (rootCallFor .scalar).inline) using verifyRootInlineSum
taint_summary verifyRootAdxInlineSum : taintS (verifySumτ [])
    (rootCallFor .adx).inline
taint_summary verifyDecodeAdxInlineSum : taintS (verifySumτ [.rsi])
    (decode Impl.X448.X86_64.adx 6 7 (rootCallFor .adx).inline) using verifyRootAdxInlineSum

theorem verifyPrefix_ct (v : Impl.Ed448.X86_64.FieldVariant) :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub
      (verifyPrefix v.field (rootCallFor v).inline) := by
  cases v
  · obtain ⟨_, hc⟩ : ∃ h, (taintS.check verifyEquationτ
        (verifyPrefix Impl.X448.X86_64.baseline (rootCallFor .scalar).inline) h).isSome = true := by
      taint_decide_sum [verifyDecodeInlineSum]
    exact VG.Taint.constantTime (A := taintS) verifyEquationτ
      (fun _ _ h₁ h₂ hp => verifyEquation_agree h₁ h₂ hp) hc
  · obtain ⟨_, hc⟩ : ∃ h, (taintS.check verifyEquationτ
        (verifyPrefix Impl.X448.X86_64.adx (rootCallFor .adx).inline) h).isSome = true := by
      taint_decide_sum [verifyDecodeAdxInlineSum]
    exact VG.Taint.constantTime (A := taintS) verifyEquationτ
      (fun _ _ h₁ h₂ hp => verifyEquation_agree h₁ h₂ hp) hc

theorem verifyFinish_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) :
    RelCT isa (fun s u => s.gpr .rdi = base ∧ u.gpr .rdi = base)
      (vfinish v.field v.bodies) (fun _ _ => True) := by
  cases v <;> apply relCT_sum (Taint.ofRegs [.rdi]) _ (by taint_decide_sum [dblSum, addSum, dblAdxSum, addAdxSum])
  all_goals
    intro s u h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    exact h.1.trans h.2.symm

theorem verifyRest_ct (v : Impl.Ed448.X86_64.FieldVariant) (base : Addr) (S K : Nat)
    (hS : S < 2 ^ 456) (hK : K < 2 ^ 456) :
    RelCT isa (fun s u => Window.JointTimingCtx base S K s ∧ Window.JointTimingCtx base S K u)
      (.seq (Wnaf.joint v.field v.bodies KBITS) (vfinish v.field v.bodies)) (fun _ _ => True) := by
  apply Window.seq_same (Wnaf.joint_ct v base S K hS hK) _ (verifyFinish_ct v base)
  intro s h
  exact WP.mono (Wnaf.joint_ok (FieldVariant.field_ok v) (FieldVariant.bodies_ok v)
    h.scr (by decide) (by decide) h.bs h.bk hS hK h.d h.z h.p) fun u hu => hu.1.rdi

theorem signatureScalar_below (s : State) : signatureScalar s < 2 ^ 456 := by
  exact decodeLE_below (bytesAt57_len s.mem (s.gpr .rsi + BitVec.ofNat 64 57))

theorem challengeScalar_below (s : State) : challengeScalar s < 2 ^ 456 := by
  exact decodeLE_below (bytesAt57_len s.mem (s.gpr .rdx))

theorem verifyEquationFor_ctI (v : Impl.Ed448.X86_64.FieldVariant) (hR : Proof.Ed448.RecoverOk) :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub (verifyEquationFor v).inline := by
  let P (s u : State) := verifyEquationLocal.pre s ∧ verifyEquationLocal.pre u ∧ verifyEquationLocal.pub s u
  have head : RelCT isa P (verifyPrefix v.field (rootCallFor v).inline) (fun _ _ => True) :=
    fun s u t1 t2 s' u' h e1 e2 => ⟨verifyPrefix_ct v s u t1 t2 s' u' h.1 h.2.1 h.2.2 e1 e2, trivial⟩
  have hw := head.wpDep (F := fun (s u : State) =>
      Window.JointTimingCtx (s.gpr .rcx) (signatureScalar s) (challengeScalar s) u)
    (fun s u h => ⟨verifyPrefix_ok (FieldVariant.field_ok v) hR (rootCallFor_ok v) h.1,
      verifyPrefix_ok (FieldVariant.field_ok v) hR (rootCallFor_ok v) h.2.1⟩)
  have hh := hw.seq (Q := fun _ _ => True) (by
    intro s u t1 t2 s' u' h e1 e2
    obtain ⟨_, a, b, hab, ha, hb⟩ := h
    obtain ⟨_, _, _, _, base, sig, chal⟩ := hab.2.2
    rw [← base, ← sig, ← chal] at hb
    have hS := signatureScalar_below a
    have hK := challengeScalar_below a
    exact verifyRest_ct v (a.gpr .rcx) (signatureScalar a) (challengeScalar a) hS hK
      s u t1 t2 s' u' ⟨ha, hb⟩ e1 e2)
  have result := hh.assoc.assoc.assoc.assoc
  rw [verifyEquationFor_inline]
  exact result.constantTime

theorem verifyEquation_implies :
    verifyEquationLocal.Implies (Proof.Ed448.verifyEquationContract X86_64.abi) where
  pre := by
    sig_implies_pre [Proof.Ed448.verifyEquationContract, Proof.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, verifyEquationLocal]
  post s t _ h := by
    sig_post [Proof.Ed448.verifyEquationContract, Proof.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs]
    have h' : t.gpr .rax = _ := h
    rw [h']
    generalize Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .rdi) 57)
      (Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Proof.Ed448.verifyEquationContract, Proof.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨sp, bytes, pk, sig, ch, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [bytesAt57_len])
    obtain ⟨_, middle⟩ := List.append_inj' first (by simp only [bytesAt114_len])
    refine ⟨sp, pk, sig, ch, base, ?_, congrArg Spec.Ed448.decodeLE last⟩
    have hd := congrArg (fun bs => Spec.Ed448.decodeLE (bs.drop 57)) middle
    rw [bytesAt_drop57, bytesAt_drop57] at hd
    exact hd
  sat := by
    sig_implies_sat [Proof.Ed448.verifyEquationContract, Proof.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs] [verifyEquationSat] using verifyEquationSat

/-- The contract with 8 bytes of stack, for the call's return address. -/
theorem verifyEquation_implies8 :
    verifyEquationLocal.Implies (Proof.Ed448.verifyEquationContract X86_64.abi 8) :=
  verifyEquation_implies.stack8_abi (by
    sig_implies_sat [Proof.Ed448.verifyEquationContract, Proof.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, verifyEquationSat] [verifyEquationSat]
      using verifyEquationSat)

theorem verifyEquation_verified (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) :
    Verified X86_64.target verifyEquation (Proof.Ed448.verifyEquationContract X86_64.abi 8) :=
  Verified.of_inline verifyEquation_inlineOk (verifyEquation_okI hR hE) (verifyEquationFor_ctI .scalar hR)
    verifyEquation_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ _ hp => hp)
    (fun s t hs ht hp => (verifyEquation_implies8.pub s t hs ht hp).1)

end VG.Proof.Ed448.X86_64
