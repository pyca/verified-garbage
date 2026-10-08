import VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 verification's equation on x86-64: `Verified`

Correctness including the ABI, given the reference computations' agreement
with the specification (`RecoverOk`, `VerifyEqOk`, which the registration
files pass in), constant time (by taint tracking: the only branches are on
the loop counters, and every address is an argument plus a constant or a
counter, or a pointer the code stored in the working space before any store
at a counter's offset could change it), and a concrete state satisfying the
signature's contract. The contract lets timing depend on the
inputs; the code's depends on the pointers alone.
-/

namespace VG.Proof.Ed448.X86_64

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
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx], flags := false, lens := [8192], bases := [(.rcx, 0, 0)] }

theorem verifyEquation_agree {s₁ s₂ : State} (h₁ : verifyEquationLocal.pre s₁)
    (h₂ : verifyEquationLocal.pre s₂) (hpub : verifyEquationLocal.pub s₁ s₂) :
    X86_64.Taint.Agree verifyEquationτ s₁ s₂ := by
  obtain ⟨-, p1, p2, p3, p4⟩ := hpub
  have wf : ∀ s, verifyEquationLocal.pre s → X86_64.Taint.Wf verifyEquationτ s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, -, d⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, verifyEquationτ], by simp [hw], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [verifyEquationτ, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · simp only [verifyEquationτ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p4]
  · intro sl h; simp [verifyEquationτ] at h
  · intro sl h; simp [verifyEquationτ] at h

theorem verifyEquation_ok (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) (s : State)
    (hs : verifyEquationLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verifyEquation_correct Proof.X448.X86_64.baseline_ok hR hE hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := verifyEquation) (by lit_decide) he h.1, h.2⟩

/-! ## Constant time, with summaries

The constants stored in the working space are public, and the analysis keeps
them as public slots: some fifty, which every store of a secret and every
comparison of taints goes through. Nothing reads them as an address or a
condition: only the working space at `rdi` (region 0), the pointers to `A`
and the signature saved there (`PPK`, `PSIG`), and the decodings' loop's
pointer and count (`PCUR`, `CNT`) need to be public. The decoding and the
loop over the bits are analysed as summaries (`taint_summary`) from that
alone, so their analyses (and what follows them) carry no constants. -/

/-- What the code needs public after the entry, and the registers `rs` (the
encoding's address `rsi`, for the decoding). -/
def verifySumτ (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.rdi]), flags := false, lens := [8192], bases := [(.rdi, 0, 0)],
    slots := [(0, PPK, 8), (0, PSIG, 8), (0, PCUR, 8), (0, CNT, 8)] }

taint_summary verifyRootSum : taintS (verifySumτ []) (root Impl.X448.X86_64.baseline 12)

taint_summary verifyDecodeASum : taintS (verifySumτ [.rsi]) (decode Impl.X448.X86_64.baseline 6 7)
  using verifyRootSum
taint_summary verifyLoopSum : taintS (verifySumτ []) (vloop Impl.X448.X86_64.baseline)

theorem verifyEquation_ct :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation := by
  obtain ⟨_, hc⟩ : ∃ h, (taintS.check verifyEquationτ verifyEquation h).isSome = true := by
    taint_decide_sum [verifyDecodeASum, verifyLoopSum]
  exact VG.Taint.constantTime (A := taintS) verifyEquationτ
    (fun _ _ h₁ h₂ hp => verifyEquation_agree h₁ h₂ hp) hc

theorem verifyEquation_implies :
    verifyEquationLocal.Implies (Spec.Ed448.verifyEquationContract X86_64.abi) where
  pre := by
    sig_implies_pre [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs, verifyEquationLocal]
  post s t _ h := by
    sig_post [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs]
    have h' : t.gpr .rax = _ := h
    rw [h']
    generalize Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .rdi) 57)
      (Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨sp, -, pk, sig, ch, base⟩ := h
    exact ⟨sp, pk, sig, ch, base⟩
  sat := by
    sig_implies_sat [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86_64.abi, X86_64.argRegs] [verifyEquationSat] using verifyEquationSat

theorem verifyEquation_verified (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) :
    Verified X86_64.target verifyEquation (Spec.Ed448.verifyEquationContract X86_64.abi) :=
  Verified.of_correct (verifyEquation_ok hR hE) verifyEquation_ct verifyEquation_implies

end VG.Proof.Ed448.X86_64
