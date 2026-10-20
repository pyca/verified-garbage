module

public import VerifiedGarbage.Proof.Idea.X86.FbVerified
import VerifiedGarbage.Proof.Modes.X86.CbcChained
public import VerifiedGarbage.Proof.Idea.CbcScratch
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Idea.X86.ModesLit
import VerifiedGarbage.Proof.Idea.KeyLit32
meta import VerifiedGarbage.Proof.Idea.X86.FbVerified
meta import VerifiedGarbage.Proof.Modes.X86.CbcChained
meta import VerifiedGarbage.Proof.Idea.CbcScratch
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Idea.X86.ModesLit
meta import VerifiedGarbage.Proof.Idea.KeyLit32

/-!
# Idea-CBC on x86 (32-bit) meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value (`Proof.Modes.X86.cbcEncChained_wp`, `cbcDecChained_wp`)
over Idea's core for each direction (`dirCoreSpec`), with the working space
as the argument after `n`. The chaining value is written back, so it is
writable, as for OFB and CFB (`Fb.fbX86`), whose contract, taint and
narrowing (`Fb.fb_verified`) these share. The `_framed` theorems run them
with their working space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Idea.X86.Cbc

open VG VG.X86 VG.Impl.Idea.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (cbcEncChained_wp cbcDecChained_wp)
open VG.Proof.Idea.X86 (scr_eq disjoint_empty KeyArgs modeCoreSpec cbcBlocksAt_chunks modeCore_ka)
open VG.Proof.Idea.X86.Fb

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def decPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

theorem cbcEncryptChained_wp {s₀ : State} (hp : (fbX86 encPost).pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 encPost).post s₀ s' :=
  WP.mono (cbcEncChained_wp modeCoreSpec (seqPre_of rfl hp) (keyArgs_of hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, modeCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem cbcDecryptChained_wp {s₀ : State} (hp : (fbX86 decPost).pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 decPost).post s₀ s' :=
  WP.mono (cbcDecChained_wp modeCoreSpec (seqPre_of rfl hp) (keyArgs_of hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, modeCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

/-! ## Constant time -/

theorem cbcEncryptChained_ct : ConstantTime isa (fbX86 encPost).pre (fbX86 encPost).pub cbcEncryptChained :=
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cbcDecryptChained_ct : ConstantTime isa (fbX86 decPost).pre (fbX86 decPost).pub cbcDecryptChained :=
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The contracts -/

theorem wide_implies_enc :
    (wideContract encPost).Implies (Proof.Idea.cbcEncChainedScratchContract X86.abi 23) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Idea.cbcEncChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Proof.Idea.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost] at h
    sig_split h
    sig_reduce [Proof.Idea.cbcEncChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Proof.Idea.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Idea.cbcEncChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Proof.Idea.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Idea.cbcEncChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Proof.Idea.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost]
  · sig_implies_sat [Proof.Idea.cbcEncChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Proof.Idea.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_dec :
    (wideContract decPost).Implies (Proof.Idea.cbcDecChainedScratchContract X86.abi 23) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Idea.cbcDecChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Proof.Idea.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost] at h
    sig_split h
    sig_reduce [Proof.Idea.cbcDecChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Proof.Idea.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Idea.cbcDecChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Proof.Idea.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Idea.cbcDecChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Proof.Idea.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost]
  · sig_implies_sat [Proof.Idea.cbcDecChainedScratchContract, Proof.Idea.cbcChainedScratchSig, Spec.Idea.cbcChainedSig, Proof.Idea.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem frameSat_pre (post : Spec.Idea.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Idea.cbcChainedSig.contract X86.abi (post := post) (writeArgs := true) (stack := 208)).pre s := by
  implies_sat [Spec.Idea.cbcChainedSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem cbcEncryptChained_verified :
    Verified X86.target cbcEncryptChained (Proof.Idea.cbcEncChainedScratchContract X86.abi 23) :=
  fb_verified (fun _ hs => cbcEncryptChained_wp hs) cbcEncryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_enc

theorem cbcDecryptChained_verified :
    Verified X86.target cbcDecryptChained (Proof.Idea.cbcDecChainedScratchContract X86.abi 23) :=
  fb_verified (fun _ hs => cbcDecryptChained_wp hs) cbcDecryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_dec

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 208 4 46 cbcEncryptChained)
      (Spec.Idea.cbcEncryptChainedContract X86.abi 208) :=
  X86.Verified.stackScratchWiped (sig := Spec.Idea.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 23) (post := Proof.Idea.cbcEncChainedPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 208) cbcEncryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Idea.cbcEncChainedPost_local _) (Proof.Idea.cbcEncChainedPostOut_local _) (frameSat_pre _)

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 208 4 46 cbcDecryptChained)
      (Spec.Idea.cbcDecryptChainedContract X86.abi 208) :=
  X86.Verified.stackScratchWiped (sig := Spec.Idea.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 23) (post := Proof.Idea.cbcDecChainedPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 208) cbcDecryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Idea.cbcDecChainedPost_local _) (Proof.Idea.cbcDecChainedPostOut_local _) (frameSat_pre _)
end VG.Proof.Idea.X86.Cbc
