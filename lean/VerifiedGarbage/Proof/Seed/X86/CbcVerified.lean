module

public import VerifiedGarbage.Proof.Seed.X86.FbVerified
import VerifiedGarbage.Proof.Modes.X86.CbcChained
public import VerifiedGarbage.Proof.Seed.CbcScratch
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Seed.X86.CbcLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Seed.SboxLit
meta import VerifiedGarbage.Proof.Seed.X86.FbVerified
meta import VerifiedGarbage.Proof.Modes.X86.CbcChained
meta import VerifiedGarbage.Proof.Seed.CbcScratch
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Seed.X86.CbcLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Seed.SboxLit
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# SEED-CBC on x86 (32-bit) meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value (`Proof.Modes.X86.cbcEncChained_wp`, `cbcDecChained_wp`)
over SEED's core for each direction (`dirCoreSpec`), with the working space
as a fifth argument. The chaining value is written back, so it is writable,
as for OFB and CFB128 (`Fb.fbX86`), whose contract, taint, summary of the
loop of rounds and narrowing (`Fb.fb_verified`) these share. The `_framed`
theorems run them with their working space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Seed.X86.Cbc

open VG VG.X86 VG.Impl.Seed.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (cbcEncChained_wp cbcDecChained_wp)
open VG.Proof.Seed.X86 (dirCoreSpec)
open VG.Proof.Seed.X86.Fb

/-- SEED's inverse under the schedule at the first argument. -/
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Seed.invCipher (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64))

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def decPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

attribute [local irreducible] Spec.Seed.invCipher in
theorem invCipher_eq (s : State) :
    (dirCoreSpec .decrypt).cipher (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64)) = invCiph s := rfl

theorem cbcEncryptChained_wp {s₀ : State} (hp : (fbX86 encPost).pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 encPost).post s₀ s' :=
  WP.mono (cbcEncChained_wp (dirCoreSpec .encrypt) (seqPre_of .encrypt rfl hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem cbcDecryptChained_wp {s₀ : State} (hp : (fbX86 decPost).pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 decPost).post s₀ s' :=
  WP.mono (cbcDecChained_wp (dirCoreSpec .decrypt) (seqPre_of .decrypt rfl hp) (keyArgs_of .decrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, invCipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

/-! ## Constant time -/

theorem cbcEncryptChained_ct :
    ConstantTime isa (fbX86 encPost).pre (fbX86 encPost).pub cbcEncryptChained :=
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by native_taint_decide)

theorem cbcDecryptChained_ct :
    ConstantTime isa (fbX86 decPost).pre (fbX86 decPost).pub cbcDecryptChained :=
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by native_taint_decide)

/-! ## The contracts -/

theorem wide_implies_enc :
    (Fb.wideContract encPost).Implies (Proof.Seed.cbcEncChainedScratchContract X86.abi 143 20) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Seed.cbcEncChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, fbX86, encPost] at h
    sig_split h
    sig_reduce [Proof.Seed.cbcEncChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, fbX86, encPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Seed.cbcEncChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, fbX86, encPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Seed.cbcEncChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, fbX86, encPost]
  · sig_implies_sat [Proof.Seed.cbcEncChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, fbX86, encPost]
      [Fb.satState, arg, argAddr, Mem.readW, Mem.read] using Fb.satState

theorem wide_implies_dec :
    (Fb.wideContract decPost).Implies (Proof.Seed.cbcDecChainedScratchContract X86.abi 143 20) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, fbX86, decPost] at h
    sig_split h
    sig_reduce [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, fbX86, decPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, fbX86, decPost, invCiph, ivAt, dataAt]
  · sig_implies_pub [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, fbX86, decPost]
  · sig_implies_sat [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, fbX86, decPost]
      [Fb.satState, arg, argAddr, Mem.readW, Mem.read] using Fb.satState

/-- A state satisfying the functions' precondition: the schedule at `0x1000`,
the chaining value at `0x2000`, and no blocks at `0x3000`, as stack arguments
at `0x8004`, which are writable. -/
theorem frameSat_pre (post : Spec.Seed.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Seed.cbcChainedSig.contract X86.abi (post := post) (writeArgs := true) (stack := 1188)).pre s := by
  implies_sat [Spec.Seed.cbcChainedSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem cbcEncryptChained_verified :
    Verified X86.target cbcEncryptChained (Proof.Seed.cbcEncChainedScratchContract X86.abi 143 20) :=
  fb_verified (fun _ hs => cbcEncryptChained_wp hs) cbcEncryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_enc

theorem cbcDecryptChained_verified :
    Verified X86.target cbcDecryptChained (Proof.Seed.cbcDecChainedScratchContract X86.abi 143 20) :=
  fb_verified (fun _ hs => cbcDecryptChained_wp hs) cbcDecryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_dec

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 cbcEncryptChained)
      (Spec.Seed.cbcEncryptChainedContract X86.abi 1188) :=
  X86.Verified.stackScratchWiped (sig := Spec.Seed.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 143) (post := Proof.Seed.cbcEncChainedPost X86.abi.ptrBits) (wa := true) (stack := 20)
    (bytes := 1168) cbcEncryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.cbcEncChainedPost_local _) (Proof.Seed.cbcEncChainedPostOut_local _) (frameSat_pre _)

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 cbcDecryptChained)
      (Spec.Seed.cbcDecryptChainedContract X86.abi 1188) :=
  X86.Verified.stackScratchWiped (sig := Spec.Seed.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 143) (post := Proof.Seed.cbcDecChainedPost X86.abi.ptrBits) (wa := true) (stack := 20)
    (bytes := 1168) cbcDecryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.cbcDecChainedPost_local _) (Proof.Seed.cbcDecChainedPostOut_local _) (frameSat_pre _)

end VG.Proof.Seed.X86.Cbc
