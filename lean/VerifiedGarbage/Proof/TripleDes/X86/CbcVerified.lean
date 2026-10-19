module

public import VerifiedGarbage.Proof.TripleDes.X86.FbVerified
meta import VerifiedGarbage.Proof.TripleDes.X86.FbVerified
import VerifiedGarbage.Proof.Modes.X86.CbcChained
meta import VerifiedGarbage.Proof.Modes.X86.CbcChained
public import VerifiedGarbage.Proof.TripleDes.CbcScratch
meta import VerifiedGarbage.Proof.TripleDes.CbcScratch
public import VerifiedGarbage.Proof.TripleDes.X86.CbcLit
meta import VerifiedGarbage.Proof.TripleDes.X86.CbcLit
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.AesSiv.Words
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Modes.StepsChained
import VerifiedGarbage.Proof.Modes.X86.Counter
import VerifiedGarbage.Proof.Modes.X86.Ops
import VerifiedGarbage.Proof.Rc2.Select
import VerifiedGarbage.Proof.Rc2.Select32
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Rc2.Word32
import VerifiedGarbage.Proof.Rc2.X86.BlockArgs
import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
import VerifiedGarbage.Proof.Rc2.X86.KeyIO
import VerifiedGarbage.Proof.Rc2.X86.KeyLookup
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.EcbMemory
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.X86.BlockCT
import VerifiedGarbage.Proof.TripleDes.X86.Bytes
import VerifiedGarbage.Proof.TripleDes.X86.RestoredOutput
import VerifiedGarbage.Proof.TripleDes.X86.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.X86.WordStore
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.AesCcm.Mac
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.AesSiv.Ctr32
meta import VerifiedGarbage.Proof.AesSiv.Words
meta import VerifiedGarbage.Proof.Cmac.Dbl32
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Modes.StepsChained
meta import VerifiedGarbage.Proof.Modes.X86.Counter
meta import VerifiedGarbage.Proof.Modes.X86.Ops
meta import VerifiedGarbage.Proof.Rc2.Select
meta import VerifiedGarbage.Proof.Rc2.Select32
meta import VerifiedGarbage.Proof.Rc2.Word
meta import VerifiedGarbage.Proof.Rc2.Word32
meta import VerifiedGarbage.Proof.Rc2.X86.BlockArgs
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
meta import VerifiedGarbage.Proof.Rc2.X86.KeyIO
meta import VerifiedGarbage.Proof.Rc2.X86.KeyLookup
meta import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
meta import VerifiedGarbage.Proof.TripleDes.Bytes
meta import VerifiedGarbage.Proof.TripleDes.EcbMemory
meta import VerifiedGarbage.Proof.TripleDes.Permutation
meta import VerifiedGarbage.Proof.TripleDes.Round
meta import VerifiedGarbage.Proof.TripleDes.Schedule
meta import VerifiedGarbage.Proof.TripleDes.Word
meta import VerifiedGarbage.Proof.TripleDes.X86.BlockCT
meta import VerifiedGarbage.Proof.TripleDes.X86.Bytes
meta import VerifiedGarbage.Proof.TripleDes.X86.RestoredOutput
meta import VerifiedGarbage.Proof.TripleDes.X86.VerifiedBlock
meta import VerifiedGarbage.Proof.TripleDes.X86.WordStore
meta import VerifiedGarbage.Spec.Ctr.Contract

/-!
# Triple DES-CBC on x86 (32-bit) meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value (`Proof.Modes.X86.cbcEncChained_wp`, `cbcDecChained_wp`)
over Triple DES's core for each direction (`dirCoreSpec`), with the working
space as the fifth argument. The chaining value is written back, so it is
writable, as for OFB and CFB (`Fb.fbX86`), whose contract, taint and
narrowing (`Fb.fb_verified`) these share; encryption's analysis reads the
summary of the block function's call (`encSum`). The `_framed` theorems run
them with their working space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Cbc

open VG VG.X86 VG.Impl.TripleDes.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (cbcEncChained_wp cbcDecChained_wp)
open VG.Proof.TripleDes.X86.Mode (dirCoreSpec KeyArgs)
open VG.Proof.TripleDes.X86.Fb

/-- Triple DES decryption under the schedule at the first argument. -/
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.TripleDes.invCipher (Spec.TripleDes.scheduleAt s.mem ((arg s 0).setWidth 64))

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def decPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

theorem invCipher_eq (s : State) :
    (dirCoreSpec .decrypt).cipher (Spec.TripleDes.scheduleAt s.mem ((arg s 0).setWidth 64)) = invCiph s := rfl

theorem cbcEncryptChained_wp {s₀ : State} (hp : (fbX86 8 encPost).pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 8 encPost).post s₀ s' :=
  WP.mono (cbcEncChained_wp (dirCoreSpec .encrypt) (seqPre_of .encrypt rfl (by decide) (by decide) hp)
      (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by tdes_post_eq h2 h3; exact ⟨h1, h2, h3⟩

theorem cbcDecryptChained_wp {s₀ : State} (hp : (fbX86 8 decPost).pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 8 decPost).post s₀ s' :=
  WP.mono (cbcDecChained_wp (dirCoreSpec .decrypt) (seqPre_of .decrypt rfl (by decide) (by decide) hp)
      (keyArgs_of .decrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, invCipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

/-! ## Constant time -/

theorem cbcEncryptChained_ct :
    ConstantTime isa (fbX86 8 encPost).pre (fbX86 8 encPost).pub cbcEncryptChained := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check fbTaint cbcEncryptChained h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cbcDecryptChained_ct :
    ConstantTime isa (fbX86 8 decPost).pre (fbX86 8 decPost).pub cbcDecryptChained :=
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The contracts -/

theorem wide_implies_enc :
    (wideContract 8 encPost).Implies (Proof.TripleDes.cbcEncChainedScratchContract X86.abi 118 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; try simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, encPost, ciph, ivAt, dataAt, bytesOf]
  · sig_implies_pub [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
  · sig_implies_sat [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_dec :
    (wideContract 8 decPost).Implies (Proof.TripleDes.cbcDecChainedScratchContract X86.abi 118 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; try simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, decPost, invCiph, ivAt, dataAt, bytesOf]
  · sig_implies_pub [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
  · sig_implies_sat [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem frameSat_pre (post : Spec.TripleDes.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.cbcChainedSig.contract X86.abi (post := post) (writeArgs := true) (stack := 984)).pre s := by
  implies_sat [Spec.TripleDes.cbcChainedSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem cbcEncryptChained_verified :
    Verified X86.target cbcEncryptChained (Proof.TripleDes.cbcEncChainedScratchContract X86.abi 118 16) :=
  fb_verified (fun _ hs => cbcEncryptChained_wp hs) cbcEncryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_enc

theorem cbcDecryptChained_verified :
    Verified X86.target cbcDecryptChained (Proof.TripleDes.cbcDecChainedScratchContract X86.abi 118 16) :=
  fb_verified (fun _ hs => cbcDecryptChained_wp hs) cbcDecryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_dec

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cbcEncryptChained)
      (Spec.TripleDes.cbcEncryptChainedContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cbcEncChainedPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cbcEncryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cbcEncChainedPost_local _) (Proof.TripleDes.cbcEncChainedPostOut_local _) (frameSat_pre _)

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cbcDecryptChained)
      (Spec.TripleDes.cbcDecryptChainedContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cbcDecChainedPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cbcDecryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cbcDecChainedPost_local _) (Proof.TripleDes.cbcDecChainedPostOut_local _) (frameSat_pre _)

end VG.Proof.TripleDes.X86.Cbc
