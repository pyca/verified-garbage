module

public import VerifiedGarbage.Proof.Sm4.X86.FbVerified
meta import VerifiedGarbage.Proof.Sm4.X86.FbVerified
import VerifiedGarbage.Proof.Modes.X86.CbcChained
meta import VerifiedGarbage.Proof.Modes.X86.CbcChained
public import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Proof.Sm4.CbcScratch
public import VerifiedGarbage.Proof.Sm4.X86.CbcLit
meta import VerifiedGarbage.Proof.Sm4.X86.CbcLit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Modes.StepsChained
import VerifiedGarbage.Proof.Modes.X86.Counter
import VerifiedGarbage.Proof.Modes.X86.Ops
import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Sm4.Planes
import VerifiedGarbage.Proof.Sm4.X86.Copy
import VerifiedGarbage.Proof.Sm4.X86.Crypt8
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Proof.AesCtr.Inc
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Modes.StepsChained
meta import VerifiedGarbage.Proof.Modes.X86.Counter
meta import VerifiedGarbage.Proof.Modes.X86.Ops
meta import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
meta import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.Sm4.Layout
meta import VerifiedGarbage.Proof.Sm4.Planes
meta import VerifiedGarbage.Proof.Sm4.X86.Copy
meta import VerifiedGarbage.Proof.Sm4.X86.Crypt8
meta import VerifiedGarbage.Spec.Ctr.Contract

/-!
# SM4-CBC on x86 (32-bit) meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value (`Proof.Modes.X86.cbcEncChained_wp`, `cbcDecChained_wp`)
over SM4's core for each direction (`dirCoreSpec`), with the working space
as a fifth argument. The chaining value is written back, so it is writable,
as for OFB and CFB (`Fb.fbX86`), whose contract, taint and narrowing these
share; the taint analysis knows the argument words holding the addresses of
the data, the chaining value and the scratch buffer as the base addresses of
the writable regions. The `_framed` theorems run them with their working
space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.Cbc

open VG VG.X86 VG.Impl.Sm4.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (SeqPre cbcEncChained_wp cbcDecChained_wp)
open VG.Proof.Sm4.X86 (dirCoreSpec dirCoreSpec_cipher)
open VG.Proof.Sm4.X86.Fb (fbX86 ciph ivAt dataAt fbTaint fbTaint_agree wideContract fb_verified satState frameSat
  seqPre_of keyArgs_of)

/-- SM4's inverse under the schedule at the first argument. -/
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Sm4.invCipher (Spec.Sm4.scheduleAt s.mem ((arg s 0).setWidth 64))

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def decPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

theorem dirCore_ka (d : Dir) : (dirCore d).ka = 1 := rfl

theorem data_eq (d : Dir) (m : Mem) (s : State) :
    Proof.Modes.chunksAt (4 * (dirCore d).bw) m ((arg s 2).setWidth 64) (arg s 3).toNat = dataAt m s := rfl
theorem iv_eq (d : Dir) (m : Mem) (s : State) :
    Spec.Aes.bytesAt m ((arg s 1).setWidth 64) (4 * (dirCore d).bw) = ivAt m s := rfl
theorem cipher_enc (s : State) :
    (dirCoreSpec .encrypt).cipher (Spec.Sm4.scheduleAt s.mem ((arg s 0).setWidth 64)) = ciph s := by
  rw [dirCoreSpec_cipher]; rfl
theorem cipher_dec (s : State) :
    (dirCoreSpec .decrypt).cipher (Spec.Sm4.scheduleAt s.mem ((arg s 0).setWidth 64)) = invCiph s := by
  rw [dirCoreSpec_cipher]; rfl

theorem cbcEncryptChained_wp {s₀ : State} (hp : (fbX86 encPost).pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 encPost).post s₀ s' :=
  WP.mono (cbcEncChained_wp (dirCoreSpec .encrypt) (seqPre_of .encrypt rfl hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_enc] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem cbcDecryptChained_wp {s₀ : State} (hp : (fbX86 decPost).pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 decPost).post s₀ s' :=
  WP.mono (cbcDecChained_wp (dirCoreSpec .decrypt) (seqPre_of .decrypt rfl hp) (keyArgs_of .decrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_dec] at h2 h3
      exact ⟨h1, h2, h3⟩

/-! ## Constant time -/

theorem cbcEncryptChained_ct : ConstantTime isa (fbX86 encPost).pre (fbX86 encPost).pub cbcEncryptChained :=
  VG.Taint.constantTime_of_exists (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide_sum [prepSum, cryptSum])

theorem cbcDecryptChained_ct : ConstantTime isa (fbX86 decPost).pre (fbX86 decPost).pub cbcDecryptChained :=
  VG.Taint.constantTime_of_exists (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide_sum [prepSum, cryptSum])

/-! ## The contracts -/

theorem wide_implies_enc :
    (wideContract encPost).Implies (Proof.Sm4.cbcEncChainedScratchContract X86.abi 184 20) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, encPost] at h
    sig_split h
    sig_reduce [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, encPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; try simp only [Nat.mul_comm] at *
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, encPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, encPost]
  · sig_implies_sat [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, encPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_dec :
    (wideContract decPost).Implies (Proof.Sm4.cbcDecChainedScratchContract X86.abi 184 20) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, decPost] at h
    sig_split h
    sig_reduce [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, decPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; try simp only [Nat.mul_comm] at *
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, decPost, ciph, invCiph, ivAt, dataAt]
  · sig_implies_pub [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, decPost]
  · sig_implies_sat [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, decPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem frameSat_pre (post : Spec.Sm4.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Sm4.cbcChainedSig.contract X86.abi (post := post) (writeArgs := true) (stack := 1516)).pre s := by
  implies_sat [Spec.Sm4.cbcChainedSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem cbcEncryptChained_verified :
    Verified X86.target cbcEncryptChained (Proof.Sm4.cbcEncChainedScratchContract X86.abi 184 20) :=
  fb_verified (fun _ hs => cbcEncryptChained_wp hs) cbcEncryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_enc

theorem cbcDecryptChained_verified :
    Verified X86.target cbcDecryptChained (Proof.Sm4.cbcDecChainedScratchContract X86.abi 184 20) :=
  fb_verified (fun _ hs => cbcDecryptChained_wp hs) cbcDecryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_dec

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 cbcEncryptChained)
      (Spec.Sm4.cbcEncryptChainedContract X86.abi 1516) :=
  X86.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 184) (post := Proof.Sm4.cbcEncChainedPost X86.abi.ptrBits) (wa := true) (stack := 20)
    (bytes := 1496) cbcEncryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.cbcEncChainedPost_local _) (Proof.Sm4.cbcEncChainedPostOut_local _) (frameSat_pre _)

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 cbcDecryptChained)
      (Spec.Sm4.cbcDecryptChainedContract X86.abi 1516) :=
  X86.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 184) (post := Proof.Sm4.cbcDecChainedPost X86.abi.ptrBits) (wa := true) (stack := 20)
    (bytes := 1496) cbcDecryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.cbcDecChainedPost_local _) (Proof.Sm4.cbcDecChainedPostOut_local _) (frameSat_pre _)

end VG.Proof.Sm4.X86.Cbc
