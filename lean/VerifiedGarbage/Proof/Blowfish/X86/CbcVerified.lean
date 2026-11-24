module

import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Blowfish.X86.FbVerified
import VerifiedGarbage.Proof.Modes.X86.CbcChained
public import VerifiedGarbage.Proof.Blowfish.CbcScratch
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Blowfish.X86.ModesLit
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Blowfish.X86.FbVerified
meta import VerifiedGarbage.Proof.Modes.X86.CbcChained
meta import VerifiedGarbage.Proof.Blowfish.CbcScratch
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Blowfish.X86.ModesLit

/-!
# Blowfish-CBC on x86 (32-bit) meets its contracts

`cbcEncryptChained_wp_of`, `cbcDecryptChained_wp_of`: the modes' CBC that
updates the chaining value (`Proof.Modes.X86.cbcEncChained_wp`,
`cbcDecChained_wp`) over any core that fits (`Fits`) whose cipher is
Blowfish's or its inverse; `cbcEncryptChained_wp`, `cbcDecryptChained_wp`
are those of Blowfish's core for each direction (`dirCoreSpec`), with the
working space as the argument after `n`. The chaining value is written back, so it is
writable, as for OFB and CFB (`Fb.fbX86`), whose contract, taint and
narrowing (`Fb.fb_verified`) these share. The `_framed` theorems run them
with their working space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86.Cbc

open VG VG.X86 VG.Impl.Blowfish.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (cbcEncChained_wp cbcDecChained_wp)
open VG.Proof.Blowfish.X86 (scr_eq disjoint_empty KeyArgs Fits dirFits below0 dirCoreSpec cbcBlocksAt_chunks)
open VG.Proof.Blowfish.X86.Fb

/-- Blowfish's inverse under the schedule at the first argument. -/
abbrev invCiph (s : State) : Spec.Cbc.Cipher := Spec.Blowfish.invCipher (Spec.Blowfish.scheduleAt s.mem ((arg s 0).setWidth 64))

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def decPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

section
variable {c : VG.Impl.Modes.X86.Core} {cs : Proof.Modes.X86.CoreSpec c} {w n : Nat}

/-- CBC encryption that updates the chaining value, over any core that
fits, whose cipher is Blowfish's. -/
theorem cbcEncryptChained_wp_of (f : Fits cs w n) (hc : ∀ k, cs.cipher (f.toKey k) = Spec.Blowfish.cipher k)
    {s₀ : State} (hp : (fbX86 w n encPost).pre s₀) :
    WP isa (c.seq (Mode.cbcEncChained c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 w n encPost).post s₀ s' :=
  WP.mono (cbcEncChained_wp cs (seqPre_of f (step_block f) hp) (keyArgs_of f hp))
    fun _ ⟨h1, h2, h3⟩ => by bf_post_eq f hc h2 h3; exact ⟨h1, h2, h3⟩

/-- CBC decryption that updates the chaining value, over any core that
fits, whose cipher is Blowfish's inverse. -/
theorem cbcDecryptChained_wp_of (f : Fits cs w n) (hc : ∀ k, cs.cipher (f.toKey k) = Spec.Blowfish.invCipher k)
    {s₀ : State} (hp : (fbX86 w n decPost).pre s₀) :
    WP isa (c.seq (Mode.cbcDecChained c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 w n decPost).post s₀ s' :=
  WP.mono (cbcDecChained_wp cs (seqPre_of f (step_block f) hp) (keyArgs_of f hp))
    fun _ ⟨h1, h2, h3⟩ => by bf_post_eq f hc h2 h3; exact ⟨h1, h2, h3⟩

end

theorem cbcEncryptChained_wp {s₀ : State} (hp : (fbX86 11 0 encPost).pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 11 0 encPost).post s₀ s' :=
  cbcEncryptChained_wp_of (dirFits true) (fun _ => rfl) hp

theorem cbcDecryptChained_wp {s₀ : State} (hp : (fbX86 11 0 decPost).pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 11 0 decPost).post s₀ s' :=
  cbcDecryptChained_wp_of (dirFits false) (fun _ => rfl) hp

/-! ## Constant time -/

theorem cbcEncryptChained_ct : ConstantTime isa (fbX86 11 0 encPost).pre (fbX86 11 0 encPost).pub cbcEncryptChained :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 11 0) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cbcDecryptChained_ct : ConstantTime isa (fbX86 11 0 decPost).pre (fbX86 11 0 decPost).pub cbcDecryptChained :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 11 0) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The contracts -/

theorem wide_implies_enc :
    (wideContract 11 0 encPost).Implies (Proof.Blowfish.cbcEncChainedScratchContract X86.abi 11) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost] at h
    sig_split h
    sig_reduce [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | with_reducible exact below0 _ _
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost]
  · sig_implies_sat [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_dec :
    (wideContract 11 0 decPost).Implies (Proof.Blowfish.cbcDecChainedScratchContract X86.abi 11) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost] at h
    sig_split h
    sig_reduce [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | with_reducible exact below0 _ _
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost, invCiph, ivAt, dataAt]
  · sig_implies_pub [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost]
  · sig_implies_sat [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem frameSat_pre (post : Spec.Blowfish.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Blowfish.cbcChainedSig.contract X86.abi (post := post) (writeArgs := true) (stack := 112)).pre s := by
  implies_sat [Spec.Blowfish.cbcChainedSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem cbcEncryptChained_verified :
    Verified X86.target cbcEncryptChained (Proof.Blowfish.cbcEncChainedScratchContract X86.abi 11) :=
  fb_verified (fun _ hs => cbcEncryptChained_wp hs) cbcEncryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_enc

theorem cbcDecryptChained_verified :
    Verified X86.target cbcDecryptChained (Proof.Blowfish.cbcDecChainedScratchContract X86.abi 11) :=
  fb_verified (fun _ hs => cbcDecryptChained_wp hs) cbcDecryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_dec

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 cbcEncryptChained)
      (Spec.Blowfish.cbcEncryptChainedContract X86.abi 112) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 11) (post := Proof.Blowfish.cbcEncChainedPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 112) cbcEncryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.cbcEncChainedPost_local _) (Proof.Blowfish.cbcEncChainedPostOut_local _) (frameSat_pre _)

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 112 4 22 cbcDecryptChained)
      (Spec.Blowfish.cbcDecryptChainedContract X86.abi 112) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 11) (post := Proof.Blowfish.cbcDecChainedPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 112) cbcDecryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.cbcDecChainedPost_local _) (Proof.Blowfish.cbcDecChainedPostOut_local _) (frameSat_pre _)
end VG.Proof.Blowfish.X86.Cbc
