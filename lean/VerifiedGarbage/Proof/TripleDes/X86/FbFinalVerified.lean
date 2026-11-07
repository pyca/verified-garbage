module

public import VerifiedGarbage.Proof.TripleDes.X86.FbVerified
public import VerifiedGarbage.Impl.TripleDes.X86.FbFinal
public import VerifiedGarbage.Spec.TripleDes.CfbFinal
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Modes.X86.SeqFinal
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.TripleDes.X86.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.X86.BlockSum
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.TripleDes.X86.FbVerified
meta import VerifiedGarbage.Impl.TripleDes.X86.FbFinal
meta import VerifiedGarbage.Spec.TripleDes.CfbFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Modes.X86.SeqFinal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.TripleDes.X86.FbFinalLit
meta import VerifiedGarbage.Proof.TripleDes.X86.BlockSum
meta import VerifiedGarbage.Proof.TripleDes.CbcBlocks
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe

/-!
# Triple DES-CFB64 of a message's last piece on x86 (32-bit) meets its contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`: the modes' CFB over a message's
last piece (`Proof.Modes.X86.cfbEncFinal_wp`, `cfbDecFinal_wp`) over Triple
DES's core in the encryption direction (`Mode.dirCoreSpec .encrypt`), with the
working space as a fifth argument: `Fb.fbX86` with steps of a byte, as
CFB8's, the data `len` bytes. Each is correct and constant time, by the taint
analysis from the same initial taint (`Fb.fbTaint`) with the block function's
summary; the `_framed` theorems run them with their working space on the
stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.FbFinal

open VG VG.X86 VG.Impl.TripleDes.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (byteMode)
open VG.Proof.TripleDes.X86.Mode (dirCoreSpec)
open VG.Proof.TripleDes.X86.Fb (ciph fbX86 fbTaint fbTaint_agree seqPre_of keyArgs_of wideContract fb_verified
  frameSat)

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (ciph s) 8 s.mem s'.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) (arg s 3).toNat
def decPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (ciph s) 8 s.mem s'.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) (arg s 3).toNat

theorem cfbEncryptFinal_wp {s₀ : State} (hp : (fbX86 1 encPost).pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 1 encPost).post s₀ s' :=
  WP.mono (Proof.Modes.X86.cfbEncFinal_wp (dirCoreSpec .encrypt)
      (seqPre_of (M := byteMode) .encrypt rfl (by decide) (by decide) hp) rfl rfl (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2⟩ => ⟨h1, h2⟩

theorem cfbDecryptFinal_wp {s₀ : State} (hp : (fbX86 1 decPost).pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 1 decPost).post s₀ s' :=
  WP.mono (Proof.Modes.X86.cfbDecFinal_wp (dirCoreSpec .encrypt)
      (seqPre_of (M := byteMode) .encrypt rfl (by decide) (by decide) hp) rfl rfl (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2⟩ => ⟨h1, h2⟩

/-! ## Constant time -/

theorem cfbEncryptFinal_ct : ConstantTime isa (fbX86 1 encPost).pre (fbX86 1 encPost).pub cfbEncryptFinal := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check fbTaint cfbEncryptFinal h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cfbDecryptFinal_ct : ConstantTime isa (fbX86 1 decPost).pre (fbX86 1 decPost).pub cfbDecryptFinal := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check fbTaint cfbDecryptFinal h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

/-! ## The contracts -/

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 1, 0x4000` at `0x8004`. -/
def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30
    else if a = 0x8010 then 1 else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩, ⟨0x4000, 944⟩, ⟨0x8004, 20⟩]

/-- Triple DES's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 384 8

/-- The final encryption's contract with the working space as an argument. -/
abbrev encScratch : Contract isa :=
  Sig.scratchContract X86.abi finalSig "scratch" .u64 118 (Curry.const (fun _ => True) _)
    (Proof.Modes.encFinalPost ciphAt 8 X86.abi.ptrBits) true 16

/-- The final decryption's contract with the working space as an argument. -/
abbrev decScratch : Contract isa :=
  Sig.scratchContract X86.abi finalSig "scratch" .u64 118 (Curry.const (fun _ => True) _)
    (Proof.Modes.decFinalPost ciphAt 8 X86.abi.ptrBits) true 16

theorem wide_implies_enc : (wideContract 1 encPost).Implies encScratch := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below,
      encPost] at h
    sig_split h
    sig_reduce [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, encPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.one_mul] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; simp only [Nat.one_mul] at *; with_reducible assumption)
  · sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, encPost,
      ciph, ciphAt]
  · sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, encPost]
  · sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, encPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_dec : (wideContract 1 decPost).Implies decScratch := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below,
      decPost] at h
    sig_split h
    sig_reduce [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, decPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.one_mul] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; simp only [Nat.one_mul] at *; with_reducible assumption)
  · sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, decPost,
      ciph, ciphAt]
  · sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, decPost]
  · sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, decPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem cfbEncryptFinal_verified : Verified X86.target cfbEncryptFinal encScratch :=
  fb_verified (fun _ hs => cfbEncryptFinal_wp hs) cfbEncryptFinal_ct (fun _ _ _ _ _ _ h => h) wide_implies_enc

theorem cfbDecryptFinal_verified : Verified X86.target cfbDecryptFinal decScratch :=
  fb_verified (fun _ hs => cfbDecryptFinal_wp hs) cfbDecryptFinal_ct (fun _ _ _ _ _ _ h => h) wide_implies_dec

theorem frameSat_pre (post : Spec.TripleDes.cfbFinalSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.cfbFinalSig.contract X86.abi (post := post) (writeArgs := true) (stack := 984)).pre s := by
  implies_sat [Spec.TripleDes.cfbFinalSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

/-- Triple DES's cipher reads only the schedule. -/
theorem ciphAt_congr : ∀ m₁ m₂ k, (∀ i < 384, m₂ (k + BitVec.ofNat 64 i) = m₁ (k + BitVec.ofNat 64 i)) →
    ciphAt m₂ k = ciphAt m₁ k := fun _ _ _ h => congrArg Spec.TripleDes.cipher (Proof.TripleDes.scheduleAt_copy h)

/-- The final CFB64 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cfbEncryptFinal)
      (Spec.TripleDes.cfbEncryptFinalContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.Modes.encFinalPost ciphAt 8 X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cfbEncryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.encFinalPost_inLocal _ ciphAt_congr) (Proof.Modes.encFinalPost_local _) (frameSat_pre _)

/-- The final CFB64 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cfbDecryptFinal)
      (Spec.TripleDes.cfbDecryptFinalContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.Modes.decFinalPost ciphAt 8 X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cfbDecryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.decFinalPost_inLocal _ ciphAt_congr) (Proof.Modes.decFinalPost_local _) (frameSat_pre _)

end VG.Proof.TripleDes.X86.FbFinal
