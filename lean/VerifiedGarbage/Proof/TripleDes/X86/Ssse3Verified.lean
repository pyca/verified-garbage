module

public import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Core
public import VerifiedGarbage.Proof.TripleDes.X86.CbcVerified
public import VerifiedGarbage.Proof.TripleDes.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86.Scrub
import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Core
meta import VerifiedGarbage.Proof.TripleDes.X86.CbcVerified
meta import VerifiedGarbage.Proof.TripleDes.X86.FbFinalVerified
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.TripleDes.X86.Scrub
meta import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Lit
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Triple DES's modes with its S-boxes by `pshufb` on x86 (32-bit) meet their contracts

`cbcEncryptChained_wp`, `ofb_wp`, `cfbEncrypt_wp`, `cfb8Encrypt_wp`,
`cfb8Decrypt_wp`, and for a message's last piece `cfbEncryptFinal_wp`,
`cfbDecryptFinal_wp`, `ofbFinal_wp`: the modes' CBC encryption that updates
the chaining value, OFB, CFB64 encryption and CFB8 (the `_of` theorems of
`CbcVerified.lean`, `FbVerified.lean` and `FbFinalVerified.lean`) over the
core of one block by `pshufb` (`ssse3CoreSpec`, `ssse3Fits`), with the
working space, 118 64-bit words, as the fifth argument (`Fb.fbX86`): the
contract, taint and narrowing (`Fb.fb_verified`) of the functions over the
other cores. Each is constant time by the taint analysis of its code with
the SSE instructions (`X86.sseTaint`); the `_framed` theorems run them with
their working space on the stack, zeroed on return.

As emitted (`Impl.TripleDes.X86.Ssse3.Fn`), each function then zeroes, of
the 996 bytes of stack its contract reserves below `esp`, the nine
doublewords that the residue analysis (`X86.rtaint`) finds it may leave
different in two runs, the header of that frame and its last three
doublewords, clears the registers a
callee may change, and returns without secret residue
(`X86.Scrub.verifiedScrubbedSel`, the kernel evaluating the analysis of the
code with its cleanup: `taint_decide_ct`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Ssse3

open VG VG.X86 VG.X86.Scrub VG.Impl.TripleDes.X86.Ssse3
open VG.Proof.TripleDes.X86.Fb (fbX86 fbTaint fbTaint_agree fb_verified ofb_wp_of cfbEncrypt_wp_of cfb8Encrypt_wp_of
  cfb8Decrypt_wp_of wide_implies_ofb wide_implies_cfbEnc wide_implies_cfb8Enc wide_implies_cfb8Dec)
open VG.Proof.TripleDes.X86.Cbc (encPost cbcEncryptChained_wp_of wide_implies_enc)

/-! ## The stack of these functions

Their frame is 980 bytes (`Impl.TripleDes.X86.Ssse3.Fn`), 12 more than the
baseline's functions', so their contracts state 996 bytes of stack for the
baseline's 984: the baseline's facts about a contract that name its stack
(`Fb.frameSat_pre`, `Scrub.ofbOut`, …), for 996 bytes. -/

theorem frameSat_cbc (post : Spec.TripleDes.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.cbcChainedSig.contract X86.abi (post := post) (writeArgs := true) (stack := 996)).pre s := by
  implies_sat [Spec.TripleDes.cbcChainedSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Fb.frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Fb.frameSat

theorem frameSat_fb (post : Spec.TripleDes.ofbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.ofbSig.contract X86.abi (post := post) (writeArgs := true) (stack := 996)).pre s := by
  implies_sat [Spec.TripleDes.ofbSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Fb.frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Fb.frameSat

theorem frameSat_fb8 (post : Spec.TripleDes.cfb8Sig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.cfb8Sig.contract X86.abi (post := post) (writeArgs := true) (stack := 996)).pre s := by
  implies_sat [Spec.TripleDes.cfb8Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Fb.frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Fb.frameSat

theorem frameSat_final (post : Spec.TripleDes.cfbFinalSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.cfbFinalSig.contract X86.abi (post := post) (writeArgs := true) (stack := 996)).pre s := by
  implies_sat [Spec.TripleDes.cfbFinalSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Fb.frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Fb.frameSat

theorem frameSat_ofbFinal (post : Spec.TripleDes.ofbFinalSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.ofbFinalSig.contract X86.abi (post := post) (writeArgs := true) (stack := 996)).pre s := by
  implies_sat [Spec.TripleDes.ofbFinalSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Fb.frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Fb.frameSat

theorem cbcEncryptOut : PostOut (Spec.TripleDes.cbcEncryptChainedContract X86.abi 996) (Spec.TripleDes.cbcChainedSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cbcEncChainedPostOut_local _)

theorem ofbOut : PostOut (Spec.TripleDes.ofbContract X86.abi 996) (Spec.TripleDes.ofbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.ofbPostOut_local _)

theorem cfbEncryptOut : PostOut (Spec.TripleDes.cfbEncryptContract X86.abi 996) (Spec.TripleDes.cfbSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfbEncPostOut_local _)

theorem cfb8EncryptOut : PostOut (Spec.TripleDes.cfb8EncryptContract X86.abi 996) (Spec.TripleDes.cfb8Sig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8EncPostOut_local _)

theorem cfb8DecryptOut : PostOut (Spec.TripleDes.cfb8DecryptContract X86.abi 996) (Spec.TripleDes.cfb8Sig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.TripleDes.cfb8DecPostOut_local _)

theorem cfbEncryptFinalOut : PostOut (Spec.TripleDes.cfbEncryptFinalContract X86.abi 996) (Spec.TripleDes.cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.encFinalPost_local _)

theorem cfbDecryptFinalOut : PostOut (Spec.TripleDes.cfbDecryptFinalContract X86.abi 996) (Spec.TripleDes.cfbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.decFinalPost_local _)

theorem ofbFinalOut : PostOut (Spec.TripleDes.ofbFinalContract X86.abi 996) (Spec.TripleDes.ofbFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Modes.ofbFinalPost_local _)

theorem cbcEncryptChained_wp {s₀ : State} (hp : (fbX86 118 8 encPost).pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 118 8 encPost).post s₀ s' :=
  cbcEncryptChained_wp_of ssse3Fits (fun _ => rfl) hp

theorem cbcEncryptChained_ct :
    ConstantTime isa (fbX86 118 8 encPost).pre (fbX86 118 8 encPost).pub cbcEncryptChained :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 118) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cbcEncryptChained_verified :
    Verified X86.target cbcEncryptChained (Proof.TripleDes.cbcEncChainedScratchContract X86.abi 118 16) :=
  fb_verified (fun _ hs => cbcEncryptChained_wp hs) cbcEncryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_enc

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 980 4 236 cbcEncryptChained)
      (Spec.TripleDes.cbcEncryptChainedContract X86.abi 996) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cbcEncChainedPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 980) cbcEncryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cbcEncChainedPost_local _) (Proof.TripleDes.cbcEncChainedPostOut_local _) (frameSat_cbc _)

theorem ofb_wp {s₀ : State} (hp : (fbX86 118 8 Fb.ofbPost).pre s₀) :
    WP isa ofb s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 118 8 Fb.ofbPost).post s₀ s' :=
  ofb_wp_of ssse3Fits (fun _ => rfl) hp

theorem ofb_ct : ConstantTime isa (fbX86 118 8 Fb.ofbPost).pre (fbX86 118 8 Fb.ofbPost).pub ofb :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 118) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem ofb_verified : Verified X86.target ofb (Proof.TripleDes.fbScratchContract X86.abi 118 Proof.TripleDes.ofbPost 16) :=
  fb_verified (fun _ hs => ofb_wp hs) ofb_ct (fun _ _ _ _ _ _ h => h) wide_implies_ofb

/-- `ofb` with its working space on the stack. -/
theorem ofb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 980 4 236 ofb)
      (Spec.TripleDes.ofbContract X86.abi 996) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.ofbSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.ofbPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 980) ofb_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.ofbPost_local _) (Proof.TripleDes.ofbPostOut_local _) (frameSat_fb _)

theorem cfbEncrypt_wp {s₀ : State} (hp : (fbX86 118 8 Fb.cfbEncPost).pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 118 8 Fb.cfbEncPost).post s₀ s' :=
  cfbEncrypt_wp_of ssse3Fits (fun _ => rfl) hp

theorem cfbEncrypt_ct : ConstantTime isa (fbX86 118 8 Fb.cfbEncPost).pre (fbX86 118 8 Fb.cfbEncPost).pub cfbEncrypt :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 118) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbEncrypt_verified : Verified X86.target cfbEncrypt (Proof.TripleDes.fbScratchContract X86.abi 118 Proof.TripleDes.cfbEncPost 16) :=
  fb_verified (fun _ hs => cfbEncrypt_wp hs) cfbEncrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfbEnc

/-- `cfbEncrypt` with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 980 4 236 cfbEncrypt)
      (Spec.TripleDes.cfbEncryptContract X86.abi 996) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cfbEncPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 980) cfbEncrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfbEncPost_local _) (Proof.TripleDes.cfbEncPostOut_local _) (frameSat_fb _)

theorem cfb8Encrypt_wp {s₀ : State} (hp : (fbX86 118 1 Fb.cfb8EncPost).pre s₀) :
    WP isa cfb8Encrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 118 1 Fb.cfb8EncPost).post s₀ s' :=
  cfb8Encrypt_wp_of ssse3Fits (fun _ => rfl) hp

theorem cfb8Encrypt_ct : ConstantTime isa (fbX86 118 1 Fb.cfb8EncPost).pre (fbX86 118 1 Fb.cfb8EncPost).pub cfb8Encrypt :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 118) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfb8Encrypt_verified : Verified X86.target cfb8Encrypt (Proof.TripleDes.cfb8ScratchContract X86.abi 118 Proof.TripleDes.cfb8EncPost 16) :=
  fb_verified (fun _ hs => cfb8Encrypt_wp hs) cfb8Encrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfb8Enc

/-- `cfb8Encrypt` with its working space on the stack. -/
theorem cfb8Encrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 980 4 236 cfb8Encrypt)
      (Spec.TripleDes.cfb8EncryptContract X86.abi 996) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cfb8EncPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 980) cfb8Encrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfb8EncPost_local _) (Proof.TripleDes.cfb8EncPostOut_local _) (frameSat_fb8 _)

theorem cfb8Decrypt_wp {s₀ : State} (hp : (fbX86 118 1 Fb.cfb8DecPost).pre s₀) :
    WP isa cfb8Decrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 118 1 Fb.cfb8DecPost).post s₀ s' :=
  cfb8Decrypt_wp_of ssse3Fits (fun _ => rfl) hp

theorem cfb8Decrypt_ct : ConstantTime isa (fbX86 118 1 Fb.cfb8DecPost).pre (fbX86 118 1 Fb.cfb8DecPost).pub cfb8Decrypt :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 118) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfb8Decrypt_verified : Verified X86.target cfb8Decrypt (Proof.TripleDes.cfb8ScratchContract X86.abi 118 Proof.TripleDes.cfb8DecPost 16) :=
  fb_verified (fun _ hs => cfb8Decrypt_wp hs) cfb8Decrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfb8Dec

/-- `cfb8Decrypt` with its working space on the stack. -/
theorem cfb8Decrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 980 4 236 cfb8Decrypt)
      (Spec.TripleDes.cfb8DecryptContract X86.abi 996) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cfb8DecPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 980) cfb8Decrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfb8DecPost_local _) (Proof.TripleDes.cfb8DecPostOut_local _) (frameSat_fb8 _)

theorem cfbEncryptFinal_wp {s₀ : State} (hp : (fbX86 118 1 FbFinal.encPost).pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 118 1 FbFinal.encPost).post s₀ s' :=
  FbFinal.cfbEncryptFinal_wp_of ssse3Fits (fun _ => rfl) hp

theorem cfbEncryptFinal_ct : ConstantTime isa (fbX86 118 1 FbFinal.encPost).pre (fbX86 118 1 FbFinal.encPost).pub cfbEncryptFinal :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 118) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbEncryptFinal_verified : Verified X86.target cfbEncryptFinal (FbFinal.encScratch) :=
  fb_verified (fun _ hs => cfbEncryptFinal_wp hs) cfbEncryptFinal_ct (fun _ _ _ _ _ _ h => h) FbFinal.wide_implies_enc

/-- `cfbEncryptFinal` with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 980 4 236 cfbEncryptFinal)
      (Spec.TripleDes.cfbEncryptFinalContract X86.abi 996) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.Modes.encFinalPost FbFinal.ciphAt 8 X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 980) cfbEncryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.encFinalPost_inLocal _ FbFinal.ciphAt_congr) (Proof.Modes.encFinalPost_local _) (frameSat_final _)

theorem cfbDecryptFinal_wp {s₀ : State} (hp : (fbX86 118 1 FbFinal.decPost).pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 118 1 FbFinal.decPost).post s₀ s' :=
  FbFinal.cfbDecryptFinal_wp_of ssse3Fits (fun _ => rfl) hp

theorem cfbDecryptFinal_ct : ConstantTime isa (fbX86 118 1 FbFinal.decPost).pre (fbX86 118 1 FbFinal.decPost).pub cfbDecryptFinal :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 118) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbDecryptFinal_verified : Verified X86.target cfbDecryptFinal (FbFinal.decScratch) :=
  fb_verified (fun _ hs => cfbDecryptFinal_wp hs) cfbDecryptFinal_ct (fun _ _ _ _ _ _ h => h) FbFinal.wide_implies_dec

/-- `cfbDecryptFinal` with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 980 4 236 cfbDecryptFinal)
      (Spec.TripleDes.cfbDecryptFinalContract X86.abi 996) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.Modes.decFinalPost FbFinal.ciphAt 8 X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 980) cfbDecryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.decFinalPost_inLocal _ FbFinal.ciphAt_congr) (Proof.Modes.decFinalPost_local _) (frameSat_final _)

theorem ofbFinal_wp {s₀ : State} (hp : (fbX86 118 1 FbFinal.ofbPost).pre s₀) :
    WP isa ofbFinal s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 118 1 FbFinal.ofbPost).post s₀ s' :=
  FbFinal.ofbFinal_wp_of ssse3Fits (fun _ => rfl) hp

theorem ofbFinal_ct : ConstantTime isa (fbX86 118 1 FbFinal.ofbPost).pre (fbX86 118 1 FbFinal.ofbPost).pub ofbFinal :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (fbTaint 118) (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem ofbFinal_verified : Verified X86.target ofbFinal (FbFinal.ofbScratch) :=
  fb_verified (fun _ hs => ofbFinal_wp hs) ofbFinal_ct (fun _ _ _ _ _ _ h => h) FbFinal.wide_implies_ofb

/-- `ofbFinal` with its working space on the stack. -/
theorem ofbFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 980 4 236 ofbFinal)
      (Spec.TripleDes.ofbFinalContract X86.abi 996) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.ofbFinalSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.Modes.ofbFinalPost FbFinal.ciphAt 8 X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 980) ofbFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.ofbFinalPost_inLocal _ FbFinal.ciphAt_congr) (Proof.Modes.ofbFinalPost_local _) (frameSat_ofbFinal _)

/-! ## The functions as emitted -/

/-- `Spec.TripleDes.cbcEncryptChainedApi` as emitted (`Impl.TripleDes.X86.Ssse3.Fn.cbcEncryptChained`)
meets its contract in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Fn.cbcEncryptChained (Spec.TripleDes.cbcEncryptChainedContract X86.abi 996) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cbcEncryptChainedApi) (W := 996)
    { code := Impl.StackScratch.X86.withStackScratchWiped 980 4 236 cbcEncryptChained
      verified := cbcEncryptChained_framed }
    Fn.words cbcEncryptOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.ofbApi` as emitted (`Impl.TripleDes.X86.Ssse3.Fn.ofb`) meets its contract in constant time
and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Fn.ofb (Spec.TripleDes.ofbContract X86.abi 996) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ofbApi) (W := 996)
    { code := Impl.StackScratch.X86.withStackScratchWiped 980 4 236 ofb
      verified := ofb_framed }
    Fn.words ofbOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.cfbEncryptApi` as emitted (`Impl.TripleDes.X86.Ssse3.Fn.cfbEncrypt`) meets its contract in constant time
and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Fn.cfbEncrypt (Spec.TripleDes.cfbEncryptContract X86.abi 996) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfbEncryptApi) (W := 996)
    { code := Impl.StackScratch.X86.withStackScratchWiped 980 4 236 cfbEncrypt
      verified := cfbEncrypt_framed }
    Fn.words cfbEncryptOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.cfb8EncryptApi` as emitted (`Impl.TripleDes.X86.Ssse3.Fn.cfb8Encrypt`) meets its contract in constant time
and returns without secret residue. -/
theorem cfb8Encrypt_scrubbed :
    VerifiedScrubbed X86.target Fn.cfb8Encrypt (Spec.TripleDes.cfb8EncryptContract X86.abi 996) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfb8EncryptApi) (W := 996)
    { code := Impl.StackScratch.X86.withStackScratchWiped 980 4 236 cfb8Encrypt
      verified := cfb8Encrypt_framed }
    Fn.words cfb8EncryptOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.cfb8DecryptApi` as emitted (`Impl.TripleDes.X86.Ssse3.Fn.cfb8Decrypt`) meets its contract in constant time
and returns without secret residue. -/
theorem cfb8Decrypt_scrubbed :
    VerifiedScrubbed X86.target Fn.cfb8Decrypt (Spec.TripleDes.cfb8DecryptContract X86.abi 996) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfb8DecryptApi) (W := 996)
    { code := Impl.StackScratch.X86.withStackScratchWiped 980 4 236 cfb8Decrypt
      verified := cfb8Decrypt_framed }
    Fn.words cfb8DecryptOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.cfbEncryptFinalApi` as emitted (`Impl.TripleDes.X86.Ssse3.Fn.cfbEncryptFinal`) meets its contract in constant time
and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Fn.cfbEncryptFinal (Spec.TripleDes.cfbEncryptFinalContract X86.abi 996) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfbEncryptFinalApi) (W := 996)
    { code := Impl.StackScratch.X86.withStackScratchWiped 980 4 236 cfbEncryptFinal
      verified := cfbEncryptFinal_framed }
    Fn.words cfbEncryptFinalOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.cfbDecryptFinalApi` as emitted (`Impl.TripleDes.X86.Ssse3.Fn.cfbDecryptFinal`) meets its contract in constant time
and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Fn.cfbDecryptFinal (Spec.TripleDes.cfbDecryptFinalContract X86.abi 996) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.cfbDecryptFinalApi) (W := 996)
    { code := Impl.StackScratch.X86.withStackScratchWiped 980 4 236 cfbDecryptFinal
      verified := cfbDecryptFinal_framed }
    Fn.words cfbDecryptFinalOut (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.TripleDes.ofbFinalApi` as emitted (`Impl.TripleDes.X86.Ssse3.Fn.ofbFinal`) meets its contract in constant time
and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Fn.ofbFinal (Spec.TripleDes.ofbFinalContract X86.abi 996) 0 :=
  verifiedScrubbedSel (api := Spec.TripleDes.ofbFinalApi) (W := 996)
    { code := Impl.StackScratch.X86.withStackScratchWiped 980 4 236 ofbFinal
      verified := ofbFinal_framed }
    Fn.words ofbFinalOut (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.TripleDes.X86.Ssse3
