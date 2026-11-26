module

public import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Core
public import VerifiedGarbage.Proof.Blowfish.X86.CbcVerified
public import VerifiedGarbage.Proof.Blowfish.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Blowfish.Contract
import VerifiedGarbage.Proof.Blowfish.X86.Scrub
import VerifiedGarbage.Proof.Blowfish.X86.Frame
import VerifiedGarbage.Proof.Blowfish.Scratch
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Core
meta import VerifiedGarbage.Proof.Blowfish.X86.CbcVerified
meta import VerifiedGarbage.Proof.Blowfish.X86.FbFinalVerified
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Blowfish.Contract
meta import VerifiedGarbage.Proof.Blowfish.X86.Scrub
meta import VerifiedGarbage.Proof.Blowfish.X86.Frame
meta import VerifiedGarbage.Proof.Blowfish.Scratch
meta import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Lit
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.TaintCTAll
public meta import VerifiedGarbage.Proof.Framework.TaintCTAll

/-!
# Blowfish's functions over its block function by `pshufb` on x86 (32-bit) meet their contracts

`cbcEncryptChained_wp`, `ofb_wp`, `cfbEncrypt_wp`, and for
a message's last piece `cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`,
`ofbFinal_wp`: the modes' CBC encryption that updates the chaining value,
OFB and CFB64 (the `_of` theorems of `CbcVerified.lean`, `FbVerified.lean`
and `FbFinalVerified.lean`) over the core that calls the block function
(`ssse3CoreSpec`, `ssse3Fits`), with the working space, 53 64-bit words, as
the fifth argument and eight bytes of stack (`Fb.fbX86`, `FbFinal.finalX86`):
the contract, taint and narrowing (`Fb.fb_verified`, `FbFinal.final_verified`)
of the functions over the baseline's core. Each is constant time by the
taint analysis of its code with the SSE instructions (`X86.sseTaint`), which
analyses the block function at its call; the `_framed` theorems run them
with their working space on the stack, zeroed on return.

As emitted (`Impl.Blowfish.X86.Ssse3.Fn`), each function then zeroes, of the
460 bytes of stack its contract reserves below `esp`, the eight doublewords
that the residue analysis (`X86.rtaint`) finds it may leave different in two
runs (the block function's return address, the header of the working
space's frame and the frame's last doubleword), clears the registers a callee may change, and returns
without secret residue (`X86.Scrub.verifiedScrubbedSel`, the kernel
evaluating the analysis of the code with its cleanup: `taint_decide_ct`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86.Ssse3

open VG VG.X86 VG.X86.Scrub VG.Impl.Blowfish.X86.Ssse3

/-! ## States that satisfy the contracts -/

/-- Memory holding the arguments `0x5000, 0x2000, 0x3000, 0, 0x4000` at `0x8004`. -/
def sat53 : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x50 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30
    else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x5000, 4168⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 424⟩, ⟨0x8004, 20⟩]

/-- Memory holding the arguments `0x5000, 0x2000, 0x3000, 1, 0x4000` at `0x8004`. -/
def satF53 : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x50 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30
    else if a = 0x8010 then 1 else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x5000, 4168⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩, ⟨0x4000, 424⟩, ⟨0x8004, 20⟩]

theorem frameSat_ofb (post : Spec.Blowfish.ofbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Blowfish.ofbSig.contract X86.abi (post := post) (writeArgs := true) (stack := 460)).pre s := by
  implies_sat [Spec.Blowfish.ofbSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Fb.frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Fb.frameSat

theorem frameSat_cbc (post : Spec.Blowfish.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Blowfish.cbcChainedSig.contract X86.abi (post := post) (writeArgs := true) (stack := 460)).pre s := by
  implies_sat [Spec.Blowfish.cbcChainedSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Fb.frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Fb.frameSat

theorem frameSat_cfbFinal (post : Spec.Blowfish.cfbFinalSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Blowfish.cfbFinalSig.contract X86.abi (post := post) (writeArgs := true) (stack := 460)).pre s := by
  implies_sat [Spec.Blowfish.cfbFinalSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Fb.frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Fb.frameSat

theorem frameSat_ofbFinal (post : Spec.Blowfish.ofbFinalSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Blowfish.ofbFinalSig.contract X86.abi (post := post) (writeArgs := true) (stack := 460)).pre s := by
  implies_sat [Spec.Blowfish.ofbFinalSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Fb.frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Fb.frameSat

/-- The eight bytes below `sp`, as the contracts state them. -/
theorem below8 {sp : BitVec 32} (h : 8 ≤ sp.toNat) : below sp 8 = ⟨sp.setWidth 64 - 8#64, 8⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]

/-- The final functions' contracts with the working space as an argument. -/
abbrev encScratch : Contract isa :=
  Sig.scratchContract X86.abi FbFinal.finalSig "scratch" .u64 53 (Curry.const (fun _ => True) _)
    (Proof.Modes.encFinalPost FbFinal.ciphAt 8 X86.abi.ptrBits) true 8

abbrev decScratch : Contract isa :=
  Sig.scratchContract X86.abi FbFinal.finalSig "scratch" .u64 53 (Curry.const (fun _ => True) _)
    (Proof.Modes.decFinalPost FbFinal.ciphAt 8 X86.abi.ptrBits) true 8

abbrev ofbScratch : Contract isa :=
  Sig.scratchContract X86.abi FbFinal.finalSig "scratch" .u64 53 (Curry.const (fun _ => True) _)
    (Proof.Modes.ofbFinalPost FbFinal.ciphAt 8 X86.abi.ptrBits) true 8

/-! ## `cbcEncryptChained` -/

theorem cbcEncryptChained_wp {s₀ : State} (hp : (Fb.fbX86 53 8 Cbc.encPost).pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (Fb.fbX86 53 8 Cbc.encPost).post s₀ s' :=
  Cbc.cbcEncryptChained_wp_of ssse3Fits (fun _ => rfl) hp

theorem cbcEncryptChained_ct : ConstantTime isa (Fb.fbX86 53 8 Cbc.encPost).pre (Fb.fbX86 53 8 Cbc.encPost).pub cbcEncryptChained :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (Fb.fbTaint 53 8) (fun _ _ h₁ h₂ hp => Fb.fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cbcEncryptChained_implies :
    (Fb.wideContract 53 8 Cbc.encPost).Implies (Proof.Blowfish.cbcEncChainedScratchContract X86.abi 53 8) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Cbc.encPost] at h
    sig_split h
    sig_reduce [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Cbc.encPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Cbc.encPost, Fb.ciph, Fb.ivAt, Fb.dataAt]
  · sig_implies_pub [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Cbc.encPost]
  · sig_implies_sat [Proof.Blowfish.cbcEncChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Cbc.encPost]
      [sat53, arg, argAddr, Mem.readW, Mem.read] using sat53

theorem cbcEncryptChained_verified : Verified X86.target cbcEncryptChained (Proof.Blowfish.cbcEncChainedScratchContract X86.abi 53 8) :=
  Fb.fb_verified (fun _ hs => cbcEncryptChained_wp hs) cbcEncryptChained_ct (fun _ _ _ _ _ _ h => h) cbcEncryptChained_implies

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 452 4 106 cbcEncryptChained)
      (Spec.Blowfish.cbcEncryptChainedContract X86.abi 460) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 53) (post := Proof.Blowfish.cbcEncChainedPost X86.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 452) cbcEncryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.cbcEncChainedPost_local _) (Proof.Blowfish.cbcEncChainedPostOut_local _) (frameSat_cbc _)

/-- The residue analyses of the functions' code, in one kernel evaluation
(`taint_decide_ct_all`), which analyses the code they share once. -/
theorem residue :
    rtaint.Ends (RTaint.init 460 0) Fn.cbcEncryptChained (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 460 0) Fn.ofb (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 460 0) Fn.cfbEncrypt (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 460 0) Fn.cfbEncryptFinal (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 460 0) Fn.cfbDecryptFinal (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 460 0) Fn.ofbFinal (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 424 0) Fn.expandKey (RTaint.done 0) := by
  taint_decide_ct_all

/-- `Spec.Blowfish.cbcEncryptChainedApi` as emitted (`Impl.Blowfish.X86.Ssse3.Fn.cbcEncryptChained`) meets its contract in constant
time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Fn.cbcEncryptChained (Spec.Blowfish.cbcEncryptChainedContract X86.abi 460) 0 :=
  verifiedScrubbedSel (api := Spec.Blowfish.cbcEncryptChainedApi) (W := 460)
    { code := Impl.StackScratch.X86.withStackScratchWiped 452 4 106 cbcEncryptChained
      verified := cbcEncryptChained_framed }
    Fn.words (Scrub.cbcEncryptOut _) (by decide) residue.1

/-! ## `ofb` -/

theorem ofb_wp {s₀ : State} (hp : (Fb.fbX86 53 8 Fb.ofbPost).pre s₀) :
    WP isa ofb s₀ fun s' => abiPreserved s₀ s' ∧ (Fb.fbX86 53 8 Fb.ofbPost).post s₀ s' :=
  Fb.ofb_wp_of ssse3Fits (fun _ => rfl) hp

theorem ofb_ct : ConstantTime isa (Fb.fbX86 53 8 Fb.ofbPost).pre (Fb.fbX86 53 8 Fb.ofbPost).pub ofb :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (Fb.fbTaint 53 8) (fun _ _ h₁ h₂ hp => Fb.fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem ofb_implies :
    (Fb.wideContract 53 8 Fb.ofbPost).Implies (Proof.Blowfish.fbScratchContract X86.abi 53 Proof.Blowfish.ofbPost 8) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.ofbPost] at h
    sig_split h
    sig_reduce [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.ofbPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.ofbPost, Fb.ciph, Fb.ivAt, Fb.dataAt]
  · sig_implies_pub [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.ofbPost]
  · sig_implies_sat [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.ofbPost]
      [sat53, arg, argAddr, Mem.readW, Mem.read] using sat53

theorem ofb_verified : Verified X86.target ofb (Proof.Blowfish.fbScratchContract X86.abi 53 Proof.Blowfish.ofbPost 8) :=
  Fb.fb_verified (fun _ hs => ofb_wp hs) ofb_ct (fun _ _ _ _ _ _ h => h) ofb_implies

/-- `ofb` with its working space on the stack. -/
theorem ofb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 452 4 106 ofb)
      (Spec.Blowfish.ofbContract X86.abi 460) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.ofbSig) (nm := "scratch") (e := .u64)
    (n := 53) (post := Proof.Blowfish.ofbPost X86.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 452) ofb_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.ofbPost_local _) (Proof.Blowfish.ofbPostOut_local _) (frameSat_ofb _)

/-- `Spec.Blowfish.ofbApi` as emitted (`Impl.Blowfish.X86.Ssse3.Fn.ofb`) meets its contract in constant
time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Fn.ofb (Spec.Blowfish.ofbContract X86.abi 460) 0 :=
  verifiedScrubbedSel (api := Spec.Blowfish.ofbApi) (W := 460)
    { code := Impl.StackScratch.X86.withStackScratchWiped 452 4 106 ofb
      verified := ofb_framed }
    Fn.words (Scrub.ofbOut _) (by decide) residue.2.1

/-! ## `cfbEncrypt` -/

theorem cfbEncrypt_wp {s₀ : State} (hp : (Fb.fbX86 53 8 Fb.cfbEncPost).pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ (Fb.fbX86 53 8 Fb.cfbEncPost).post s₀ s' :=
  Fb.cfbEncrypt_wp_of ssse3Fits (fun _ => rfl) hp

theorem cfbEncrypt_ct : ConstantTime isa (Fb.fbX86 53 8 Fb.cfbEncPost).pre (Fb.fbX86 53 8 Fb.cfbEncPost).pub cfbEncrypt :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (Fb.fbTaint 53 8) (fun _ _ h₁ h₂ hp => Fb.fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbEncrypt_implies :
    (Fb.wideContract 53 8 Fb.cfbEncPost).Implies (Proof.Blowfish.fbScratchContract X86.abi 53 Proof.Blowfish.cfbEncPost 8) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.cfbEncPost] at h
    sig_split h
    sig_reduce [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.cfbEncPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.cfbEncPost, Fb.ciph, Fb.ivAt, Fb.dataAt]
  · sig_implies_pub [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.cfbEncPost]
  · sig_implies_sat [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.cfbEncPost]
      [sat53, arg, argAddr, Mem.readW, Mem.read] using sat53

theorem cfbEncrypt_verified : Verified X86.target cfbEncrypt (Proof.Blowfish.fbScratchContract X86.abi 53 Proof.Blowfish.cfbEncPost 8) :=
  Fb.fb_verified (fun _ hs => cfbEncrypt_wp hs) cfbEncrypt_ct (fun _ _ _ _ _ _ h => h) cfbEncrypt_implies

/-- `cfbEncrypt` with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 452 4 106 cfbEncrypt)
      (Spec.Blowfish.cfbEncryptContract X86.abi 460) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64)
    (n := 53) (post := Proof.Blowfish.cfbEncPost X86.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 452) cfbEncrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.cfbEncPost_local _) (Proof.Blowfish.cfbEncPostOut_local _) (frameSat_ofb _)

/-- `Spec.Blowfish.cfbEncryptApi` as emitted (`Impl.Blowfish.X86.Ssse3.Fn.cfbEncrypt`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Fn.cfbEncrypt (Spec.Blowfish.cfbEncryptContract X86.abi 460) 0 :=
  verifiedScrubbedSel (api := Spec.Blowfish.cfbEncryptApi) (W := 460)
    { code := Impl.StackScratch.X86.withStackScratchWiped 452 4 106 cfbEncrypt
      verified := cfbEncrypt_framed }
    Fn.words (Scrub.cfbEncryptOut _) (by decide) residue.2.2.1

/-! ## `cfbEncryptFinal` -/

theorem cfbEncryptFinal_wp {s₀ : State} (hp : (FbFinal.finalX86 53 8 FbFinal.encPost).pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (FbFinal.finalX86 53 8 FbFinal.encPost).post s₀ s' :=
  FbFinal.cfbEncryptFinal_wp_of ssse3Fits (fun _ => rfl) hp

theorem cfbEncryptFinal_ct : ConstantTime isa (FbFinal.finalX86 53 8 FbFinal.encPost).pre (FbFinal.finalX86 53 8 FbFinal.encPost).pub cfbEncryptFinal :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (Fb.fbTaint 53 8) (fun _ _ h₁ h₂ hp => FbFinal.fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbEncryptFinal_implies : (FbFinal.wideContract 53 8 FbFinal.encPost).Implies encScratch := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86,
      FbFinal.encPost] at h
    sig_split h
    sig_reduce [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86, FbFinal.encPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86, FbFinal.encPost,
      Fb.ciph, FbFinal.ciphAt]
  · sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86, FbFinal.encPost]
  · sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86, FbFinal.encPost]
      [satF53, arg, argAddr, Mem.readW, Mem.read] using satF53

theorem cfbEncryptFinal_verified : Verified X86.target cfbEncryptFinal encScratch :=
  FbFinal.final_verified (fun _ hs => cfbEncryptFinal_wp hs) cfbEncryptFinal_ct (fun _ _ _ _ _ _ h => h) cfbEncryptFinal_implies

/-- `cfbEncryptFinal` with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 452 4 106 cfbEncryptFinal)
      (Spec.Blowfish.cfbEncryptFinalContract X86.abi 460) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 53) (post := Proof.Modes.encFinalPost FbFinal.ciphAt 8 X86.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 452) cfbEncryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.encFinalPost_inLocal _ FbFinal.ciphAt_congr) (Proof.Modes.encFinalPost_local _) (frameSat_cfbFinal _)

/-- `Spec.Blowfish.cfbEncryptFinalApi` as emitted (`Impl.Blowfish.X86.Ssse3.Fn.cfbEncryptFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Fn.cfbEncryptFinal (Spec.Blowfish.cfbEncryptFinalContract X86.abi 460) 0 :=
  verifiedScrubbedSel (api := Spec.Blowfish.cfbEncryptFinalApi) (W := 460)
    { code := Impl.StackScratch.X86.withStackScratchWiped 452 4 106 cfbEncryptFinal
      verified := cfbEncryptFinal_framed }
    Fn.words (Scrub.cfbEncryptFinalOut _) (by decide) residue.2.2.2.1

/-! ## `cfbDecryptFinal` -/

theorem cfbDecryptFinal_wp {s₀ : State} (hp : (FbFinal.finalX86 53 8 FbFinal.decPost).pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (FbFinal.finalX86 53 8 FbFinal.decPost).post s₀ s' :=
  FbFinal.cfbDecryptFinal_wp_of ssse3Fits (fun _ => rfl) hp

theorem cfbDecryptFinal_ct : ConstantTime isa (FbFinal.finalX86 53 8 FbFinal.decPost).pre (FbFinal.finalX86 53 8 FbFinal.decPost).pub cfbDecryptFinal :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (Fb.fbTaint 53 8) (fun _ _ h₁ h₂ hp => FbFinal.fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbDecryptFinal_implies : (FbFinal.wideContract 53 8 FbFinal.decPost).Implies decScratch := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86,
      FbFinal.decPost] at h
    sig_split h
    sig_reduce [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86, FbFinal.decPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86, FbFinal.decPost,
      Fb.ciph, FbFinal.ciphAt]
  · sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86, FbFinal.decPost]
  · sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86, FbFinal.decPost]
      [satF53, arg, argAddr, Mem.readW, Mem.read] using satF53

theorem cfbDecryptFinal_verified : Verified X86.target cfbDecryptFinal decScratch :=
  FbFinal.final_verified (fun _ hs => cfbDecryptFinal_wp hs) cfbDecryptFinal_ct (fun _ _ _ _ _ _ h => h) cfbDecryptFinal_implies

/-- `cfbDecryptFinal` with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 452 4 106 cfbDecryptFinal)
      (Spec.Blowfish.cfbDecryptFinalContract X86.abi 460) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 53) (post := Proof.Modes.decFinalPost FbFinal.ciphAt 8 X86.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 452) cfbDecryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.decFinalPost_inLocal _ FbFinal.ciphAt_congr) (Proof.Modes.decFinalPost_local _) (frameSat_cfbFinal _)

/-- `Spec.Blowfish.cfbDecryptFinalApi` as emitted (`Impl.Blowfish.X86.Ssse3.Fn.cfbDecryptFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Fn.cfbDecryptFinal (Spec.Blowfish.cfbDecryptFinalContract X86.abi 460) 0 :=
  verifiedScrubbedSel (api := Spec.Blowfish.cfbDecryptFinalApi) (W := 460)
    { code := Impl.StackScratch.X86.withStackScratchWiped 452 4 106 cfbDecryptFinal
      verified := cfbDecryptFinal_framed }
    Fn.words (Scrub.cfbDecryptFinalOut _) (by decide) residue.2.2.2.2.1

/-! ## `ofbFinal` -/

theorem ofbFinal_wp {s₀ : State} (hp : (FbFinal.finalX86 53 8 FbFinal.ofbPost).pre s₀) :
    WP isa ofbFinal s₀ fun s' => abiPreserved s₀ s' ∧ (FbFinal.finalX86 53 8 FbFinal.ofbPost).post s₀ s' :=
  FbFinal.ofbFinal_wp_of ssse3Fits (fun _ => rfl) hp

theorem ofbFinal_ct : ConstantTime isa (FbFinal.finalX86 53 8 FbFinal.ofbPost).pre (FbFinal.finalX86 53 8 FbFinal.ofbPost).pub ofbFinal :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (Fb.fbTaint 53 8) (fun _ _ h₁ h₂ hp => FbFinal.fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem ofbFinal_implies : (FbFinal.wideContract 53 8 FbFinal.ofbPost).Implies ofbScratch := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.ofbFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86,
      FbFinal.ofbPost] at h
    sig_split h
    sig_reduce [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.ofbFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86, FbFinal.ofbPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.ofbFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86, FbFinal.ofbPost,
      Fb.ciph, FbFinal.ciphAt]
  · sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.ofbFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86, FbFinal.ofbPost]
  · sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.ofbFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, FbFinal.wideContract, FbFinal.finalX86, FbFinal.ofbPost]
      [satF53, arg, argAddr, Mem.readW, Mem.read] using satF53

theorem ofbFinal_verified : Verified X86.target ofbFinal ofbScratch :=
  FbFinal.final_verified (fun _ hs => ofbFinal_wp hs) ofbFinal_ct (fun _ _ _ _ _ _ h => h) ofbFinal_implies

/-- `ofbFinal` with its working space on the stack. -/
theorem ofbFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 452 4 106 ofbFinal)
      (Spec.Blowfish.ofbFinalContract X86.abi 460) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.ofbFinalSig) (nm := "scratch") (e := .u64)
    (n := 53) (post := Proof.Modes.ofbFinalPost FbFinal.ciphAt 8 X86.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 452) ofbFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.ofbFinalPost_inLocal _ FbFinal.ciphAt_congr) (Proof.Modes.ofbFinalPost_local _) (frameSat_ofbFinal _)

/-- `Spec.Blowfish.ofbFinalApi` as emitted (`Impl.Blowfish.X86.Ssse3.Fn.ofbFinal`) meets its contract in constant
time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Fn.ofbFinal (Spec.Blowfish.ofbFinalContract X86.abi 460) 0 :=
  verifiedScrubbedSel (api := Spec.Blowfish.ofbFinalApi) (W := 460)
    { code := Impl.StackScratch.X86.withStackScratchWiped 452 4 106 ofbFinal
      verified := ofbFinal_framed }
    Fn.words (Scrub.ofbFinalOut _) (by decide) residue.2.2.2.2.2.1

/-! ## Key expansion -/

open VG.Spec.Blowfish (expandKeyPre expandKeyPost validKey scheduleAt)

/-- `vg_blowfish_expand_key` with `scratch: *mut [u64; 48]`. -/
def keySig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("schedule", .array true .u8 4168),
    ("scratch", .array true .u64 48)]

/-- `expandKeyContract`, whatever `scratch` is, for a working space of 384
bytes and eight bytes of stack. -/
def keyScratch : Contract isa :=
  keySig.contract X86.abi
    (pre := fun key keyLen schedule _scratch => expandKeyPre X86.abi.ptrBits key keyLen schedule)
    (post := fun key keyLen schedule _scratch => expandKeyPost X86.abi.ptrBits key keyLen schedule)
    (stack := 8)

/-- `keyScratch` spelled out. -/
def keyC8 : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let sch : Region := ⟨(arg s 2).setWidth 64, 4168⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 384⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 8
    s.rd = [key, args] ∧ s.wr = [sch, scratch] ∧ key.Disjoint sch ∧ key.Disjoint scratch ∧
      sch.Disjoint scratch ∧ args.Disjoint sch ∧ args.Disjoint scratch ∧ ret.Disjoint sch ∧
      ret.Disjoint scratch ∧ stack.Disjoint sch ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + 4168 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 384 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ 8 ≤ (s.gpr .esp).toNat ∧
      validKey (arg s 1).toNat
  post s s' :=
    scheduleAt s'.mem ((arg s 2).setWidth 64) =
      Spec.Blowfish.expandKey (Spec.Blowfish.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- `expand_key(0x1000, 4, 0x2000, 0x4000)`. -/
def keySat8 : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x6008 then 4 else if a = 0x600d then 0x20 else
    if a = 0x6011 then 0x40 else 0
  rd := [⟨0x1000, 4⟩, ⟨0x6004, 16⟩]
  wr := [⟨0x2000, 4168⟩, ⟨0x4000, 384⟩]

theorem key_implies : keyC8.Implies keyScratch where
  pre := by
    intro s h
    sig_pre [keyScratch, keySig, expandKeyPre, expandKeyPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, keyC8,
      validKey] at h
    sig_split h
    sig_reduce [keyScratch, keySig, expandKeyPre, expandKeyPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
      keyC8, validKey]
    sig_simp [keyScratch, keySig, expandKeyPre, expandKeyPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
      keyC8, validKey] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  post := by
    sig_implies_post [keyScratch, keySig, expandKeyPre, expandKeyPost, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, keyC8, validKey]
  pub := by
    sig_implies_pub [keyScratch, keySig, expandKeyPre, expandKeyPost, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, keyC8, validKey]
  sat := by
    sig_implies_sat [keyScratch, keySig, expandKeyPre, expandKeyPost, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, keyC8, validKey]
      [keySat8, arg, argAddr, Mem.readW, Mem.read] using keySat8

/-- Key expansion over the block function by `pshufb`. -/
theorem expandKey_ok (s : State) (hs : keyC8.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyC8.post s s' := by
  obtain ⟨hrd, hwr, ks, kb, sb, as, ab, rs, rb, ss, sbf, fKey, fSch, fBuf, fsp, hlo, valid⟩ := hs
  obtain wSub : Region.Sub (wR (arg s 3)) ⟨(arg s 3).setWidth 64, 384⟩ := Offset.sub_base _ (by decide)
  obtain e : (s.gpr .esp - BitVec.ofNat 32 8).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 8 :=
    VG.X86.Taint.sub_setWidth hlo
  obtain ea : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  obtain sA : Region.Disjoint (below (s.gpr .esp) 8) ⟨argAddr s 0, 16⟩ := by
    show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 8).setWidth 64, 8⟩ _
    rw [e, ea]; exact VG.Offset.disjoint_below_above _ (by omega)
  obtain sR : Region.Disjoint (below (s.gpr .esp) 8) ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
    show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 8).setWidth 64, 8⟩ _
    have h := VG.Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := 8) (a := 0) (l := 4) (by omega)
    rw [BitVec.add_zero] at h
    rw [e]; exact h
  obtain ⟨t, s', he, ha, hp⟩ := expandKeyWith_correct (W := 384) (X := [wR (arg s 3), below (s.gpr .esp) 8])
    ⟨hrd, hwr, ks, kb, sb, as, ab, rs, rb, fKey, fSch, fBuf, fsp, valid, by decide⟩
    (fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨sb.sub_right wSub, Offset.base_disjoint _ (Nat.le_refl 64) (by decide), ab.sub_right wSub,
          rb.sub_right wSub⟩
      · rw [List.mem_singleton.mp hr]
        exact ⟨ss.symm, (sbf.symm).sub_left (Region.sub_prefix (by decide)), sA.symm, sR.symm⟩)
    (blkOk_blkKey ⟨fBuf, fun o n h => ⟨_, by rw [hwr]; exact List.mem_append_right _ List.mem_cons_self,
        Offset.contains_base _ (by omega) (by omega)⟩,
      fun o n h h' => ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        Offset.contains_base _ (by omega) (by omega)⟩,
      sb.sub_right wSub, hlo, ss.symm, (sbf.sub_right wSub).symm⟩)
  exact ⟨t, s', he, ha, hp⟩

/-- The initial taint of key expansion: the stack pointer, and the schedule
and the working space, the writable regions, at the arguments 12 and 16
bytes up; eight bytes of stack. -/
def τK8 : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [4168, 384], argLen := 20, argBases := [(12, 0), (16, 1)],
    room := 8 }

theorem τK8_wf {s : State} (hs : keyC8.pre s) : VG.X86.Taint.Wf τK8 s := by
  obtain ⟨_, hwr, _, _, sb, as, ab, rs, rb, ss, sbf, _, fS, fB, fsp, hlo, _⟩ := hs
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨fsp, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨sb, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rs as
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rb ab
  · intro p hp
    simp only [τK8, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · intro _
    refine ⟨hlo, fun r hr => ?_⟩
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 8 = (s.gpr .esp - BitVec.ofNat 32 8).setWidth 64 :=
      (VG.X86.Taint.sub_setWidth hlo).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 8, 8⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [ss, sbf]

theorem expandKey_agree {s t : State} (hs : keyC8.pre s) (ht : keyC8.pre t) (hp : keyC8.pub s t) :
    VG.X86.Taint.Agree τK8 s t := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, keyC8.pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τK8_wf hs, τK8_wf ht,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τK8, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 2 (by decide), args 3 (by decide)]
  · simp only [τK8] at hk
    rw [show VG.X86.Taint.depth τK8.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem expandKey_ct : ConstantTime isa keyC8.pre keyC8.pub expandKey :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) τK8 (fun _ _ h₁ h₂ hp => expandKey_agree h₁ h₂ hp) (by taint_decide)

theorem expandKey_verified : Verified X86.target expandKey keyScratch :=
  Verified.of_correct expandKey_ok expandKey_ct key_implies

theorem keyFrameSat_pre : ∃ s, (Spec.Blowfish.expandKeyContract X86.abi 424).pre s := by
  implies_sat [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig, Spec.Blowfish.expandKeyPre,
    Spec.Blowfish.expandKeyPost, Spec.Blowfish.validKey, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [expandKeyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using expandKeyFrameSat

/-- Key expansion with its working space on the stack. -/
theorem expandKey_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 416 3 96 expandKey)
      (Spec.Blowfish.expandKeyContract X86.abi 424) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.expandKeySig) (nm := "scratch") (e := .u64) (n := 48)
    (pre := Spec.Blowfish.expandKeyPre X86.abi.ptrBits) (post := Spec.Blowfish.expandKeyPost X86.abi.ptrBits)
    (wa := false) (stack := 8) (bytes := 416)
    expandKey_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Blowfish.expandKeyPre_local _) (Proof.Blowfish.expandKeyPost_local _)
    (Proof.Blowfish.expandKeyPostOut_local _) keyFrameSat_pre

/-- `Spec.Blowfish.expandKeyApi` as emitted (`Impl.Blowfish.X86.Ssse3.Fn.expandKey`) meets its contract in
constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed X86.target Fn.expandKey (Spec.Blowfish.expandKeyContract X86.abi 424) 0 :=
  verifiedScrubbedSel (api := Spec.Blowfish.expandKeyApi) (W := 424)
    { code := Impl.StackScratch.X86.withStackScratchWiped 416 3 96 expandKey
      verified := expandKey_framed }
    Fn.keyWords (Scrub.expandKeyOut _) (by decide) residue.2.2.2.2.2.2

end VG.Proof.Blowfish.X86.Ssse3
