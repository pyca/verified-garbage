module

public import VerifiedGarbage.Proof.Blowfish.X86.Ssse3WideCore
public import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Verified
public import VerifiedGarbage.Proof.Blowfish.X86.CbcVerified
public import VerifiedGarbage.Proof.Blowfish.X86.FbVerified
public import VerifiedGarbage.Proof.Modes.X86.Wide
public import VerifiedGarbage.Proof.Modes.X86.Ecb
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Spec.Blowfish.Contract
public import VerifiedGarbage.Proof.Blowfish.X86.Frame
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Blowfish.X86.Scrub
import VerifiedGarbage.Proof.Blowfish.Scratch
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Lit
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3WideLit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Blowfish.X86.Ssse3WideCore
meta import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Verified
meta import VerifiedGarbage.Proof.Blowfish.X86.CbcVerified
meta import VerifiedGarbage.Proof.Blowfish.X86.FbVerified
meta import VerifiedGarbage.Proof.Modes.X86.Wide
meta import VerifiedGarbage.Proof.Modes.X86.Ecb
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Blowfish.Contract
meta import VerifiedGarbage.Proof.Blowfish.X86.Scrub
meta import VerifiedGarbage.Proof.Blowfish.X86.Frame
meta import VerifiedGarbage.Proof.Blowfish.Scratch
meta import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Lit
meta import VerifiedGarbage.Proof.Blowfish.X86.Ssse3WideLit
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# Blowfish's functions over its sixteen-block function by `pshufb` on x86 (32-bit) meet their contracts

`cbcDecryptChained_wp`, `cfbDecrypt_wp`: the modes' CBC decryption that
updates the chaining value and CFB64 decryption by groups of blocks
(`Proof.Modes.X86.cbcDecLevels_wp`, `cfbDecLevels_wp`) over the core that
calls the sixteen-block function (`wideCoreSpec`, `wideFits`), in groups of
16, 8, 4 and 2 blocks and then a block at a time, with the working space,
111 64-bit words, as the fifth argument and eight bytes of stack
(`Fb.fbX86`); `Ecb.ecb_wp`: ECB for any core
(`Proof.Modes.X86.ecbLevels_wp`) over the same core in either direction,
with the working space as the fourth argument. Each is constant time by
the taint analysis of its code with the SSE instructions (`X86.sseTaint`),
which analyses the sixteen-block function at each of its calls; the
`_framed` theorems run them with their working space on the stack, zeroed
on return.

As emitted (`Impl.Blowfish.X86.Ssse3.Wide.Fn`), each function then zeroes,
of the stack its contract reserves below `esp` (924 bytes, 920 for ECB),
the doublewords that the residue analysis (`X86.rtaint`) finds it may leave
different in two runs (the sixteen-block function's return address, the
header of the working space's frame and the frame's last doubleword),
clears the registers a callee may change, and returns without secret
residue (`X86.Scrub.verifiedScrubbedSel`, the kernel evaluating the
analysis of the code with its cleanup: `taint_decide_ct`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86.Ssse3.Wide

open VG VG.X86 VG.X86.Scrub VG.Impl.Blowfish.X86.Ssse3.Wide
open VG.Proof.Modes.X86 (cbcDecLevels_wp cfbDecLevels_wp LevelsFit)

/-! ## The core in the functions' lemmas -/

theorem levels_fit (up : Bool) : LevelsFit (core16 up) levels := by
  intro g hg
  simp only [levels, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by show _ ≤ 16; decide⟩

theorem cipher_enc : ∀ k, (wideCoreSpec true).cipher ((wideFits true).toKey k) = Spec.Blowfish.cipher k :=
  fun _ => rfl

theorem cipher_dec : ∀ k, (wideCoreSpec false).cipher ((wideFits false).toKey k) = Spec.Blowfish.invCipher k :=
  fun _ => rfl

/-! ## States that satisfy the contracts -/

/-- Memory holding the arguments `0x5000, 0x2000, 0x3000, 0, 0x4000` at `0x8004`. -/
def sat111 : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x50 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30
    else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x5000, 4168⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 888⟩, ⟨0x8004, 20⟩]

theorem frameSat_ofb (post : Spec.Blowfish.ofbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Blowfish.ofbSig.contract X86.abi (post := post) (writeArgs := true) (stack := 924)).pre s := by
  implies_sat [Spec.Blowfish.ofbSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Fb.frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Fb.frameSat

theorem frameSat_cbc (post : Spec.Blowfish.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Blowfish.cbcChainedSig.contract X86.abi (post := post) (writeArgs := true) (stack := 924)).pre s := by
  implies_sat [Spec.Blowfish.cbcChainedSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [Fb.frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Fb.frameSat

/-! ## `cbcDecryptChained` -/

theorem cbcDecryptChained_wp {s₀ : State} (hp : (Fb.fbX86 111 8 Cbc.decPost).pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (Fb.fbX86 111 8 Cbc.decPost).post s₀ s' :=
  WP.mono (cbcDecLevels_wp (wideCoreSpec false) (levels_fit false) (Fb.seqPre_of (wideFits false) rfl hp)
    (Fb.keyArgs_of (wideFits false) hp)) fun _ ⟨h1, h2, h3⟩ => by
      bf_post_eq (wideFits false) cipher_dec h2 h3; exact ⟨h1, h2, h3⟩

theorem cbcDecryptChained_ct : ConstantTime isa (Fb.fbX86 111 8 Cbc.decPost).pre (Fb.fbX86 111 8 Cbc.decPost).pub cbcDecryptChained :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (Fb.fbTaint 111 8) (fun _ _ h₁ h₂ hp => Fb.fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cbcDecryptChained_implies :
    (Fb.wideContract 111 8 Cbc.decPost).Implies (Proof.Blowfish.cbcDecChainedScratchContract X86.abi 111 8) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Cbc.decPost] at h
    sig_split h
    sig_reduce [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Cbc.decPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Cbc.decPost, Cbc.invCiph, Fb.ivAt, Fb.dataAt]
  · sig_implies_pub [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Cbc.decPost]
  · sig_implies_sat [Proof.Blowfish.cbcDecChainedScratchContract, Proof.Blowfish.cbcChainedScratchSig, Spec.Blowfish.cbcChainedSig, Proof.Blowfish.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Cbc.decPost]
      [sat111, arg, argAddr, Mem.readW, Mem.read] using sat111

theorem cbcDecryptChained_verified : Verified X86.target cbcDecryptChained (Proof.Blowfish.cbcDecChainedScratchContract X86.abi 111 8) :=
  Fb.fb_verified (fun _ hs => cbcDecryptChained_wp hs) cbcDecryptChained_ct (fun _ _ _ _ _ _ h => h) cbcDecryptChained_implies

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 916 4 222 cbcDecryptChained)
      (Spec.Blowfish.cbcDecryptChainedContract X86.abi 924) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 111) (post := Proof.Blowfish.cbcDecChainedPost X86.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 916) cbcDecryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.cbcDecChainedPost_local _) (Proof.Blowfish.cbcDecChainedPostOut_local _) (frameSat_cbc _)

/-- `Spec.Blowfish.cbcDecryptChainedApi` as emitted (`Impl.Blowfish.X86.Ssse3.Wide.Fn.cbcDecryptChained`) meets its contract in constant
time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Fn.cbcDecryptChained (Spec.Blowfish.cbcDecryptChainedContract X86.abi 924) 0 :=
  verifiedScrubbedSel (api := Spec.Blowfish.cbcDecryptChainedApi) (W := 924)
    { code := Impl.StackScratch.X86.withStackScratchWiped 916 4 222 cbcDecryptChained
      verified := cbcDecryptChained_framed }
    Fn.words (Scrub.cbcDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-! ## `cfbDecrypt` -/

theorem cfbDecrypt_wp {s₀ : State} (hp : (Fb.fbX86 111 8 Fb.cfbDecPost).pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (Fb.fbX86 111 8 Fb.cfbDecPost).post s₀ s' :=
  WP.mono (cfbDecLevels_wp (wideCoreSpec true) (levels_fit true) (Fb.seqPre_of (wideFits true) rfl hp)
    (Fb.keyArgs_of (wideFits true) hp)) fun _ ⟨h1, h2, h3⟩ => by
      bf_post_eq (wideFits true) cipher_enc h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_ct : ConstantTime isa (Fb.fbX86 111 8 Fb.cfbDecPost).pre (Fb.fbX86 111 8 Fb.cfbDecPost).pub cfbDecrypt :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (Fb.fbTaint 111 8) (fun _ _ h₁ h₂ hp => Fb.fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbDecrypt_implies :
    (Fb.wideContract 111 8 Fb.cfbDecPost).Implies (Proof.Blowfish.fbScratchContract X86.abi 111 Proof.Blowfish.cfbDecPost 8) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.cfbDecPost] at h
    sig_split h
    sig_reduce [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.cfbDecPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; rw [below8 ‹8 ≤ (s.gpr Reg.esp).toNat›]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.cfbDecPost, Fb.ciph, Fb.ivAt, Fb.dataAt]
  · sig_implies_pub [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.cfbDecPost]
  · sig_implies_sat [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig, Proof.Blowfish.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Fb.wideContract, Fb.fbX86, Fb.cfbDecPost]
      [sat111, arg, argAddr, Mem.readW, Mem.read] using sat111

theorem cfbDecrypt_verified : Verified X86.target cfbDecrypt (Proof.Blowfish.fbScratchContract X86.abi 111 Proof.Blowfish.cfbDecPost 8) :=
  Fb.fb_verified (fun _ hs => cfbDecrypt_wp hs) cfbDecrypt_ct (fun _ _ _ _ _ _ h => h) cfbDecrypt_implies

/-- `cfbDecrypt` with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 916 4 222 cfbDecrypt)
      (Spec.Blowfish.cfbDecryptContract X86.abi 924) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64)
    (n := 111) (post := Proof.Blowfish.cfbDecPost X86.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 916) cfbDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.cfbDecPost_local _) (Proof.Blowfish.cfbDecPostOut_local _) (frameSat_ofb _)

/-- `Spec.Blowfish.cfbDecryptApi` as emitted (`Impl.Blowfish.X86.Ssse3.Wide.Fn.cfbDecrypt`) meets its contract in constant
time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Fn.cfbDecrypt (Spec.Blowfish.cfbDecryptContract X86.abi 924) 0 :=
  verifiedScrubbedSel (api := Spec.Blowfish.cfbDecryptApi) (W := 924)
    { code := Impl.StackScratch.X86.withStackScratchWiped 916 4 222 cfbDecrypt
      verified := cfbDecrypt_framed }
    Fn.words (Scrub.cfbDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-! ## ECB -/

namespace Ecb

open VG.Impl.Modes
open VG.Proof.Modes.X86 (stkRegion ecbLevels_wp eScrR)
open VG.Proof.Blowfish (dirCipher dirCipher_bytes bytesAt_eq dirBlock)
open VG.Proof.Blowfish.X86 (dir KeyArgs KeyArgsN ecbFrameSat)
open VG.Impl.Blowfish.X86 (at_)

/-- ECB on x86 with its working space as the fourth argument, encrypting
(`up`) or decrypting. -/
def ecbX86 (up : Bool) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 4168⟩
    let data : Region := ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8 * 111⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 8
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint scratch ∧
    stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 4168 ≤ 2 ^ 32 ∧
    (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8 * 111 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ 8 ≤ (s.gpr .esp).toNat
  post s s' :=
    Spec.Blowfish.blocksAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Blowfish.ecb (Spec.Blowfish.scheduleAt s.mem ((arg s 0).setWidth 64)) (dir up)
        (Spec.Blowfish.blocksAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

theorem scr_eq (up : Bool) (s : State) : eScrR s (core16 up) = ⟨(arg s 3).setWidth 64, 8 * 111⟩ := by
  simp [eScrR, core16]

/-- The eight bytes of stack below `esp` are apart from the arguments and the return address. -/
theorem stk_apart {s : State} (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) (hlo : 8 ≤ (s.gpr .esp).toNat) :
    Region.Disjoint (stkRegion (s.gpr .esp) 8) ⟨argAddr s 0, 16⟩ ∧
      Region.Disjoint (stkRegion (s.gpr .esp) 8) ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
  have e : (s.gpr .esp - BitVec.ofNat 32 8).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 8 :=
    VG.X86.Taint.sub_setWidth hlo
  have ea : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_arith)
  refine ⟨?_, ?_⟩
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 8).setWidth 64, 8⟩ _
    rw [e, ea]; exact VG.Offset.disjoint_below_above _ (by decide)
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 8).setWidth 64, 8⟩ _
    have := VG.Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := 8) (a := 0) (l := 4) (by decide)
    rw [BitVec.add_zero] at this
    rw [e]; exact this

/-- `ecbX86`'s precondition gives the mode's. -/
theorem ecbPre_of {up : Bool} {s : State} (h : (ecbX86 up).pre s) :
    Proof.Modes.X86.EcbPre (core16 up) s := by
  obtain ⟨hrd, hwr, -, dKS, dDS, dAD, dAS, dRD, dRS, -, dSD, dSS, fK, fD, fS, fE, fLo⟩ := h
  have hL := (wideCoreSpec up).layout
  obtain ⟨sA, sR⟩ := stk_apart fE fLo
  refine ⟨(by rw [hrd]; simp [core16]), fE, ⟨(by rw [hwr]; simp [core16]),
      (by simp only [core16]; omega_arith)⟩, (by rw [hwr]; simp [core16]),
    fD, ?_, ?_, ?_, dRD, dSD, ?_, sA, sR, fLo, hL⟩
  · rw [scr_eq]; exact dDS
  · rw [scr_eq]; exact dAS
  · rw [scr_eq]; exact dRS
  · exact dSS.sub_right (VG.Offset.sub_base _ (by simp only [core16]; omega_arith))

theorem keyArgs_of {up : Bool} {s : State} (h : (ecbX86 up).pre s) :
    (wideCoreSpec up).KeyArgs s [eScrR s (core16 up)]
      (Spec.Blowfish.scheduleAt s.mem ((arg s 0).setWidth 64)) := by
  obtain ⟨hrd, hwr, dKD, dKS, -, dAD, dAS, -, -, dSK, -, dSS, fK, -, -, fE, fLo⟩ := h
  obtain ⟨sA, -⟩ := stk_apart fE fLo
  have hA : ∀ r : Region, (⟨argAddr s 0, 16⟩ : Region).Disjoint r → Region.Disjoint ⟨s.ea (at_ .esp 4), 4⟩ r :=
    fun r h => h.sub_left (Region.sub_prefix (by decide))
  refine ⟨⟨arg s 0, ⟨⟨⟨argAddr s 0, 16⟩, by rw [hrd]; simp, ?_⟩, rfl, rfl, by rw [hrd]; simp, fK⟩,
    fun r hr => ?_, fun r hr => ?_⟩, fun r hr => ?_, dSK, sA.sub_right (Region.sub_prefix (by decide))⟩
  · show (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s 0) 4
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact ⟨dKS, hA _ dAS⟩
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨dKD, hA _ dAD⟩, ⟨dKS, hA _ dAS⟩]
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dSS

/-- The blocks, from their bytes: each the block function of the block it
was. -/
theorem blocksAt_of_chunks {m m' : Mem} {p : Addr} {n : Nat} {up : Bool} {k : Spec.Blowfish.Schedule}
    (h : Proof.Modes.chunksAt 8 m' p n = (Proof.Modes.chunksAt 8 m p n).map (dirCipher up k)) :
    Spec.Blowfish.blocksAt m' p n = (Spec.Blowfish.blocksAt m p n).map (dirBlock k up) := by
  simp only [Proof.Modes.chunksAt, List.map_map] at h
  simp only [Spec.Blowfish.blocksAt, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have e := List.map_inj_left.mp h i hi
  simp only [Function.comp_apply] at e ⊢
  rw [dirCipher_bytes, bytesAt_eq] at e
  exact Vector.toList_inj.mp e

theorem ecb_eq (up : Bool) (k : Spec.Blowfish.Schedule) (xs : List Spec.Blowfish.Block) :
    Spec.Blowfish.ecb k (dir up) xs = xs.map (dirBlock k up) := by
  cases up <;> rfl

theorem ecb_wp (up : Bool) {s₀ : State} (hp : (ecbX86 up).pre s₀) :
    WP isa (ecb up) s₀ fun s' => abiPreserved s₀ s' ∧ (ecbX86 up).post s₀ s' :=
  WP.mono (ecbLevels_wp (wideCoreSpec up) (gs := levels) (levels_fit up) (ecbPre_of hp) (keyArgs_of hp))
    fun s' ⟨h1, h2⟩ => ⟨h1, by
      show Spec.Blowfish.blocksAt s'.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat = Spec.Blowfish.ecb _ _ _
      rw [ecb_eq]
      exact blocksAt_of_chunks h2⟩

/-! ### Constant time -/

/-- The initial taint: `esp` public, and the words holding `data` and
`scratch` known to be the base addresses of the writable regions. -/
def ecbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 8 * 111], argLen := 20,
    argBases := [(8, 0), (16, 1)], room := 8 }

theorem ecbTaint_wf {up : Bool} {s : State} (hp : (ecbX86 up).pre s) : VG.X86.Taint.Wf ecbTaint s := by
  obtain ⟨hrd, hwr, -, dKS, dDS, dAD, dAS, dRD, dRS, -, dSD, dSS, fK, fD, fS, fE, fLo⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [ecbTaint]; omega_arith, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨dDS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_arith) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_arith) dRS dAS
  · intro p hp'
    simp only [ecbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · intro _
    refine ⟨fLo, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 8 =
        (s.gpr .esp - BitVec.ofNat 32 8).setWidth 64 := (VG.X86.Taint.sub_setWidth fLo).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 8, 8⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dSD
    · exact dSS

theorem ecbTaint_agree {up : Bool} {s₁ s₂ : State} (h₁ : (ecbX86 up).pre s₁) (h₂ : (ecbX86 up).pre s₂)
    (hpub : (ecbX86 up).pub s₁ s₂) : VG.X86.Taint.Agree ecbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbTaint_wf h₁, ecbTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ecbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 1 (by omega_arith), ha 2 (by omega_arith), ha 3 (by omega_arith)]
  · simp only [ecbTaint] at hk
    rw [show VG.X86.Taint.depth ecbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 20) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 20) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_arith)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_arith))]
    exact congrArg _ (ha _ (by omega_arith))

theorem ecb_ct (up : Bool) : ConstantTime isa (ecbX86 up).pre (ecbX86 up).pub (ecb up) := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.sseTaint.check ecbTaint (ecb up) h).isSome = true := by
    cases up <;> exact ⟨_, by taint_decide⟩
  exact VG.Taint.constantTime (A := VG.X86.sseTaint) ecbTaint (fun _ _ h₁ h₂ hp => ecbTaint_agree h₁ h₂ hp) h

/-! ### The contracts -/

/-- The ECB functions' contract with the working space as an argument. -/
abbrev ecbScratch (up : Bool) : Contract isa :=
  Sig.scratchContract X86.abi Spec.Blowfish.ecbSig "scratch" .u64 111 (Curry.const (fun _ => True) _)
    (Spec.Blowfish.ecbPost (dir up) X86.abi.ptrBits) true 8

/-- `ecbX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`ecb_verified` narrows to `ecbX86`). -/
def wideContract (up : Bool) : Contract isa :=
  { ecbX86 up with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 4168⟩
      let data : Region := ⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 8 * 111⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 8
      s.rd = [sched] ∧ s.wr = [data, scratch, args] ∧
      sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint scratch ∧
      stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 4168 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8 * 111 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ 8 ≤ (s.gpr .esp).toNat }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 4168⟩, ⟨argAddr s 0, 16⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, 8 * (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, 8 * 111⟩]

tactic_template "bf_wide_ecb_narrow" : tactic =>
  `(tactic| simp only [VG.Proof.Blowfish.X86.Ssse3.Wide.Ecb.ecbX86, VG.Proof.Blowfish.X86.Ssse3.Wide.Ecb.wideContract,
                     VG.Proof.Blowfish.X86.Ssse3.Wide.Ecb.narrowRd, VG.Proof.Blowfish.X86.Ssse3.Wide.Ecb.narrowWr,
                     VG.X86.arg_withRegions, VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr,
                     VG.X86.State.withRegions_mem, VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])

tactic_template "bf_wide_ecb_narrow" loc:Lean.Parser.Tactic.location : tactic =>
  `(tactic| simp only [VG.Proof.Blowfish.X86.Ssse3.Wide.Ecb.ecbX86, VG.Proof.Blowfish.X86.Ssse3.Wide.Ecb.wideContract,
                     VG.Proof.Blowfish.X86.Ssse3.Wide.Ecb.narrowRd, VG.Proof.Blowfish.X86.Ssse3.Wide.Ecb.narrowWr,
                     VG.X86.arg_withRegions, VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr,
                     VG.X86.State.withRegions_mem, VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $loc)

theorem wide_pre (up : Bool) (s : State) (h : (wideContract up).pre s) :
    (ecbX86 up).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  bf_wide_ecb_narrow
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 0x3000, 0, 0x4000` at `0x8004`. -/
def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30 else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 888⟩, ⟨0x8004, 16⟩]

theorem wide_implies (up : Bool) : (wideContract up).Implies (ecbScratch up) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Blowfish.ecbSig, Spec.Blowfish.ecbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, below] at h
    sig_split h
    sig_reduce [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Blowfish.ecbSig, Spec.Blowfish.ecbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; try simp only [Nat.mul_comm] at *
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Blowfish.ecbSig, Spec.Blowfish.ecbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, below, dir]
  · sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Blowfish.ecbSig, Spec.Blowfish.ecbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, below]
  · sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Blowfish.ecbSig, Spec.Blowfish.ecbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem ecb_verified (up : Bool) : Verified X86.target (ecb up) (ecbScratch up) := by
  have hsat := (wide_implies up).sat_left
  have narrowSat : ∃ s, (ecbX86 up).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre up s hs⟩
  apply Verified.of_implies _ (wide_implies up)
  refine Verified.narrowTo
    (Verified.of_correct (fun _ hs => ecb_wp up hs) (ecb_ct up) (.refl narrowSat))
    narrowRd narrowWr (wide_pre up) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    bf_wide_ecb_narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    bf_wide_ecb_narrow
    exact h

theorem frameSat_pre (d : Spec.Blowfish.Direction) : ∃ s, (Spec.Blowfish.ecbContract X86.abi d 920).pre s := by
  have h0 : (X86.arg ecbFrameSat 2).toNat = 0 := by decide
  refine ⟨ecbFrameSat, ?_⟩
  sig_pre [Spec.Blowfish.ecbContract, Spec.Blowfish.ecbSig, Spec.Blowfish.ecbPost, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
  sig_and_intros
  -- The data is empty.
  all_goals first
    | rfl
    | decide
    | (intro a _ h₂; simp only [Region.Contains, h0] at h₂; omega)
    | exact Region.disjoint_of_sep (by decide)

/-- ECB encrypting (`up`) or decrypting, with its working space on the stack. -/
theorem ecb_framed (up : Bool) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 912 3 222 (ecb up))
      (Spec.Blowfish.ecbContract X86.abi (dir up) 920) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.ecbSig) (nm := "scratch") (e := .u64)
    (n := 111) (post := Spec.Blowfish.ecbPost (dir up) X86.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 912) (ecb_verified up) (by decide) (by cases up <;> lit_decide)
    (by cases up <;> lit_decide) (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.ecbPost_local _ (dir up)) (Proof.Blowfish.ecbPostOut_local _ (dir up)) (frameSat_pre _)

/-! ### The functions as emitted -/

/-- `Spec.Blowfish.ecbEncryptApi` as emitted (`Impl.Blowfish.X86.Ssse3.Wide.Fn.ecbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Fn.ecbEncrypt (Spec.Blowfish.ecbContract X86.abi (dir true) 920) 0 :=
  verifiedScrubbedSel (api := Spec.Blowfish.ecbEncryptApi) (W := 920)
    { code := Impl.StackScratch.X86.withStackScratchWiped 912 3 222 (ecb true)
      verified := ecb_framed true }
    Fn.ecbWords (Scrub.ecbOut _ _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Blowfish.ecbDecryptApi` as emitted (`Impl.Blowfish.X86.Ssse3.Wide.Fn.ecbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Fn.ecbDecrypt (Spec.Blowfish.ecbContract X86.abi (dir false) 920) 0 :=
  verifiedScrubbedSel (api := Spec.Blowfish.ecbDecryptApi) (W := 920)
    { code := Impl.StackScratch.X86.withStackScratchWiped 912 3 222 (ecb false)
      verified := ecb_framed false }
    Fn.ecbWords (Scrub.ecbOut _ _) (by decide) ⟨_, by taint_decide_ct⟩

end Ecb

end VG.Proof.Blowfish.X86.Ssse3.Wide
