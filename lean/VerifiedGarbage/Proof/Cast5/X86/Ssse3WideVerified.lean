module

public import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideCore
public import VerifiedGarbage.Proof.Cast5.X86.Ssse3Verified
public import VerifiedGarbage.Proof.Cast5.X86.ModesVerified
public import VerifiedGarbage.Proof.Modes.X86.Wide
public import VerifiedGarbage.Proof.Modes.X86.Ecb
public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Proof.Cast5.Rounds
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Cast5.ScrubLocal
import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideLit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideCore
meta import VerifiedGarbage.Proof.Cast5.X86.Ssse3Verified
meta import VerifiedGarbage.Proof.Cast5.X86.ModesVerified
meta import VerifiedGarbage.Proof.Modes.X86.Wide
meta import VerifiedGarbage.Proof.Modes.X86.Ecb
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.Spec.Cast5.Cbc
meta import VerifiedGarbage.Spec.Cast5.Cfb
meta import VerifiedGarbage.Proof.Cast5.Rounds
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Cast5.ScrubLocal
meta import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideLit
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# CAST5's functions over its sixteen-block function by `pshufb` on x86 (32-bit) meet their contracts

`cbcDecryptChained_wp`, `cfbDecrypt_wp`: the modes' CBC decryption that
updates the chaining value and CFB64 decryption by groups of blocks
(`Proof.Modes.X86.cbcDecLevels_wp`, `cfbDecLevels_wp`) over the core that
calls the sixteen-block function (`coreSpec16`, `fits16`), in groups of 16,
8, 4 and 2 blocks and then a block at a time, with the working space, 111
64-bit words, as the sixth argument and eight bytes of stack; `Ecb.ecb_wp`:
ECB for any core (`Proof.Modes.X86.ecbLevels_wp`) over the same core in
either direction, with the working space as the fifth argument.

Each is constant time by the taint analysis of its code with the SSE
instructions (`X86.sseTaint`), which analyses the sixteen-block function at
each of its calls. The function's branches are on the round's number: the
count of rounds left, the number and its step are doublewords of the working
space that the analysis finds public, written from the argument `rounds`
and constants, as the baseline's count is.

The `_framed` theorems run the functions with their working space on the
stack, zeroed on return. ECB's `Api` gives the function a `scratch` of 32
64-bit words, the fifth argument, which is too small for sixteen blocks:
the function has a frame of its own, as the modes have, and neither reads
nor writes the caller's. `Ecb.ecb_framed` is the frame's theorem for the
signature without that argument (`Ecb.sig4`), and `Ecb.ecb_rounds` gives
the `Api`'s contract from it (`Verified.narrowTo`): the regions the contract
gives the function less the caller's `scratch` and the argument slot that
holds its address.

As emitted (`Impl.Cast5.X86.Ssse3.Wide.Fn`), each function then zeroes, of
the stack its contract reserves below `esp` (928 bytes, 924 for ECB), the
doublewords that the residue analysis (`X86.rtaint`) finds it may leave
different in two runs, clears the registers a callee may change, and returns
without secret residue (`X86.Scrub.verifiedScrubbedSel`, the kernel
evaluating the analysis of the code with its cleanup: `taint_decide_ct`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86.Ssse3.Wide

open VG VG.X86 VG.X86.Scrub VG.Impl.Cast5.X86.Ssse3.Wide
open VG.Proof.Cast5.X86.ModeFns (GPre Fits keyA ivA dataA argsA retA scrG stkG rdG wrG τG)
open VG.Proof.Modes.X86 (CoreSpec cbcDecLevels_wp cfbDecLevels_wp LevelsFit)

/-! ## The core in the functions' lemmas -/

theorem levels_fit (up : Bool) : LevelsFit (core16 up) levels := by
  intro g hg
  simp only [levels, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by show _ ≤ 16; decide⟩

theorem cipher_enc : ∀ k r, (coreSpec16 true).cipher ((fits16 true).toKey (k, r)) = Spec.Cast5.cipher k r :=
  fun _ _ => rfl

theorem cipher_dec : ∀ k r, (coreSpec16 false).cipher ((fits16 false).toKey (k, r)) = Spec.Cast5.invCipher k r :=
  fun _ _ => rfl

/-- A mode on x86 over this core, with the working space as a sixth argument
and the postcondition `post`. -/
def modeW (post : State → State → Prop) : Contract isa where
  pre := GPre false 888 8 true
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-! ## Correctness and constant time -/

theorem cbcDecryptChained_wp {s₀ : State} (hp : (modeW ModeFns.cbcDecPost).pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (modeW ModeFns.cbcDecPost).post s₀ s' :=
  WP.mono (cbcDecLevels_wp (coreSpec16 false) (levels_fit false)
      (ModeFns.seqPre_of (fits16 false) (ModeFns.step_block (fits16 false)) rfl hp)
      (ModeFns.keyArgs_of (fits16 false) hp)) fun _ ⟨h1, h2, h3⟩ => by
    post_eq_cast5_x86_modesverified (fits16 false) cipher_dec h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_wp {s₀ : State} (hp : (modeW ModeFns.cfbDecPost).pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (modeW ModeFns.cfbDecPost).post s₀ s' :=
  WP.mono (cfbDecLevels_wp (coreSpec16 true) (levels_fit true)
      (ModeFns.seqPre_of (fits16 true) (ModeFns.step_block (fits16 true)) rfl hp)
      (ModeFns.keyArgs_of (fits16 true) hp)) fun _ ⟨h1, h2, h3⟩ => by
    post_eq_cast5_x86_modesverified (fits16 true) cipher_enc h2 h3; exact ⟨h1, h2, h3⟩

theorem cbcDecryptChained_ct :
    ConstantTime isa (modeW ModeFns.cbcDecPost).pre (modeW ModeFns.cbcDecPost).pub cbcDecryptChained :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (τG 888 8)
    (fun _ _ h₁ h₂ hp => ModeFns.τG_agree h₁ h₂ hp.1 hp.2) (by taint_decide)

theorem cfbDecrypt_ct : ConstantTime isa (modeW ModeFns.cfbDecPost).pre (modeW ModeFns.cfbDecPost).pub cfbDecrypt :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (τG 888 8)
    (fun _ _ h₁ h₂ hp => ModeFns.τG_agree h₁ h₂ hp.1 hp.2) (by taint_decide)

/-! ## The contracts -/

/-- CFB's or CBC's contract (`sig`) with the working space as a sixth
argument, under the calling convention with no table. -/
abbrev pW (sig : Sig) (pre : Curry (sig.words X86.abi.ptrBits) (Mem → Prop)) (post : sig.Post X86.abi.ptrBits) :
    Contract isa :=
  Sig.scratchContract X86.abi sig "scratch" .u64 111 pre post true 8

/-! ## States that satisfy the contracts -/

/-- A state satisfying the modes' precondition: the schedule at `0x1000`, 16
rounds, the chaining value at `0x2000`, no data at `0x3000` and the working
space at `0x4000`, as stack arguments at `0x8004`. -/
def satW : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ModeFns.satArgs
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 888⟩, ⟨0x8004, 24⟩]
  syms _ := 0

/-- A state satisfying the functions' precondition, with 928 bytes of stack. -/
def frameSatW : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ModeFns.satArgs
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩]
  syms _ := 0

theorem cfb_pre {post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits} (s : State)
    (h : (pW Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s) :
    GPre false 888 8 true (s.withRegions (rdG false true s) (wrG 888 true s)) ∧ s.rd = [keyA s] ∧
      s.wr = [ivA s, ⟨(arg s 3).setWidth 64, (arg s 4).toNat * 8⟩, scrG 888 s, argsA s] := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, stackBelow, Curry.withScratch] at h
  obtain ⟨h8, hsp, hrd, hwr, dKV, dKD, dKS, -, dVD, dVS, dVA, dDS, dDA, dSA, -, dRV, dRD, dRS, -, dBK, dBV, dBD,
    dBS, -, fK, fV, fD, fS, nv⟩ := h
  have be := below8 h8
  have e8 : (arg s 4).toNat * 8 = 8 * (arg s 4).toNat := Nat.mul_comm _ _
  rw [e8] at hwr dKD dVD dDS dDA dRD dBD fD
  refine ⟨⟨rfl, rfl, h8, (by show (s.gpr .esp).toNat + 28 ≤ 2 ^ 32; omega_using [hsp]), nv, fK, fV, fD, fS,
    (fun h => nomatch h), dDS, dVS, (fun _ => dVD), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_),
    (by show Region.Disjoint _ (below (s.gpr .esp) 8); rw [be]; exact dBK.symm)⟩, hrd, (by rw [← e8] at hwr; exact hwr)⟩
  all_goals
    simp only [State.withRegions_wr, wrG, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
  · exact dKD
  · exact dKV
  · exact dKS
  · exact dDA.symm
  · exact dVA.symm
  · exact dSA.symm
  · exact dRD
  · exact dRV
  · exact dRS
  · show Region.Disjoint (below (s.gpr .esp) 8) _; rw [be]; exact dBD
  · show Region.Disjoint (below (s.gpr .esp) 8) _; rw [be]; exact dBV
  · show Region.Disjoint (below (s.gpr .esp) 8) _; rw [be]; exact dBS

theorem cfb_pub {post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits} {postX : State → State → Prop} (s₁ s₂ : State)
    (_ : (pW Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s₁) (_ : (pW Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s₂)
    (h : (pW Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pub s₁ s₂) :
    (modeW postX).pub (s₁.withRegions (rdG false true s₁) (wrG 888 true s₁)) (s₂.withRegions (rdG false true s₂) (wrG 888 true s₂)) := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, Curry.withScratch] at h
  obtain ⟨hsp, h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨hsp, fun i hi => ?_⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem cfbK_verified {post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits} {postX : State → State → Prop} {c : Prog isa}
    (hwp : ∀ s, (modeW postX).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (modeW postX).post s s')
    (hct : ConstantTime isa (modeW postX).pre (modeW postX).pub c)
    (hpost : ∀ s s', (pW Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s →
      postX (s.withRegions (rdG false true s) (wrG 888 true s)) (s'.withRegions (rdG false true s) (wrG 888 true s)) →
        (pW Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).post s s')
    (hsat : ∃ s, (pW Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s) :
    Verified X86.target c (pW Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post) := by
  have narrowSat : ∃ s, (modeW postX).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, (cfb_pre s hs).1⟩
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat)) (rdG false true) (wrG 888 true)
    (fun s h => (cfb_pre s h).1) (fun s h => ?_) (fun s h => ?_) hpost cfb_pub hsat
  · obtain ⟨-, hrd, hwr⟩ := cfb_pre s h
    rw [hrd, hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [rdG, wrG, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h | h | h <;> simp only [h, true_or, or_true]
  · obtain ⟨-, -, hwr⟩ := cfb_pre s h
    rw [hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [wrG, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]

theorem cfb_sat {post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits} :
    ∃ s, (pW Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s := by
  refine ⟨satW, ?_⟩
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, Curry.withScratch, satW, ModeFns.satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

theorem cfb_frameSat (post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cfbSig.contract X86.abi (Spec.Cast5.cfbPre X86.abi.ptrBits) post true 928).pre s := by
  refine ⟨frameSatW, ?_⟩
  sig_pre [Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, frameSatW, ModeFns.satArgs, X86.arg,
    X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

theorem cbcC_pre {post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits} (s : State)
    (h : (pW Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s) :
    GPre false 888 8 true (s.withRegions (rdG false true s) (wrG 888 true s)) ∧ s.rd = [keyA s] ∧
      s.wr = [ivA s, ⟨(arg s 3).setWidth 64, (arg s 4).toNat * 8⟩, scrG 888 s, argsA s] := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, stackBelow, Curry.withScratch] at h
  obtain ⟨h8, hsp, hrd, hwr, dKV, dKD, dKS, -, dVD, dVS, dVA, dDS, dDA, dSA, -, dRV, dRD, dRS, -, dBK, dBV, dBD,
    dBS, -, fK, fV, fD, fS, nv⟩ := h
  have be := below8 h8
  have e8 : (arg s 4).toNat * 8 = 8 * (arg s 4).toNat := Nat.mul_comm _ _
  rw [e8] at hwr dKD dVD dDS dDA dRD dBD fD
  refine ⟨⟨rfl, rfl, h8, (by show (s.gpr .esp).toNat + 28 ≤ 2 ^ 32; omega_using [hsp]), nv, fK, fV, fD, fS,
    (fun h => nomatch h), dDS, dVS, (fun _ => dVD), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_),
    (by show Region.Disjoint _ (below (s.gpr .esp) 8); rw [be]; exact dBK.symm)⟩, hrd, (by rw [← e8] at hwr; exact hwr)⟩
  all_goals
    simp only [State.withRegions_wr, wrG, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
  · exact dKD
  · exact dKV
  · exact dKS
  · exact dDA.symm
  · exact dVA.symm
  · exact dSA.symm
  · exact dRD
  · exact dRV
  · exact dRS
  · show Region.Disjoint (below (s.gpr .esp) 8) _; rw [be]; exact dBD
  · show Region.Disjoint (below (s.gpr .esp) 8) _; rw [be]; exact dBV
  · show Region.Disjoint (below (s.gpr .esp) 8) _; rw [be]; exact dBS

theorem cbcC_pub {post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits} {postX : State → State → Prop} (s₁ s₂ : State)
    (_ : (pW Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s₁) (_ : (pW Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s₂)
    (h : (pW Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pub s₁ s₂) :
    (modeW postX).pub (s₁.withRegions (rdG false true s₁) (wrG 888 true s₁)) (s₂.withRegions (rdG false true s₂) (wrG 888 true s₂)) := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, Curry.withScratch] at h
  obtain ⟨hsp, h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨hsp, fun i hi => ?_⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem cbcCK_verified {post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits} {postX : State → State → Prop} {c : Prog isa}
    (hwp : ∀ s, (modeW postX).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (modeW postX).post s s')
    (hct : ConstantTime isa (modeW postX).pre (modeW postX).pub c)
    (hpost : ∀ s s', (pW Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s →
      postX (s.withRegions (rdG false true s) (wrG 888 true s)) (s'.withRegions (rdG false true s) (wrG 888 true s)) →
        (pW Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).post s s')
    (hsat : ∃ s, (pW Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s) :
    Verified X86.target c (pW Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post) := by
  have narrowSat : ∃ s, (modeW postX).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, (cbcC_pre s hs).1⟩
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat)) (rdG false true) (wrG 888 true)
    (fun s h => (cbcC_pre s h).1) (fun s h => ?_) (fun s h => ?_) hpost cbcC_pub hsat
  · obtain ⟨-, hrd, hwr⟩ := cbcC_pre s h
    rw [hrd, hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [rdG, wrG, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h | h | h <;> simp only [h, true_or, or_true]
  · obtain ⟨-, -, hwr⟩ := cbcC_pre s h
    rw [hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [wrG, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]

theorem cbcC_sat {post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits} :
    ∃ s, (pW Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s := by
  refine ⟨satW, ?_⟩
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, Curry.withScratch, satW, ModeFns.satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

theorem cbcC_frameSat (post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cbcChainedSig.contract X86.abi (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post true 928).pre s := by
  refine ⟨frameSatW, ?_⟩
  sig_pre [Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, frameSatW, ModeFns.satArgs, X86.arg,
    X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

/-! ## The functions -/

open VG.Proof.Cast5.ScrubLocal
open VG.Proof.Aes.ScrubLocal (bytesAt_of0)

/-! ## `cbcDecryptChained` -/

theorem cbcDecryptChained_verified :
    Verified X86.target cbcDecryptChained (pW Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) (Proof.Cast5.cbcDecChainedPost X86.abi.ptrBits)) :=
  cbcCK_verified (fun _ hs => cbcDecryptChained_wp hs) cbcDecryptChained_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcDecChainedPost, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Curry.withScratch]
      exact h) cbcC_sat

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 920 5 222 cbcDecryptChained)
      (Proof.Cast5.cbcDecryptChainedRoundsContract X86.abi 928) :=
  X86.Verified.stackScratchWiped (sig := Spec.Cast5.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 111)
    (pre := Proof.Cast5.cbcChainedPre X86.abi.ptrBits) (post := Proof.Cast5.cbcDecChainedPost X86.abi.ptrBits) (wa := true) (stack := 8) (bytes := 920)
    cbcDecryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cbcDecChainedPost_local _) (Proof.Cast5.cbcDecChainedPostOut_local _) (cbcC_frameSat _)

theorem cbcDecryptChainedOut (stack : Nat) :
    PostOut (Spec.Cast5.cbcDecryptChainedContract X86.abi stack) (Spec.Cast5.cbcChainedSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenP ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-- `Spec.Cast5.cbcDecryptChainedApi` as emitted (`Impl.Cast5.X86.Ssse3.Wide.Fn.cbcDecryptChained`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed X86.target Fn.cbcDecryptChained (Spec.Cast5.cbcDecryptChainedContract X86.abi 928) 0 :=
  verifiedScrubbedSel (api := Spec.Cast5.cbcDecryptChainedApi) (W := 928)
    { code := Impl.StackScratch.X86.withStackScratchWiped 920 5 222 cbcDecryptChained
      verified := Proof.Cast5.cbcDecryptChained_keyed cbcDecryptChained_framed }
    Fn.words (cbcDecryptChainedOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-! ## `cfbDecrypt` -/

theorem cfbDecrypt_verified :
    Verified X86.target cfbDecrypt (pW Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) (Proof.Cast5.cfbDecPost X86.abi.ptrBits)) :=
  cfbK_verified (fun _ hs => cfbDecrypt_wp hs) cfbDecrypt_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, Proof.Cast5.cfbDecPost, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Curry.withScratch]
      exact h) cfb_sat

/-- `cfbDecrypt` with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 920 5 222 cfbDecrypt)
      (Proof.Cast5.cfbDecryptRoundsContract X86.abi 928) :=
  X86.Verified.stackScratchWiped (sig := Spec.Cast5.cfbSig) (nm := "scratch") (e := .u64) (n := 111)
    (pre := Spec.Cast5.cfbPre X86.abi.ptrBits) (post := Proof.Cast5.cfbDecPost X86.abi.ptrBits) (wa := true) (stack := 8) (bytes := 920)
    cfbDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbDecPost_local _) (Proof.Cast5.cfbDecPostOut_local _) (cfb_frameSat _)

theorem cfbDecryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbDecryptContract X86.abi stack) (Spec.Cast5.cfbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenP ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-- `Spec.Cast5.cfbDecryptApi` as emitted (`Impl.Cast5.X86.Ssse3.Wide.Fn.cfbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Fn.cfbDecrypt (Spec.Cast5.cfbDecryptContract X86.abi 928) 0 :=
  verifiedScrubbedSel (api := Spec.Cast5.cfbDecryptApi) (W := 928)
    { code := Impl.StackScratch.X86.withStackScratchWiped 920 5 222 cfbDecrypt
      verified := Proof.Cast5.cfbDecrypt_keyed cfbDecrypt_framed }
    Fn.words (cfbDecryptOut _) (by decide) ⟨_, by taint_decide_ct⟩

/-! ## ECB -/

namespace Ecb

open VG.Impl.Modes
open VG.Proof.Modes.X86 (stkRegion ecbLevels_wp eScrR EcbPre)
open VG.Proof.Cast5 (dirCipher bytesAt_eq)
open VG.Impl.Cast5.X86 (at_)

/-- The direction: encryption (`up`) or decryption. -/
abbrev dir (up : Bool) : Spec.Cast5.Direction := if up then .encrypt else .decrypt

/-- ECB's signature without the working space that its `Api` gives it. -/
def sig4 : Sig where
  params := [("schedule", .array false .u8 128), ("rounds", .int .usize true),
    ("data", .slice true (.array .u8 8) "n")]

/-- `rounds` is 12 or 16. -/
def pre4 (pb : Nat) : Curry (sig4.words pb) (Mem → Prop) :=
  fun _schedule rounds _data _n _ => rounds.toNat = 12 ∨ rounds.toNat = 16

/-- The `n` blocks at `data` are replaced with their encryption or decryption
with `rounds` rounds under the subkeys at `schedule`. -/
def post4 (d : Spec.Cast5.Direction) (pb : Nat) : sig4.Post pb :=
  fun schedule rounds data n m m' _ =>
    Spec.Cast5.blocksAt m' data n.toNat =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt m schedule) rounds.toNat d (Spec.Cast5.blocksAt m data n.toNat)

/-- ECB on x86 with its working space as the fifth argument, encrypting
(`up`) or decrypting. -/
def ecbX (up : Bool) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 888⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 8
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint scratch ∧
    stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 8 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 888 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ 8 ≤ (s.gpr .esp).toNat ∧
    ((arg s 1).toNat = 12 ∨ (arg s 1).toNat = 16)
  post s s' :=
    Spec.Cast5.blocksAt s'.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64)) (arg s 1).toNat (dir up)
        (Spec.Cast5.blocksAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

theorem scr_eq (up : Bool) (s : State) : eScrR s (core16 up) = ⟨(arg s 4).setWidth 64, 888⟩ := by
  simp [eScrR, core16]

/-- The eight bytes of stack below `esp` are apart from the arguments and the return address. -/
theorem stk_apart {s : State} (hfit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) (hlo : 8 ≤ (s.gpr .esp).toNat) :
    Region.Disjoint (stkRegion (s.gpr .esp) 8) ⟨argAddr s 0, 20⟩ ∧
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

/-- `ecbX`'s precondition gives the mode's. -/
theorem ecbPre_of {up : Bool} {s : State} (h : (ecbX up).pre s) : EcbPre (core16 up) s := by
  obtain ⟨hrd, hwr, -, dKS, dDS, dAD, dAS, dRD, dRS, -, dSD, dSS, fK, fD, fS, fE, fLo, -⟩ := h
  have hL := (coreSpec16 up).layout
  obtain ⟨sA, sR⟩ := stk_apart fE fLo
  refine ⟨(by rw [hrd]; simp [core16]), fE, ⟨(by rw [hwr]; simp [core16]),
      (by simp only [core16]; omega_arith)⟩, (by rw [hwr]; simp [core16]),
    fD, ?_, ?_, ?_, dRD, dSD, ?_, sA, sR, fLo, hL⟩
  · rw [scr_eq]; exact dDS
  · rw [scr_eq]; exact dAS
  · rw [scr_eq]; exact dRS
  · exact dSS.sub_right (VG.Offset.sub_base _ (by simp only [core16]; omega_arith))

/-- `ecbX`'s precondition gives the key's: the subkeys and the number of
rounds, the first two arguments. -/
theorem keyArgs_of {up : Bool} {s : State} (h : (ecbX up).pre s) :
    (coreSpec16 up).KeyArgs s [eScrR s (core16 up)]
      (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64), (arg s 1).toNat) := by
  obtain ⟨hrd, hwr, dKD, dKS, -, dAD, dAS, -, -, dSK, -, dSS, fK, -, -, fE, fLo, nv⟩ := h
  obtain ⟨sA, -⟩ := stk_apart fE fLo
  have argSub : (Mode.argR s).Sub ⟨argAddr s 0, 20⟩ := by
    have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_arith)
    show Region.Sub ⟨addr (s.gpr .esp) 4, 8⟩ ⟨argAddr s 0, 20⟩
    rw [e0, show addr (s.gpr .esp) 4 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 + BitVec.ofNat 64 0 by
      rw [BitVec.add_zero]; exact addr_eq (by omega_arith)]
    exact VG.Offset.sub_base _ (by decide)
  have dW : ∀ r ∈ s.wr, Region.Disjoint ⟨(arg s 0).setWidth 64, 128⟩ r ∧ Region.Disjoint ⟨argAddr s 0, 20⟩ r := by
    intro r hr
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨dKD, dAD⟩, ⟨dKS, dAS⟩]
  refine ⟨arg s 0, ⟨by omega_arith, fLo, ⟨⟨argAddr s 0, 20⟩, by rw [hrd]; simp, ?_⟩, rfl, ?_, nv, fK,
    ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩, rfl, (fun ht => nomatch ht),
    fun r hr => ⟨(dW r hr).1, (dW r hr).2.sub_left argSub⟩, dSK.symm, (sA.symm.sub_left argSub)⟩, fun r hr => ?_⟩
  · show (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s 0) 8
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  · show arg s 1 = BitVec.ofNat 32 (arg s 1).toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact ⟨dKS, (fun ht => nomatch ht), dAS.sub_left argSub, dSS⟩

/-- The blocks, from their bytes: each the block function of the block it
was. -/
theorem blocksAt_of_chunks {m m' : Mem} {p : Addr} {n r : Nat} {up : Bool} {k : Spec.Cast5.Schedule}
    (h : Proof.Modes.chunksAt 8 m' p n = (Proof.Modes.chunksAt 8 m p n).map (dirCipher up k r)) :
    Spec.Cast5.blocksAt m' p n = (Spec.Cast5.blocksAt m p n).map (VG.Proof.Cast5.X86.cipher up k r) := by
  simp only [Proof.Modes.chunksAt, List.map_map] at h
  simp only [Spec.Cast5.blocksAt, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have e := List.map_inj_left.mp h i hi
  simp only [Function.comp_apply] at e ⊢
  rw [Mode.dirCipher_bytes, bytesAt_eq] at e
  exact Vector.toList_inj.mp e

theorem ecb_eq (up : Bool) (k : Spec.Cast5.Schedule) (r : Nat) (xs : List Spec.Cast5.Block) :
    Spec.Cast5.ecb k r (dir up) xs = xs.map (VG.Proof.Cast5.X86.cipher up k r) := by
  cases up <;> rfl

theorem ecb_wp (up : Bool) {s₀ : State} (hp : (ecbX up).pre s₀) :
    WP isa (ecb up) s₀ fun s' => abiPreserved s₀ s' ∧ (ecbX up).post s₀ s' :=
  WP.mono (ecbLevels_wp (coreSpec16 up) (gs := levels) (levels_fit up) (ecbPre_of hp) (keyArgs_of hp))
    fun s' ⟨h1, h2⟩ => ⟨h1, by
      show Spec.Cast5.blocksAt s'.mem ((arg s₀ 2).setWidth 64) (arg s₀ 3).toNat = Spec.Cast5.ecb _ _ _ _
      rw [ecb_eq]
      exact blocksAt_of_chunks h2⟩

/-! ### Constant time -/

/-- The initial taint: `esp` public, and the words holding `data` and
`scratch` known to be the base addresses of the writable regions. -/
def ecbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 8 * 111], argLen := 24,
    argBases := [(12, 0), (20, 1)], room := 8 }

theorem ecbTaint_wf {up : Bool} {s : State} (hp : (ecbX up).pre s) : VG.X86.Taint.Wf ecbTaint s := by
  obtain ⟨hrd, hwr, -, dKS, dDS, dAD, dAS, dRD, dRS, -, dSD, dSS, fK, fD, fS, fE, fLo, -⟩ := hp
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
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRS dAS
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

theorem ecbTaint_agree {up : Bool} {s₁ s₂ : State} (h₁ : (ecbX up).pre s₁) (h₂ : (ecbX up).pre s₂)
    (hpub : (ecbX up).pub s₁ s₂) : VG.X86.Taint.Agree ecbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁, -, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂, -, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbTaint_wf h₁, ecbTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ecbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 2 (by omega_arith), ha 3 (by omega_arith), ha 4 (by omega_arith)]
  · simp only [ecbTaint] at hk
    rw [show VG.X86.Taint.depth ecbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 24) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_arith)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_arith))]
    exact congrArg _ (ha _ (by omega_arith))

/-- Constant time: the round's type, on which the sixteen-block function
branches, is computed from the round's number in the working space, which
the analysis finds public, as it does the count of rounds left. -/
theorem ecb_ct (up : Bool) : ConstantTime isa (ecbX up).pre (ecbX up).pub (ecb up) := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.sseTaint.check ecbTaint (ecb up) h).isSome = true := by
    cases up <;> exact ⟨_, by taint_decide⟩
  exact VG.Taint.constantTime (A := VG.X86.sseTaint) ecbTaint (fun _ _ h₁ h₂ hp => ecbTaint_agree h₁ h₂ hp) h

/-! ### The contracts -/

/-- The ECB functions' contract with the working space as the fifth
argument. -/
abbrev ecbScratch (up : Bool) : Contract isa :=
  Sig.scratchContract X86.abi sig4 "scratch" .u64 111 (pre4 X86.abi.ptrBits) (post4 (dir up) X86.abi.ptrBits) false 8

/-- The arguments of the witnesses, at `0x8004`: the subkeys at `0x1000`, 16
rounds, no data at `0x2000` and a working space at `0x4000`. -/
def satArgs : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20 else if a = 0x8015 then 0x40
  else 0

/-- A state with those arguments that may read `rd` and write `wr`. -/
def satS (rd wr : List Region) : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satArgs
  rd := rd
  wr := wr
  syms _ := 0

theorem ecbX_implies (up : Bool) : (ecbX up).Implies (ecbScratch up) where
  pre s h := by
    sig_pre [Sig.scratchContract, Sig.withScratch, sig4, pre4, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, stackBelow, Curry.withScratch, Curry.app] at h
    obtain ⟨h8, hsp, hrd, hwr, dKD, dKS, dDS, dDA, dSA, -, dRD, dRS, -, dBK, dBD, dBS, -, fK, fD, fS, nv⟩ := h
    have be := below8 h8
    have e8 : (arg s 3).toNat * 8 = 8 * (arg s 3).toNat := Nat.mul_comm _ _
    rw [e8] at hwr dKD dDS dDA dRD dBD fD
    exact ⟨hrd, hwr, dKD, dKS, dDS, dDA.symm, dSA.symm, dRD, dRS, by rw [be]; exact dBK, by rw [be]; exact dBD,
      by rw [be]; exact dBS, fK, fD, fS, by omega_using [hsp], h8, nv⟩
  post := by
    intro s t _ h
    sig_post [Sig.scratchContract, Sig.withScratch, sig4, post4, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, Curry.withScratch]
    exact h
  pub s t _ _ h := by
    sig_pub [Sig.scratchContract, Sig.withScratch, sig4, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
      Curry.withScratch] at h
    obtain ⟨hsp, h0, h1, h2, h3, h4⟩ := h
    refine ⟨hsp, fun i hi => ?_⟩
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  sat := by
    refine ⟨satS [⟨0x1000, 128⟩, ⟨0x8004, 20⟩] [⟨0x2000, 0⟩, ⟨0x4000, 888⟩], ?_⟩
    sig_pre [Sig.scratchContract, Sig.withScratch, sig4, pre4, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, Curry.withScratch, Curry.app, satS, satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    sig_and_intros
    all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

theorem ecb_verified (up : Bool) : Verified X86.target (ecb up) (ecbScratch up) :=
  Verified.of_correct (fun _ hs => ecb_wp up hs) (ecb_ct up) (ecbX_implies up)

/-! ### The frame -/

open VG.Proof.Cast5.ScrubLocal

/-- The precondition reads no memory. -/
theorem pre4_local : ∀ vs m₁ m₂, vs.length = (sig4.words X86.abi.ptrBits).length →
    (∀ b ∈ Sig.bufs sig4.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sig4.words X86.abi.ptrBits) (pre4 X86.abi.ptrBits) vs m₁ →
      Curry.apply (sig4.words X86.abi.ptrBits) (pre4 X86.abi.ptrBits) vs m₂ := by
  intro vs m₁ m₂ hlen _ h
  match vs, hlen with
  | [sch, rd, dt, ln], _ => exact h

/-- The postcondition reads the memory on entry only within the subkeys and
the data. -/
theorem post4_local (d : Spec.Cast5.Direction) : ∀ vs m₁ m₂ m' r,
    vs.length = (sig4.words X86.abi.ptrBits).length →
    (∀ b ∈ Sig.bufs sig4.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sig4.words X86.abi.ptrBits) (post4 d X86.abi.ptrBits) vs m₁ m' r →
      Curry.apply (sig4.words X86.abi.ptrBits) (post4 d X86.abi.ptrBits) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  match vs, hlen with
  | [sch, rd, dt, ln], _ =>
    simp only [sig4, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    show Spec.Cast5.blocksAt m' dt _ =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt m₂ sch) _ d (Spec.Cast5.blocksAt m₂ dt _)
    rw [blocksAt_of0 hb.2 (lenP ln 8), scheduleAt_of hb.1]
    exact h

/-- The postcondition reads the memory on return only within the data. -/
theorem post4Out_local (d : Spec.Cast5.Direction) : ∀ vs m m₁ m₂ r,
    vs.length = (sig4.words X86.abi.ptrBits).length →
    (∀ b ∈ Sig.bufs sig4.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sig4.words X86.abi.ptrBits) (post4 d X86.abi.ptrBits) vs m m₁ r →
      Curry.apply (sig4.words X86.abi.ptrBits) (post4 d X86.abi.ptrBits) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [sch, rd, dt, ln], _ =>
    simp only [sig4, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    show Spec.Cast5.blocksAt m₂ dt _ = _
    rw [blocksAt_of0 hb.2 (lenP ln 8)]
    exact h

/-- The contract of the function with its working space in a frame, by the
signature without the caller's: 924 bytes of stack. -/
abbrev ecbFrame (up : Bool) : Contract isa :=
  sig4.contract X86.abi (pre4 X86.abi.ptrBits) (post4 (dir up) X86.abi.ptrBits) false 924

theorem frame_sat (up : Bool) : ∃ s, (ecbFrame up).pre s := by
  refine ⟨satS [⟨0x1000, 128⟩, ⟨0x8004, 16⟩] [⟨0x2000, 0⟩], ?_⟩
  sig_pre [sig4, pre4, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, satS, satArgs, X86.arg, X86.argAddr,
    Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

/-- ECB encrypting (`up`) or decrypting, with its working space on the
stack, zeroed on return. -/
theorem ecb_framed (up : Bool) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 916 4 222 (ecb up)) (ecbFrame up) :=
  X86.Verified.stackScratchWiped (sig := sig4) (nm := "scratch") (e := .u64) (n := 111)
    (pre := pre4 X86.abi.ptrBits) (post := post4 (dir up) X86.abi.ptrBits) (wa := false) (stack := 8)
    (bytes := 916) (ecb_verified up) (by decide) (by cases up <;> lit_decide) (by cases up <;> lit_decide)
    (by decide) pre4_local (post4_local _) (post4Out_local _) (frame_sat up)

/-! ### The `Api`'s contract -/

/-- What the function reads, of what its `Api`'s contract lets it: the
subkeys and its first four arguments. -/
def rd4 (s : State) : List Region := [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 16⟩]
/-- What it writes: the data, and not the caller's `scratch`. -/
def wr4 (s : State) : List Region := [⟨(arg s 2).setWidth 64, (arg s 3).toNat * 8⟩]

/-- The `Api`'s precondition gives the frame's, with the regions `rd4` and
`wr4`. -/
theorem api_pre (up : Bool) (s : State) (h : (Proof.Cast5.ecbRoundsContract X86.abi (dir up) 924).pre s) :
    (ecbFrame up).pre (s.withRegions (rd4 s) (wr4 s)) ∧
      s.rd = [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 20⟩] ∧
      s.wr = [⟨(arg s 2).setWidth 64, (arg s 3).toNat * 8⟩, ⟨(arg s 4).setWidth 64, 256⟩] := by
  sig_pre [Proof.Cast5.ecbRoundsContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, stackBelow] at h
  obtain ⟨h9, hsp, hrd, hwr, dKD, -, -, dDA, -, dRK, dRD, -, dRA, dBK, dBD, -, dBA, fK, fD, -, nv⟩ := h
  refine ⟨?_, hrd, hwr⟩
  sig_pre [sig4, pre4, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, stackBelow, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr, rd4, wr4]
  exact ⟨h9, by omega_using [hsp], dKD, dDA.sub_right (Region.sub_prefix (by decide)), dRK, dRD,
    dRA.sub_right (Region.sub_prefix (by decide)), dBK, dBD, dBA.sub_right (Region.sub_prefix (by decide)), fK, fD,
    nv⟩

theorem api_sat (up : Bool) : ∃ s, (Proof.Cast5.ecbRoundsContract X86.abi (dir up) 924).pre s := by
  refine ⟨satS [⟨0x1000, 128⟩, ⟨0x8004, 20⟩] [⟨0x2000, 0⟩, ⟨0x4000, 256⟩], ?_⟩
  sig_pre [Proof.Cast5.ecbRoundsContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, satS, satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

/-- **ECB with the working space in the function's own frame meets the
contract of its `Api`**, with `rounds` for the key's length: it reads the
subkeys and its first four arguments and writes the data, so neither reads
nor writes the caller's `scratch`. -/
theorem ecb_rounds (up : Bool) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 916 4 222 (ecb up))
      (Proof.Cast5.ecbRoundsContract X86.abi (dir up) 924) := by
  refine Verified.narrowTo (ecb_framed up) rd4 wr4 (fun s h => (api_pre up s h).1) (fun s h => ?_) (fun s h => ?_)
    (fun s s' _ hp => ?_) (fun s₁ s₂ _ _ hp => ?_) (api_sat up)
  · obtain ⟨-, hrd, hwr⟩ := api_pre up s h
    rw [hrd, hwr]
    intro a n ⟨r, hr, hc⟩
    simp only [rd4, wr4, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, hc⟩
    · exact ⟨⟨argAddr s 0, 20⟩, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [Region.Contains] at hc ⊢; omega_arith⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hc⟩
  · obtain ⟨-, -, hwr⟩ := api_pre up s h
    rw [hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [wr4, List.mem_singleton] at hr
    subst hr; exact List.mem_cons_self
  · sig_post [sig4, post4, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, VG.X86.arg_withRegions,
      VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem] at hp
    sig_post [Proof.Cast5.ecbRoundsContract, Proof.Cast5.ecbRoundsPost, Spec.Cast5.ecbSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes]
    exact hp
  · sig_pub [Proof.Cast5.ecbRoundsContract, Spec.Cast5.ecbSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at hp
    obtain ⟨hsp, h0, h1, h2, h3, -⟩ := hp
    sig_pub [sig4, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, VG.X86.arg_withRegions,
      VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem]
    exact ⟨hsp, h0, h1, h2, h3⟩

/-! ### The functions as emitted -/

/-- The postcondition reads the memory on return only within the data. -/
theorem ecbOut (d : Spec.Cast5.Direction) (stack : Nat) :
    PostOut (Spec.Cast5.ecbContract X86.abi d stack) (Spec.Cast5.ecbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, dt, ln, sc], _ =>
      simp only [Spec.Cast5.ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key → Spec.Cast5.blocksAt m₂ dt _ = _
      intro key hk
      rw [blocksAt_of0 hb.2.1 (lenP ln 8)]
      exact h key hk

/-- `Spec.Cast5.ecbEncryptApi` as emitted (`Impl.Cast5.X86.Ssse3.Wide.Fn.ecbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Fn.ecbEncrypt (Spec.Cast5.ecbEncryptContract X86.abi 924) 0 :=
  verifiedScrubbedSel (api := Spec.Cast5.ecbEncryptApi) (W := 924)
    { code := Impl.StackScratch.X86.withStackScratchWiped 916 4 222 (ecb true)
      verified := Proof.Cast5.ecbEncrypt_keyed (ecb_rounds true) }
    Fn.ecbWords (ecbOut .encrypt _) (by decide) ⟨_, by taint_decide_ct⟩

/-- `Spec.Cast5.ecbDecryptApi` as emitted (`Impl.Cast5.X86.Ssse3.Wide.Fn.ecbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Fn.ecbDecrypt (Spec.Cast5.ecbDecryptContract X86.abi 924) 0 :=
  verifiedScrubbedSel (api := Spec.Cast5.ecbDecryptApi) (W := 924)
    { code := Impl.StackScratch.X86.withStackScratchWiped 916 4 222 (ecb false)
      verified := Proof.Cast5.ecbDecrypt_keyed (ecb_rounds false) }
    Fn.ecbWords (ecbOut .decrypt _) (by decide) ⟨_, by taint_decide_ct⟩

end Ecb

end VG.Proof.Cast5.X86.Ssse3.Wide
