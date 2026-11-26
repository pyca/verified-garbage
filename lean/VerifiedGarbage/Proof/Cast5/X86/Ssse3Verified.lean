module

public import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lookup
public import VerifiedGarbage.Proof.Cast5.X86.ModesVerified
public import VerifiedGarbage.Proof.Cast5.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
public import VerifiedGarbage.Spec.Cast5.OfbFinal
public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.CfbFinal
import VerifiedGarbage.Proof.Cast5.X86.Scrub
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Cast5.ScrubLocal
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lookup
meta import VerifiedGarbage.Proof.Cast5.X86.ModesVerified
meta import VerifiedGarbage.Proof.Cast5.X86.FbFinalVerified
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Cast5.Cbc
meta import VerifiedGarbage.Spec.Cast5.Cfb
meta import VerifiedGarbage.Spec.Cast5.Ofb
meta import VerifiedGarbage.Spec.Cast5.CfbFinal
meta import VerifiedGarbage.Spec.Cast5.OfbFinal
meta import VerifiedGarbage.Proof.Cast5.Rounds
meta import VerifiedGarbage.Proof.Cast5.CfbFinal
meta import VerifiedGarbage.Proof.Cast5.X86.Scrub
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Cast5.ScrubLocal
meta import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Framework.TaintCTAll
public meta import VerifiedGarbage.Proof.Framework.TaintCTAll

/-!
# CAST5's modes over the look-ups by `pshufb` on x86 (32-bit): the contracts

The modes that encrypt a block at a time (CBC encryption, OFB, CFB64
encryption and the three functions for a message's last piece), over the
rounds whose look-ups are the function by `pshufb`
(`Impl.Cast5.X86.Ssse3.core`, `Ssse3Lookup.lean`): the look-ups as the
modes' core takes them (`lookupCore`), the core's `CoreSpec` (`coreSpec`)
and that it fits the lemmas for any core (`fits`: no table in memory, 632
bytes of working space, eight bytes of stack).

Each function meets the contract of its `Api` over the calling convention
with no table of constants (the planes are in the instructions that load
them, `movdquTbl`), with 672 bytes of stack: 664 of the frame of its working
space and the eight of the call of the look-ups' function and its own.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86.Ssse3

open VG VG.X86 VG.X86.Scrub VG.Impl.Cast5.X86.Ssse3
open VG.Proof.Cast5.X86.Mode (LkCore coreSpecWith)
open VG.Proof.Cast5.X86.ModeFns (GPre Fits keyA ivA dataA argsA retA scrG stkG rdG wrG τG)
open VG.Proof.Cast5.X86.FbFinal (GFPre dataF rdGF wrGF)
open VG.Proof.Modes.X86 (CoreSpec)

/-! ## The core -/

/-- The look-ups' function fits the core of 148 slots, with no table in memory. -/
theorem lookupCore : LkCore lookupLk false 148 where
  ok := lookupLk_ok
  cs66 := by decide
  xin _ _ hx := ⟨272, 320, List.mem_singleton.mp hx, by decide, by decide⟩
  pre hb hw hfit hsd :=
    ⟨hb.sp, by omega, fun _ _ _ _ => ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩,
      (hsd.sub_right (Offset.sub_base _ (by decide))).symm⟩

/-- CAST5's core over the look-ups by `pshufb`, encrypting (`up`) or
decrypting, meets what the modes need. -/
def coreSpec (up : Bool) : CoreSpec (core up) := coreSpecWith lookupCore up

/-- The core fits: no table in memory, 632 bytes and eight of stack. -/
def fits (up : Bool) : Fits (coreSpec up) false 632 8 where
  toKey := id
  keyArgs h := h
  bw := rfl
  ka := rfl
  stack := rfl
  total := rfl

/-- A mode on x86 over this core, with the working space as a sixth argument
and the postcondition `post`. -/
def modeP (post : State → State → Prop) : Contract isa where
  pre := GPre false 632 8 true
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-- A function for a message's last piece over this core. -/
def finalP (post : State → State → Prop) : Contract isa where
  pre := GFPre false 632 8
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-! ## Correctness and constant time -/

theorem cbcEncryptChained_wp {s₀ : State} (hp : (modeP ModeFns.cbcEncPost).pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (modeP ModeFns.cbcEncPost).post s₀ s' :=
  ModeFns.cbcEncryptChained_wp_of (fits true) (fun _ _ => rfl) hp

theorem ofb_wp {s₀ : State} (hp : (modeP ModeFns.ofbPost).pre s₀) :
    WP isa ofb s₀ fun s' => abiPreserved s₀ s' ∧ (modeP ModeFns.ofbPost).post s₀ s' :=
  ModeFns.ofb_wp_of (fits true) (fun _ _ => rfl) hp

theorem cfbEncrypt_wp {s₀ : State} (hp : (modeP ModeFns.cfbEncPost).pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ (modeP ModeFns.cfbEncPost).post s₀ s' :=
  ModeFns.cfbEncrypt_wp_of (fits true) (fun _ _ => rfl) hp

theorem cfbEncryptFinal_wp {s₀ : State} (hp : (finalP FbFinal.encPost).pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (finalP FbFinal.encPost).post s₀ s' :=
  FbFinal.cfbEncryptFinal_wp_of (fits true) (fun _ _ => rfl) hp

theorem cfbDecryptFinal_wp {s₀ : State} (hp : (finalP FbFinal.decPost).pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (finalP FbFinal.decPost).post s₀ s' :=
  FbFinal.cfbDecryptFinal_wp_of (fits true) (fun _ _ => rfl) hp

theorem ofbFinal_wp {s₀ : State} (hp : (finalP FbFinal.ofbPost).pre s₀) :
    WP isa ofbFinal s₀ fun s' => abiPreserved s₀ s' ∧ (finalP FbFinal.ofbPost).post s₀ s' :=
  FbFinal.ofbFinal_wp_of (fits true) (fun _ _ => rfl) hp

theorem cbcEncryptChained_ct :
    ConstantTime isa (modeP ModeFns.cbcEncPost).pre (modeP ModeFns.cbcEncPost).pub cbcEncryptChained :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (τG 632 8)
    (fun _ _ h₁ h₂ hp => ModeFns.τG_agree h₁ h₂ hp.1 hp.2) (by native_taint_decide)

theorem ofb_ct : ConstantTime isa (modeP ModeFns.ofbPost).pre (modeP ModeFns.ofbPost).pub ofb :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (τG 632 8)
    (fun _ _ h₁ h₂ hp => ModeFns.τG_agree h₁ h₂ hp.1 hp.2) (by native_taint_decide)

theorem cfbEncrypt_ct : ConstantTime isa (modeP ModeFns.cfbEncPost).pre (modeP ModeFns.cfbEncPost).pub cfbEncrypt :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (τG 632 8)
    (fun _ _ h₁ h₂ hp => ModeFns.τG_agree h₁ h₂ hp.1 hp.2) (by native_taint_decide)

theorem cfbEncryptFinal_ct :
    ConstantTime isa (finalP FbFinal.encPost).pre (finalP FbFinal.encPost).pub cfbEncryptFinal :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (τG 632 8)
    (fun _ _ h₁ h₂ hp => FbFinal.τG_agree h₁ h₂ hp.1 hp.2) (by native_taint_decide)

theorem cfbDecryptFinal_ct :
    ConstantTime isa (finalP FbFinal.decPost).pre (finalP FbFinal.decPost).pub cfbDecryptFinal :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (τG 632 8)
    (fun _ _ h₁ h₂ hp => FbFinal.τG_agree h₁ h₂ hp.1 hp.2) (by native_taint_decide)

theorem ofbFinal_ct :
    ConstantTime isa (finalP FbFinal.ofbPost).pre (finalP FbFinal.ofbPost).pub ofbFinal :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (τG 632 8)
    (fun _ _ h₁ h₂ hp => FbFinal.τG_agree h₁ h₂ hp.1 hp.2) (by native_taint_decide)

/-! ## The contracts -/

/-- OFB's, CFB's or CBC's contract (`sig`) with the working space as a sixth
argument, under the calling convention with no table. -/
abbrev pK (sig : Sig) (pre : Curry (sig.words X86.abi.ptrBits) (Mem → Prop)) (post : sig.Post X86.abi.ptrBits) :
    Contract isa :=
  Sig.scratchContract X86.abi sig "scratch" .u64 79 pre post true 8

/-! ## States that satisfy the contracts -/

/-- A state satisfying the modes' precondition: the schedule at `0x1000`, 16
rounds, the chaining value at `0x2000`, no data at `0x3000` and the working
space at `0x4000`, as stack arguments at `0x8004`. -/
def satP : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ModeFns.satArgs
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 632⟩, ⟨0x8004, 24⟩]
  syms _ := 0

/-- A state satisfying the functions' precondition, with 672 bytes of stack. -/
def frameSatP : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ModeFns.satArgs
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩]
  syms _ := 0

/-- The eight bytes below `sp`, as the contracts state them. -/
theorem below8 {sp : BitVec 32} (h : 8 ≤ sp.toNat) : below sp 8 = ⟨sp.setWidth 64 - BitVec.ofNat 64 8, 8⟩ := by
  simp only [below, VG.X86.Taint.sub_setWidth h]

theorem ofb_pre {post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits} (s : State)
    (h : (pK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s) :
    GPre false 632 8 true (s.withRegions (rdG false true s) (wrG 632 true s)) ∧ s.rd = [keyA s] ∧
      s.wr = [ivA s, ⟨(arg s 3).setWidth 64, (arg s 4).toNat * 8⟩, scrG 632 s, argsA s] := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, X86.abi, X86.argSlots,
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

theorem ofb_pub {post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits} {postX : State → State → Prop} (s₁ s₂ : State)
    (_ : (pK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s₁) (_ : (pK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s₂)
    (h : (pK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pub s₁ s₂) :
    (modeP postX).pub (s₁.withRegions (rdG false true s₁) (wrG 632 true s₁)) (s₂.withRegions (rdG false true s₂) (wrG 632 true s₂)) := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, X86.abi, X86.argSlots, X86.argVal,
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

theorem ofbK_verified {post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits} {postX : State → State → Prop} {c : Prog isa}
    (hwp : ∀ s, (modeP postX).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (modeP postX).post s s')
    (hct : ConstantTime isa (modeP postX).pre (modeP postX).pub c)
    (hpost : ∀ s s', (pK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s →
      postX (s.withRegions (rdG false true s) (wrG 632 true s)) (s'.withRegions (rdG false true s) (wrG 632 true s)) →
        (pK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).post s s')
    (hsat : ∃ s, (pK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s) :
    Verified X86.target c (pK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post) := by
  have narrowSat : ∃ s, (modeP postX).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, (ofb_pre s hs).1⟩
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat)) (rdG false true) (wrG 632 true)
    (fun s h => (ofb_pre s h).1) (fun s h => ?_) (fun s h => ?_) hpost ofb_pub hsat
  · obtain ⟨-, hrd, hwr⟩ := ofb_pre s h
    rw [hrd, hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [rdG, wrG, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h | h | h <;> simp only [h, true_or, or_true]
  · obtain ⟨-, -, hwr⟩ := ofb_pre s h
    rw [hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [wrG, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]

theorem ofb_sat {post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits} :
    ∃ s, (pK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s := by
  refine ⟨satP, ?_⟩
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, Curry.withScratch, satP, ModeFns.satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

theorem ofb_frameSat (post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.ofbSig.contract X86.abi (Spec.Cast5.ofbPre X86.abi.ptrBits) post true 672).pre s := by
  refine ⟨frameSatP, ?_⟩
  sig_pre [Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, frameSatP, ModeFns.satArgs, X86.arg,
    X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

theorem cfb_pre {post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits} (s : State)
    (h : (pK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s) :
    GPre false 632 8 true (s.withRegions (rdG false true s) (wrG 632 true s)) ∧ s.rd = [keyA s] ∧
      s.wr = [ivA s, ⟨(arg s 3).setWidth 64, (arg s 4).toNat * 8⟩, scrG 632 s, argsA s] := by
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
    (_ : (pK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s₁) (_ : (pK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s₂)
    (h : (pK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pub s₁ s₂) :
    (modeP postX).pub (s₁.withRegions (rdG false true s₁) (wrG 632 true s₁)) (s₂.withRegions (rdG false true s₂) (wrG 632 true s₂)) := by
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
    (hwp : ∀ s, (modeP postX).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (modeP postX).post s s')
    (hct : ConstantTime isa (modeP postX).pre (modeP postX).pub c)
    (hpost : ∀ s s', (pK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s →
      postX (s.withRegions (rdG false true s) (wrG 632 true s)) (s'.withRegions (rdG false true s) (wrG 632 true s)) →
        (pK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).post s s')
    (hsat : ∃ s, (pK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s) :
    Verified X86.target c (pK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post) := by
  have narrowSat : ∃ s, (modeP postX).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, (cfb_pre s hs).1⟩
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat)) (rdG false true) (wrG 632 true)
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
    ∃ s, (pK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s := by
  refine ⟨satP, ?_⟩
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, Curry.withScratch, satP, ModeFns.satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

theorem cfb_frameSat (post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cfbSig.contract X86.abi (Spec.Cast5.cfbPre X86.abi.ptrBits) post true 672).pre s := by
  refine ⟨frameSatP, ?_⟩
  sig_pre [Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, frameSatP, ModeFns.satArgs, X86.arg,
    X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

theorem cbcC_pre {post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits} (s : State)
    (h : (pK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s) :
    GPre false 632 8 true (s.withRegions (rdG false true s) (wrG 632 true s)) ∧ s.rd = [keyA s] ∧
      s.wr = [ivA s, ⟨(arg s 3).setWidth 64, (arg s 4).toNat * 8⟩, scrG 632 s, argsA s] := by
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
    (_ : (pK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s₁) (_ : (pK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s₂)
    (h : (pK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pub s₁ s₂) :
    (modeP postX).pub (s₁.withRegions (rdG false true s₁) (wrG 632 true s₁)) (s₂.withRegions (rdG false true s₂) (wrG 632 true s₂)) := by
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
    (hwp : ∀ s, (modeP postX).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (modeP postX).post s s')
    (hct : ConstantTime isa (modeP postX).pre (modeP postX).pub c)
    (hpost : ∀ s s', (pK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s →
      postX (s.withRegions (rdG false true s) (wrG 632 true s)) (s'.withRegions (rdG false true s) (wrG 632 true s)) →
        (pK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).post s s')
    (hsat : ∃ s, (pK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s) :
    Verified X86.target c (pK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post) := by
  have narrowSat : ∃ s, (modeP postX).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, (cbcC_pre s hs).1⟩
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat)) (rdG false true) (wrG 632 true)
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
    ∃ s, (pK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s := by
  refine ⟨satP, ?_⟩
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, Curry.withScratch, satP, ModeFns.satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

theorem cbcC_frameSat (post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cbcChainedSig.contract X86.abi (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post true 672).pre s := by
  refine ⟨frameSatP, ?_⟩
  sig_pre [Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, frameSatP, ModeFns.satArgs, X86.arg,
    X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

theorem final_pre {post : Spec.Cast5.cfbFinalSig.Post X86.abi.ptrBits} (s : State)
    (h : (pK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pre s) :
    GFPre false 632 8 (s.withRegions (rdGF false s) (wrGF 632 s)) ∧ s.rd = [keyA s] ∧
      s.wr = [ivA s, dataF s, scrG 632 s, argsA s] := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, stackBelow, Curry.withScratch] at h
  obtain ⟨h8, hsp, hrd, hwr, dKV, dKD, dKS, -, dVD, dVS, dVA, dDS, dDA, dSA, -, dRV, dRD, dRS, -, dBK, dBV, dBD,
    dBS, -, fK, fV, fD, fS, nv⟩ := h
  have be := below8 h8
  refine ⟨⟨rfl, rfl, h8, (by show (s.gpr .esp).toNat + 28 ≤ 2 ^ 32; omega_using [hsp]), nv, fK, fV, fD, fS,
    (fun h => nomatch h), dDS, dVS, dVD, (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_),
    (by show Region.Disjoint _ (below (s.gpr .esp) 8); rw [be]; exact dBK.symm)⟩, hrd, hwr⟩
  all_goals
    simp only [State.withRegions_wr, wrGF, List.mem_cons, List.not_mem_nil, or_false] at hr
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

theorem final_pub {post : Spec.Cast5.cfbFinalSig.Post X86.abi.ptrBits} {postX : State → State → Prop} (s₁ s₂ : State)
    (_ : (pK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pre s₁) (_ : (pK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pre s₂)
    (h : (pK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pub s₁ s₂) :
    (finalP postX).pub (s₁.withRegions (rdGF false s₁) (wrGF 632 s₁)) (s₂.withRegions (rdGF false s₂) (wrGF 632 s₂)) := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig, X86.abi, X86.argSlots, X86.argVal,
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

theorem finalK_verified {post : Spec.Cast5.cfbFinalSig.Post X86.abi.ptrBits} {postX : State → State → Prop} {c : Prog isa}
    (hwp : ∀ s, (finalP postX).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (finalP postX).post s s')
    (hct : ConstantTime isa (finalP postX).pre (finalP postX).pub c)
    (hpost : ∀ s s', (pK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pre s →
      postX (s.withRegions (rdGF false s) (wrGF 632 s)) (s'.withRegions (rdGF false s) (wrGF 632 s)) →
        (pK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).post s s')
    (hsat : ∃ s, (pK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pre s) :
    Verified X86.target c (pK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post) := by
  have narrowSat : ∃ s, (finalP postX).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, (final_pre s hs).1⟩
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat)) (rdGF false) (wrGF 632)
    (fun s h => (final_pre s h).1) (fun s h => ?_) (fun s h => ?_) hpost final_pub hsat
  · obtain ⟨-, hrd, hwr⟩ := final_pre s h
    rw [hrd, hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [rdGF, wrGF, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp only [h, true_or, or_true]
  · obtain ⟨-, -, hwr⟩ := final_pre s h
    rw [hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [wrGF, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]

theorem final_sat {post : Spec.Cast5.cfbFinalSig.Post X86.abi.ptrBits} :
    ∃ s, (pK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pre s := by
  refine ⟨satP, ?_⟩
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, Curry.withScratch, satP, ModeFns.satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

theorem final_frameSat (post : Spec.Cast5.cfbFinalSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cfbFinalSig.contract X86.abi (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post true 672).pre s := by
  refine ⟨frameSatP, ?_⟩
  sig_pre [Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, frameSatP, ModeFns.satArgs, X86.arg,
    X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

/-! ## The functions -/

open VG.Proof.Cast5.ScrubLocal
open VG.Proof.Aes.ScrubLocal (bytesAt_of0)

/-- The data's length. -/
theorem lenP (x : BitVec 64) (k : Nat) :
    ((ArgWord.int X86.abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.mul_le_mul_right _ (by simp only [ArgWord.ofRaw, BitVec.toNat_setWidth]; exact Nat.mod_le _ _)

theorem len1P (x : BitVec 64) : ((ArgWord.int X86.abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size := by
  have := lenP x 1
  simpa only [Nat.mul_one, Elem.size] using this

/-- The final OFB function's frame is satisfiable. -/
theorem ofbFinalX_frameSat (post : Spec.Cast5.ofbFinalSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.ofbFinalSig.contract X86.abi (Spec.Cast5.ofbFinalPre X86.abi.ptrBits) post true 672).pre s := by
  refine ⟨frameSatP, ?_⟩
  sig_pre [Spec.Cast5.ofbFinalSig, Spec.Cast5.ofbFinalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
    frameSatP, ModeFns.satArgs, X86.arg, X86.argAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide) | exact Or.inr rfl

/-! ## `cbcEncryptChained` -/

theorem cbcEncryptChained_verified :
    Verified X86.target cbcEncryptChained (pK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) (Proof.Cast5.cbcEncChainedPost X86.abi.ptrBits)) :=
  cbcCK_verified (fun _ hs => cbcEncryptChained_wp hs) cbcEncryptChained_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcEncChainedPost, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Curry.withScratch]
      exact h) cbcC_sat

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 664 5 158 cbcEncryptChained)
      (Proof.Cast5.cbcEncryptChainedRoundsContract X86.abi 672) :=
  X86.Verified.stackScratchWiped (sig := Spec.Cast5.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 79)
    (pre := Proof.Cast5.cbcChainedPre X86.abi.ptrBits) (post := Proof.Cast5.cbcEncChainedPost X86.abi.ptrBits) (wa := true) (stack := 8) (bytes := 664)
    cbcEncryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cbcEncChainedPost_local _) (Proof.Cast5.cbcEncChainedPostOut_local _) (cbcC_frameSat _)

theorem cbcEncryptChainedOut (stack : Nat) :
    PostOut (Spec.Cast5.cbcEncryptChainedContract X86.abi stack) (Spec.Cast5.cbcChainedSig.retBits 32) :=
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

/-- The residue analyses of the functions' code, in one kernel evaluation
(`taint_decide_ct_all`), which analyses the code they share once. -/
theorem residue :
    rtaint.Ends (RTaint.init 672 0) Fn.cbcEncryptChained (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 672 0) Fn.ofb (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 672 0) Fn.cfbEncrypt (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 672 0) Fn.cfbEncryptFinal (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 672 0) Fn.cfbDecryptFinal (RTaint.done 0) ∧
    rtaint.Ends (RTaint.init 672 0) Fn.ofbFinal (RTaint.done 0) := by
  taint_decide_ct_all

/-- `Spec.Cast5.cbcEncryptChainedApi` as emitted (`Impl.Cast5.X86.Ssse3.Fn.cbcEncryptChained`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed X86.target Fn.cbcEncryptChained (Spec.Cast5.cbcEncryptChainedContract X86.abi 672) 0 :=
  verifiedScrubbedSel (api := Spec.Cast5.cbcEncryptChainedApi) (W := 672)
    { code := Impl.StackScratch.X86.withStackScratchWiped 664 5 158 cbcEncryptChained
      verified := Proof.Cast5.cbcEncryptChained_keyed cbcEncryptChained_framed }
    Fn.words (cbcEncryptChainedOut _) (by decide) residue.1

/-! ## `ofb` -/

theorem ofb_verified :
    Verified X86.target ofb (pK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) (Proof.Cast5.ofbPost X86.abi.ptrBits)) :=
  ofbK_verified (fun _ hs => ofb_wp hs) ofb_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, Proof.Cast5.ofbPost, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Curry.withScratch]
      exact h) ofb_sat

/-- `ofb` with its working space on the stack. -/
theorem ofb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 664 5 158 ofb)
      (Proof.Cast5.ofbRoundsContract X86.abi 672) :=
  X86.Verified.stackScratchWiped (sig := Spec.Cast5.ofbSig) (nm := "scratch") (e := .u64) (n := 79)
    (pre := Spec.Cast5.ofbPre X86.abi.ptrBits) (post := Proof.Cast5.ofbPost X86.abi.ptrBits) (wa := true) (stack := 8) (bytes := 664)
    ofb_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.ofbPost_local _) (Proof.Cast5.ofbPostOut_local _) (ofb_frameSat _)

theorem ofbOut (stack : Nat) :
    PostOut (Spec.Cast5.ofbContract X86.abi stack) (Spec.Cast5.ofbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenP ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-- `Spec.Cast5.ofbApi` as emitted (`Impl.Cast5.X86.Ssse3.Fn.ofb`) meets its contract in
constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed X86.target Fn.ofb (Spec.Cast5.ofbContract X86.abi 672) 0 :=
  verifiedScrubbedSel (api := Spec.Cast5.ofbApi) (W := 672)
    { code := Impl.StackScratch.X86.withStackScratchWiped 664 5 158 ofb
      verified := Proof.Cast5.ofb_keyed ofb_framed }
    Fn.words (ofbOut _) (by decide) residue.2.1

/-! ## `cfbEncrypt` -/

theorem cfbEncrypt_verified :
    Verified X86.target cfbEncrypt (pK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) (Proof.Cast5.cfbEncPost X86.abi.ptrBits)) :=
  cfbK_verified (fun _ hs => cfbEncrypt_wp hs) cfbEncrypt_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, Proof.Cast5.cfbEncPost, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Curry.withScratch]
      exact h) cfb_sat

/-- `cfbEncrypt` with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 664 5 158 cfbEncrypt)
      (Proof.Cast5.cfbEncryptRoundsContract X86.abi 672) :=
  X86.Verified.stackScratchWiped (sig := Spec.Cast5.cfbSig) (nm := "scratch") (e := .u64) (n := 79)
    (pre := Spec.Cast5.cfbPre X86.abi.ptrBits) (post := Proof.Cast5.cfbEncPost X86.abi.ptrBits) (wa := true) (stack := 8) (bytes := 664)
    cfbEncrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbEncPost_local _) (Proof.Cast5.cfbEncPostOut_local _) (cfb_frameSat _)

theorem cfbEncryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbEncryptContract X86.abi stack) (Spec.Cast5.cfbSig.retBits 32) :=
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

/-- `Spec.Cast5.cfbEncryptApi` as emitted (`Impl.Cast5.X86.Ssse3.Fn.cfbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Fn.cfbEncrypt (Spec.Cast5.cfbEncryptContract X86.abi 672) 0 :=
  verifiedScrubbedSel (api := Spec.Cast5.cfbEncryptApi) (W := 672)
    { code := Impl.StackScratch.X86.withStackScratchWiped 664 5 158 cfbEncrypt
      verified := Proof.Cast5.cfbEncrypt_keyed cfbEncrypt_framed }
    Fn.words (cfbEncryptOut _) (by decide) residue.2.2.1

/-! ## `cfbEncryptFinal` -/

theorem cfbEncryptFinal_verified :
    Verified X86.target cfbEncryptFinal (pK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) (Proof.Cast5.cfbEncFinalPost X86.abi.ptrBits)) :=
  finalK_verified (fun _ hs => cfbEncryptFinal_wp hs) cfbEncryptFinal_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig, Proof.Cast5.cfbEncFinalPost, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Curry.withScratch]
      exact h) final_sat

/-- `cfbEncryptFinal` with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 664 5 158 cfbEncryptFinal)
      (Proof.Cast5.cfbEncryptFinalRoundsContract X86.abi 672) :=
  X86.Verified.stackScratchWiped (sig := Spec.Cast5.cfbFinalSig) (nm := "scratch") (e := .u64) (n := 79)
    (pre := Spec.Cast5.cfbFinalPre X86.abi.ptrBits) (post := Proof.Cast5.cfbEncFinalPost X86.abi.ptrBits) (wa := true) (stack := 8) (bytes := 664)
    cfbEncryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.cfbFinalPre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbEncFinalPost_local _) (Proof.Cast5.cfbEncFinalPostOut_local _) (final_frameSat _)

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbEncryptFinalContract X86.abi stack) (Spec.Cast5.cfbFinalSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1P ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-- `Spec.Cast5.cfbEncryptFinalApi` as emitted (`Impl.Cast5.X86.Ssse3.Fn.cfbEncryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed X86.target Fn.cfbEncryptFinal (Spec.Cast5.cfbEncryptFinalContract X86.abi 672) 0 :=
  verifiedScrubbedSel (api := Spec.Cast5.cfbEncryptFinalApi) (W := 672)
    { code := Impl.StackScratch.X86.withStackScratchWiped 664 5 158 cfbEncryptFinal
      verified := Proof.Cast5.cfbEncryptFinal_keyed cfbEncryptFinal_framed }
    Fn.words (cfbEncryptFinalOut _) (by decide) residue.2.2.2.1

/-! ## `cfbDecryptFinal` -/

theorem cfbDecryptFinal_verified :
    Verified X86.target cfbDecryptFinal (pK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) (Proof.Cast5.cfbDecFinalPost X86.abi.ptrBits)) :=
  finalK_verified (fun _ hs => cfbDecryptFinal_wp hs) cfbDecryptFinal_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig, Proof.Cast5.cfbDecFinalPost, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Curry.withScratch]
      exact h) final_sat

/-- `cfbDecryptFinal` with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 664 5 158 cfbDecryptFinal)
      (Proof.Cast5.cfbDecryptFinalRoundsContract X86.abi 672) :=
  X86.Verified.stackScratchWiped (sig := Spec.Cast5.cfbFinalSig) (nm := "scratch") (e := .u64) (n := 79)
    (pre := Spec.Cast5.cfbFinalPre X86.abi.ptrBits) (post := Proof.Cast5.cfbDecFinalPost X86.abi.ptrBits) (wa := true) (stack := 8) (bytes := 664)
    cfbDecryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.cfbFinalPre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbDecFinalPost_local _) (Proof.Cast5.cfbDecFinalPostOut_local _) (final_frameSat _)

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbDecryptFinalContract X86.abi stack) (Spec.Cast5.cfbFinalSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1P ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-- `Spec.Cast5.cfbDecryptFinalApi` as emitted (`Impl.Cast5.X86.Ssse3.Fn.cfbDecryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed X86.target Fn.cfbDecryptFinal (Spec.Cast5.cfbDecryptFinalContract X86.abi 672) 0 :=
  verifiedScrubbedSel (api := Spec.Cast5.cfbDecryptFinalApi) (W := 672)
    { code := Impl.StackScratch.X86.withStackScratchWiped 664 5 158 cfbDecryptFinal
      verified := Proof.Cast5.cfbDecryptFinal_keyed cfbDecryptFinal_framed }
    Fn.words (cfbDecryptFinalOut _) (by decide) residue.2.2.2.2.1

/-! ## `ofbFinal` -/

theorem ofbFinal_verified :
    Verified X86.target ofbFinal (pK Spec.Cast5.ofbFinalSig (Spec.Cast5.ofbFinalPre X86.abi.ptrBits) (Proof.Cast5.ofbFinalPost X86.abi.ptrBits)) :=
  finalK_verified (fun _ hs => ofbFinal_wp hs) ofbFinal_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbFinalSig, Proof.Cast5.ofbFinalPost, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Curry.withScratch]
      exact h) final_sat

/-- `ofbFinal` with its working space on the stack. -/
theorem ofbFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 664 5 158 ofbFinal)
      (Proof.Cast5.ofbFinalRoundsContract X86.abi 672) :=
  X86.Verified.stackScratchWiped (sig := Spec.Cast5.ofbFinalSig) (nm := "scratch") (e := .u64) (n := 79)
    (pre := Spec.Cast5.ofbFinalPre X86.abi.ptrBits) (post := Proof.Cast5.ofbFinalPost X86.abi.ptrBits) (wa := true) (stack := 8) (bytes := 664)
    ofbFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.ofbFinalPre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.ofbFinalPost_local _) (Proof.Cast5.ofbFinalPostOut_local _) (ofbFinalX_frameSat _)

theorem ofbFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.ofbFinalContract X86.abi stack) (Spec.Cast5.ofbFinalSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1P ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-- `Spec.Cast5.ofbFinalApi` as emitted (`Impl.Cast5.X86.Ssse3.Fn.ofbFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed X86.target Fn.ofbFinal (Spec.Cast5.ofbFinalContract X86.abi 672) 0 :=
  verifiedScrubbedSel (api := Spec.Cast5.ofbFinalApi) (W := 672)
    { code := Impl.StackScratch.X86.withStackScratchWiped 664 5 158 ofbFinal
      verified := Proof.Cast5.ofbFinal_keyed ofbFinal_framed }
    Fn.words (ofbFinalOut _) (by decide) residue.2.2.2.2.2

end VG.Proof.Cast5.X86.Ssse3
