module

public import VerifiedGarbage.Proof.Camellia.X86.FbVerified
import VerifiedGarbage.Proof.Modes.X86.CbcChained
public import VerifiedGarbage.Proof.Camellia.CbcScratch
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Camellia.X86.CbcLit
meta import VerifiedGarbage.Proof.Camellia.X86.FbVerified
meta import VerifiedGarbage.Proof.Modes.X86.CbcChained
meta import VerifiedGarbage.Proof.Camellia.CbcScratch
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Camellia.X86.CbcLit

/-!
# Camellia-CBC on x86 (32-bit) meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value (`Proof.Modes.X86.cbcEncChained_wp`, `cbcDecChained_wp`)
over Camellia's core for each direction (`dirCoreSpec`), with the working space
as an argument after `n`. The chaining value is written back, so it is
writable, as for OFB and CFB (`Fb.fbX86`), whose contract, taint and
narrowing these share. The `_framed` theorems run them with their working
space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.Cbc

open VG VG.X86 VG.Impl.Camellia.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (SeqPre cbcEncChained_wp cbcDecChained_wp)
open VG.Proof.Camellia.X86 (scr_eq disjoint_empty KeyArgs dirCoreSpec dirCore_ka)
open VG.Proof.Camellia (schedWords)
open VG.Proof.Modes.X86 (argAddr_eq)
open VG.Proof.Camellia.X86.Fb

/-- Camellia's inverse, as `ciph`. -/
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Camellia.invCipher (Spec.Camellia.subkeysAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def decPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

/-- `fbX86`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (d : Dir) (hstep : M.step = 16) {s : State}
    (h : (fbX86 post).pre s) : SeqPre (dirCore d) M s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, fK, fV, fD, fS, fE, hRn⟩ := h
  have hL := (dirCoreSpec d).layout
  refine ⟨(by rw [hrd]; simp [dirCore]), fE, ⟨(by rw [hwr]; simp [dirCore, slots_eq]),
      (by simp only [dirCore, slots_eq]; omega)⟩, (by rw [hwr]; simp [dirCore]),
    (fun _ => by rw [hwr]; simp [dirCore]), (by simp only [dirCore]; omega), (by rw [hwr, hstep]; simp [dirCore]),
    (by rw [hstep]; exact fD), ?_, ?_, (fun _ => ?_), ?_, ?_, ?_, ?_,
    (fun _ => ?_), disjoint_empty _ _, disjoint_empty _ _,
    disjoint_empty _ _, disjoint_empty _ _, (by simp [dirCore]), (by rw [hstep]; simp [dirCore]), hL⟩
  · rw [hstep, scr_eq]; exact dDS
  · rw [scr_eq]; exact dVS
  · rw [hstep]; exact dVD
  · rw [scr_eq]; exact dAS
  · rw [hstep]; exact dAD
  · rw [scr_eq]; exact dRS
  · rw [hstep]; exact dRD
  · exact dRV

theorem keyArgs_of {post : State → State → Prop} (d : Dir) {s : State} (h : (fbX86 post).pre s) :
    KeyArgs s [Modes.X86.scrR s (dirCore d)]
      ((arg s 1).toNat, schedWords s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) := by
  obtain ⟨hrd, hwr, dKS, -, -, -, dAD, dAV, dAS, -, -, -, fK, -, -, -, fE, hRn⟩ := h
  have inA : ∀ i < 6, InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Aes.X86.argOp i)) 4 := fun i hi =>
    ⟨⟨argAddr s 0, 24⟩, by rw [hrd]; simp, by
      rw [show s.ea (VG.Impl.Aes.X86.argOp i) = argAddr s i from rfl, argAddr_eq s (n := 6) (by omega) hi]
      exact VG.Offset.contains_base _ (by omega) (by omega)⟩
  have subA : ∀ i < 6, Region.Sub ⟨s.ea (VG.Impl.Aes.X86.argOp i), 4⟩ ⟨argAddr s 0, 24⟩ := fun i hi => by
    rw [show s.ea (VG.Impl.Aes.X86.argOp i) = argAddr s i from rfl, argAddr_eq s (n := 6) (by omega) hi]
    exact VG.Offset.sub_base _ (by omega)
  refine ⟨arg s 0, inA 0 (by decide), rfl, inA 1 (by decide), ?_, hRn, rfl, by rw [hrd]; simp, fK,
    fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · show arg s 1 = BitVec.ofNat 32 (arg s 1).toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (subA 0 (by decide))
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (subA 1 (by decide))
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dAD.sub_left (subA 1 (by decide))
    · exact dAV.sub_left (subA 1 (by decide))
    · exact dAS.sub_left (subA 1 (by decide))

theorem data_eq (d : Dir) (m : Mem) (s : State) :
    Proof.Modes.chunksAt (4 * (dirCore d).bw) m ((arg s 3).setWidth 64) (arg s 4).toNat = dataAt m s := rfl
theorem iv_eq (d : Dir) (m : Mem) (s : State) :
    Spec.Aes.bytesAt m ((arg s 2).setWidth 64) (4 * (dirCore d).bw) = ivAt m s := rfl
attribute [local irreducible] Spec.Camellia.cipher in
theorem cipher_enc (s : State) :
    (dirCoreSpec .encrypt).cipher ((arg s 1).toNat, schedWords s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) =
      ciph s := rfl

attribute [local irreducible] Spec.Camellia.invCipher in
theorem decCipher_eq (s : State) :
    (dirCoreSpec .decrypt).cipher ((arg s 1).toNat, schedWords s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) =
      invCiph s := rfl

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
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, decCipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem cbcEncryptChained_ct : ConstantTime isa (fbX86 encPost).pre (fbX86 encPost).pub cbcEncryptChained :=
  let ⟨_, h⟩ := (by native_taint_decide_sum [fbPairSum] :
    ∃ h, (VG.X86.taint.check fbTaint cbcEncryptChained h).isSome = true)
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cbcDecryptChained_ct : ConstantTime isa (fbX86 decPost).pre (fbX86 decPost).pub cbcDecryptChained :=
  let ⟨_, h⟩ := (by native_taint_decide_sum [fbPairSum] :
    ∃ h, (VG.X86.taint.check fbTaint cbcDecryptChained h).isSome = true)
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem wide_implies_enc :
    (wideContract encPost).Implies (Proof.Camellia.cbcEncChainedScratchContract X86.abi 341) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.cbcEncChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcEncChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost] at h
    sig_split h
    sig_reduce [Proof.Camellia.cbcEncChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcEncChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Camellia.cbcEncChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcEncChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Camellia.cbcEncChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcEncChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost]
  · sig_implies_sat [Proof.Camellia.cbcEncChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcEncChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_dec :
    (wideContract decPost).Implies (Proof.Camellia.cbcDecChainedScratchContract X86.abi 341) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcDecChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost] at h
    sig_split h
    sig_reduce [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcDecChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcDecChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcDecChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost]
  · sig_implies_sat [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcDecChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem frameSat_cbc (post : Spec.Camellia.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Camellia.cbcChainedSig.contract X86.abi (pre := Proof.Camellia.cbcChainedPre X86.abi.ptrBits) (post := post)
      (writeArgs := true) (stack := 2756)).pre s := by
  implies_sat [Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem cbcEncryptChained_verified :
    Verified X86.target cbcEncryptChained (Proof.Camellia.cbcEncChainedScratchContract X86.abi 341) :=
  fb_verified (fun _ hs => cbcEncryptChained_wp hs) cbcEncryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_enc

theorem cbcDecryptChained_verified :
    Verified X86.target cbcDecryptChained (Proof.Camellia.cbcDecChainedScratchContract X86.abi 341) :=
  fb_verified (fun _ hs => cbcDecryptChained_wp hs) cbcDecryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_dec

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 cbcEncryptChained)
      (Spec.Camellia.cbcEncryptChainedContract X86.abi 2756) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 341) (pre := Proof.Camellia.cbcChainedPre X86.abi.ptrBits) (post := Proof.Camellia.cbcEncChainedPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2756) cbcEncryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.cbcChainedPre_local _)
    (Proof.Camellia.cbcEncChainedPost_local _) (Proof.Camellia.cbcEncChainedPostOut_local _) (frameSat_cbc _)

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 cbcDecryptChained)
      (Spec.Camellia.cbcDecryptChainedContract X86.abi 2756) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 341) (pre := Proof.Camellia.cbcChainedPre X86.abi.ptrBits) (post := Proof.Camellia.cbcDecChainedPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2756) cbcDecryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.cbcChainedPre_local _)
    (Proof.Camellia.cbcDecChainedPost_local _) (Proof.Camellia.cbcDecChainedPostOut_local _) (frameSat_cbc _)

end VG.Proof.Camellia.X86.Cbc
