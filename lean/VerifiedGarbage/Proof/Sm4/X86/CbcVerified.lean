module

public import VerifiedGarbage.Proof.Sm4.X86.FbVerified
meta import VerifiedGarbage.Proof.Sm4.X86.FbVerified
public import VerifiedGarbage.Proof.Modes.X86.CbcChained
meta import VerifiedGarbage.Proof.Modes.X86.CbcChained
public import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Proof.Sm4.CbcScratch
public import VerifiedGarbage.Proof.Sm4.X86.CbcLit
meta import VerifiedGarbage.Proof.Sm4.X86.CbcLit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

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
open VG.Proof.Sm4.X86 (scr_eq disjoint_empty KeyArgs dirCoreSpec dirCoreSpec_cipher τCrypt)
open VG.Proof.Sm4.X86.Fb (fbX86 ciph ivAt dataAt fbTaint fbTaint_agree wideContract fb_verified satState frameSat)

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

/-- `fbX86`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (d : Dir) (hstep : M.step = 16) {s : State}
    (h : (fbX86 post).pre s) :
    SeqPre (dirCore d) M s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, fK, fV, fD, fS, fE⟩ := h
  have hL := (dirCoreSpec d).layout
  refine ⟨(by rw [hrd]; simp [dirCore]), fE, ⟨(by rw [hwr]; simp [dirCore, tableEnd_eq]),
      (by simp only [dirCore, tableEnd_eq]; omega)⟩, (by rw [hwr]; simp [dirCore]),
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
    KeyArgs s [Modes.X86.scrR s (dirCore d)] (Spec.Sm4.scheduleAt s.mem ((arg s 0).setWidth 64)) := by
  obtain ⟨hrd, -, dKS, -, -, -, -, -, dAS, -, -, -, fK, -, -, -, -⟩ := h
  refine ⟨arg s 0, ⟨⟨argAddr s 0, 20⟩, by rw [hrd]; simp, ?_⟩, rfl, rfl, by rw [hrd]; simp, fK, fun r hr => ?_,
    fun r hr => ?_⟩
  · show (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s 0) 4
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (Region.sub_prefix (by decide))

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

/-- What CBC has public where it runs the core: OFB's and CFB's regions, but
not the flags, which encryption's XOR before the core leaves secret. -/
def τCryptChained : VG.X86.Taint.T := { τCrypt with flags := false }

taint_summary cryptSumChained : taint τCryptChained Impl.Sm4.X86.crypt8

theorem cbcEncryptChained_ct : ConstantTime isa (fbX86 encPost).pre (fbX86 encPost).pub cbcEncryptChained := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check fbTaint cbcEncryptChained h).isSome = true :=
    by taint_decide_sum [cryptSumChained]
  exact VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cbcDecryptChained_ct : ConstantTime isa (fbX86 decPost).pre (fbX86 decPost).pub cbcDecryptChained := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check fbTaint cbcDecryptChained h).isSome = true :=
    by taint_decide_sum [cryptSumChained]
  exact VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

/-! ## The contracts -/

theorem wide_implies_enc :
    (wideContract encPost).Implies (Proof.Sm4.cbcEncChainedScratchContract X86.abi 181) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost] at h
    sig_split h
    sig_reduce [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost]
  · sig_implies_sat [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcEncChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, encPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_dec :
    (wideContract decPost).Implies (Proof.Sm4.cbcDecChainedScratchContract X86.abi 181) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost] at h
    sig_split h
    sig_reduce [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost, ciph, invCiph, ivAt, dataAt]
  · sig_implies_pub [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost]
  · sig_implies_sat [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig, Proof.Sm4.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, decPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem frameSat_pre (post : Spec.Sm4.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Sm4.cbcChainedSig.contract X86.abi (post := post) (writeArgs := true) (stack := 1472)).pre s := by
  implies_sat [Spec.Sm4.cbcChainedSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem cbcEncryptChained_verified :
    Verified X86.target cbcEncryptChained (Proof.Sm4.cbcEncChainedScratchContract X86.abi 181) :=
  fb_verified (fun _ hs => cbcEncryptChained_wp hs) cbcEncryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_enc

theorem cbcDecryptChained_verified :
    Verified X86.target cbcDecryptChained (Proof.Sm4.cbcDecChainedScratchContract X86.abi 181) :=
  fb_verified (fun _ hs => cbcDecryptChained_wp hs) cbcDecryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_dec

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1472 4 362 cbcEncryptChained)
      (Spec.Sm4.cbcEncryptChainedContract X86.abi 1472) :=
  X86.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 181) (post := Proof.Sm4.cbcEncChainedPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1472) cbcEncryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.cbcEncChainedPost_local _) (Proof.Sm4.cbcEncChainedPostOut_local _) (frameSat_pre _)

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1472 4 362 cbcDecryptChained)
      (Spec.Sm4.cbcDecryptChainedContract X86.abi 1472) :=
  X86.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 181) (post := Proof.Sm4.cbcDecChainedPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1472) cbcDecryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.cbcDecChainedPost_local _) (Proof.Sm4.cbcDecChainedPostOut_local _) (frameSat_pre _)

end VG.Proof.Sm4.X86.Cbc
