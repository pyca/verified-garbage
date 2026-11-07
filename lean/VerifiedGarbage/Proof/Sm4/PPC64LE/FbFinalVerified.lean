module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Impl.Sm4.PPC64LE.FbFinal
public import VerifiedGarbage.Spec.Sm4.CfbFinal
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Sm4.PPC64LE.CallSum
import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.FbFinalLit
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesVerified
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.ModesFrame
meta import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.FbFinal
meta import VerifiedGarbage.Spec.Sm4.CfbFinal
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.CallSum
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# SM4-CFB128 of a message's last piece on PPC64LE meets its contracts

`cfbEncryptFinal_verified`, `cfbDecryptFinal_verified`: the modes' CFB over
a message's last piece (`Proof.Modes.PPC64LE.cfbEncFinal_wp`, …) over
SM4's core (`Mode.dirCoreSpec`), with the working space as a fifth
argument (`finalContract`), as the whole-block functions are
(`ModesVerified.lean`), but the data `len` bytes. Each is constant time by the
slot taint analysis with the prepared functions' summaries, as theirs are; the
`_framed` theorems run them with their working space on the stack, zeroed on
return.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE.FbFinal

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE VG.Impl.Modes
open VG.Proof.Modes.PPC64LE (SeqPre ivR scrRegion S byteMode)
open VG.Proof.Sm4.PPC64LE (dirCoreSpec KeyArgs)
open VG.Proof.Sm4.PPC64LE.Modes (modeSat modePub_iff cipher_enc)

/-- SM4 under the schedule at `r3`. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .r3))

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (ciph s) 16 s.mem s'.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6).toNat
def decPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (ciph s) 16 s.mem s'.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6).toNat

/-- A final CFB128 function on PPC64LE with its working space as the fifth
argument, the data `len` bytes (`modeContract` with steps of a byte), and the
postcondition `post`. -/
abbrev finalContract (post : State → State → Prop) : Contract isa := modeContract 1 post

/-- `finalContract`'s precondition gives the modes', for steps of a byte. -/
theorem seqPre_of {post : State → State → Prop} {s : State} (h : (finalContract post).pre s) :
    SeqPre (dirCore .encrypt) byteMode s := by
  obtain ⟨hrd, hwr, -, -, -, dVD, dVS, dDS, -, fV, fD, fS⟩ := h
  have eB : 4 * (dirCore .encrypt).bw = 16 := rfl
  have eS : scrRegion (dirCore .encrypt) (S s) = ⟨s.gpr .r7, 8 * (slots + 6)⟩ := rfl
  have eV : ivR s (dirCore .encrypt) = ⟨s.gpr .r4, 16⟩ := rfl
  have eD : Proof.Modes.PPC64LE.dataRegion (s.gpr .r5) byteMode.step (s.gpr .r6).toNat =
      ⟨s.gpr .r5, 1 * (s.gpr .r6).toNat⟩ := rfl
  refine ⟨⟨by rw [hwr]; simp [dirCore], fS⟩, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp,
    by rw [eB]; exact fV, by rw [eD, hwr]; simp, fD,
    by rw [eD, eS]; exact dDS, by rw [eV, eS]; exact dVS, fun _ => by rw [eV, eD]; exact dVD,
    ⟨by decide, by rw [eB]; decide⟩, (dirCoreSpec .encrypt).layout⟩

theorem keyArgs_of {post : State → State → Prop} {s : State} (h : (finalContract post).pre s) :
    KeyArgs s (Proof.Modes.PPC64LE.wrs0 (dirCore .encrypt) byteMode s) (Spec.Sm4.scheduleAt s.mem (s.gpr .r3)) := by
  obtain ⟨hrd, -, -, dKD, dKS, -, -, -, fK, -, -, -⟩ := h
  refine ⟨_, rfl, rfl, by rw [hrd]; exact List.mem_singleton_self _, fK, fun r hr => ?_⟩
  simp only [Proof.Modes.PPC64LE.wrs0, Proof.Modes.PPC64LE.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .r3) 128).Disjoint ⟨s.gpr .r5, byteMode.step * (s.gpr .r6).toNat⟩
    exact dKD
  · exact dKS

theorem cfbEncryptFinal_correct (s : State) (hs : (finalContract encPost).pre s) :
    ∃ t s', Exec isa cfbEncryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract encPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbEncFinal_wp (dirCoreSpec .encrypt) (seqPre_of hs) (keyArgs_of hs))
    fun _ ⟨h1, h2⟩ => by simp only [cipher_enc] at h2; exact ⟨h1, h2⟩

theorem cfbDecryptFinal_correct (s : State) (hs : (finalContract decPost).pre s) :
    ∃ t s', Exec isa cfbDecryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract decPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbDecFinal_wp (dirCoreSpec .encrypt) (seqPre_of hs) (keyArgs_of hs))
    fun _ ⟨h1, h2⟩ => by simp only [cipher_enc] at h2; exact ⟨h1, h2⟩

/-! ## Constant time -/

theorem cfbEncryptFinal_constantTime {post : State → State → Prop} :
    ConstantTime isa (finalContract post).pre modePub cfbEncryptFinal :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree
    (by taint_decide_sum [prepSum, cryptSum])

theorem cfbDecryptFinal_constantTime {post : State → State → Prop} :
    ConstantTime isa (finalContract post).pre modePub cfbDecryptFinal :=
  VG.Taint.constantTime_of_exists (A := slotTaint) modeTaint modes_agree
    (by taint_decide_sum [prepSum, cryptSum])

/-! ## The contracts -/

/-- SM4's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.Sm4.cipher (Spec.Sm4.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 128 16

/-- The final encryption's contract with the working space as an argument. -/
abbrev encScratch : Contract isa :=
  Sig.scratchContract PPC64LE.abi finalSig "scratch" .u64 408 (Curry.const (fun _ => True) _)
    (Proof.Modes.encFinalPost ciphAt 16 PPC64LE.abi.ptrBits) true 0

/-- The final decryption's contract with the working space as an argument. -/
abbrev decScratch : Contract isa :=
  Sig.scratchContract PPC64LE.abi finalSig "scratch" .u64 408 (Curry.const (fun _ => True) _)
    (Proof.Modes.decFinalPost ciphAt 16 PPC64LE.abi.ptrBits) true 0

theorem cfbEncryptFinal_verified : Verified target cfbEncryptFinal encScratch := by
  refine Verified.of_correct cfbEncryptFinal_correct cfbEncryptFinal_constantTime ?_
  sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
    Proof.Modes.encFinalPost, abi, argRegs, finalContract, modeContract, encPost, ciph, ciphAt, modePub_iff, slots_eq, Nat.one_mul] [modeSat]
    using modeSat

theorem cfbDecryptFinal_verified : Verified target cfbDecryptFinal decScratch := by
  refine Verified.of_correct cfbDecryptFinal_correct cfbDecryptFinal_constantTime ?_
  sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
    Proof.Modes.decFinalPost, abi, argRegs, finalContract, modeContract, decPost, ciph, ciphAt, modePub_iff, slots_eq, Nat.one_mul] [modeSat]
    using modeSat

theorem frameSat_pre (post : Spec.Sm4.cfbFinalSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.Sm4.cfbFinalSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 3296)).pre s := by
  implies_sat [Spec.Sm4.cfbFinalSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

theorem ciphAt_congr {m₁ m₂ : Mem} {k : Addr}
    (h : ∀ i < 128 * Elem.size .u8, m₂ (k + BitVec.ofNat 64 i) = m₁ (k + BitVec.ofNat 64 i)) :
    ciphAt m₂ k = ciphAt m₁ k := by
  simp only [ciphAt, Proof.Sm4.scheduleAt_congr (m := m₁) (m' := m₂) h]

/-- The final CFB128 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 cfbEncryptFinal)
      (Spec.Sm4.cfbEncryptFinalContract PPC64LE.abi 3296) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Sm4.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Modes.encFinalPost ciphAt 16 PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3296) (words := 408) cfbEncryptFinal_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.encFinalPostIn_local _ ciphAt_congr) (Proof.Modes.encFinalPost_local _) (frameSat_pre _)

/-- The final CFB128 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 cfbDecryptFinal)
      (Spec.Sm4.cfbDecryptFinalContract PPC64LE.abi 3296) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Sm4.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Modes.decFinalPost ciphAt 16 PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3296) (words := 408) cfbDecryptFinal_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.decFinalPostIn_local _ ciphAt_congr) (Proof.Modes.decFinalPost_local _) (frameSat_pre _)

end VG.Proof.Sm4.PPC64LE.FbFinal
