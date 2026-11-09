module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
public import VerifiedGarbage.Proof.Seed.PPC64LE.SerialCore
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Impl.Seed.PPC64LE.FbFinal
public import VerifiedGarbage.Spec.Seed.CfbFinal
public import VerifiedGarbage.Spec.Seed.OfbFinal
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalLit
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
meta import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
meta import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Impl.Seed.PPC64LE.FbFinal
meta import VerifiedGarbage.Spec.Seed.CfbFinal
meta import VerifiedGarbage.Spec.Seed.OfbFinal
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# SEED-CFB128 and SEED-OFB of a message's last piece on PPC64LE meet their contracts

`cfbEncryptFinal_verified`, `cfbDecryptFinal_verified`, `ofbFinal_verified`:
the modes' CFB and OFB over a message's last piece
(`Proof.Modes.PPC64LE.cfbEncFinal_wp`, …, `ofbFinal_wp`) over
SEED's single-block core (`Serial.coreSpec`), with the working space as a
fifth argument (`finalContract`), as the whole-block functions are
(`ModesVerified.lean`), but the data `len` bytes. Each is constant time by the
vector taint analysis, as the serial whole-block functions are; the
`_framed` theorems run them with their working space on the stack, zeroed on
return.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE.FbFinal

open VG VG.PPC64LE VG.Impl.Seed.PPC64LE VG.Impl.Modes
open VG.Proof.Modes.PPC64LE (SeqPre ivR scrRegion S byteMode)
open VG.Proof.Seed.PPC64LE.Mode (KeyArgs)
open VG.Proof.Seed.PPC64LE.Modes (modeSat modePub_iff)

/-- SEED under the schedule at `r3`. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.Seed.cipher (Spec.Seed.scheduleAt s.mem (s.gpr .r3))

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (ciph s) 16 s.mem s'.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6).toNat
def decPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (ciph s) 16 s.mem s'.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6).toNat

/-- A final CFB128 function on PPC64LE with its working space as the fifth
argument, the data `len` bytes, and the postcondition `post`. -/
def finalContract (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 128⟩
    let iv : Region := ⟨s.gpr .r4, 16⟩
    let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 8 * 144⟩
    s.rd = [key] ∧ s.wr = [iv, data, scratch] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint scratch ∧ iv.Disjoint data ∧
      iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r4).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + 8 * 144 ≤ 2 ^ 64
  post := post
  pub := modePub

/-- `finalContract`'s precondition gives the modes', for steps of a byte. -/
theorem seqPre_of {post : State → State → Prop} {s : State} (h : (finalContract post).pre s) :
    SeqPre Serial.core byteMode s := by
  obtain ⟨hrd, hwr, -, -, -, dVD, dVS, dDS, fV, fD, fS⟩ := h
  have eB : 4 * Serial.core.bw = 16 := rfl
  have eS : scrRegion Serial.core (S s) = ⟨s.gpr .r7, 8 * 144⟩ := rfl
  have eV : ivR s Serial.core = ⟨s.gpr .r4, 16⟩ := rfl
  have eD : Proof.Modes.PPC64LE.dataRegion (s.gpr .r5) byteMode.step (s.gpr .r6).toNat =
      ⟨s.gpr .r5, (s.gpr .r6).toNat⟩ := by simp [byteMode]
  refine ⟨⟨by rw [hwr]; simp [Serial.core, bufSlot], fS⟩, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp,
    by rw [eB]; exact fV, by rw [eD, hwr]; simp, by simp only [byteMode, Nat.one_mul]; exact fD,
    by rw [eD, eS]; exact dDS, by rw [eV, eS]; exact dVS, fun _ => by rw [eV, eD]; exact dVD,
    ⟨by decide, by rw [eB]; decide⟩, Serial.coreSpec.layout⟩

theorem keyArgs_of {post : State → State → Prop} {s : State} (h : (finalContract post).pre s) :
    KeyArgs s (Proof.Modes.PPC64LE.wrs0 Serial.core byteMode s) (Spec.Seed.scheduleAt s.mem (s.gpr .r3)) := by
  obtain ⟨hrd, -, -, dKD, dKS, -, -, -, -, -, -⟩ := h
  refine ⟨rfl, by rw [hrd]; exact List.mem_singleton_self _, fun r hr => ?_⟩
  simp only [Proof.Modes.PPC64LE.wrs0, Proof.Modes.PPC64LE.wrs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl
  · show (Region.mk (s.gpr .r3) 128).Disjoint ⟨s.gpr .r5, byteMode.step * (s.gpr .r6).toNat⟩
    simp only [byteMode, Nat.one_mul]; exact dKD
  · exact dKS

theorem cfbEncryptFinal_correct (s : State) (hs : (finalContract encPost).pre s) :
    ∃ t s', Exec isa cfbEncryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract encPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbEncFinal_wp Serial.coreSpec (seqPre_of hs) (keyArgs_of hs)) fun _ h => h

theorem cfbDecryptFinal_correct (s : State) (hs : (finalContract decPost).pre s) :
    ∃ t s', Exec isa cfbDecryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract decPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbDecFinal_wp Serial.coreSpec (seqPre_of hs) (keyArgs_of hs)) fun _ h => h

/-! ## Constant time -/

/-- The public arguments agree: the vector analysis's taint on entry. -/
theorem final_agree {post : State → State → Prop} (s₁ s₂ : State)
    (_ : (finalContract post).pre s₁) (_ : (finalContract post).pre s₂) (hp : modePub s₁ s₂) :
    VG.PPC64LE.Taint.Agree (VG.PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  obtain ⟨hsp, hr⟩ := hp
  refine ⟨hsp, fun r h => hr r ?_⟩
  simpa only [VG.PPC64LE.Taint.mem_ofRegs] using h

theorem cfbEncryptFinal_constantTime {post : State → State → Prop} :
    ConstantTime isa (finalContract post).pre modePub cfbEncryptFinal :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) final_agree
    (by taint_decide)

theorem cfbDecryptFinal_constantTime {post : State → State → Prop} :
    ConstantTime isa (finalContract post).pre modePub cfbDecryptFinal :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) final_agree
    (by taint_decide)

/-! ## The contracts -/

/-- SEED's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.Seed.cipher (Spec.Seed.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 128 16

/-- The final encryption's contract with the working space as an argument. -/
abbrev encScratch : Contract isa :=
  Sig.scratchContract PPC64LE.abi finalSig "scratch" .u64 144 (Curry.const (fun _ => True) _)
    (Proof.Modes.encFinalPost ciphAt 16 PPC64LE.abi.ptrBits) true 0

/-- The final decryption's contract with the working space as an argument. -/
abbrev decScratch : Contract isa :=
  Sig.scratchContract PPC64LE.abi finalSig "scratch" .u64 144 (Curry.const (fun _ => True) _)
    (Proof.Modes.decFinalPost ciphAt 16 PPC64LE.abi.ptrBits) true 0

theorem cfbEncryptFinal_verified : Verified target cfbEncryptFinal encScratch := by
  refine Verified.of_correct cfbEncryptFinal_correct cfbEncryptFinal_constantTime ?_
  sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
    Proof.Modes.encFinalPost, abi, argRegs, finalContract, encPost, ciph, ciphAt, modePub_iff] [modeSat]
    using modeSat

theorem cfbDecryptFinal_verified : Verified target cfbDecryptFinal decScratch := by
  refine Verified.of_correct cfbDecryptFinal_correct cfbDecryptFinal_constantTime ?_
  sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
    Proof.Modes.decFinalPost, abi, argRegs, finalContract, decPost, ciph, ciphAt, modePub_iff] [modeSat]
    using modeSat

theorem frameSat_pre (post : Spec.Seed.cfbFinalSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.Seed.cfbFinalSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 1184)).pre s := by
  implies_sat [Spec.Seed.cfbFinalSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

theorem ciphAt_congr {m₁ m₂ : Mem} {k : Addr}
    (h : ∀ i < 128 * Elem.size .u8, m₂ (k + BitVec.ofNat 64 i) = m₁ (k + BitVec.ofNat 64 i)) :
    ciphAt m₂ k = ciphAt m₁ k := by
  simp only [ciphAt, Proof.Seed.scheduleAt_congr h]

/-- The final CFB128 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 cfbEncryptFinal)
      (Spec.Seed.cfbEncryptFinalContract PPC64LE.abi 1184) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Seed.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 144) (post := Proof.Modes.encFinalPost ciphAt 16 PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1184) (words := 144) cfbEncryptFinal_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.encFinalPostIn_local _ ciphAt_congr) (Proof.Modes.encFinalPost_local _) (frameSat_pre _)

/-- The final CFB128 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 cfbDecryptFinal)
      (Spec.Seed.cfbDecryptFinalContract PPC64LE.abi 1184) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Seed.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 144) (post := Proof.Modes.decFinalPost ciphAt 16 PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1184) (words := 144) cfbDecryptFinal_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.decFinalPostIn_local _ ciphAt_congr) (Proof.Modes.decFinalPost_local _) (frameSat_pre _)

/-! ## OFB of a message's last piece -/

/-- The final OFB function's postcondition. -/
def ofbPost (s s' : State) : Prop :=
  Spec.Ofb.CryptFinal (ciph s) 16 s.mem s'.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6).toNat

theorem ofbFinal_correct (s : State) (hs : (finalContract ofbPost).pre s) :
    ∃ t s', Exec isa ofbFinal s t s' ∧ abiPreserved s s' ∧ (finalContract ofbPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.ofbFinal_wp Serial.coreSpec (seqPre_of hs) (keyArgs_of hs)) fun _ h => h

theorem ofbFinal_constantTime {post : State → State → Prop} :
    ConstantTime isa (finalContract post).pre modePub ofbFinal :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) final_agree
    (by taint_decide)

/-- The final OFB function's contract with the working space as an argument. -/
abbrev ofbScratch : Contract isa :=
  Sig.scratchContract PPC64LE.abi finalSig "scratch" .u64 144 (Curry.const (fun _ => True) _)
    (Proof.Modes.ofbFinalPost ciphAt 16 PPC64LE.abi.ptrBits) true 0

theorem ofbFinal_verified : Verified target ofbFinal ofbScratch := by
  refine Verified.of_correct ofbFinal_correct ofbFinal_constantTime ?_
  sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
    Proof.Modes.ofbFinalPost, abi, argRegs, finalContract, ofbPost, ciph, ciphAt, modePub_iff] [modeSat]
    using modeSat

theorem ofbFrameSat_pre (post : Spec.Seed.ofbFinalSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.Seed.ofbFinalSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 1184)).pre s := by
  implies_sat [Spec.Seed.ofbFinalSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

/-- The final OFB function with its working space on the stack. -/
theorem ofbFinal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 1184 .r7 144 ofbFinal)
      (Spec.Seed.ofbFinalContract PPC64LE.abi 1184) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Seed.ofbFinalSig) (nm := "scratch") (e := .u64)
    (n := 144) (post := Proof.Modes.ofbFinalPost ciphAt 16 PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1184) (words := 144) ofbFinal_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.ofbFinalPostIn_local _ ciphAt_congr) (Proof.Modes.ofbFinalPost_local _) (ofbFrameSat_pre _)

end VG.Proof.Seed.PPC64LE.FbFinal
