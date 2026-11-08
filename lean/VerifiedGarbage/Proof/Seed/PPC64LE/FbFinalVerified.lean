module

public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Seed.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Impl.Seed.PPC64LE.FbFinal
public import VerifiedGarbage.Spec.Seed.CfbFinal
public import VerifiedGarbage.Spec.Seed.OfbFinal
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Seed.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Seed.PPC64LE.CallSum
import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
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
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Proof.Seed.PPC64LE.CallSum
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# SEED-CFB128 and SEED-OFB of a message's last piece on PPC64LE meet their contracts

`cfbEncryptFinal_verified`, `cfbDecryptFinal_verified`, `ofbFinal_verified`:
the modes' CFB and OFB over a message's last piece
(`Proof.Modes.PPC64LE.cfbEncFinal_wp`, …, `ofbFinal_wp`) over
SEED's core (`Mode.dirCoreSpec`), with the working space as a fifth
argument (`finalContract`), as the whole-block functions are
(`ModesVerified.lean`), but the data `len` bytes. Each is constant time by the
slot taint analysis with the blocks functions' summaries, as theirs are; the
`_framed` theorems run them with their working space on the stack, zeroed on
return.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE.FbFinal

open VG VG.PPC64LE VG.Impl.Seed.PPC64LE VG.Impl.Modes
open VG.Proof.Modes.PPC64LE (SeqPre ivR scrRegion S byteMode)
open VG.Proof.Seed.PPC64LE.Mode (dirCoreSpec KeyArgs)
open VG.Proof.Seed.PPC64LE.Modes (modeSat modePub_iff cipher_enc)

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
    SeqPre (dirCore .encrypt) byteMode s := by
  obtain ⟨hrd, hwr, -, -, -, dVD, dVS, dDS, fV, fD, fS⟩ := h
  have eB : 4 * (dirCore .encrypt).bw = 16 := rfl
  have eS : scrRegion (dirCore .encrypt) (S s) = ⟨s.gpr .r7, 8 * 144⟩ := rfl
  have eV : ivR s (dirCore .encrypt) = ⟨s.gpr .r4, 16⟩ := rfl
  have eD : Proof.Modes.PPC64LE.dataRegion (s.gpr .r5) byteMode.step (s.gpr .r6).toNat =
      ⟨s.gpr .r5, (s.gpr .r6).toNat⟩ := by simp [byteMode]
  refine ⟨⟨by rw [hwr]; simp [core, bufSlot], fS⟩, by rw [eV, hwr]; simp, fun _ => by rw [eV, hwr]; simp,
    by rw [eB]; exact fV, by rw [eD, hwr]; simp, by simp only [byteMode, Nat.one_mul]; exact fD,
    by rw [eD, eS]; exact dDS, by rw [eV, eS]; exact dVS, fun _ => by rw [eV, eD]; exact dVD,
    ⟨by decide, by rw [eB]; decide⟩, (dirCoreSpec .encrypt).layout⟩

theorem keyArgs_of {post : State → State → Prop} {s : State} (h : (finalContract post).pre s) :
    KeyArgs s (Proof.Modes.PPC64LE.wrs0 (dirCore .encrypt) byteMode s) (Spec.Seed.scheduleAt s.mem (s.gpr .r3)) := by
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
  WP.mono (Proof.Modes.PPC64LE.cfbEncFinal_wp (dirCoreSpec .encrypt) (seqPre_of hs) (keyArgs_of hs))
    fun _ ⟨h1, h2⟩ => by simp only [cipher_enc] at h2; exact ⟨h1, h2⟩

theorem cfbDecryptFinal_correct (s : State) (hs : (finalContract decPost).pre s) :
    ∃ t s', Exec isa cfbDecryptFinal s t s' ∧ abiPreserved s s' ∧ (finalContract decPost).post s s' :=
  WP.mono (Proof.Modes.PPC64LE.cfbDecFinal_wp (dirCoreSpec .encrypt) (seqPre_of hs) (keyArgs_of hs))
    fun _ ⟨h1, h2⟩ => by simp only [cipher_enc] at h2; exact ⟨h1, h2⟩

/-! ## Constant time -/

theorem final_agree {post : State → State → Prop} (s₁ s₂ : State)
    (h₁ : (finalContract post).pre s₁) (h₂ : (finalContract post).pre s₂) (hp : modePub s₁ s₂) :
    SlotTaint.Agree (modeTaint 144) s₁ s₂ := by
  obtain ⟨-, hw₁, -, -, -, dVD, dVS, dDS, fV, fD, fS⟩ := h₁
  obtain ⟨-, hw₂, -⟩ := h₂
  obtain ⟨hsp, hr⟩ := hp
  have r4 := hr .r4 (by simp)
  have r5 := hr .r5 (by simp)
  have r6 := hr .r6 (by simp)
  have r7 := hr .r7 (by simp)
  refine SlotTaint.agree_mk' hsp (fun r h => hr r (by simpa using h)) (by rw [hw₁, hw₂, r4, r5, r6, r7])
    ?_ ?_ ?_ ?_ ?_
  · rw [hw₁]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil))
  · rw [hw₁]
    refine .cons (fun r hr => ?_) (.cons (fun r hr => ?_) (.cons (fun r hr => absurd hr List.not_mem_nil) .nil))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dVD
      · exact dVS
    · simp only [List.mem_singleton] at hr; subst hr; exact dDS
  · rw [hw₁]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [SlotTaint.region, hw₁]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [SlotTaint.region, hw₂]

theorem cfbEncryptFinal_constantTime {post : State → State → Prop} :
    ConstantTime isa (finalContract post).pre modePub cfbEncryptFinal :=
  VG.Taint.constantTime_of_exists (A := slotTaint) (modeTaint 144) final_agree (by taint_decide_sum [encryptSum])

theorem cfbDecryptFinal_constantTime {post : State → State → Prop} :
    ConstantTime isa (finalContract post).pre modePub cfbDecryptFinal :=
  VG.Taint.constantTime_of_exists (A := slotTaint) (modeTaint 144) final_agree (by taint_decide_sum [encryptSum])

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
  WP.mono (Proof.Modes.PPC64LE.ofbFinal_wp (dirCoreSpec .encrypt) (seqPre_of hs) (keyArgs_of hs))
    fun _ ⟨h1, h2⟩ => by simp only [cipher_enc] at h2; exact ⟨h1, h2⟩

theorem ofbFinal_constantTime {post : State → State → Prop} :
    ConstantTime isa (finalContract post).pre modePub ofbFinal :=
  VG.Taint.constantTime_of_exists (A := slotTaint) (modeTaint 144) final_agree (by taint_decide_sum [encryptSum])

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
