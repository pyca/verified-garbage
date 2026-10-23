module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.ModeCore
import VerifiedGarbage.Proof.Camellia.AArch64.Link
import VerifiedGarbage.Proof.Modes.AArch64.Fb
import VerifiedGarbage.Proof.Modes.AArch64.CfbDec.Whole
import VerifiedGarbage.Proof.Modes.AArch64.Steps
public import VerifiedGarbage.Proof.Camellia.FbScratch
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
public import VerifiedGarbage.Impl.Camellia.AArch64.Fb
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Camellia.AArch64.ModeCore
meta import VerifiedGarbage.Proof.Camellia.AArch64.Link
meta import VerifiedGarbage.Proof.Modes.AArch64.Fb
meta import VerifiedGarbage.Proof.Camellia.FbScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
meta import VerifiedGarbage.Impl.Camellia.AArch64.Fb
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Camellia-OFB and Camellia-CFB128 on AArch64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.AArch64.fb_wp`) over the serial encryption core for dependent
feedback and short decryption. Longer CFB decryption uses the independent
batch proof (`Proof.Modes.AArch64.CfbDec.batched_wp`) over the eight-block
encryption core. Both give the specification's results (`Proof.Modes.ofb_of`, …). `ofb_verified`, …: each
is correct and constant time, by the taint analysis with public values in
vector registers (`VectorTaint`): the pointers, `rounds`, `n` and the stack
pointer are public, and so is everything the code computes from them, which
it keeps in registers (the IV's address in `x19` across the core); the IV is secret. `ofb_framed`, … run them with
their working space on the stack, zeroed on return: 3344 bytes, the 418
words of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.Impl.Camellia.AArch64
open VG.Proof.Camellia (schedWords)

/-- The precondition of the feedback modes on AArch64, with the working
space at `x5`. -/
def fbPre (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .x0, 272⟩
  let iv : Region := ⟨s.gpr .x2, 16⟩
  let data : Region := ⟨s.gpr .x3, 16 * (s.gpr .x4).toNat⟩
  let scratch : Region := ⟨s.gpr .x5, 8 * (slots + 12)⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x0).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + 16 * (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 8 * (slots + 12) ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 18 ∨ (s.gpr .x1).toNat = 24)

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

/-- The cipher, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher :=
  Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .x2) 16
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.Cbc.blocksAt m (s.gpr .x3) (s.gpr .x4).toNat

def ofbAArch64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 16 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .x4).toNat
  pub := fbPub

def cfbEncAArch64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 16 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

def cfbDecAArch64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 16 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- The serial encryption core for dependent feedback modes. -/
def fbCoreSpec : Modes.AArch64.BlockSpec fbCore := Serial.blockSpec

attribute [local irreducible] Spec.Camellia.cipher in
/-- The core's cipher is the contract's, without unfolding it. -/
theorem fbCipher_eq (m : Mem) (p : Addr) (R : Nat) :
    fbCoreSpec.cipher (R, schedWords m p R) = Spec.Camellia.cipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

/-- The serial core naturally preserves the feedback modes' IV pointer. -/
theorem keeps_x19 : Modes.AArch64.KeepsReg .x19 fbCore.prepare ∧ Modes.AArch64.KeepsReg .x19 fbCore.crypt :=
  Serial.keeps_x19

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the IV
as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre s₀) :
    WP isa (fbCore.fb mo ⟨.x2, .x3, .x4, .x5⟩ .x19) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      Modes.blocksOf 16 s'.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat =
        (List.range (s₀.gpr .x4).toNat).map (Modes.fbOut mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .x2) 16 =
        Modes.fbIn mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (s₀.gpr .x4).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB, hR⟩ := hp
  have hwS : (⟨s₀.gpr .x5, 8 * (slots + 12)⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.fb_wp fbCoreSpec mo (r := ⟨.x2, .x3, .x4, .x5⟩)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x19)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := ((s₀.gpr .x1).toNat, schedWords s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ keeps_x19)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [fbCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem ofb_wp {s₀ : State} (hp : ofbAArch64.pre s₀) :
    WP isa ofb s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ofbAArch64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (s₀.gpr .x4).toNat
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncAArch64.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbEncAArch64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (s₀.gpr .x4).toNat
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

theorem cfbDecryptSerial_wp {s₀ : State} (hp : cfbDecAArch64.pre s₀) :
    WP isa (fbCore.fb .cfbDec ⟨.x2,.x3,.x4,.x5⟩ .x19) s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecAArch64.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (s₀.gpr .x4).toNat
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

attribute [local irreducible] Spec.Camellia.cipher in
theorem batchCipher_eq (m : Mem) (p : Addr) (R : Nat) :
    (modeCoreSpec.toBlock rfl).cipher (R,schedWords m p R) =
      Spec.Camellia.cipher (Spec.Camellia.subkeysAt m p R) := rfl

/-- The parallel core encrypts the preceding ciphertext blocks for CFB decryption. -/
theorem cfbDecryptBatch_wp {s₀ : State} (hp : cfbDecAArch64.pre s₀) :
    WP isa (modeCore.cfbDecryptBatched ⟨.x2,.x3,.x4,.x5⟩) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecAArch64.post s₀ s' := by
  obtain ⟨hrd,hwr,dKV,dKD,dKS,dVD,dVS,dDS,fitK,fitV,fitD,fitB,hR⟩ := hp
  have hwS : (⟨s₀.gpr .x5,8*(slots+12)⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Modes.AArch64.CfbDec.batched_wp (modeCoreSpec.toBlock rfl) rfl
    (r:=⟨.x2,.x3,.x4,.x5⟩) ⟨by decide,by decide,by decide⟩ (by decide)
    (B:=s₀.gpr .x5) (P:=s₀.gpr .x2) (D:=s₀.gpr .x3) (n:=(s₀.gpr .x4).toNat)
    (k:=((s₀.gpr .x1).toNat,schedWords s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat))
    rfl rfl rfl rfl ⟨hwS,fitB⟩ (by rw [hwr]; simp) (by rw [hwr]; simp)
    dVS dDS dVD fitD
    ⟨s₀.gpr .x0,rfl,by apply BitVec.eq_of_toNat_eq; simp,hR,rfl,by rw [hrd]; simp,fitK,
      fun r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · exact dKS
        · exact dKV⟩) fun s' ⟨hg,hd,hv,_,_,_⟩ => ⟨hg,?_⟩
  rw [batchCipher_eq] at hd
  exact ⟨hd,hv⟩

attribute [local irreducible] Spec.Camellia.cipher in
theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecAArch64.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecAArch64.post s₀ s' := by
  obtain ⟨s₁,e₁,_,g₁,m₁,rd₁,wr₁⟩ := Modes.AArch64.lsr_ok s₀ .x13 .x4 (sh:=2) (by decide)
  have hp₁ : cfbDecAArch64.pre s₁ := by
    simpa only [cfbDecAArch64,fbPre,m₁,rd₁,wr₁,g₁ .x0 (by decide),g₁ .x1 (by decide),g₁ .x2 (by decide),g₁ .x3 (by decide),g₁ .x4 (by decide),g₁ .x5 (by decide)] using hp
  have transfer {s' : State}
      (h : (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₁.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecAArch64.post s₁ s') :
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecAArch64.post s₀ s' := by
    refine ⟨fun i hi => (h.1 i hi).trans (g₁ _ ?_),?_⟩
    · have : ∀ i < 10, Impl.Modes.AArch64.Core.savedRegs.getD i .x19 ≠ .x13 := by decide
      exact this i hi
    · simpa only [cfbDecAArch64,blocksOf,ciphOf,ivOf,m₁,g₁ .x0 (by decide),g₁ .x1 (by decide),g₁ .x2 (by decide),g₁ .x3 (by decide),g₁ .x4 (by decide),g₁ .x5 (by decide)] using h.2
  unfold cfbDecrypt
  refine WP.seq (WP.of_runBlock ⟨s₁,e₁,?_⟩)
  refine WP.ite _ rfl (fun _ => WP.mono (cfbDecryptSerial_wp hp₁) fun _ h => transfer h)
    (fun _ => WP.mono (cfbDecryptBatch_wp hp₁) fun _ h => transfer h)

/-- The callee-saved registers and the rest of the ABI, from what a mode
keeps. -/
theorem abi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (h₁ : ∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19))
    (h₃ : ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r) (hv : c.allInstrs keepsV = true) : abiPreserved s s' :=
  ⟨Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he hv⟩

/-! ## Constant time -/

theorem fbTaint_agree (s₁ s₂ : State) (_ : fbPre s₁) (_ : fbPre s₂) (hp : fbPub s₁ s₂) :
    VectorTaint.Agree (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hsp⟩ := hp
  refine ⟨⟨hsp, fun r hr => ?_⟩, ?_⟩
  · simp only [VectorTaint.ofRegs, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · intro r hr
    simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hr

/-- A state satisfying the precondition (one block, 18 rounds). -/
def fbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 18 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 418⟩]

/-- A state satisfying the contracts' precondition: the schedule at
`0x1000`, the IV at `0x2000`, one block at `0x3000`, 18 rounds. -/
def fbFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 18 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩]

theorem ofb_verified :
    Verified AArch64.target ofb (Proof.Camellia.ofbScratchContract AArch64.abi (slots + 12)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' ofb_keeps_x30 (ofb_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
      fbTaint_agree (by taint_decide)) (by
    sig_implies [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig,
      Spec.Camellia.ofbSig, Spec.Camellia.ofbPre, Spec.Camellia.ofbPost, ofbAArch64, fbPre, fbPub, AArch64.abi,
      AArch64.argRegs, slots, tailSlot, savedSlot, endSlot, keySlot] [fbSat] using fbSat)

theorem ofbFrameSat_pre : ∃ s, (Spec.Camellia.ofbContract AArch64.abi 3344).pre s := by
  implies_sat [Spec.Camellia.ofbContract, Spec.Camellia.ofbSig, Spec.Camellia.ofbPre,
    Spec.Camellia.ofbPost, AArch64.abi, AArch64.argRegs] [fbFrameSat] using fbFrameSat

theorem cfbEncrypt_verified :
    Verified AArch64.target cfbEncrypt (Proof.Camellia.cfbEncScratchContract AArch64.abi (slots + 12)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cfbEncrypt_keeps_x30 (cfbEncrypt_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
      fbTaint_agree (by taint_decide)) (by
    sig_implies [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig,
      Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Spec.Camellia.cfbEncryptPost, cfbEncAArch64, fbPre, fbPub,
      AArch64.abi, AArch64.argRegs, slots, tailSlot, savedSlot, endSlot, keySlot] [fbSat] using fbSat)

theorem cfbEncryptFrameSat_pre : ∃ s, (Spec.Camellia.cfbEncryptContract AArch64.abi 3344).pre s := by
  implies_sat [Spec.Camellia.cfbEncryptContract, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre,
    Spec.Camellia.cfbEncryptPost, AArch64.abi, AArch64.argRegs] [fbFrameSat] using fbFrameSat

theorem cfbDecrypt_verified :
    Verified AArch64.target cfbDecrypt (Proof.Camellia.cfbDecScratchContract AArch64.abi (slots + 12)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cfbDecrypt_keeps_x30 (cfbDecrypt_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
      fbTaint_agree (by taint_decide)) (by
    sig_implies [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig,
      Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Spec.Camellia.cfbDecryptPost, cfbDecAArch64, fbPre, fbPub,
      AArch64.abi, AArch64.argRegs, slots, tailSlot, savedSlot, endSlot, keySlot] [fbSat] using fbSat)

theorem cfbDecryptFrameSat_pre : ∃ s, (Spec.Camellia.cfbDecryptContract AArch64.abi 3344).pre s := by
  implies_sat [Spec.Camellia.cfbDecryptContract, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre,
    Spec.Camellia.cfbDecryptPost, AArch64.abi, AArch64.argRegs] [fbFrameSat] using fbFrameSat

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 ofb)
      (Spec.Camellia.ofbContract AArch64.abi 3344) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Camellia.ofbSig) (nm := "scratch") (e := .u64)
    (n := 418) (pre := Spec.Camellia.ofbPre AArch64.abi.ptrBits)
    (post := Spec.Camellia.ofbPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3344) (by rw [← Proof.Camellia.ofbScratchContract_eq]; exact ofb_verified)
    (by decide) (by decide) (by decide) (Proof.Camellia.ofbPostOut_local _) ofbFrameSat_pre

/-- CFB128 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 cfbEncrypt)
      (Spec.Camellia.cfbEncryptContract AArch64.abi 3344) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Camellia.cfbSig) (nm := "scratch") (e := .u64)
    (n := 418) (pre := Spec.Camellia.cfbPre AArch64.abi.ptrBits)
    (post := Spec.Camellia.cfbEncryptPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3344) (by rw [← Proof.Camellia.cfbEncScratchContract_eq]; exact cfbEncrypt_verified)
    (by decide) (by decide) (by decide) (Proof.Camellia.cfbEncryptPostOut_local _) cfbEncryptFrameSat_pre

/-- CFB128 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 cfbDecrypt)
      (Spec.Camellia.cfbDecryptContract AArch64.abi 3344) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Camellia.cfbSig) (nm := "scratch") (e := .u64)
    (n := 418) (pre := Spec.Camellia.cfbPre AArch64.abi.ptrBits)
    (post := Spec.Camellia.cfbDecryptPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3344) (by rw [← Proof.Camellia.cfbDecScratchContract_eq]; exact cfbDecrypt_verified)
    (by decide) (by decide) (by decide) (Proof.Camellia.cfbDecryptPostOut_local _) cfbDecryptFrameSat_pre

end VG.Proof.Camellia.AArch64
