module

public import VerifiedGarbage.Proof.Sm4.X86_64.ModeCore
import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
public import VerifiedGarbage.Impl.Sm4.X86_64.FbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Spec.Sm4.CfbFinal
public import VerifiedGarbage.Spec.Sm4.OfbFinal
public import VerifiedGarbage.Proof.Modes.FbFinal
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sm4.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Sm4.X86_64.FbFinalLit
meta import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
meta import VerifiedGarbage.Impl.Sm4.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Spec.Sm4.CfbFinal
meta import VerifiedGarbage.Spec.Sm4.OfbFinal
meta import VerifiedGarbage.Proof.Modes.FbFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Modes.X86_64.Fb
import VerifiedGarbage.Proof.Modes.X86_64.CfbDec
public import VerifiedGarbage.Proof.Sm4.FbScratch
public import VerifiedGarbage.Impl.Sm4.X86_64.Fb
public import VerifiedGarbage.Proof.Modes.Fb
public import VerifiedGarbage.Spec.Sm4.Cfb
meta import VerifiedGarbage.Proof.Modes.X86_64.Fb
meta import VerifiedGarbage.Proof.Modes.X86_64.CfbDec
meta import VerifiedGarbage.Proof.Sm4.FbScratch
meta import VerifiedGarbage.Impl.Sm4.X86_64.Fb
meta import VerifiedGarbage.Proof.Modes.Fb
meta import VerifiedGarbage.Spec.Sm4.Cfb

/-! ### `Sm4.X86_64.FbVerified`, which this module and modules that import it used -/

section

/-!
# SM4-OFB and SM4-CFB128 on x86-64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.X86_64.fb_wp`) over SM4 encryption's core (`dirCoreSpec
.encrypt`), with the specification's results (`Proof.Modes.ofb_of`, …).
`ofb_verified`, …: each is correct and constant time, by the taint analysis:
the pointers, `n` and the stack pointer are public, and so is everything the
code computes from them, with the scratch buffer's base known; the IV is
secret. `ofb_framed`, … run them with
their working space on the stack, zeroed on return: 3208 bytes, the 400
words of the scratch buffer and 8 more, below the 8 bytes the call of
`vg_sm4_crypt_prepared` uses.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.Impl.Sm4.X86_64

/-- The precondition of the feedback modes on x86-64, with the data `len`
bytes long and the working space at `r8`. -/
def fbPre (len : State → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .rdi, 128⟩
  let iv : Region := ⟨s.gpr .rsi, 16⟩
  let data : Region := ⟨s.gpr .rdx, len s⟩
  let scratch : Region := ⟨s.gpr .r8, 8 * 400⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    stk.Disjoint iv ∧ stk.Disjoint data ∧ stk.Disjoint scratch ∧ 8 ≤ (s.gpr .rsp).toNat ∧
    (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + len s ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * 400 ≤ 2 ^ 64

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := 16 * (s.gpr .rcx).toNat

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The cipher, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .rdi))
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .rsi) 16
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.Cbc.blocksAt m (s.gpr .rdx) (s.gpr .rcx).toNat

def ofbX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 16 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .rcx).toNat
  pub := fbPub

def cfbEncX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 16 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

def cfbDecX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 16 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

attribute [local irreducible] Spec.Sm4.cipher in
/-- The core's cipher is the contract's, without unfolding it. -/
theorem encCipher_eq (k : Spec.Sm4.Schedule) : ((dirCoreSpec .encrypt).toBlock rfl).cipher k = Spec.Sm4.cipher k :=
  rfl

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the IV
as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre blkLen s₀) :
    WP isa ((dirCore .encrypt).fb mo ⟨.rsi, .rdx, .rcx, .r8⟩) s₀ fun s' => gprPreserved s₀ s' ∧
      Modes.blocksOf 16 s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat =
        (List.range (s₀.gpr .rcx).toNat).map (Modes.fbOut mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .rsi) 16 =
        Modes.fbIn mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, dTV, dTD, dTS, hst, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 400⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.fb_wp ((dirCoreSpec .encrypt).toBlock rfl) mo (r := ⟨.rsi, .rdx, .rcx, .r8⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS, hst, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dTS⟩
    ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), Modes.X86_64.keepsIv_of_scal (by lit_decide)⟩
    (hstk := .inr ⟨hst, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dTV
      · exact dTD
      · exact dTS⟩))
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, by rw [encCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [stkList_dirCore] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV
  · exact VG.Offset.base_disjoint_below _ (by decide)

theorem ofb_wp {s₀ : State} (hp : ofbX86_64.pre s₀) :
    WP isa ofb s₀ fun s' => gprPreserved s₀ s' ∧ ofbX86_64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncX86_64.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

/-- CFB decryption: the modes' CFB decryption a group at a time
(`Proof.Modes.X86_64.CfbDec.batched_wp`), which, unlike `fb_wp'`, needs
no register for the IV's address. -/
theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecX86_64.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, dTV, dTD, dTS, hst, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 400⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.CfbDec.batched_wp ((dirCoreSpec .encrypt).toBlock rfl) rfl
    (r := ⟨.rsi, .rdx, .rcx, .r8⟩) ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKV, hst, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dTS
      · exact dTV⟩
    (hstk := .inr ⟨hst, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dTV
      · exact dTD
      · exact dTS⟩)) fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, ?_⟩
  rw [stkList_dirCore] at hf
  · refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact dRS
    · exact dRD
    · exact dRV
    · exact VG.Offset.base_disjoint_below _ (by decide)
  · rw [encCipher_eq] at hdata; exact ⟨hdata, hiv⟩

/-! ## Constant time -/

/-- The initial taint: the registers of the arguments and the stack pointer
are public, and `r8` is the scratch buffer's base, so that the registers
`vg_sm4_crypt_prepared` saves in its slots and restores stay public. -/
def fbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [16, 0, 8 * 400], bases := [(.r8, 2, 0)] }

theorem fbTaint_wf {len : State → Nat} (s : State) (hs : fbPre len s) : Taint.Wf fbTaint s := by
  obtain ⟨_, hwr, _, _, _, dVD, dVS, dDS, _, _, _, _, _, _, _, _, fitV, fitD, fitB⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 16 ≤ 16; omega_using []) (List.Forall₂.cons (by change 0 ≤ _; omega_using [])
        (List.Forall₂.cons (by change 8 * 400 ≤ 8 * 400; omega_using []) List.Forall₂.nil))
    · refine List.Pairwise.cons (fun r hr => ?_) (List.Pairwise.cons (fun r hr => ?_)
        (List.Pairwise.cons (by simp) List.Pairwise.nil))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dVD
        · exact dVS
      · obtain rfl := List.mem_singleton.mp hr; exact dDS
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · change 16 ≤ 2 ^ 64; omega_using []
      · change len s ≤ 2 ^ 64; omega_using [fitD]
      · change 8 * 400 ≤ 2 ^ 64; omega_using []
  · intro p hp
    simp only [fbTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .r8 = s.gpr .r8 + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem fbTaint_agree {len : State → Nat} (hlen : ∀ s t, s.gpr .rcx = t.gpr .rcx → len s = len t) (s t : State)
    (hs : fbPre len s) (ht : fbPre len t) (hp : fbPub s t) : X86_64.Taint.Agree fbTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
  refine ⟨?_, ?_, fbTaint_wf s hs, fbTaint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [p1, p2, p3, p4, p5, p6]
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, p2, p3, p5, hlen s t p4]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [fbTaint, RegSet.not_mem_empty] at hr

theorem blkLen_congr : ∀ s t : State, s.gpr .rcx = t.gpr .rcx → blkLen s = blkLen t := fun _ _ h => by
  simp only [blkLen, h]

/-- A state satisfying the precondition (one block). -/
def fbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 400⟩]

theorem ofb_verified :
    Verified X86_64.target ofb (Proof.Sm4.fbScratchContract X86_64.abi 400 Proof.Sm4.ofbPost 8) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := ofb_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := ofb) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig,
      Proof.Sm4.ofbPost, ofbX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot] [fbSat] using fbSat)

theorem cfbEncrypt_verified :
    Verified X86_64.target cfbEncrypt (Proof.Sm4.fbScratchContract X86_64.abi 400 Proof.Sm4.cfbEncPost 8) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbEncrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncrypt) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig,
      Proof.Sm4.cfbEncPost, cfbEncX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd,
      tableSlot] [fbSat] using fbSat)

theorem cfbDecrypt_verified :
    Verified X86_64.target cfbDecrypt (Proof.Sm4.fbScratchContract X86_64.abi 400 Proof.Sm4.cfbDecPost 8) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbDecrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecrypt) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig,
      Proof.Sm4.cfbDecPost, cfbDecX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd,
      tableSlot] [fbSat] using fbSat)

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 ofb)
      (Spec.Sm4.ofbContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.ofbSig) (nm := "scratch") (e := .u64)
    (n := 400) (post := Proof.Sm4.ofbPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3208) ofb_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Sm4.ofbPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by lit_decide) (by rw [Curry.apply_const]; trivial))

/-- CFB128 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 cfbEncrypt)
      (Spec.Sm4.cfbEncryptContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.cfbSig) (nm := "scratch") (e := .u64)
    (n := 400) (post := Proof.Sm4.cfbEncPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3208) cfbEncrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Sm4.cfbEncPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by lit_decide) (by rw [Curry.apply_const]; trivial))

/-- CFB128 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 cfbDecrypt)
      (Spec.Sm4.cfbDecryptContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.cfbSig) (nm := "scratch") (e := .u64)
    (n := 400) (post := Proof.Sm4.cfbDecPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3208) cfbDecrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Sm4.cfbDecPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by lit_decide) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm4.X86_64

end

end

/-!
# SM4-CFB128 and SM4-OFB of a message's last piece on x86-64 meet their contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`, `ofbFinal_wp`: the modes' CFB and
OFB over a message's last piece (`Proof.Modes.X86_64.fbFinal_wp`) over SM4's
core (`dirCoreSpec .encrypt`), with the specification's results
(`Proof.Modes.cfbEncFinal_of_bytes`, …, `Proof.Modes.ofbFinal_of_bytes`).
`cfbEncryptFinal_verified`, …: each is correct and constant time, by the taint
analysis, as the whole-block functions are (`FbVerified.lean`);
`cfbEncryptFinal_framed`, … run them with their working space on the stack,
zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.Impl.Sm4.X86_64

/-- The data's length, in bytes. -/
abbrev finalLen (s : State) : Nat := (s.gpr .rcx).toNat

/-- What the modes' OFB and CFB over a message's last piece give, for a mode
`mo`: each byte of the data that of `fbOut` of its block, and the IV
`fbNextF`, keeping the callee-saved registers. -/
theorem fbFinal_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre finalLen s₀) :
    WP isa ((dirCore .encrypt).fbFinal mo ⟨.rsi, .rdx, .rcx, .r8⟩) s₀ fun s' => gprPreserved s₀ s' ∧
      (∀ i < finalLen s₀, s'.mem (s₀.gpr .rdx + BitVec.ofNat 64 i) =
        (Modes.fbOut mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (i / 16)).getD (i % 16) 0) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .rsi) 16 =
        Modes.fbNextF mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (finalLen s₀) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, dTV, dTD, dTS, hst, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 400⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.fbFinal_wp ((dirCoreSpec .encrypt).toBlock rfl) mo (r := ⟨.rsi, .rdx, .rcx, .r8⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (len := finalLen s₀)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS, hst, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dTS⟩
    ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), Modes.X86_64.keepsIv_of_scal (by lit_decide)⟩
    (hstk := .inr ⟨hst, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dTV
      · exact dTD
      · exact dTS⟩))
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, by rw [encCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [stkList_dirCore] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV
  · exact VG.Offset.base_disjoint_below _ (by decide)

theorem cipher_length (k : Spec.Sm4.Schedule) (x : List Byte) : (Spec.Sm4.cipher k x).length = 16 := by
  simp [Spec.Sm4.cipher]

/-- The final encryption's contract on x86-64: the data `len = rcx` bytes
long, and the data and the IV as `Spec.Cfb.EncryptFinal` says. -/
def cfbEncFinalX86_64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Cfb.EncryptFinal (ciphOf s) 16 s.mem s'.mem (s.gpr .rsi) (s.gpr .rdx) (finalLen s)
  pub := fbPub

/-- The final decryption's contract on x86-64. -/
def cfbDecFinalX86_64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Cfb.DecryptFinal (ciphOf s) 16 s.mem s'.mem (s.gpr .rsi) (s.gpr .rdx) (finalLen s)
  pub := fbPub

theorem cfbEncryptFinal_wp {s₀ : State} (hp : cfbEncFinalX86_64.pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncFinalX86_64.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEncFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem cfbDecryptFinal_wp {s₀ : State} (hp : cfbDecFinalX86_64.pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecFinalX86_64.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDecFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

/-! ## Verified -/

theorem finalLen_congr : ∀ s t : State, s.gpr .rcx = t.gpr .rcx → finalLen s = finalLen t := fun _ _ h => by
  simp only [finalLen, h]

/-- A state satisfying the precondition (one block). -/
def finalSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 1⟩, ⟨0x4000, 8 * 400⟩]

/-- SM4's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.Sm4.cipher (Spec.Sm4.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 128 16

theorem cfbEncryptFinal_ct : ConstantTime isa cfbEncFinalX86_64.pre cfbEncFinalX86_64.pub cfbEncryptFinal :=
  (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree finalLen_congr) (by taint_decide))

theorem cfbEncryptFinal_verified :
    Verified X86_64.target cfbEncryptFinal (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 400
      (Curry.const (fun _ => True) _) (Proof.Modes.encFinalPost ciphAt 16 X86_64.abi.ptrBits) true 8) :=
  Verified.of_correct (k := cfbEncFinalX86_64) (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbEncryptFinal_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncryptFinal) (by lit_decide) he hg, hpost⟩)
    cfbEncryptFinal_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, cfbEncFinalX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot] [finalSat]
      using finalSat)

theorem cfbDecryptFinal_ct : ConstantTime isa cfbDecFinalX86_64.pre cfbDecFinalX86_64.pub cfbDecryptFinal :=
  (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree finalLen_congr) (by taint_decide))

theorem cfbDecryptFinal_verified :
    Verified X86_64.target cfbDecryptFinal (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 400
      (Curry.const (fun _ => True) _) (Proof.Modes.decFinalPost ciphAt 16 X86_64.abi.ptrBits) true 8) :=
  Verified.of_correct (k := cfbDecFinalX86_64) (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbDecryptFinal_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecryptFinal) (by lit_decide) he hg, hpost⟩)
    cfbDecryptFinal_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, cfbDecFinalX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot] [finalSat]
      using finalSat)

/-- The final CFB128 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 cfbEncryptFinal)
      (Spec.Sm4.cfbEncryptFinalContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 400) (post := Proof.Modes.encFinalPost ciphAt 16 X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3208) cfbEncryptFinal_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Modes.encFinalPost_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- The final CFB128 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 cfbDecryptFinal)
      (Spec.Sm4.cfbDecryptFinalContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 400) (post := Proof.Modes.decFinalPost ciphAt 16 X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3208) cfbDecryptFinal_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Modes.decFinalPost_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## OFB of a message's last piece -/

/-- The final OFB function's contract on x86-64: the data `len = rcx` bytes
long, and the data and the IV as `Spec.Ofb.CryptFinal` says. -/
def ofbFinalX86_64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Ofb.CryptFinal (ciphOf s) 16 s.mem s'.mem (s.gpr .rsi) (s.gpr .rdx) (finalLen s)
  pub := fbPub

theorem ofbFinal_wp {s₀ : State} (hp : ofbFinalX86_64.pre s₀) :
    WP isa ofbFinal s₀ fun s' => gprPreserved s₀ s' ∧ ofbFinalX86_64.post s₀ s' :=
  WP.mono (fbFinal_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofbFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem ofbFinal_ct : ConstantTime isa ofbFinalX86_64.pre ofbFinalX86_64.pub ofbFinal :=
  (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree finalLen_congr) (by taint_decide))

theorem ofbFinal_verified :
    Verified X86_64.target ofbFinal (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 400
      (Curry.const (fun _ => True) _) (Proof.Modes.ofbFinalPost ciphAt 16 X86_64.abi.ptrBits) true 8) :=
  Verified.of_correct (k := ofbFinalX86_64) (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := ofbFinal_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := ofbFinal) (by lit_decide) he hg, hpost⟩)
    ofbFinal_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.ofbFinalPost, ofbFinalX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot] [finalSat]
      using finalSat)

/-- The final OFB function with its working space on the stack. -/
theorem ofbFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 ofbFinal)
      (Spec.Sm4.ofbFinalContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.ofbFinalSig) (nm := "scratch") (e := .u64)
    (n := 400) (post := Proof.Modes.ofbFinalPost ciphAt 16 X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3208) ofbFinal_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Modes.ofbFinalPost_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm4.X86_64
