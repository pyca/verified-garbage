module

public import VerifiedGarbage.Proof.Seed.X86_64.ModeCore
import VerifiedGarbage.Proof.Modes.X86_64.Fb
import VerifiedGarbage.Proof.Modes.X86_64.KeepIv
public import VerifiedGarbage.Proof.Seed.FbScratch
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
public import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Modes.Fb
public import VerifiedGarbage.Spec.Seed.Cfb
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Seed.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Seed.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Modes.X86_64.Fb
meta import VerifiedGarbage.Proof.Modes.X86_64.KeepIv
meta import VerifiedGarbage.Proof.Seed.FbScratch
meta import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Modes.Fb
meta import VerifiedGarbage.Spec.Seed.Cfb
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Seed.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# SEED-OFB and -CFB128 on x86-64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.X86_64.fb_wp`) over SEED's core (`dirCoreSpec .encrypt`), with the
specification's results (`Proof.Modes.ofb_of`, …). `ofb_verified`, …: each
is correct and constant time, by the taint analysis: the pointers, `n` and
the stack pointer are public, and so is everything the code computes from
them; the IV is secret. `ofb_framed`, … run them with their working space on
the stack, zeroed on return: 1512 bytes, the 188 words of the scratch buffer
and 8 more.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.Impl.Seed.X86_64

/-- The precondition of the feedback modes on x86-64, with the data `len`
bytes long and the working space at `r8`. -/
def fbPre (len : State → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .rdi, 128⟩
  let iv : Region := ⟨s.gpr .rsi, 16⟩
  let data : Region := ⟨s.gpr .rdx, len s⟩
  let scratch : Region := ⟨s.gpr .r8, 8 * 188⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + len s ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * 188 ≤ 2 ^ 64

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := 16 * (s.gpr .rcx).toNat

/-- The schedule, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.Seed.cipher (Spec.Seed.scheduleAt s.mem (s.gpr .rdi))
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

attribute [local irreducible] Spec.Seed.cipher in
/-- The core's cipher is the contract's (stated once, with the cipher's spec
irreducible: unifying them unfolds the spec before the core). -/
theorem encCipher_eq : (dirCoreSpec .encrypt).cipher = Spec.Seed.cipher := rfl

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the
IV as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre blkLen s₀) :
    WP isa ((dirCore .encrypt).fb mo modeRegs) s₀ fun s' => gprPreserved s₀ s' ∧
      Modes.blocksOf 16 s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat =
        (List.range (s₀.gpr .rcx).toNat).map (Modes.fbOut mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .rsi) 16 = Modes.fbIn mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 188⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.fb_wp (dirCoreSpec .encrypt) mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Seed.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [dirCore_bw, hwr]; exact List.mem_cons_self)
    (by rw [dirCore_bw, show 8 * 2 = 16 from rfl, hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide),
      Modes.X86_64.keepsIv_of_ivSafe (by lit_decide)⟩)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, by
      rw [dirCore_bw, show 8 * 2 = 16 from rfl, encCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV

theorem ofb_wp {s₀ : State} (hp : ofbX86_64.pre s₀) :
    WP isa ofb s₀ fun s' => gprPreserved s₀ s' ∧ ofbX86_64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    simp only [Modes.blocksOf_16] at h1 h2 hd
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.Cbc.blocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.Cbc.blocksAt _ _ _)
    rw [hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncX86_64.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    simp only [Modes.blocksOf_16] at h1 h2 hd
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Cbc.blocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.Cbc.blocksAt _ _ _)
      rw [hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.Cbc.blocksAt _ _ _))
      rw [hv, h2]

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecX86_64.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    simp only [Modes.blocksOf_16] at h1 h2 hd
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Cbc.blocksAt _ _ _ = Spec.Cfb.decrypt _ _ (Spec.Cbc.blocksAt _ _ _)
      rw [hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cbc.blocksAt _ _ _)
      rw [hv, h2]

/-! ## Constant time -/

def fbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [16, 0, 8 * 188], bases := [(.r8, 2, 0)] }

theorem fbTaint_wf {len : State → Nat} (s : State) (hs : fbPre len s) : Taint.Wf fbTaint s := by
  obtain ⟨_, hwr, _, _, _, dVD, dVS, dDS, _, _, _, _, fitV, fitD, fitB⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 16 ≤ 16; omega) (List.Forall₂.cons (by change 0 ≤ len s; omega)
        (List.Forall₂.cons (by change 8 * 188 ≤ 8 * 188; omega) List.Forall₂.nil))
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
      · change 16 ≤ 2 ^ 64; omega
      · change len s ≤ 2 ^ 64; omega
      · change 8 * 188 ≤ 2 ^ 64; omega
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

/-- A state satisfying the precondition (one block, or one byte). -/
def fbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 188⟩]

/-- What is public at the core's loop of rounds: the pointers (`rsi` at the
batch's blocks, `rdi` at the round keys, `r9` at the scratch buffer), the
round counter, the stack pointer, the flags, and the data's address, the
blocks left and the IV's address in `xmm13` … `xmm15`. -/
def fbRoundTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdx, .rsp, .rsi, .rdi, .r8, .r9], flags := true, lens := [16, 0, 8 * 188],
    bases := [(.r9, 2, 0), (.rsi, 2, 8 * bufSlot)], xregs := .ofList [.xmm13, .xmm14, .xmm15] }

/-! The loop of rounds, which the three modes run, analysed once, as a summary. -/

taint_summary fbRoundSum : taintS fbRoundTaint (.block (round .encrypt))

theorem ofb_ct : ConstantTime isa ofbX86_64.pre ofbX86_64.pub ofb :=
  let ⟨_, h⟩ := (by taint_decide_sum [fbRoundSum] : ∃ h, (taintS.check fbTaint ofb h).isSome = true)
  VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree blkLen_congr) h

theorem ofb_verified :
    Verified X86_64.target ofb (Proof.Seed.fbScratchContract X86_64.abi 188 Proof.Seed.ofbPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := ofb_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := ofb) (by lit_decide) he hg, hpost⟩)
    ofb_ct (by
    sig_implies [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig,
      Proof.Seed.ofbPost, ofbX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

theorem cfbEncrypt_ct : ConstantTime isa cfbEncX86_64.pre cfbEncX86_64.pub cfbEncrypt :=
  let ⟨_, h⟩ := (by taint_decide_sum [fbRoundSum] : ∃ h, (taintS.check fbTaint cfbEncrypt h).isSome = true)
  VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree blkLen_congr) h

theorem cfbEncrypt_verified :
    Verified X86_64.target cfbEncrypt (Proof.Seed.fbScratchContract X86_64.abi 188 Proof.Seed.cfbEncPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbEncrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncrypt) (by lit_decide) he hg, hpost⟩)
    cfbEncrypt_ct (by
    sig_implies [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig,
      Proof.Seed.cfbEncPost, cfbEncX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

theorem cfbDecrypt_ct : ConstantTime isa cfbDecX86_64.pre cfbDecX86_64.pub cfbDecrypt :=
  let ⟨_, h⟩ := (by taint_decide_sum [fbRoundSum] : ∃ h, (taintS.check fbTaint cfbDecrypt h).isSome = true)
  VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree blkLen_congr) h

theorem cfbDecrypt_verified :
    Verified X86_64.target cfbDecrypt (Proof.Seed.fbScratchContract X86_64.abi 188 Proof.Seed.cfbDecPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbDecrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecrypt) (by lit_decide) he hg, hpost⟩)
    cfbDecrypt_ct (by
    sig_implies [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig,
      Proof.Seed.cfbDecPost, cfbDecX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 1512 .r8 188 ofb)
      (Spec.Seed.ofbContract X86_64.abi 1512) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Seed.ofbSig) (nm := "scratch") (e := .u64)
    (n := 188) (post := Proof.Seed.ofbPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1512) ofb_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Seed.ofbPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB128 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 1512 .r8 188 cfbEncrypt)
      (Spec.Seed.cfbEncryptContract X86_64.abi 1512) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Seed.cfbSig) (nm := "scratch") (e := .u64)
    (n := 188) (post := Proof.Seed.cfbEncPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1512) cfbEncrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Seed.cfbEncPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB128 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 1512 .r8 188 cfbDecrypt)
      (Spec.Seed.cfbDecryptContract X86_64.abi 1512) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Seed.cfbSig) (nm := "scratch") (e := .u64)
    (n := 188) (post := Proof.Seed.cfbDecPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1512) cfbDecrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Seed.cfbDecPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Seed.X86_64
