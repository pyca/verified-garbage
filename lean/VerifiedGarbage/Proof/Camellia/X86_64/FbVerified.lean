import VerifiedGarbage.Proof.Camellia.X86_64.ModeCore
import VerifiedGarbage.Proof.Modes.X86_64.Fb
import VerifiedGarbage.Proof.Camellia.FbScratch
import VerifiedGarbage.Impl.Camellia.X86_64.Fb
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Camellia.X86_64.Lit

/-!
# Camellia-OFB and Camellia-CFB128 on x86-64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.X86_64.fb_wp`) over Camellia encryption's core (`dirCoreSpec
.encrypt`), with the specification's results (`Proof.Modes.ofb_of`, …).
`ofb_verified`, …: each is correct and constant time, by the taint analysis:
the pointers, `rounds`, `n` and the stack pointer are public, and so is everything the
code computes from them; the IV is secret. `ofb_framed`, … run them with
their working space on the stack, zeroed on return: 3216 bytes, the 401
words of the scratch buffer and 8 more.
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.Impl.Camellia.X86_64

/-- The precondition of the feedback modes on x86-64, with the working
space at `r8`. -/
def fbPre (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .rdi, 272⟩
  let iv : Region := ⟨s.gpr .rdx, 16⟩
  let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
  let scratch : Region := ⟨s.gpr .r9, 8 * slots⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rdi).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 8 * slots ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat = 18 ∨ (s.gpr .rsi).toNat = 24)

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The cipher, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher :=
  Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.Cbc.blocksAt m (s.gpr .rcx) (s.gpr .r8).toNat

def ofbX86_64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .r8).toNat
  pub := fbPub

def cfbEncX86_64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

def cfbDecX86_64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

attribute [local irreducible] Spec.Camellia.cipher in
/-- The core's cipher is the contract's, without unfolding it. -/
theorem encCipher_eq (m : Mem) (p : Addr) (R : Nat) :
    ((dirCoreSpec .encrypt).toBlock rfl).cipher (R, schedWords m p R) =
      Spec.Camellia.cipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the IV
as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre s₀) :
    WP isa ((dirCore .encrypt).fb mo ⟨.rdx, .rcx, .r8, .r9⟩) s₀ fun s' => gprPreserved s₀ s' ∧
      Modes.blocksOf 16 s'.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat =
        (List.range (s₀.gpr .r8).toNat).map (Modes.fbOut mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .rdx) 16 =
        Modes.fbIn mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (s₀.gpr .r8).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB, hR⟩ := hp
  have hwS : (⟨s₀.gpr .r9, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.fb_wp ((dirCoreSpec .encrypt).toBlock rfl) mo (r := ⟨.rdx, .rcx, .r8, .r9⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r9) (P := s₀.gpr .rdx) (D := s₀.gpr .rcx) (n := (s₀.gpr .r8).toNat)
    (k := ((s₀.gpr .rsi).toNat, schedWords s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), Modes.X86_64.keepsIv_of_scal (by lit_decide)⟩)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, by rw [encCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV

theorem ofb_wp {s₀ : State} (hp : ofbX86_64.pre s₀) :
    WP isa ofb s₀ fun s' => gprPreserved s₀ s' ∧ ofbX86_64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (s₀.gpr .r8).toNat
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncX86_64.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (s₀.gpr .r8).toNat
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecX86_64.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (s₀.gpr .r8).toNat
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

/-! ## Constant time -/

def fbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], flags := false,
    lens := [16, 0, 8 * slots], bases := [(.r9, 2, 0)] }

theorem fbTaint_wf (s : State) (hs : fbPre s) : Taint.Wf fbTaint s := by
  obtain ⟨_, hwr, _, _, _, dVD, dVS, dDS, _, _, _, _, fitV, fitD, fitB, _⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 16 ≤ 16; omega)
        (List.Forall₂.cons (by change 0 ≤ 16 * (s.gpr .r8).toNat; omega)
        (List.Forall₂.cons (by change 8 * slots ≤ 8 * slots; omega) List.Forall₂.nil))
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
      · change 16 * (s.gpr .r8).toNat ≤ 2 ^ 64; omega
      · change 8 * slots ≤ 2 ^ 64; rw [slots_eq]; omega
  · intro p hp
    simp only [fbTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .r9 = s.gpr .r9 + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem fbTaint_agree (s t : State) (hs : fbPre s) (ht : fbPre t) (hp : fbPub s t) :
    X86_64.Taint.Agree fbTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hp
  refine ⟨?_, ?_, fbTaint_wf s hs, fbTaint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [p1, p2, p3, p4, p5, p6, p7]
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, p3, p4, p5, p6]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [fbTaint, RegSet.not_mem_empty] at hr

/-- A state satisfying the precondition (one block). -/
def fbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 18 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .r9 => 0x4000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 401⟩]

/-- A state satisfying the precondition of the contracts on the stack. -/
def fbFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 18 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩]


theorem ofb_verified :
    Verified X86_64.target ofb (Proof.Camellia.ofbScratchContract X86_64.abi slots) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := ofb_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := ofb) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint fbTaint_agree (by taint_decide)) (by
    sig_implies [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig,
      Spec.Camellia.ofbSig, Spec.Camellia.ofbPre, Spec.Camellia.ofbPost, ofbX86_64, fbPre, fbPub, X86_64.abi,
      X86_64.argRegs, slots, tailSlot, endSlot, keySlot] [fbSat] using fbSat)

theorem ofbFrameSat_pre : ∃ s, (Spec.Camellia.ofbContract X86_64.abi 3216).pre s := by
  implies_sat [Spec.Camellia.ofbContract, Spec.Camellia.ofbSig, Spec.Camellia.ofbPre,
    Spec.Camellia.ofbPost, X86_64.abi, X86_64.argRegs] [fbFrameSat] using fbFrameSat

theorem cfbEncrypt_verified :
    Verified X86_64.target cfbEncrypt (Proof.Camellia.cfbEncScratchContract X86_64.abi slots) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbEncrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncrypt) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint fbTaint_agree (by taint_decide)) (by
    sig_implies [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig,
      Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Spec.Camellia.cfbEncryptPost, cfbEncX86_64, fbPre, fbPub, X86_64.abi,
      X86_64.argRegs, slots, tailSlot, endSlot, keySlot] [fbSat] using fbSat)

theorem cfbEncryptFrameSat_pre : ∃ s, (Spec.Camellia.cfbEncryptContract X86_64.abi 3216).pre s := by
  implies_sat [Spec.Camellia.cfbEncryptContract, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre,
    Spec.Camellia.cfbEncryptPost, X86_64.abi, X86_64.argRegs] [fbFrameSat] using fbFrameSat

theorem cfbDecrypt_verified :
    Verified X86_64.target cfbDecrypt (Proof.Camellia.cfbDecScratchContract X86_64.abi slots) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbDecrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecrypt) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint fbTaint_agree (by taint_decide)) (by
    sig_implies [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig,
      Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, Spec.Camellia.cfbDecryptPost, cfbDecX86_64, fbPre, fbPub, X86_64.abi,
      X86_64.argRegs, slots, tailSlot, endSlot, keySlot] [fbSat] using fbSat)

theorem cfbDecryptFrameSat_pre : ∃ s, (Spec.Camellia.cfbDecryptContract X86_64.abi 3216).pre s := by
  implies_sat [Spec.Camellia.cfbDecryptContract, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre,
    Spec.Camellia.cfbDecryptPost, X86_64.abi, X86_64.argRegs] [fbFrameSat] using fbFrameSat

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r9 401 ofb)
      (Spec.Camellia.ofbContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.ofbSig) (nm := "scratch") (e := .u64)
    (n := 401) (pre := Spec.Camellia.ofbPre X86_64.abi.ptrBits)
    (post := Spec.Camellia.ofbPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3216) (by rw [← Proof.Camellia.ofbScratchContract_eq]; exact ofb_verified)
    (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Camellia.ofbPostOut_local _) ofbFrameSat_pre

/-- CFB128 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r9 401 cfbEncrypt)
      (Spec.Camellia.cfbEncryptContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.cfbSig) (nm := "scratch") (e := .u64)
    (n := 401) (pre := Spec.Camellia.cfbPre X86_64.abi.ptrBits)
    (post := Spec.Camellia.cfbEncryptPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3216) (by rw [← Proof.Camellia.cfbEncScratchContract_eq]; exact cfbEncrypt_verified)
    (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Camellia.cfbEncryptPostOut_local _) cfbEncryptFrameSat_pre

/-- CFB128 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r9 401 cfbDecrypt)
      (Spec.Camellia.cfbDecryptContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.cfbSig) (nm := "scratch") (e := .u64)
    (n := 401) (pre := Spec.Camellia.cfbPre X86_64.abi.ptrBits)
    (post := Spec.Camellia.cfbDecryptPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3216) (by rw [← Proof.Camellia.cfbDecScratchContract_eq]; exact cfbDecrypt_verified)
    (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Camellia.cfbDecryptPostOut_local _) cfbDecryptFrameSat_pre

end VG.Proof.Camellia.X86_64
