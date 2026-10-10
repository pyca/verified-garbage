import VerifiedGarbage.Proof.Camellia.X86_64.ModeCore
import VerifiedGarbage.Proof.Modes.X86_64.CbcDecrypt
import VerifiedGarbage.Proof.Modes.X86_64.CbcEncrypt
import VerifiedGarbage.Proof.Camellia.CbcScratch
import VerifiedGarbage.Impl.Camellia.X86_64.Cbc
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Camellia.X86_64.Lit

/-!
# Camellia-CBC on x86-64 meets its contracts

`cbcEncrypt_wp`, `cbcDecrypt_wp`: the modes' CBC encryption and decryption
over Camellia's core for each direction (`Proof.Modes.X86_64.cbcEncrypt_wp`
and `cbcDecrypt_wp` with `dirCoreSpec`). `cbcEncrypt_verified`,
`cbcDecrypt_verified`: each is correct and constant time, by the taint
analysis: the pointers, `rounds`, `n` and the stack pointer are public, and
so is everything the code computes from them; the IV is secret.
`cbcEncrypt_framed` and `cbcDecrypt_framed` run them with their working
space on the stack, zeroed on return: 3216 bytes, the 401 words of the
scratch buffer and 8 more.
-/

namespace VG.Proof.Camellia

open VG VG.X86_64 VG.Impl.Camellia.X86_64

/-- CBC decryption on x86-64 with its working space at `r9`. -/
def cbcDecX86_64 : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 272⟩
    let iv : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let scratch : Region := ⟨s.gpr .r9, 8 * slots⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched, iv] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧ ret.Disjoint data ∧
      ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 8 * slots ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 18 ∨ (s.gpr .rsi).toNat = 24)
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
      Spec.Cbc.decrypt (Spec.Camellia.invCipher (Spec.Camellia.subkeysAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat))
        (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16) (Spec.Cbc.blocksAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp

/-- CBC encryption on x86-64 with its working space at `r9`: as decryption,
with encryption's result. -/
def cbcEncX86_64 : Contract X86_64.isa where
  pre := cbcDecX86_64.pre
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
      Spec.Cbc.encrypt (Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat))
        (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16) (Spec.Cbc.blocksAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  pub := cbcDecX86_64.pub

end VG.Proof.Camellia

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.Impl.Camellia.X86_64
open VG.Proof.Camellia (cbcDecX86_64 cbcEncX86_64)

attribute [local irreducible] Spec.Camellia.invCipher in
/-- The core's cipher is the contract's, without unfolding it (as `cipher_eq`). -/
theorem invCipher_eq (m : Mem) (p : Addr) (R : Nat) :
    (dirCoreSpec .decrypt).cipher (R, schedWords m p R) = Spec.Camellia.invCipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

theorem cbcDecrypt_wp {s₀ : State} (hp : cbcDecX86_64.pre s₀) :
    WP isa cbcDecrypt s₀ fun s' => gprPreserved s₀ s' ∧ cbcDecX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, dRD, dRS, fitK, fitV, fitD, fitB, hR⟩ := hp
  have hwS : (⟨s₀.gpr .r9, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcDecrypt_wp (dirCoreSpec .decrypt) (r := ⟨.rdx, .rcx, .r8, .r9⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r9) (P := s₀.gpr .rdx) (D := s₀.gpr .rcx) (n := (s₀.gpr .r8).toNat)
    (k := ((s₀.gpr .rsi).toNat, schedWords s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS fitD
    ⟨s₀.gpr .rdi, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩)
    fun s' ⟨hcs, hdata, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, ?_⟩
  · refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS
    · exact dRD
  · rw [invCipher_eq] at hdata; exact hdata

def cbcTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], flags := false,
    lens := [0, 8 * slots], bases := [(.r9, 1, 0)] }

theorem cbcTaint_wf (s : State) (hs : cbcDecX86_64.pre s) : Taint.Wf cbcTaint s := by
  obtain ⟨_, hwr, _, _, _, _, dDS, _, _, _, _, fitD, fitB, _⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 0 ≤ 16 * (s.gpr .r8).toNat; omega)
        (List.Forall₂.cons (by change 8 * slots ≤ 8 * slots; omega) List.Forall₂.nil)
    · exact List.Pairwise.cons (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dDS)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change 16 * (s.gpr .r8).toNat ≤ 2 ^ 64
        have := (s.gpr .rcx).isLt; omega
      · change 8 * slots ≤ 2 ^ 64; omega
  · intro p hp
    simp only [cbcTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .r9 = s.gpr .r9 + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem cbcTaint_agree (s t : State) (hs : cbcDecX86_64.pre s) (ht : cbcDecX86_64.pre t)
    (hp : cbcDecX86_64.pub s t) : X86_64.Taint.Agree cbcTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hp
  refine ⟨?_, ?_, cbcTaint_wf s hs, cbcTaint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [cbcTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [p1, p2, p3, p4, p5, p6, p7]
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, p4, p5, p6]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [cbcTaint, RegSet.not_mem_empty] at hr

theorem cbcDecrypt_ct : ConstantTime isa cbcDecX86_64.pre cbcDecX86_64.pub cbcDecrypt :=
  VG.Taint.constantTime (A := taint) cbcTaint cbcTaint_agree (by taint_decide)

theorem cbcDecrypt_correct (s : State) (hs : cbcDecX86_64.pre s) :
    ∃ t s', Exec isa cbcDecrypt s t s' ∧ abiPreserved s s' ∧ cbcDecX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cbcDecrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cbcDecrypt) (by lit_decide) he hg, hpost⟩

/-- A state satisfying the precondition (one block, 18 rounds). -/
def cbcSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 18 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .r9 => 0x4000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x2000, 16⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 401⟩]

theorem cbcDecrypt_verified :
    Verified X86_64.target cbcDecrypt (Proof.Camellia.cbcDecScratchContract X86_64.abi slots) :=
  Verified.of_correct cbcDecrypt_correct cbcDecrypt_ct (by
    sig_implies [Proof.Camellia.cbcDecScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig,
      Spec.Camellia.cbcPre, Spec.Camellia.cbcDecryptPost, cbcDecX86_64, X86_64.abi, X86_64.argRegs, slots,
      tailSlot, endSlot, keySlot] [cbcSat] using cbcSat)

/-- A state satisfying CBC's precondition: the schedule at `0x1000`, the
IV at `0x2000`, one block at `0x3000`, 18 rounds. -/
def cbcFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 18 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .rsp => 0x8000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x2000, 16⟩]
  wr := [⟨0x3000, 16⟩]

theorem cbcFrameSat_pre : ∃ s, (Spec.Camellia.cbcDecryptContract X86_64.abi 3216).pre s := by
  implies_sat [Spec.Camellia.cbcDecryptContract, Spec.Camellia.cbcSig, Spec.Camellia.cbcPre,
    Spec.Camellia.cbcDecryptPost, X86_64.abi, X86_64.argRegs] [cbcFrameSat] using cbcFrameSat

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r9 401 cbcDecrypt)
      (Spec.Camellia.cbcDecryptContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.cbcSig) (nm := "scratch") (e := .u64)
    (n := 401) (pre := Spec.Camellia.cbcPre X86_64.abi.ptrBits)
    (post := Spec.Camellia.cbcDecryptPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3216) (by rw [← Proof.Camellia.cbcDecScratchContract_eq]; exact cbcDecrypt_verified)
    (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Camellia.cbcDecPostOut_local _) cbcFrameSat_pre

/-! ## Encryption -/

attribute [local irreducible] Spec.Camellia.cipher in
/-- The core's cipher is the contract's, without unfolding it (as `cipher_eq`). -/
theorem encCipher_eq (m : Mem) (p : Addr) (R : Nat) :
    (dirCoreSpec .encrypt).cipher (R, schedWords m p R) = Spec.Camellia.cipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

theorem cbcEncrypt_wp {s₀ : State} (hp : cbcEncX86_64.pre s₀) :
    WP isa cbcEncrypt s₀ fun s' => gprPreserved s₀ s' ∧ cbcEncX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, dRD, dRS, fitK, fitV, fitD, fitB, hR⟩ := hp
  have hwS : (⟨s₀.gpr .r9, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcEncrypt_wp (dirCoreSpec .encrypt) (r := ⟨.rdx, .rcx, .r8, .r9⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r9) (P := s₀.gpr .rdx) (D := s₀.gpr .rcx) (n := (s₀.gpr .r8).toNat)
    (k := ((s₀.gpr .rsi).toNat, schedWords s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dKS
        · exact dKD⟩)
    fun s' ⟨hcs, hdata, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, ?_⟩
  · refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS
    · exact dRD
  · rw [encCipher_eq] at hdata; exact hdata

theorem cbcEncrypt_ct : ConstantTime isa cbcEncX86_64.pre cbcEncX86_64.pub cbcEncrypt :=
  VG.Taint.constantTime (A := taint) cbcTaint cbcTaint_agree (by taint_decide)

theorem cbcEncrypt_correct (s : State) (hs : cbcEncX86_64.pre s) :
    ∃ t s', Exec isa cbcEncrypt s t s' ∧ abiPreserved s s' ∧ cbcEncX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cbcEncrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cbcEncrypt) (by lit_decide) he hg, hpost⟩

theorem cbcEncrypt_verified :
    Verified X86_64.target cbcEncrypt (Proof.Camellia.cbcEncScratchContract X86_64.abi slots) :=
  Verified.of_correct cbcEncrypt_correct cbcEncrypt_ct (by
    sig_implies [Proof.Camellia.cbcEncScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig,
      Spec.Camellia.cbcPre, Spec.Camellia.cbcEncryptPost, cbcEncX86_64, cbcDecX86_64, X86_64.abi,
      X86_64.argRegs, slots, tailSlot, endSlot, keySlot] [cbcSat] using cbcSat)

theorem cbcEncFrameSat_pre : ∃ s, (Spec.Camellia.cbcEncryptContract X86_64.abi 3216).pre s := by
  implies_sat [Spec.Camellia.cbcEncryptContract, Spec.Camellia.cbcSig, Spec.Camellia.cbcPre,
    Spec.Camellia.cbcEncryptPost, X86_64.abi, X86_64.argRegs] [cbcFrameSat] using cbcFrameSat

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3216 .r9 401 cbcEncrypt)
      (Spec.Camellia.cbcEncryptContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.cbcSig) (nm := "scratch") (e := .u64)
    (n := 401) (pre := Spec.Camellia.cbcPre X86_64.abi.ptrBits)
    (post := Spec.Camellia.cbcEncryptPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3216) (by rw [← Proof.Camellia.cbcEncScratchContract_eq]; exact cbcEncrypt_verified)
    (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Camellia.cbcEncPostOut_local _) cbcEncFrameSat_pre

end VG.Proof.Camellia.X86_64
