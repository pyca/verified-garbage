import VerifiedGarbage.Proof.Sm4.X86_64.ModeCore
import VerifiedGarbage.Proof.Modes.X86_64.CbcDecrypt
import VerifiedGarbage.Proof.Modes.X86_64.CbcEncrypt
import VerifiedGarbage.Proof.Sm4.CbcScratch
import VerifiedGarbage.Impl.Sm4.X86_64.Cbc
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SM4-CBC on x86-64 meets its contracts

`cbcEncrypt_wp`, `cbcDecrypt_wp`: the modes' CBC encryption and decryption
over SM4's core for each direction (`Proof.Modes.X86_64.cbcEncrypt_wp` and
`cbcDecrypt_wp` with `dirCoreSpec`). `cbcEncrypt_verified`,
`cbcDecrypt_verified`: each is correct and constant time, by the taint
analysis: the pointers, `n` and the stack pointer are public, and so is
everything the code computes from them; the IV is secret. `cbcEncrypt_framed`
and `cbcDecrypt_framed` run them with their working space on the stack,
zeroed on return: 3144 bytes, the 392 words of the scratch buffer and 8 more.
-/

namespace VG.Proof.Sm4

open VG VG.X86_64 VG.Impl.Sm4.X86_64

/-- CBC decryption on x86-64 with its working space at `r8`. -/
def cbcDecX86_64 : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 128⟩
    let iv : Region := ⟨s.gpr .rsi, 16⟩
    let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * slots⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched, iv] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧ ret.Disjoint data ∧
      ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * slots ≤ 2 ^ 64
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      Spec.Cbc.decrypt (Spec.Sm4.invCipher (Spec.Sm4.scheduleAt s.mem (s.gpr .rdi)))
        (Spec.Aes.bytesAt s.mem (s.gpr .rsi) 16) (Spec.Cbc.blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- CBC encryption on x86-64 with its working space at `r8`: as decryption,
with encryption's result. -/
def cbcEncX86_64 : Contract X86_64.isa where
  pre := cbcDecX86_64.pre
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      Spec.Cbc.encrypt (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .rdi)))
        (Spec.Aes.bytesAt s.mem (s.gpr .rsi) 16) (Spec.Cbc.blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub := cbcDecX86_64.pub

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (cbcDecX86_64 cbcEncX86_64)

attribute [local irreducible] Spec.Sm4.invCipher in
/-- The core's cipher is the contract's, without unfolding it (as `cipher_eq`). -/
theorem invCipher_eq (k : Spec.Sm4.Schedule) : (dirCoreSpec .decrypt).cipher k = Spec.Sm4.invCipher k := rfl

theorem cbcDecrypt_wp {s₀ : State} (hp : cbcDecX86_64.pre s₀) :
    WP isa cbcDecrypt s₀ fun s' => gprPreserved s₀ s' ∧ cbcDecX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcDecrypt_wp (dirCoreSpec .decrypt) (r := ⟨.rsi, .rdx, .rcx, .r8⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩) fun s' ⟨hcs, hdata, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, ?_⟩
  · refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS
    · exact dRD
  · rw [invCipher_eq] at hdata; exact hdata

def cbcTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [0, 8 * slots], bases := [(.r8, 1, 0)] }

theorem cbcTaint_wf (s : State) (hs : cbcDecX86_64.pre s) : Taint.Wf cbcTaint s := by
  obtain ⟨_, hwr, _, _, _, _, dDS, _, _, _, _, fitD, fitB⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 0 ≤ 16 * (s.gpr .rcx).toNat; omega)
        (List.Forall₂.cons (by change 8 * slots ≤ 8 * slots; omega) List.Forall₂.nil)
    · exact List.Pairwise.cons (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dDS)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64
        have := (s.gpr .rdx).isLt; omega
      · change 8 * slots ≤ 2 ^ 64; rw [slots_eq]; omega
  · intro p hp
    simp only [cbcTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .r8 = s.gpr .r8 + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem cbcTaint_agree (s t : State) (hs : cbcDecX86_64.pre s) (ht : cbcDecX86_64.pre t)
    (hp : cbcDecX86_64.pub s t) : X86_64.Taint.Agree cbcTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
  refine ⟨?_, ?_, cbcTaint_wf s hs, cbcTaint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [cbcTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [p1, p2, p3, p4, p5, p6]
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, p3, p4, p5]
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
  exact ⟨t, s', he, abiPreserved_of_exec (c := cbcDecrypt) (by decide +kernel) he hg, hpost⟩

/-- A state satisfying the precondition (one block). -/
def cbcSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 392⟩]

theorem cbcDecrypt_verified :
    Verified X86_64.target cbcDecrypt (Proof.Sm4.cbcDecScratchContract X86_64.abi slots) :=
  Verified.of_correct cbcDecrypt_correct cbcDecrypt_ct (by
    sig_implies [Proof.Sm4.cbcDecScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcDecPost,
      cbcDecX86_64, X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot] [cbcSat] using cbcSat)

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3144 .r8 392 cbcDecrypt)
      (Spec.Sm4.cbcDecryptContract X86_64.abi 3144) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.cbcSig) (nm := "scratch") (e := .u64)
    (n := 392) (post := Proof.Sm4.cbcDecPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3144) cbcDecrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by decide +kernel)) (by decide +kernel) (by decide)
    (Proof.Sm4.cbcDecPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## Encryption -/

attribute [local irreducible] Spec.Sm4.cipher in
/-- The core's cipher is the contract's, without unfolding it (as `cipher_eq`). -/
theorem encCipher_eq (k : Spec.Sm4.Schedule) : (dirCoreSpec .encrypt).cipher k = Spec.Sm4.cipher k := rfl

theorem cbcEncrypt_wp {s₀ : State} (hp : cbcEncX86_64.pre s₀) :
    WP isa cbcEncrypt s₀ fun s' => gprPreserved s₀ s' ∧ cbcEncX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcEncrypt_wp (dirCoreSpec .encrypt) (r := ⟨.rsi, .rdx, .rcx, .r8⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKD⟩) fun s' ⟨hcs, hdata, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, ?_⟩
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
  exact ⟨t, s', he, abiPreserved_of_exec (c := cbcEncrypt) (by decide +kernel) he hg, hpost⟩

theorem cbcEncrypt_verified :
    Verified X86_64.target cbcEncrypt (Proof.Sm4.cbcEncScratchContract X86_64.abi slots) :=
  Verified.of_correct cbcEncrypt_correct cbcEncrypt_ct (by
    sig_implies [Proof.Sm4.cbcEncScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcEncPost,
      cbcEncX86_64, cbcDecX86_64, X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot] [cbcSat]
      using cbcSat)

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3144 .r8 392 cbcEncrypt)
      (Spec.Sm4.cbcEncryptContract X86_64.abi 3144) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.cbcSig) (nm := "scratch") (e := .u64)
    (n := 392) (post := Proof.Sm4.cbcEncPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3144) cbcEncrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by decide +kernel)) (by decide +kernel) (by decide)
    (Proof.Sm4.cbcEncPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm4.X86_64
