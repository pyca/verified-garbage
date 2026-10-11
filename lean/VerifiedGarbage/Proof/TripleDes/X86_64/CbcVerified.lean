import VerifiedGarbage.Proof.TripleDes.X86_64.ModeCore
import VerifiedGarbage.Proof.Modes.X86_64.CbcDecrypt
import VerifiedGarbage.Proof.Modes.X86_64.CbcEncrypt
import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.X86_64.CbcLit
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Triple DES-CBC on x86-64 meets its contracts

`cbcEncrypt_wp`, `cbcDecrypt_wp`: the modes' CBC encryption and decryption
over Triple DES's core for each direction (`Proof.Modes.X86_64.cbcEncrypt_wp` and
`cbcDecrypt_wp` with `dirCoreSpec`). `cbcEncrypt_verified`,
`cbcDecrypt_verified`: each is correct and constant time, by the taint
analysis: the pointers, `n` and the stack pointer are public, and so is
everything the code computes from them; the IV is secret. `cbcEncrypt_framed`
and `cbcDecrypt_framed` run them with their working space on the stack,
zeroed on return: 976 bytes, the 121 words of the scratch buffer and 8 more.
-/

namespace VG.Proof.TripleDes

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

/-- CBC decryption on x86-64 with its working space at `r8`. -/
def cbcDecX86_64 : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 384⟩
    let iv : Region := ⟨s.gpr .rsi, 8⟩
    let data : Region := ⟨s.gpr .rdx, 8 * (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * 121⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched, iv] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧ ret.Disjoint data ∧
      ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + 8 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * 121 ≤ 2 ^ 64
  post s s' :=
    Spec.TripleDes.cbcBlocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      Spec.Cbc.decrypt (Spec.TripleDes.invCipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)))
        (Spec.TripleDes.bytesAt s.mem (s.gpr .rsi) 8)
        (Spec.TripleDes.cbcBlocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- CBC encryption on x86-64 with its working space at `r8`: as decryption,
with encryption's result. -/
def cbcEncX86_64 : Contract X86_64.isa where
  pre := cbcDecX86_64.pre
  post s s' :=
    Spec.TripleDes.cbcBlocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      Spec.Cbc.encrypt (Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)))
        (Spec.TripleDes.bytesAt s.mem (s.gpr .rsi) 8)
        (Spec.TripleDes.cbcBlocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub := cbcDecX86_64.pub

end VG.Proof.TripleDes

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64
open VG.Proof.TripleDes (cbcDecX86_64 cbcEncX86_64)

/-- The core's cipher is the contract's. -/
theorem invCipher_eq (k : Spec.TripleDes.Schedule) : (dirCoreSpec .decrypt).cipher k = Spec.TripleDes.invCipher k := rfl

theorem cbcDecrypt_wp {s₀ : State} (hp : cbcDecX86_64.pre s₀) :
    WP isa cbcDecrypt s₀ fun s' => gprPreserved s₀ s' ∧ cbcDecX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 121⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcDecrypt_wp (dirCoreSpec .decrypt) (r := ⟨.rsi, .rdx, .rcx, .r8⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hrd]; simp) (by rw [hwr]; simp) dVS dDS fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩) fun s' ⟨hcs, hdata, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, ?_⟩
  · refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS
    · exact dRD
  · rw [dirCore_bw, Nat.mul_one, invCipher_eq] at hdata
    change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cbc.decrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata

def cbcTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [0, 8 * 121], bases := [(.r8, 1, 0)] }

theorem cbcTaint_wf (s : State) (hs : cbcDecX86_64.pre s) : Taint.Wf cbcTaint s := by
  obtain ⟨_, hwr, _, _, _, _, dDS, _, _, _, _, fitD, fitB⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 0 ≤ 8 * (s.gpr .rcx).toNat; omega)
        (List.Forall₂.cons (by change 8 * 121 ≤ 8 * 121; omega) List.Forall₂.nil)
    · exact List.Pairwise.cons (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dDS)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change 8 * (s.gpr .rcx).toNat ≤ 2 ^ 64
        have := (s.gpr .rdx).isLt; omega
      · change 8 * 121 ≤ 2 ^ 64; omega
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
  exact ⟨t, s', he, abiPreserved_of_exec (c := cbcDecrypt) (by lit_decide) he hg, hpost⟩

/-- A state satisfying the precondition (one block). -/
def cbcSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 384⟩, ⟨0x2000, 8⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 8 * 121⟩]

theorem cbcDecrypt_verified :
    Verified X86_64.target cbcDecrypt (Proof.TripleDes.cbcDecScratchContract X86_64.abi 121) :=
  Verified.of_correct cbcDecrypt_correct cbcDecrypt_ct (by
    sig_implies [Proof.TripleDes.cbcDecScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig,
      Proof.TripleDes.cbcDecPost, cbcDecX86_64, X86_64.abi, X86_64.argRegs] [cbcSat] using cbcSat)

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 cbcDecrypt)
      (Spec.TripleDes.cbcDecryptContract X86_64.abi 976) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcSig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.TripleDes.cbcDecPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 976) cbcDecrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.cbcDecPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## Encryption -/

/-- The core's cipher is the contract's. -/
theorem encCipher_eq (k : Spec.TripleDes.Schedule) : (dirCoreSpec .encrypt).cipher k = Spec.TripleDes.cipher k := rfl

theorem cbcEncrypt_wp {s₀ : State} (hp : cbcEncX86_64.pre s₀) :
    WP isa cbcEncrypt s₀ fun s' => gprPreserved s₀ s' ∧ cbcEncX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 121⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcEncrypt_wp (dirCoreSpec .encrypt) (r := ⟨.rsi, .rdx, .rcx, .r8⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
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
  · rw [dirCore_bw, Nat.mul_one, encCipher_eq] at hdata
    change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cbc.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata

theorem cbcEncrypt_ct : ConstantTime isa cbcEncX86_64.pre cbcEncX86_64.pub cbcEncrypt :=
  VG.Taint.constantTime (A := taint) cbcTaint cbcTaint_agree (by taint_decide)

theorem cbcEncrypt_correct (s : State) (hs : cbcEncX86_64.pre s) :
    ∃ t s', Exec isa cbcEncrypt s t s' ∧ abiPreserved s s' ∧ cbcEncX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cbcEncrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cbcEncrypt) (by lit_decide) he hg, hpost⟩

theorem cbcEncrypt_verified :
    Verified X86_64.target cbcEncrypt (Proof.TripleDes.cbcEncScratchContract X86_64.abi 121) :=
  Verified.of_correct cbcEncrypt_correct cbcEncrypt_ct (by
    sig_implies [Proof.TripleDes.cbcEncScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig,
      Proof.TripleDes.cbcEncPost, cbcEncX86_64, cbcDecX86_64, X86_64.abi, X86_64.argRegs] [cbcSat] using cbcSat)

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 cbcEncrypt)
      (Spec.TripleDes.cbcEncryptContract X86_64.abi 976) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcSig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.TripleDes.cbcEncPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 976) cbcEncrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.cbcEncPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.TripleDes.X86_64
