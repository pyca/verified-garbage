module

public import VerifiedGarbage.Proof.Sm4.X86_64.ModeCore
import VerifiedGarbage.Proof.Modes.X86_64.CbcDecChained
import VerifiedGarbage.Proof.Modes.X86_64.CbcEncChained
public import VerifiedGarbage.Proof.Sm4.CbcScratch
public import VerifiedGarbage.Impl.Sm4.X86_64.Cbc
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Sm4.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcEncChained
meta import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Impl.Sm4.X86_64.Cbc
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# SM4-CBC on x86-64 meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value over SM4's core for each direction
(`Proof.Modes.X86_64.cbcEncryptChained_wp` and `cbcDecryptChained_wp` with
`dirCoreSpec`); encryption keeps the IV's address in `xmm15`, which SM4's
scalar code leaves alone. `cbcEncryptChained_verified`,
`cbcDecryptChained_verified`: each is correct and constant time, by the
taint analysis: the pointers, `n` and the stack pointer are public, and so
is everything the code computes from them, with the scratch buffer's base
known; the IV is secret.
`cbcEncryptChained_framed` and `cbcDecryptChained_framed` run them with
their working space on the stack, zeroed on return: 3208 bytes, the 400
words of the scratch buffer and 8 more, below the 8 bytes the call of
`vg_sm4_crypt_prepared` uses.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.X86_64 VG.Impl.Sm4.X86_64

/-- The precondition of CBC on x86-64, with the IV read and written and the
working space at `r8`. -/
def cbcPreX86_64 (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .rdi, 128⟩
  let iv : Region := ⟨s.gpr .rsi, 16⟩
  let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
  let scratch : Region := ⟨s.gpr .r8, 8 * 400⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    stk.Disjoint iv ∧ stk.Disjoint data ∧ stk.Disjoint scratch ∧ 8 ≤ (s.gpr .rsp).toNat ∧
    (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * 400 ≤ 2 ^ 64

/-- CBC decryption on x86-64 that updates the chaining value. -/
def cbcDecX86_64 : Contract X86_64.isa where
  pre := cbcPreX86_64
  post s s' :=
    let cs := Spec.Cbc.blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
    Spec.Cbc.blocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
        Spec.Cbc.decrypt (Spec.Sm4.invCipher (Spec.Sm4.scheduleAt s.mem (s.gpr .rdi)))
          (Spec.Aes.bytesAt s.mem (s.gpr .rsi) 16) cs ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 16 = Spec.Cbc.next (Spec.Aes.bytesAt s.mem (s.gpr .rsi) 16) cs
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- CBC encryption on x86-64 that updates the chaining value: as
decryption, with encryption's result. -/
def cbcEncX86_64 : Contract X86_64.isa where
  pre := cbcPreX86_64
  post s s' :=
    let cs := Spec.Cbc.encrypt (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .rdi)))
      (Spec.Aes.bytesAt s.mem (s.gpr .rsi) 16) (Spec.Cbc.blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    Spec.Cbc.blocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat = cs ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 16 = Spec.Cbc.next (Spec.Aes.bytesAt s.mem (s.gpr .rsi) 16) cs
  pub := cbcDecX86_64.pub

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (cbcDecX86_64 cbcEncX86_64)

attribute [local irreducible] Spec.Sm4.invCipher in
/-- The core's cipher is the contract's, without unfolding it (as `cipher_eq`). -/
theorem invCipher_eq (k : Spec.Sm4.Schedule) : ((dirCoreSpec .decrypt).toBlock rfl).cipher k = Spec.Sm4.invCipher k := rfl

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecX86_64.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => gprPreserved s₀ s' ∧ cbcDecX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, dTV, dTD, dTS, hst, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 400⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcDecryptChained_wp ((dirCoreSpec .decrypt).toBlock rfl)
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
  · rw [invCipher_eq] at hdata; exact ⟨hdata, hiv⟩

/-- The initial taint: the registers of the arguments and the stack pointer
are public, and `r8` is the scratch buffer's base, so that the registers
`vg_sm4_crypt_prepared` saves in its slots and restores stay public. -/
def cbcTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [16, 0, 8 * 400], bases := [(.r8, 2, 0)] }

theorem cbcTaint_wf (s : State) (hs : cbcDecX86_64.pre s) : Taint.Wf cbcTaint s := by
  obtain ⟨_, hwr, _, _, _, dVD, dVS, dDS, _, _, _, _, _, _, _, _, fitV, fitD, fitB⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 16 ≤ 16; omega) (List.Forall₂.cons (by change 0 ≤ _; omega)
        (List.Forall₂.cons (by change 8 * 400 ≤ 8 * 400; omega) List.Forall₂.nil))
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
      · change 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64; omega
      · change 8 * 400 ≤ 2 ^ 64; omega
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
    rw [hs.2.1, ht.2.1, p2, p3, p4, p5]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [cbcTaint, RegSet.not_mem_empty] at hr

theorem cbcDecryptChained_ct : ConstantTime isa cbcDecX86_64.pre cbcDecX86_64.pub cbcDecryptChained :=
  VG.Taint.constantTime (A := taint) cbcTaint cbcTaint_agree (by taint_decide)

theorem cbcDecryptChained_correct (s : State) (hs : cbcDecX86_64.pre s) :
    ∃ t s', Exec isa cbcDecryptChained s t s' ∧ abiPreserved s s' ∧ cbcDecX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cbcDecryptChained_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cbcDecryptChained) (by lit_decide) he hg, hpost⟩

/-- A state satisfying the precondition (one block). -/
def cbcSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 400⟩]

theorem cbcDecryptChained_verified :
    Verified X86_64.target cbcDecryptChained (Proof.Sm4.cbcDecChainedScratchContract X86_64.abi 400 8) :=
  Verified.of_correct cbcDecryptChained_correct cbcDecryptChained_ct (by
    sig_implies [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig,
      Proof.Sm4.cbcDecChainedPost, cbcDecX86_64, Proof.Sm4.cbcPreX86_64, X86_64.abi, X86_64.argRegs, slots,
      savedSlot, tableEnd, tableSlot] [cbcSat] using cbcSat)

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 cbcDecryptChained)
      (Spec.Sm4.cbcDecryptChainedContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 400) (post := Proof.Sm4.cbcDecChainedPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3208) cbcDecryptChained_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Sm4.cbcDecChainedPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by lit_decide) (by rw [Curry.apply_const]; trivial))

/-! ## Encryption -/

attribute [local irreducible] Spec.Sm4.cipher in
/-- The core's cipher is the contract's, without unfolding it (as `cipher_eq`). -/
theorem encCipher_eq (k : Spec.Sm4.Schedule) : ((dirCoreSpec .encrypt).toBlock rfl).cipher k = Spec.Sm4.cipher k := rfl

theorem cbcEncryptChained_wp {s₀ : State} (hp : cbcEncX86_64.pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => gprPreserved s₀ s' ∧ cbcEncX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, dTV, dTD, dTS, hst, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 400⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcEncryptChained_wp ((dirCoreSpec .encrypt).toBlock rfl)
    (r := ⟨.rsi, .rdx, .rcx, .r8⟩) ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKD, hst, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dTS
      · exact dTD⟩
    ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), Modes.X86_64.keepsIv_of_scal (by lit_decide)⟩
    (hstk := .inr ⟨hst, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dTV
      · exact dTD
      · exact dTS⟩))
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, ?_⟩
  rw [stkList_dirCore] at hf
  · refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact dRS
    · exact dRD
    · exact dRV
    · exact VG.Offset.base_disjoint_below _ (by decide)
  · rw [encCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩

theorem cbcEncryptChained_ct : ConstantTime isa cbcEncX86_64.pre cbcEncX86_64.pub cbcEncryptChained :=
  VG.Taint.constantTime (A := taint) cbcTaint cbcTaint_agree (by taint_decide)

theorem cbcEncryptChained_correct (s : State) (hs : cbcEncX86_64.pre s) :
    ∃ t s', Exec isa cbcEncryptChained s t s' ∧ abiPreserved s s' ∧ cbcEncX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cbcEncryptChained_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cbcEncryptChained) (by lit_decide) he hg, hpost⟩

theorem cbcEncryptChained_verified :
    Verified X86_64.target cbcEncryptChained (Proof.Sm4.cbcEncChainedScratchContract X86_64.abi 400 8) :=
  Verified.of_correct cbcEncryptChained_correct cbcEncryptChained_ct (by
    sig_implies [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig,
      Proof.Sm4.cbcEncChainedPost, cbcEncX86_64, cbcDecX86_64, Proof.Sm4.cbcPreX86_64, X86_64.abi,
      X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot] [cbcSat] using cbcSat)

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 cbcEncryptChained)
      (Spec.Sm4.cbcEncryptChainedContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 400) (post := Proof.Sm4.cbcEncChainedPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3208) cbcEncryptChained_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Sm4.cbcEncChainedPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by lit_decide) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm4.X86_64
