module

public import VerifiedGarbage.Proof.Sm4.X86_64.ModeCore
import VerifiedGarbage.Proof.Modes.X86_64.Ctr32
public import VerifiedGarbage.Proof.Modes.Ctr32
public import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
public import VerifiedGarbage.Impl.Sm4.X86_64.Ctr32
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Lit
meta import VerifiedGarbage.Proof.Sm4.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Modes.X86_64.Ctr32
meta import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
meta import VerifiedGarbage.Impl.Sm4.X86_64.Ctr32
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Sm4.X86_64.Ctr32Lit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sm4.Contract

/-!
# SM4's counter mode with `inc₃₂` on x86-64 meets its contracts

`ctr32_wp`: the modes' counter mode with `inc₃₂` over SM4's core
(`Proof.Modes.X86_64.ctr32_wp` with `modeCoreSpec`). `ctr32_verified`:
`ctr32` is correct and constant time, by the taint analysis: the pointers,
`n` and the stack pointer are public, and so is everything the code computes
from them; the counter block is secret. `ctr32_framed` runs it with its
working space on the stack, zeroed on return, as `ctr_framed`
(`CtrVerified.lean`): 3208 bytes, the 400 words of the scratch buffer and 8
more, below the 8 bytes the call of `vg_sm4_crypt_prepared` uses.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.X86_64 VG.Impl.Sm4.X86_64

/-- `vg_sm4_ctr32` on x86-64 with its working space at `r8`. -/
def ctr32X86_64 : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 128⟩
    let ctr : Region := ⟨s.gpr .rsi, 16⟩
    let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * 400⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩
    s.rd = [sched] ∧ s.wr = [ctr, data, scratch] ∧ sched.Disjoint ctr ∧ sched.Disjoint data ∧
      sched.Disjoint scratch ∧ ctr.Disjoint data ∧ ctr.Disjoint scratch ∧ data.Disjoint scratch ∧
      ret.Disjoint ctr ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      stk.Disjoint ctr ∧ stk.Disjoint data ∧ stk.Disjoint scratch ∧ 8 ≤ (s.gpr .rsp).toNat ∧
      (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * 400 ≤ 2 ^ 64
  post s s' :=
    Spec.Gcm.blocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
        Spec.Gcm.ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s.mem (s.gpr .rdi))) (Spec.Gcm.blockAt s.mem (s.gpr .rsi))
          (Spec.Gcm.blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ∧
      Spec.Gcm.blockAt s'.mem (s.gpr .rsi) =
        Nat.repeat Spec.Gcm.inc32 (s.gpr .rcx).toNat (Spec.Gcm.blockAt s.mem (s.gpr .rsi))
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (ctr32X86_64)

attribute [local irreducible] Spec.Sm4.cipher in
/-- The core's cipher, on GCM's blocks, is the contract's (see `cipher_eq`,
`CtrVerified.lean`). -/
theorem gcmCipher_eq (k : Spec.Sm4.Schedule) :
    Proof.Modes.onBlocks (modeCoreSpec.cipher k) = Spec.Sm4.gcmCipher k := rfl

theorem ctr32_wp {s₀ : State} (hp : ctr32X86_64.pre s₀) :
    WP isa ctr32 s₀ fun s' => gprPreserved s₀ s' ∧ ctr32X86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKC, dKD, dKS, dCD, dCS, dDS, dRC, dRD, dRS, dTC, dTD, dTS, hst, fitK, fitC, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 400⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.ctr32_wp modeCoreSpec (r := ⟨.rsi, .rdx, .rcx, .r8⟩) ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dCS dDS dCD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKC, hst, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dTS
      · exact dTC⟩
    (hstk := .inr ⟨hst, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dTC
      · exact dTD
      · exact dTS⟩)) fun s' ⟨hcs, hdata, hctr, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, ?_, hctr⟩
  swap
  · rw [gcmCipher_eq] at hdata; exact hdata
  rw [stkList_dirCore] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact dRS
  · exact dRC
  · exact dRD
  · exact VG.Offset.base_disjoint_below _ (by decide)

/-- The initial taint: the registers of the arguments and the stack pointer
are public, and `r8` is the scratch buffer's base, so that the registers
`vg_sm4_crypt_prepared` saves in its slots and restores (the buffer's base
the core keeps in `r12`) stay public. -/
def ctr32Taint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [16, 0, 8 * 400], bases := [(.r8, 2, 0)] }

theorem ctr32Taint_wf (s : State) (hs : ctr32X86_64.pre s) : Taint.Wf ctr32Taint s := by
  obtain ⟨_, hwr, _, _, _, dCD, dCS, dDS, _, _, _, _, _, _, _, _, fitC, fitD, fitB⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 16 ≤ 16; omega) (List.Forall₂.cons (by change 0 ≤ _; omega)
        (List.Forall₂.cons (by change 8 * 400 ≤ 8 * 400; omega) List.Forall₂.nil))
    · refine List.Pairwise.cons (fun r hr => ?_) (List.Pairwise.cons (fun r hr => ?_)
        (List.Pairwise.cons (by simp) List.Pairwise.nil))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dCD
        · exact dCS
      · obtain rfl := List.mem_singleton.mp hr; exact dDS
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · change 16 ≤ 2 ^ 64; omega
      · change 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64; omega
      · change 8 * 400 ≤ 2 ^ 64; omega
  · intro p hp
    simp only [ctr32Taint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .r8 = s.gpr .r8 + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem ctr32Taint_agree (s t : State) (hs : ctr32X86_64.pre s) (ht : ctr32X86_64.pre t)
    (hp : ctr32X86_64.pub s t) : X86_64.Taint.Agree ctr32Taint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
  refine ⟨?_, ?_, ctr32Taint_wf s hs, ctr32Taint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [ctr32Taint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
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
    simp only [ctr32Taint, RegSet.not_mem_empty] at hr

theorem ctr32_ct : ConstantTime isa ctr32X86_64.pre ctr32X86_64.pub ctr32 :=
  VG.Taint.constantTime (A := taint) ctr32Taint ctr32Taint_agree (by taint_decide)

theorem ctr32_correct (s : State) (hs : ctr32X86_64.pre s) :
    ∃ t s', Exec isa ctr32 s t s' ∧ abiPreserved s s' ∧ ctr32X86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := ctr32_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := ctr32) (by lit_decide) he hg, hpost⟩

/-- A state satisfying the precondition (one block). -/
def ctr32Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 400⟩]

theorem ctr32_verified :
    Verified X86_64.target ctr32 (Proof.Sm4.ctr32ScratchContract X86_64.abi 400 8) :=
  Verified.of_correct ctr32_correct ctr32_ct (by
    sig_implies [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Post, ctr32X86_64,
      X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot] [ctr32Sat] using ctr32Sat)

/-- `vg_sm4_ctr32` with its working space on the stack. -/
theorem ctr32_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 ctr32)
      (Proof.Sm4.ctr32Contract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Proof.Sm4.ctr32Sig) (nm := "scratch") (e := .u64)
    (n := 400) (post := Proof.Sm4.ctr32Post X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3208) ctr32_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Sm4.ctr32PostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by lit_decide) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm4.X86_64
