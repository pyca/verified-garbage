module

public import VerifiedGarbage.Proof.Camellia.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Camellia.X86_64.ModeCore
public import VerifiedGarbage.Proof.Modes.X86_64.Ctr
meta import VerifiedGarbage.Proof.Modes.X86_64.Ctr
public import VerifiedGarbage.Proof.Camellia.CtrScratch
meta import VerifiedGarbage.Proof.Camellia.CtrScratch
public import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Camellia.X86_64.Lit
meta import VerifiedGarbage.Proof.Camellia.X86_64.Lit
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.AesSiv.Ctr32
public import VerifiedGarbage.Proof.AesSiv.Words
public import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Modes.X86_64.Xor
meta import VerifiedGarbage.Proof.AesSiv.Ctr32
meta import VerifiedGarbage.Proof.AesSiv.Words
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Modes.X86_64.Xor

/-!
# Camellia-CTR on x86-64 meets its contracts

`ctr_wp`: the modes' CTR over Camellia's core (`Proof.Modes.X86_64.ctr_wp`
with `modeCoreSpec`). `ctr_verified`: `ctr` is correct and constant time, by
the taint analysis: the pointers, `rounds`, `n` and the stack pointer are
public, and so is everything the code computes from them; the counter block
is secret. `ctr_framed` runs it with its working space on the stack, zeroed
on return: 3280 bytes, the 409 words of the scratch buffer and 8 more, below
the 8 bytes the call of `vg_camellia_crypt_prepared` uses.
-/

@[expose] public section

namespace VG.Proof.Camellia

open VG VG.X86_64 VG.Impl.Camellia.X86_64

/-- CTR on x86-64 with its working space at `r9`. -/
def ctrX86_64 : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 272⟩
    let ctr : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let scratch : Region := ⟨s.gpr .r9, 8 * 409⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩
    s.rd = [sched] ∧ s.wr = [ctr, data, scratch] ∧ sched.Disjoint ctr ∧ sched.Disjoint data ∧
      sched.Disjoint scratch ∧ ctr.Disjoint data ∧ ctr.Disjoint scratch ∧ data.Disjoint scratch ∧
      ret.Disjoint ctr ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      stk.Disjoint ctr ∧ stk.Disjoint data ∧ stk.Disjoint scratch ∧ 8 ≤ (s.gpr .rsp).toNat ∧
      (s.gpr .rdi).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 8 * 409 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 18 ∨ (s.gpr .rsi).toNat = 24)
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
        Spec.Ctr.crypt (Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat))
          (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16) (Spec.Cbc.blocksAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 = Spec.Ctr.next (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16) (s.gpr .r8).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Camellia

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.Impl.Camellia.X86_64
open VG.Proof.Camellia (ctrX86_64)

attribute [local irreducible] Spec.Camellia.cipher in
theorem cipher_eq (m : Mem) (p : Addr) (R : Nat) :
    modeCoreSpec.cipher (R, schedWords m p R) = Spec.Camellia.cipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

theorem ctr_wp {s₀ : State} (hp : ctrX86_64.pre s₀) :
    WP isa ctr s₀ fun s' => gprPreserved s₀ s' ∧ ctrX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKC, dKD, dKS, dCD, dCS, dDS, dRC, dRD, dRS, dTC, dTD, dTS, hst, fitK, fitC, fitD, fitB, hR⟩ :=
    hp
  have hwS : (⟨s₀.gpr .r9, 8 * 409⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.ctr_wp modeCoreSpec (r := ⟨.rdx, .rcx, .r8, .r9⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r9) (P := s₀.gpr .rdx) (D := s₀.gpr .rcx) (n := (s₀.gpr .r8).toNat)
    (k := ((s₀.gpr .rsi).toNat, schedWords s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dCS dDS dCD fitD
    ⟨s₀.gpr .rdi, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by
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
  · rw [cipher_eq] at hdata; exact hdata
  rw [stkList_dirCore] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact dRS
  · exact dRC
  · exact dRD
  · exact VG.Offset.base_disjoint_below _ (by decide)

def ctrTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], flags := false,
    lens := [16, 0, 8 * 409], bases := [(.r9, 2, 0), (.rdx, 0, 0)] }

theorem ctrTaint_wf (s : State) (hs : ctrX86_64.pre s) : Taint.Wf ctrTaint s := by
  obtain ⟨_, hwr, _, _, _, dCD, dCS, dDS, _, _, _, _, _, _, _, _, fitC, fitD, fitB, _⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 16 ≤ 16; omega)
        (List.Forall₂.cons (by change 0 ≤ 16 * (s.gpr .r8).toNat; omega)
          (List.Forall₂.cons (by change 8 * 409 ≤ 8 * 409; omega) List.Forall₂.nil))
    · refine List.Pairwise.cons (fun r hr => ?_) (List.Pairwise.cons
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dDS)
        (List.Pairwise.cons (by simp) List.Pairwise.nil))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dCD
      · exact dCS
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · change 16 ≤ 2 ^ 64; omega
      · change 16 * (s.gpr .r8).toNat ≤ 2 ^ 64
        have := (s.gpr .rcx).isLt; omega
      · change 8 * 409 ≤ 2 ^ 64; omega
  · intro p hp
    simp only [ctrTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> unfold Taint.region <;> rw [hwr]
    · change s.gpr .r9 = s.gpr .r9 + (0 : BitVec 64)
      exact (BitVec.add_zero _).symm
    · change s.gpr .rdx = s.gpr .rdx + (0 : BitVec 64)
      exact (BitVec.add_zero _).symm

theorem ctrTaint_agree (s t : State) (hs : ctrX86_64.pre s) (ht : ctrX86_64.pre t)
    (hp : ctrX86_64.pub s t) : X86_64.Taint.Agree ctrTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hp
  refine ⟨?_, ?_, ctrTaint_wf s hs, ctrTaint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [ctrTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
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
    simp only [ctrTaint, RegSet.not_mem_empty] at hr

theorem ctr_ct : ConstantTime isa ctrX86_64.pre ctrX86_64.pub ctr :=
  VG.Taint.constantTime (A := taint) ctrTaint ctrTaint_agree (by taint_decide)

theorem ctr_correct (s : State) (hs : ctrX86_64.pre s) :
    ∃ t s', Exec isa ctr s t s' ∧ abiPreserved s s' ∧ ctrX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := ctr_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := ctr) (by lit_decide) he hg, hpost⟩

/-- A state satisfying the precondition (one block, 18 rounds). -/
def ctrSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 18 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .r9 => 0x4000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 409⟩]

theorem ctr_verified :
    Verified X86_64.target ctr (Proof.Camellia.ctrScratchContract X86_64.abi 409 8) :=
  Verified.of_correct ctr_correct ctr_ct (by
    sig_implies [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig,
      Spec.Camellia.ctrPre, Spec.Camellia.ctrPost, ctrX86_64, X86_64.abi, X86_64.argRegs, slots,
      tailSlot, endSlot, keySlot] [ctrSat] using ctrSat)

/-- A state satisfying CTR's precondition: the schedule at `0x1000`, the
counter block at `0x2000`, one block at `0x3000`, 18 rounds. -/
def ctrFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 18 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .rsp => 0x8000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩]

theorem ctrFrameSat_pre : ∃ s, (Spec.Camellia.ctrContract X86_64.abi 3288).pre s := by
  implies_sat [Spec.Camellia.ctrContract, Spec.Camellia.ctrSig, Spec.Camellia.ctrPre,
    Spec.Camellia.ctrPost, X86_64.abi, X86_64.argRegs] [ctrFrameSat] using ctrFrameSat

/-- CTR with its working space on the stack. -/
theorem ctr_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 ctr)
      (Spec.Camellia.ctrContract X86_64.abi 3288) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.ctrSig) (nm := "scratch") (e := .u64)
    (n := 409) (pre := Spec.Camellia.ctrPre X86_64.abi.ptrBits)
    (post := Spec.Camellia.ctrPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3280) (by rw [← Proof.Camellia.ctrScratchContract_eq]; exact ctr_verified)
    (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Camellia.ctrPostOut_local _) ctrFrameSat_pre

end VG.Proof.Camellia.X86_64
