module

public import VerifiedGarbage.Proof.Sm4.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Sm4.X86_64.ModeCore
public import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit
public import VerifiedGarbage.Proof.Modes.X86_64.Ctr
meta import VerifiedGarbage.Proof.Modes.X86_64.Ctr
public import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
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
# SM4-CTR on x86-64 meets its contracts

`ctr_wp`: the modes' CTR over SM4's core (`Proof.Modes.X86_64.ctr_wp` with
`modeCoreSpec`). `ctr_verified`: `ctr` is correct and constant time, by
the taint analysis: the pointers, `n` and the stack pointer are public, and
so is everything the code computes from them; the counter block is secret.
`ctr_framed` runs it with its working space on the stack, zeroed on return:
3144 bytes, the 392 words of the scratch buffer and 8 more.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.X86_64 VG.Impl.Sm4.X86_64

/-- CTR on x86-64 with its working space at `r8`. -/
def ctrX86_64 : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 128⟩
    let ctr : Region := ⟨s.gpr .rsi, 16⟩
    let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * slots⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [ctr, data, scratch] ∧ sched.Disjoint ctr ∧ sched.Disjoint data ∧
      sched.Disjoint scratch ∧ ctr.Disjoint data ∧ ctr.Disjoint scratch ∧ data.Disjoint scratch ∧
      ret.Disjoint ctr ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * slots ≤ 2 ^ 64
  post s s' :=
    Spec.Cbc.blocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
        Spec.Ctr.crypt (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (s.gpr .rdi))) (Spec.Aes.bytesAt s.mem (s.gpr .rsi) 16)
          (Spec.Cbc.blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 16 = Spec.Ctr.next (Spec.Aes.bytesAt s.mem (s.gpr .rsi) 16) (s.gpr .rcx).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (ctrX86_64)

attribute [local irreducible] Spec.Sm4.cipher in
/-- The core's cipher is the contract's. Proved with `Spec.Sm4.cipher`
irreducible: otherwise the unifier unfolds it (`CoreSpec.cipher`, a
projection, is lower) and compares the two encryptions term by term. -/
theorem cipher_eq (k : Spec.Sm4.Schedule) : modeCoreSpec.cipher k = Spec.Sm4.cipher k := rfl

theorem ctr_wp {s₀ : State} (hp : ctrX86_64.pre s₀) :
    WP isa ctr s₀ fun s' => gprPreserved s₀ s' ∧ ctrX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKC, dKD, dKS, dCD, dCS, dDS, dRC, dRD, dRS, fitK, fitC, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.ctr_wp modeCoreSpec (r := ⟨.rsi, .rdx, .rcx, .r8⟩) ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dCS dDS dCD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKC⟩) fun s' ⟨hcs, hdata, hctr, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, ?_, hctr⟩
  swap
  · rw [cipher_eq] at hdata; exact hdata
  rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dRS
  · exact dRC
  · exact dRD

/-- The initial taint: the registers of the arguments and the stack pointer are
public. It knows nothing of the writable regions: the code never reads a public
value back from them, and tracking them would cost the kernel at every store. -/
def ctrTaint : X86_64.Taint.T := Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]

theorem ctrTaint_agree (s t : State) (_ : ctrX86_64.pre s) (_ : ctrX86_64.pre t)
    (hp : ctrX86_64.pub s t) : X86_64.Taint.Agree ctrTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [p1, p2, p3, p4, p5, p6]

theorem ctr_ct : ConstantTime isa ctrX86_64.pre ctrX86_64.pub ctr :=
  VG.Taint.constantTime (A := taint) ctrTaint ctrTaint_agree (by taint_decide)

theorem ctr_correct (s : State) (hs : ctrX86_64.pre s) :
    ∃ t s', Exec isa ctr s t s' ∧ abiPreserved s s' ∧ ctrX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := ctr_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := ctr) (by lit_decide) he hg, hpost⟩

/-- A state satisfying the precondition (one block). -/
def ctrSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 392⟩]

theorem ctr_verified :
    Verified X86_64.target ctr (Proof.Sm4.ctrScratchContract X86_64.abi slots) :=
  Verified.of_correct ctr_correct ctr_ct (by
    sig_implies [Proof.Sm4.ctrScratchContract, Proof.Sm4.ctrScratchSig, Proof.Sm4.ctrPost, ctrX86_64,
      X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot] [ctrSat] using ctrSat)

/-- CTR with its working space on the stack. -/
theorem ctr_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3144 .r8 392 ctr)
      (Spec.Sm4.ctrContract X86_64.abi 3144) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.ctrSig) (nm := "scratch") (e := .u64)
    (n := 392) (post := Proof.Sm4.ctrPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3144) ctr_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Sm4.ctrPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by lit_decide) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm4.X86_64
