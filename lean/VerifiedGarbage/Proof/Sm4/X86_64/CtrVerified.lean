import VerifiedGarbage.Proof.Sm4.X86_64.Ctr
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SM4-CTR on x86-64 meets its contracts

`ctr_verified`: `ctr` is correct (`ctr_wp`) and constant time, by the taint
analysis: the pointers, `n` and the stack pointer are public, and so is
everything the code computes from them; the counter block is secret.
`ctr_framed` runs it with its working space on the stack, zeroed on return:
3144 bytes, the 392 words of the scratch buffer and 8 more.
-/

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (ctrX86_64)

def ctrTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [16, 0, 8 * slots], bases := [(.r8, 2, 0)] }

theorem ctrTaint_wf (s : State) (hs : ctrX86_64.pre s) : Taint.Wf ctrTaint s := by
  obtain ⟨_, hwr, _, _, _, dCD, dCS, dDS, _, _, _, _, fitC, fitD, fitB⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 16 ≤ 16; omega)
        (List.Forall₂.cons (by change 0 ≤ 16 * (s.gpr .rcx).toNat; omega)
          (List.Forall₂.cons (by change 8 * slots ≤ 8 * slots; omega) List.Forall₂.nil))
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
      · change 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64
        have := (s.gpr .rdx).isLt; omega
      · change 8 * slots ≤ 2 ^ 64; rw [slots_eq]; omega
  · intro p hp
    simp only [ctrTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .r8 = s.gpr .r8 + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem ctrTaint_agree (s t : State) (hs : ctrX86_64.pre s) (ht : ctrX86_64.pre t)
    (hp : ctrX86_64.pub s t) : X86_64.Taint.Agree ctrTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
  refine ⟨?_, ?_, ctrTaint_wf s hs, ctrTaint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [ctrTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
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
    simp only [ctrTaint, RegSet.not_mem_empty] at hr

theorem ctr_ct : ConstantTime isa ctrX86_64.pre ctrX86_64.pub ctr :=
  VG.Taint.constantTime (A := taint) ctrTaint ctrTaint_agree (by taint_decide)

theorem ctr_correct (s : State) (hs : ctrX86_64.pre s) :
    ∃ t s', Exec isa ctr s t s' ∧ abiPreserved s s' ∧ ctrX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := ctr_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := ctr) (by decide +kernel) he hg, hpost⟩

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
    (Code.all_of_allInstrs (by decide +kernel)) (by decide +kernel) (by decide)
    (Proof.Sm4.ctrPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm4.X86_64
