import VerifiedGarbage.Proof.Camellia.X86_64.Ecb
import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Camellia ECB on x86-64 meets its contracts

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis: the pointers, `rounds`, `n` and the stack pointer are
public, and so is everything the code computes from them, which it keeps
in registers or, while `crypt8` runs, in public slots of the scratch
buffer (the data pointer, the blocks left and the postwhitening's address).
`ecb_framed` runs it with its working space on the stack, zeroed on return:
3152 bytes, the 393 words of the scratch buffer and 8 more.
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.Impl.Camellia.X86_64

def ecbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [0, 8 * slots], bases := [(.r8, 1, 0)] }

theorem ecbTaint_wf (dir : Dir) (s : State) (hs : (ecbX86_64 dir).pre s) : Taint.Wf ecbTaint s := by
  obtain ⟨_, hwr, _, _, dDS, _, _, _, _, fitB, _⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 0 ≤ 16 * (s.gpr .rcx).toNat; omega)
        (List.Forall₂.cons (by change 8 * slots ≤ 8 * slots; omega) List.Forall₂.nil)
    · exact List.Pairwise.cons
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dDS)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64
        have := (s.gpr .rdx).isLt; omega
      · change 8 * slots ≤ 2 ^ 64; omega
  · intro p hp
    simp only [ecbTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .r8 = s.gpr .r8 + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem ecbTaint_agree (dir : Dir) (s t : State) (hs : (ecbX86_64 dir).pre s) (ht : (ecbX86_64 dir).pre t)
    (hp : (ecbX86_64 dir).pub s t) : X86_64.Taint.Agree ecbTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
  refine ⟨?_, ?_, ecbTaint_wf dir s hs, ecbTaint_wf dir t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [ecbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
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
    simp only [ecbTaint, RegSet.not_mem_empty] at hr

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbX86_64 dir).pre (ecbX86_64 dir).pub (ecb dir) := by
  cases dir
  · exact VG.Taint.constantTime (A := taint) ecbTaint (ecbTaint_agree .encrypt) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) ecbTaint (ecbTaint_agree .decrypt) (by taint_decide)

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbX86_64 dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbX86_64 dir).post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := ecb_wp dir hs
  refine ⟨t, s', he, abiPreserved_of_exec (c := ecb dir) ?_ he hg, hpost⟩
  cases dir <;> decide +kernel

/-- A state satisfying the precondition (one block, 18 rounds). -/
def ecbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 18 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 393⟩]

theorem ecb_verified (dir : Dir) :
    Verified X86_64.target (ecb dir) (Proof.Camellia.ecbScratchContract X86_64.abi (specDir dir) slots) :=
  Verified.of_correct (ecb_correct dir) (ecb_ct dir) (by
    cases dir <;>
    sig_implies [Proof.Camellia.ecbScratchContract, Proof.Camellia.ecbScratchSig, Spec.Camellia.ecbSig,
      Spec.Camellia.ecbPre, Spec.Camellia.ecbPost, ecbX86_64, specDir, X86_64.abi, X86_64.argRegs, slots,
      tailSlot, endSlot, keySlot] [ecbSat] using ecbSat)

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000`, one block at `0x3000`, 18 rounds. -/
def ecbFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 18 | .rdx => 0x3000 | .rcx => 1 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x3000, 16⟩]

theorem ecbFrameSat_pre (d : Spec.Camellia.Direction) :
    ∃ s, (Spec.Camellia.ecbContract X86_64.abi d 3152).pre s := by
  implies_sat [Spec.Camellia.ecbContract, Spec.Camellia.ecbSig, Spec.Camellia.ecbPre,
    Spec.Camellia.ecbPost, X86_64.abi, X86_64.argRegs] [ecbFrameSat] using ecbFrameSat

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3152 .r8 393 (ecb dir))
      (Spec.Camellia.ecbContract X86_64.abi (specDir dir) 3152) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.ecbSig) (nm := "scratch") (e := .u64)
    (n := 393) (pre := Spec.Camellia.ecbPre X86_64.abi.ptrBits)
    (post := Spec.Camellia.ecbPost (specDir dir) X86_64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3152) (by rw [← Proof.Camellia.ecbScratchContract_eq]; exact ecb_verified dir)
    (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by cases dir <;> decide +kernel))
    (by cases dir <;> decide +kernel) (by decide) (Proof.Camellia.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Camellia.X86_64
