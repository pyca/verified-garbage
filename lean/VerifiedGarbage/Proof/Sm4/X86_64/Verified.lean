import VerifiedGarbage.Proof.Sm4.X86_64.Ecb
import VerifiedGarbage.Proof.Sm4.X86_64.Lit
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SM4 ECB on x86-64 meets its contracts

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis: the pointers, `n` and the stack pointer are public, and so
is everything the code computes from them. `ecb_framed` runs it with its
working space on the stack, zeroed on return: 3128 bytes, the 390 words of
the scratch buffer and 8 more.
-/

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (specDir ecbX86_64)

def ecbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false,
    lens := [0, 8 * slots], bases := [(.rcx, 1, 0)] }

theorem ecbTaint_wf (dir : Dir) (s : State) (hs : (ecbX86_64 dir).pre s) : Taint.Wf ecbTaint s := by
  obtain ⟨_, hwr, _, _, dDS, _, _, _, fitD, fitB⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 0 ≤ 16 * (s.gpr .rdx).toNat; omega)
        (List.Forall₂.cons (by change 8 * slots ≤ 8 * slots; omega) List.Forall₂.nil)
    · exact List.Pairwise.cons
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dDS)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64
        have := (s.gpr .rsi).isLt; omega
      · change 8 * slots ≤ 2 ^ 64; rw [slots_eq]; omega
  · intro p hp
    simp only [ecbTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .rcx = s.gpr .rcx + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem ecbTaint_agree (dir : Dir) (s t : State) (hs : (ecbX86_64 dir).pre s) (ht : (ecbX86_64 dir).pre t)
    (hp : (ecbX86_64 dir).pub s t) : X86_64.Taint.Agree ecbTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp
  refine ⟨?_, ?_, ecbTaint_wf dir s hs, ecbTaint_wf dir t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [ecbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [p1, p2, p3, p4, p5]
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, p2, p3, p4]
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
  cases dir <;> lit_decide

/-- A state satisfying the precondition (one block). -/
def ecbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 1 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 8 * 390⟩]

theorem ecb_verified (dir : Dir) :
    Verified X86_64.target (ecb dir) (Proof.Sm4.ecbScratchContract X86_64.abi (specDir dir) slots) :=
  Verified.of_correct (ecb_correct dir) (ecb_ct dir) (by
    cases dir <;>
    sig_implies [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, ecbX86_64, specDir,
      X86_64.abi, X86_64.argRegs, slots, savedSlot, tableEnd, tableSlot] [ecbSat] using ecbSat)

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3128 .rcx 390 (ecb dir))
      (Spec.Sm4.ecbContract X86_64.abi (specDir dir) 3128) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Sm4.ecbSig) (nm := "scratch") (e := .u64)
    (n := 390) (post := Spec.Sm4.ecbPost (specDir dir) X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3128) (ecb_verified dir) (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by cases dir <;> lit_decide)) (by cases dir <;> lit_decide) (by decide)
    (Proof.Sm4.ecbPostOut_local _ _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm4.X86_64
