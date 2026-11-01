module

public import VerifiedGarbage.Impl.Seed.X86_64.Modes
public import VerifiedGarbage.Proof.Seed.Contract
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.TCB.X86_64.Target

import VerifiedGarbage.Proof.Seed.X86_64.Verified
import VerifiedGarbage.Proof.Seed.ModeBytes
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Seed.X86_64.Lit
meta import VerifiedGarbage.Impl.Seed.X86_64.Modes
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Seed.X86_64.Verified
meta import VerifiedGarbage.Proof.Seed.ModeBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.Depth
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Seed.X86_64.Lit

/-!
# SEED ECB on x86-64: calls of the blocks functions

`vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt` allocate their working
space on the stack (1088 bytes, as `vg_seed_{en,de}crypt_blocks` need) and
call the blocks function of their direction with it (`ecbCall`), which
stores its return address in the 8 bytes below `rsp`. `ecbCall_verified`
proves that code from the blocks functions' contracts, with the working
space as an argument and 8 bytes of stack; `ecbCall_framed` adds the frame
of the working space.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.Impl.Seed.X86_64

/-- The ECB contracts with `scratch: *mut [u64; 136]` and `stack = 8`, as
`sig_pre` evaluates them. -/
def ecbCallX86_64 (d : Spec.Seed.Direction) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 128⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat * 16⟩
    let scr : Region := ⟨s.gpr .rcx, 1088⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := below (s.gpr .rsp) 8
    s.rd = [sched] ∧ s.wr = [data, scr] ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧
      data.Disjoint scr ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧ stk.Disjoint sched ∧ stk.Disjoint data ∧
      stk.Disjoint scr ∧ 8 ≤ (s.gpr .rsp).toNat ∧
      (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat * 16 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 1088 ≤ 2 ^ 64
  post s s' :=
    Spec.Seed.blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem (s.gpr .rdi)) d
        (Spec.Seed.blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The code of the blocks function of `d`. -/
def blocksCode : Spec.Seed.Direction → Prog isa
  | .encrypt => encrypt
  | .decrypt => decrypt

theorem blockCall_eq (d : Spec.Seed.Direction) :
    blockCall d = .call (match d with | .encrypt => "vg_seed_encrypt_blocks" | .decrypt => "vg_seed_decrypt_blocks")
      (blocksCode d) := by
  cases d <;> rfl

theorem blocks_verified (d : Spec.Seed.Direction) :
    Verified target (blocksCode d) (Proof.Seed.blocksContract abi d) := by
  cases d
  · exact encrypt_blocks_verified
  · exact decrypt_blocks_verified

theorem blocks_nosp (d : Spec.Seed.Direction) : NoSp (blocksCode d) := by
  have h : ∀ c : Prog isa, c.allInstrs (fun i => !Taint.clobbers i .rsp) = true →
      ∀ i ∈ instrs c, Taint.clobbers i .rsp = false := fun c h => by
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    exact fun i hi => by simpa using h i hi
  cases d
  · exact h _ (by lit_decide)
  · exact h _ (by lit_decide)

theorem blocks_depth (d : Spec.Seed.Direction) : (blocksCode d).depth = 0 := by
  cases d <;> rfl

/-- The return address a call stores. -/
theorem callEntry_frame' (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- A call of code meeting the blocks contract of `d`. -/
theorem ecbCall_correct (d : Spec.Seed.Direction) (s₀ : State) (hs : (ecbCallX86_64 d).pre s₀) :
    ∃ t s', Exec isa (ecbCall d) s₀ t s' ∧ abiPreserved s₀ s' ∧ (ecbCallX86_64 d).post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, rD, rS, sK, sD, sS, hsp, fitK, fitD, fitS⟩ := hs
  have hv := blocks_verified d
  rw [show ecbCall d = blockCall d from rfl, blockCall_eq]
  refine (WP.call_mx (k := Proof.Seed.blocksContract abi d) hv.1 (blocks_nosp d)
    (by rw [blocks_depth]; decide) (rd := s₀.rd) (wr := s₀.wr) ?_
    (Covers.refl _) (Covers.refl _)
    (Q := fun s' => abiPreserved s₀ s' ∧ (ecbCallX86_64 d).post s₀ s') ?_).elim
    fun t ⟨s', he, hq⟩ => ⟨t, s', he, hq⟩
  · sig_pre [Proof.Seed.blocksContract, Proof.Seed.blocksSig, abi, argRegs]
    exact ⟨hrd, hwr, dKD, dKS, dDS, sK, sD, sS, fitK, fitD, fitS⟩
  · intro s' _ _ hcs hf _ ⟨s₂, hm₂, _, hpost⟩ hmx
    sig_reduce [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, abi, argRegs] at hpost
    rw [BitVec.setWidth_eq] at hpost
    rw [blocks_depth] at hf
    have hfr := callEntry_frame' s₀
    rw [State.callEntry_mem] at hfr
    have hsch := Proof.Seed.scheduleAt_frame hfr (p := s₀.gpr .rdi) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact sK.symm
    have hblk := Proof.Seed.blocksAt_frame hfr (p := s₀.gpr .rsi) (n := (s₀.gpr .rdx).toNat) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact sD.symm) (by omega)
    refine ⟨⟨hcs, hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), hmx⟩, ?_⟩
    · rw [hwr] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact rD
      · exact rS
      · exact Offset.base_disjoint_below _ (by decide)
    · show Spec.Seed.blocksAt s'.mem (s₀.gpr .rsi) (s₀.gpr .rdx).toNat = _
      rw [← hm₂, hpost, hsch, hblk]

/-- The pointers, `n` and the stack pointer are public, and the working
space, at `rcx`, is the second writable region. -/
def ecbCallTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false, lens := [0, 1088],
    bases := [(.rcx, 1, 0)] }

theorem ecbCallTaint_wf (d : Spec.Seed.Direction) (s : State) (hs : (ecbCallX86_64 d).pre s) :
    Taint.Wf ecbCallTaint s := by
  obtain ⟨_, hwr, _, _, dataSep, _, _, _, _, _, _, _, fitD, fitS⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 0 ≤ (s.gpr .rdx).toNat * 16; omega)
        (List.Forall₂.cons (by change 1088 ≤ 1088; omega) List.Forall₂.nil)
    · exact List.Pairwise.cons
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dataSep)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change (s.gpr .rdx).toNat * 16 ≤ 2 ^ 64; omega
      · change 1088 ≤ 2 ^ 64; decide
  · intro p hp
    simp only [ecbCallTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .rcx = s.gpr .rcx + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem ecbCallTaint_agree (d : Spec.Seed.Direction) (s t : State) (hs : (ecbCallX86_64 d).pre s)
    (ht : (ecbCallX86_64 d).pre t) (hp : (ecbCallX86_64 d).pub s t) : X86_64.Taint.Agree ecbCallTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp
  refine ⟨?_, ?_, ecbCallTaint_wf d s hs, ecbCallTaint_wf d t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [ecbCallTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
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
    simp only [ecbCallTaint, RegSet.not_mem_empty] at hr

theorem ecbCall_ct (d : Spec.Seed.Direction) :
    ConstantTime isa (ecbCallX86_64 d).pre (ecbCallX86_64 d).pub (ecbCall d) := by
  cases d
  · exact VG.Taint.constantTime (A := taint) ecbCallTaint (ecbCallTaint_agree .encrypt) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) ecbCallTaint (ecbCallTaint_agree .decrypt) (by taint_decide)

/-- A state satisfying the precondition with the working space as an
argument: the schedule at `0x1000`, one block at `0x3000`, the working space
at `0x4000`. -/
def ecbCallSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 1 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 1088⟩]

theorem ecbCall_verified (d : Spec.Seed.Direction) :
    Verified X86_64.target (ecbCall d) (Proof.Seed.ecbScratchContract X86_64.abi d 136 8) :=
  Verified.of_correct (ecbCall_correct d) (ecbCall_ct d) (by
    sig_implies [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, ecbCallX86_64,
      X86_64.abi, X86_64.argRegs] [ecbCallSat] using ecbCallSat)

/-- `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`: the call in a frame
allocating the working space, 1096 bytes (the 1088 of the working space and 8
to keep `rsp` aligned at the call), and the call's 8: 1104 bytes of stack in
all. -/
theorem ecbCall_framed (d : Spec.Seed.Direction) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 1096 .rcx 136 (ecbCall d))
      (Spec.Seed.ecbContract X86_64.abi d 1104) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Seed.ecbSig) (nm := "scratch") (e := .u64)
    (n := 136) (post := Spec.Seed.ecbPost d X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 1096) (ecbCall_verified d) (by decide) (by decide) (by decide)
    (by cases d <;> exact Code.all_of_allInstrs (by lit_decide)) (by cases d <;> lit_decide) (by decide)
    (Proof.Seed.ecbPostOut_local _ d)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Seed.X86_64
