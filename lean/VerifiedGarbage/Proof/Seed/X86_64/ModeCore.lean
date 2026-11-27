module

public import VerifiedGarbage.Proof.Seed.X86_64.Ecb
public import VerifiedGarbage.Proof.Seed.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Impl.X86_64Scal
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Modes.X86_64.Core
public import VerifiedGarbage.Impl.Seed.X86_64.Modes
public import VerifiedGarbage.Proof.Seed.ModeBytes
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Seed.X86_64.Lit
import VerifiedGarbage.Proof.Modes.X86_64.Fb
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.Depth
meta import VerifiedGarbage.Impl.Seed.X86_64.Modes
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Seed.ModeBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.Depth
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Seed.X86_64.Lit
public import VerifiedGarbage.Proof.Seed.X86_64.ConstantTime
public import VerifiedGarbage.Spec.Seed.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Seed.X86_64.Ecb
meta import VerifiedGarbage.Proof.Seed.X86_64.ConstantTime
meta import VerifiedGarbage.Spec.Seed.Contract
meta import VerifiedGarbage.Proof.Seed.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.TaintSum

/-! ### `Seed.X86_64.EcbCall`, which this module and modules that import it used -/

section

/-! ### `Seed.X86_64.Verified`, which only this module used -/

section

/-! # The ECB functions meet their contracts, with the scratch buffer as an argument -/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64

/-- With `n` bytes of working space at `rcx` (1056 for ECB, 1088 for the blocks functions). -/
def contract (d : Spec.Seed.Direction) (n : Nat := 1056) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 128⟩
    let data : Region := ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, n⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
      (s.gpr .rsi).toNat + 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.Seed.blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem (s.gpr .rdi)) d
        (Spec.Seed.blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem ecbPre_of {s : State} {d : Spec.Seed.Direction} {n : Nat} (hn : 1056 ≤ n) (hs : (contract d n).pre s) :
    EcbPre s := by
  obtain ⟨rd, wr, kd, kb, db, rdt, rb, fit⟩ := hs
  have sub : Region.Sub ⟨s.gpr .rcx, 8 * Impl.Seed.X86_64.scratchSlots⟩ ⟨s.gpr .rcx, n⟩ :=
    Region.sub_prefix (by unfold Impl.Seed.X86_64.scratchSlots; omega_using [hn])
  exact { scratch := ⟨n, by unfold Impl.Seed.X86_64.scratchSlots; omega_using [hn], by
            rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
          dataIn := by rw [wr]; exact List.mem_cons_self
          keyIn := by rw [rd]; exact List.mem_cons_self
          keyData := kd
          keyBuf := kb.sub_right sub
          dataBuf := db.sub_right sub
          retData := rdt
          retBuf := rb.sub_right sub
          fit := by omega_using [fit] }

theorem ecbTaint_wf (d : Spec.Seed.Direction) {n : Nat} (hn : 1056 ≤ n) (hn' : n ≤ 2 ^ 64) (s : State)
    (hs : (contract d n).pre s) : Taint.Wf ecbTaint s := by
  obtain ⟨_, hwr, _, _, dataSep, _, _, fit⟩ := hs
  refine ⟨?_, ?_⟩
  · intro _
    rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 0 ≤ 16 * (s.gpr .rdx).toNat; omega_using [])
        (List.Forall₂.cons (by change 8 * Impl.Seed.X86_64.scratchSlots ≤ n; unfold Impl.Seed.X86_64.scratchSlots; omega_using [hn])
          List.Forall₂.nil)
    · exact List.Pairwise.cons
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dataSep)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64; omega_using [fit]
      · exact hn'
  · intro p hp
    simp only [ecbTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .rcx = s.gpr .rcx + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem ecbTaint_agree (d : Spec.Seed.Direction) {n : Nat} (hn : 1056 ≤ n) (hn' : n ≤ 2 ^ 64) (s t : State)
    (hs : (contract d n).pre s) (ht : (contract d n).pre t)
    (hp : (contract d n).pub s t) : X86_64.Taint.Agree ecbTaint s t := by
  refine ⟨?_, ?_, ecbTaint_wf d hn hn' s hs, ecbTaint_wf d hn hn' t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      exact hp r (by simpa only [ecbTaint, RegSet.mem_ofList] using hr)
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, hp .rsi (by decide), hp .rdx (by decide), hp .rcx (by decide)]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [ecbTaint, RegSet.not_mem_empty] at hr

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1056⟩]

theorem ecb_correct (d : Spec.Seed.Direction) {n : Nat} (hn : 1056 ≤ n) (s : State) (hs : (contract d n).pre s) :
    ∃ t s', Exec isa (Impl.Seed.X86_64.ecb d) s t s' ∧ gprPreserved s s' ∧ (contract d n).post s s' := by
  obtain ⟨t, s', he, hp⟩ := ecb_ok d (ecbPre_of hn hs)
  exact ⟨t, s', he, hp.gpr, ecb_blocks _ _ _ _ _ _ hp.done⟩

theorem encrypt_correct {n : Nat} (hn : 1056 ≤ n) (s : State) (hs : (contract .encrypt n).pre s) :
    ∃ t s', Exec isa Impl.Seed.X86_64.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt n).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := ecb_correct .encrypt hn s hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.Seed.X86_64.encrypt) (by lit_decide) he hg, hp⟩

theorem decrypt_correct {n : Nat} (hn : 1056 ≤ n) (s : State) (hs : (contract .decrypt n).pre s) :
    ∃ t s', Exec isa Impl.Seed.X86_64.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt n).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := ecb_correct .decrypt hn s hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.Seed.X86_64.decrypt) (by lit_decide) he hg, hp⟩

theorem publicRegs_five (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx, .rsp] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp := by
  simp [PublicRegs]

/-- `satState` with the 1088 bytes of `vg_seed_*_blocks`'s working space. -/
def satStateBlocks : State := { satState with wr := [⟨0x2000, 0⟩, ⟨0x3000, 1088⟩] }

/-- ECB against `vg_seed_encrypt_blocks`'s contract: its working space is 136 words, of which
the code uses the first 132. -/
theorem encrypt_blocks_verified : Verified target Impl.Seed.X86_64.encrypt
    (Proof.Seed.blocksContract abi .encrypt) := by
  refine Verified.of_correct (encrypt_correct (n := 1088) (by decide))
    (encrypt_constantTime _ _ (ecbTaint_agree .encrypt (n := 1088) (by decide) (by decide))) ?_
  sig_implies [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, abi, argRegs,
    contract, publicRegs_five] [satStateBlocks] using satStateBlocks

theorem decrypt_blocks_verified : Verified target Impl.Seed.X86_64.decrypt
    (Proof.Seed.blocksContract abi .decrypt) := by
  refine Verified.of_correct (decrypt_correct (n := 1088) (by decide))
    (decrypt_constantTime _ _ (ecbTaint_agree .decrypt (n := 1088) (by decide) (by decide))) ?_
  sig_implies [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, abi, argRegs,
    contract, publicRegs_five] [satStateBlocks] using satStateBlocks

end VG.Proof.Seed.X86_64

end

end

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
      rw [List.mem_singleton] at hr; subst hr; exact sD.symm) (by omega_using [fitD])
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
    · exact List.Forall₂.cons (by change 0 ≤ (s.gpr .rdx).toNat * 16; omega_using [])
        (List.Forall₂.cons (by change 1088 ≤ 1088; omega_using []) List.Forall₂.nil)
    · exact List.Pairwise.cons
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dataSep)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change (s.gpr .rdx).toNat * 16 ≤ 2 ^ 64; omega_using [fitD]
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
    (by cases d <;> exact Code.all_of_spTest (by lit_decide)) (by cases d <;> lit_decide) (by decide)
    (Proof.Seed.ecbPostOut_local _ d)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Seed.X86_64

end

end

/-!
# SEED's core for the modes on x86-64

`dirCoreSpec d`: SEED's core for the direction `d`
(`Impl.Seed.X86_64.dirCore d`) meets what the modes need of a core of
16-byte blocks (`Proof.Modes.X86_64.BlockSpec`, with `bw = 2`), with the key
a schedule, its cipher `Spec.Seed.cipher` for encryption and
`Spec.Seed.invCipher` for decryption, and the key ready when its copy in the
core's slots is the schedule and the 8 bytes below `rsp` are apart from the
slots. `crypt` calls the blocks function of `d` (`WP.call`, with
`Proof.Seed.blocksContract`) on the buffer's sixteen blocks, its return
address stored in the 8 bytes below `rsp`; the scratch buffer's address,
the data's address and the blocks left cross the call in `xmm12` …
`xmm14`, since the callee writes no `xmm` register (`scalCode`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Seed.X86_64
open VG.Impl.Aes.X86_64 (sb)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.X86_64 (ScrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp movR_ok addImm_ok movImm_ok
  signExtend_small runBlock_app addr_add stkRegion stkList coreFrame WrIn)
open VG.Spec.Seed (Direction)

/-- The schedule's copy and the buffer, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)
abbrev bufAt (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * bufSlot)

/-- The schedule at `rdi`, outside the regions `rs`, and the 8 bytes below
`rsp`, where the core's call stores its return address, apart from `rs`. -/
def ModeKeyArgs (s : State) (rs : List Region) (k : Spec.Seed.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ k = Spec.Seed.scheduleAt s.mem p ∧ (⟨p, 128⟩ : Region) ∈ s.rd ∧
    p.toNat + 128 ≤ 2 ^ 64 ∧ (∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r) ∧
    8 ≤ (s.gpr .rsp).toNat ∧ ∀ r ∈ rs, Region.Disjoint (stkRegion (s.gpr .rsp) 8) r

/-- The schedule's copy is `k`, and the 8 bytes below `rsp` are apart from
the scratch buffer. -/
def Ready (s : State) (B : Addr) (k : Spec.Seed.Schedule) : Prop :=
  Spec.Seed.scheduleAt s.mem (schedAddr B) = k ∧ 8 ≤ (s.gpr .rsp).toNat ∧
    Region.Disjoint (stkRegion (s.gpr .rsp) 8) ⟨B, 8 * 192⟩

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (d : Direction) : (dirCore d).bw = 2 := rfl

theorem dirCipher_bytes (d : Direction) (k : Spec.Seed.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 16) = (cipher d k (Spec.Seed.blockAt m p)).toList := by
  obtain h : (Vector.ofFn fun i : Fin 16 => (Spec.Aes.bytesAt m p 16).getD i.val 0) = Spec.Seed.blockAt m p := by
    ext i hi; simp [Spec.Aes.bytesAt, Spec.Seed.blockAt]
  cases d <;> simp only [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher, cipher, h]

/-- The core's slots, its buffer and the schedule's copy. -/
theorem core_eq (d : Direction) (B : Addr) : coreRegion (dirCore d) B = ⟨B, 1472⟩ := by
  simp only [coreRegion, dirCore, schedSlot, bufSlot]
theorem blk_eq (d : Direction) (B : Addr) : blkRegion (dirCore d) B = ⟨B + BitVec.ofNat 64 1088, 256⟩ := by
  simp only [blkRegion, dirCore, bufSlot]
theorem total_eq (d : Direction) : (dirCore d).total = 192 := by
  simp only [dirCore, schedSlot, bufSlot]
theorem stkList_dirCore (d : Direction) (rsp : Addr) : stkList (dirCore d) rsp = [stkRegion rsp 8] := rfl

theorem sched_sub (B : Addr) : Region.Sub ⟨schedAddr B, 128⟩ ⟨B, 1472⟩ := Offset.sub_base B (by decide)
theorem sched_buf (B : Addr) : Region.Disjoint ⟨schedAddr B, 128⟩ ⟨B + BitVec.ofNat 64 1088, 256⟩ :=
  Offset.disjoint B (.inr (by decide)) (by decide) (by decide)
theorem sched_work (B : Addr) : Region.Disjoint ⟨schedAddr B, 128⟩ ⟨B, 1088⟩ :=
  Offset.disjoint_base B (by decide) (by decide)

theorem ready_frame {d : Direction} {s s' : State} {B : Addr} {k : Spec.Seed.Schedule} {rs : List Region}
    (h : Ready s B k) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B))
    (_ : WrIn rs s s') (hg : ∀ r, r ∉ Proof.Modes.X86_64.modeRegs (dirCore d) → s'.gpr r = s.gpr r) : Ready s' B k := by
  obtain ⟨hk, hst, hsd⟩ := h
  obtain hsp : s'.gpr .rsp = s.gpr .rsp := hg .rsp (by simp only [Proof.Modes.X86_64.modeRegs, dirCore]; decide)
  refine ⟨?_, by rw [hsp]; exact hst, by rw [hsp]; exact hsd⟩
  rw [scheduleAt_frame hf fun r hr => ?_]
  · exact hk
  rcases hd r hr with h' | h'
  · rw [core_eq] at h'; exact h'.sub_left (sched_sub B)
  · rw [blk_eq] at h'; exact (sched_buf B).sub_right h'

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Seed.Schedule} (h : ModeKeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.rdi, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis, hst, hsd⟩ := h
  obtain hsp : s'.gpr .rsp = s.gpr .rsp := hr .rsp (by simp)
  refine ⟨p, by rw [hr .rdi (by simp), hp], ?_, by rw [hrd]; exact hin, hfit, hdis, by rw [hsp]; exact hst,
    by rw [hsp]; exact hsd⟩
  rw [hk]
  exact (scheduleAt_frame hf hdis).symm

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.Seed.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready s' B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧
      Frame (coreFrame (dirCore d) B (s.gpr .rsp)) s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis, hst, hsd⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  obtain hsep : Region.Disjoint ⟨p, 128⟩ ⟨B, 1536⟩ := (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]))
  refine WP.mono (copyN_wp (k := 16) (P := schedAddr B) (Q := p) ⟨by rw [hB], by rw [hp]; simp, by decide,
    by decide, fun w hw => ⟨_, hs.wr, by
      rw [addr_add, total_eq]; exact Offset.contains_base B (by simp only [schedSlot, bufSlot]; omega_using [hw])
        (by simp only [schedSlot, bufSlot]; omega_using [hw])⟩,
    fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega_using [hw]) (by omega_using [hw])⟩,
    (hsep.sub_right (Offset.sub_base B (by decide))).symm, by omega_using []⟩) fun s' h => ?_
  obtain hsp : s'.gpr .rsp = s.gpr .rsp := h.regs .rsp (by decide)
  refine ⟨⟨scheduleAt_congr_at fun i hi => by rw [h.mem, over_at hi (by omega_using [])], by rw [hsp]; exact hst,
      by rw [hsp, ← total_eq d]; exact hsd _ hR⟩,
    by rw [h.regs _ (by decide), hB], hsp, h.regs _ (by decide), h.regs _ (by decide), ?_, h.rd, h.wr⟩
  rw [h.mem]
  exact (over_frame _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, by rw [core_eq]; exact sched_sub B⟩

/-- Block `j` of blocks transformed by ECB. -/
theorem blockAt_of_ecb {K : Spec.Seed.Schedule} {d : Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Seed.blocksAt m' D n = Spec.Seed.ecb K d (Spec.Seed.blocksAt m D n)) {j : Nat} (hj : j < n) :
    Spec.Seed.blockAt m' (D + BitVec.ofNat 64 (16 * j)) = cipher d K (Spec.Seed.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have := congrArg (fun l => l[j]?) h
  cases d <;> simpa [Spec.Seed.blocksAt, Spec.Seed.ecb, cipher, hj] using this

/-- The blocks functions write no `xmm` register. -/
theorem blockCall_scal (d : Direction) : scalCode (blockCall d) = true := by
  cases d <;> lit_decide

theorem crypt_wp (d : Direction) {s : State} {B : Addr} {k : Spec.Seed.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : Ready s B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧ Ready s' B k ∧
      Frame (coreFrame (dirCore d) B (s.gpr .rsp)) s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hk, hst, hsd⟩ := hr
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hw := hs.wr
  rw [total_eq] at hw
  -- `sb`, the data's address and the blocks left to `xmm12` … `xmm14`.
  obtain ⟨s₁, e₁, x₁, g₁, m₁, rd₁, wr₁⟩ := Modes.X86_64.movqX_ok s .xmm12 sb
  obtain ⟨s₂, e₂, x₂, g₂, m₂, rd₂, wr₂⟩ := Modes.X86_64.movqX_ok s₁ .xmm13 .r12
  obtain ⟨s₃, e₃, x₃, g₃, m₃, rd₃, wr₃⟩ := Modes.X86_64.movqX_ok s₂ .xmm14 .r13
  obtain x₃₁₂ : s₃.xmm .xmm12 = (0 : BitVec 64) ++ s.gpr sb := by
    have h₂ : some (s₁.setXmm .xmm13 ((0 : BitVec 64) ++ s₁.gpr .r12)) = some s₂ := e₂
    have h₃ : some (s₂.setXmm .xmm14 ((0 : BitVec 64) ++ s₂.gpr .r13)) = some s₃ := e₃
    rw [← Option.some.inj h₃, RegUpd.xmm_setXmm_of_ne _ _ (by decide), ← Option.some.inj h₂,
      RegUpd.xmm_setXmm_of_ne _ _ (by decide), x₁]
  obtain x₃₁₃ : s₃.xmm .xmm13 = (0 : BitVec 64) ++ s.gpr .r12 := by
    have h₃ : some (s₂.setXmm .xmm14 ((0 : BitVec 64) ++ s₂.gpr .r13)) = some s₃ := e₃
    rw [← Option.some.inj h₃, RegUpd.xmm_setXmm_of_ne _ _ (by decide), x₂, g₁]
  obtain x₃₁₄ : s₃.xmm .xmm14 = (0 : BitVec 64) ++ s.gpr .r13 := by rw [x₃, g₂, g₁]
  -- The arguments: `rdi`, `rsi`, `rdx` and `rcx` to the schedule's copy, the buffer, its sixteen blocks and
  -- the working space.
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .rdi sb
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addImm_ok s₄ .rdi (BitVec.ofNat 32 (8 * schedSlot))
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := movR_ok s₅ .rsi sb
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := addImm_ok s₆ .rsi (BitVec.ofNat 32 (8 * bufSlot))
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := movImm_ok s₇ .rdx 16
  obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := movR_ok s₈ .rcx sb
  obtain g₉ : ∀ x, x ≠ .rdi → x ≠ .rsi → x ≠ .rdx → x ≠ .rcx → s₉.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [o₉ x h4, o₈ x h3, o₇ x h2, o₆ x h2, o₅ x h1, o₄ x h1, g₃, g₂, g₁]
  obtain sb₃ : s₃.gpr sb = B := by rw [g₃, g₂, g₁, hB]
  obtain rdi₉ : s₉.gpr .rdi = schedAddr B := by
    rw [o₉ _ (by decide), o₈ _ (by decide), o₇ _ (by decide), o₆ _ (by decide), r₅, r₄, sb₃,
      signExtend_small (by decide)]
  obtain rsi₉ : s₉.gpr .rsi = bufAt B := by
    rw [o₉ _ (by decide), o₈ _ (by decide), r₇, r₆, o₅ _ (by decide), o₄ _ (by decide), sb₃,
      signExtend_small (by decide)]
  obtain rdx₉ : s₉.gpr .rdx = 16 := by rw [o₉ _ (by decide), r₈]
  obtain rcx₉ : s₉.gpr .rcx = B := by
    rw [r₉, o₈ _ (by decide), o₇ _ (by decide), o₆ _ (by decide), o₅ _ (by decide), o₄ _ (by decide), sb₃]
  obtain rsp₉ : s₉.gpr .rsp = s.gpr .rsp := g₉ _ (by decide) (by decide) (by decide) (by decide)
  obtain mem₉ : s₉.mem = s.mem := by rw [m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]
  obtain rd₉' : s₉.rd = s.rd := by rw [rd₉, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
  obtain wr₉' : s₉.wr = s.wr := by rw [wr₉, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]
  obtain xmm₉ : s₉.xmm = s₃.xmm := by
    rw [Modes.X86_64.runBlock_vec (by decide) e₉, Modes.X86_64.runBlock_vec (by decide) e₈,
      Modes.X86_64.runBlock_vec (by decide) e₇, Modes.X86_64.runBlock_vec (by decide) e₆,
      Modes.X86_64.runBlock_vec (by decide) e₅, Modes.X86_64.runBlock_vec (by decide) e₄]
  show WP isa (.seq (.block cryptHead) (.seq (blockCall d) (.block cryptTail))) s _
  refine WP.seq (WP.of_runBlock ⟨s₉, by
    rw [show cryptHead = [.xop (.movq .xmm12 sb)] ++ ([.xop (.movq .xmm13 .r12)] ++ ([.xop (.movq .xmm14 .r13)] ++
      ([Impl.Aes.X86_64.movR .rdi sb] ++ ([.alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot)))] ++
      ([Impl.Aes.X86_64.movR .rsi sb] ++ ([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * bufSlot)))] ++
      ([.movImm64 .rdx 16] ++ [Impl.Aes.X86_64.movR .rcx sb]))))))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some,
      runBlock_app, e₇, Option.bind_some, runBlock_app, e₈, Option.bind_some, e₉], ?_⟩)
  -- The call.
  have stS : Region.Disjoint (stkRegion (s.gpr .rsp) 8) ⟨B, 1536⟩ := hsd
  obtain sub : ∀ off len, off + len ≤ 1536 → ∃ r' ∈ s₉.wr, ∃ o,
      (B + BitVec.ofNat 64 off) = r'.base + BitVec.ofNat 64 o ∧ o + len ≤ r'.len :=
    fun off len h => ⟨_, by rw [wr₉']; exact hw, off, rfl, h⟩
  obtain sub0 : ∃ r' ∈ s₉.wr, ∃ o, B = r'.base + BitVec.ofNat 64 o ∧ o + 1088 ≤ r'.len := by
    obtain ⟨r', h1, o, h2, h3⟩ := sub 0 1088 (by decide)
    exact ⟨r', h1, o, by rw [← h2]; exact (BitVec.add_zero B).symm, h3⟩
  obtain w : WP isa (blockCall d) s₉ fun s' => (s'.rd = s₉.rd ∧ s'.wr = s₉.wr ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s₉.gpr r) ∧
      Frame [⟨bufAt B, 256⟩, ⟨B, 1088⟩, stkRegion (s.gpr .rsp) 8] s₉.mem s'.mem ∧
      Spec.Seed.blocksAt s'.mem (bufAt B) 16 =
        Spec.Seed.ecb (Spec.Seed.scheduleAt s₉.mem (schedAddr B)) d (Spec.Seed.blocksAt s₉.mem (bufAt B) 16)) ∧
      s'.xmm = s₉.xmm ∧ s'.ymmHi = s₉.ymmHi := by
    refine WP.vecKeep (blockCall_scal d) ?_
    rw [blockCall_eq]
    refine WP.call (k := Proof.Seed.blocksContract abi d) (blocks_verified d).1 (blocks_nosp d)
      (by rw [blocks_depth]; decide) (rd := [⟨schedAddr B, 128⟩]) (wr := [⟨bufAt B, 256⟩, ⟨B, 1088⟩]) ?_
      (Covers.of_sub fun r hr => ?_) (Covers.of_sub fun r hr => ?_)
      (fun s' hrd hwr hcs hf _ hpost => ?_)
    · sig_pre [Proof.Seed.blocksContract, Proof.Seed.blocksSig, abi, argRegs]
      rw [rdi₉, rsi₉, rdx₉, rcx₉, rsp₉, show (16 : BitVec 64).toNat * 16 = 256 from rfl]
      obtain hfit : ∀ off, off < 1536 → (B + BitVec.ofNat 64 off).toNat = B.toNat + off := fun off h => by
        rw [Offset.toNat_add_ofNat]; omega_using [hfB, h]
      refine ⟨rfl, rfl, sched_buf B, sched_work B, Offset.disjoint_base B (by decide) (by decide),
        stS.sub_right (Offset.sub_base B (by decide)), stS.sub_right (Offset.sub_base B (by decide)),
        stS.sub_right (Region.sub_prefix (by decide)), ?_, ?_, by omega_using [hfB]⟩
      · rw [schedAddr, hfit _ (by decide)]; simp only [schedSlot, bufSlot]; omega_using [hfB]
      · rw [bufAt, hfit _ (by decide)]; simp only [bufSlot]; omega_using [hfB]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hr
      rcases hr with rfl | rfl | rfl
      · obtain ⟨r', h1, o, h2, h3⟩ := sub (8 * schedSlot) 128 (by decide)
        exact ⟨r', List.mem_append_right _ h1, o, h2, h3⟩
      · obtain ⟨r', h1, o, h2, h3⟩ := sub (8 * bufSlot) 256 (by decide)
        exact ⟨r', List.mem_append_right _ h1, o, h2, h3⟩
      · obtain ⟨r', h1, o, h2, h3⟩ := sub0
        exact ⟨r', List.mem_append_right _ h1, o, h2, h3⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub (8 * bufSlot) 256 (by decide)
      · exact sub0
    · obtain ⟨s₂', hm₂, _, hpost⟩ := hpost
      rw [blocks_depth, rsp₉] at hf
      refine ⟨hrd, hwr, hcs, by simpa using hf, ?_⟩
      sig_reduce [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, abi, argRegs] at hpost
      rw [BitVec.setWidth_eq, rdi₉, rsi₉, rdx₉, show (16 : BitVec 64).toNat = 16 from rfl] at hpost
      obtain hfr := callEntry_frame' s₉
      rw [State.callEntry_mem, rsp₉] at hfr
      rw [rsp₉] at hpost
      rw [← hm₂, hpost, Proof.Seed.scheduleAt_frame hfr (p := schedAddr B) fun r hr => by
          rw [List.mem_singleton] at hr; subst hr; exact (stS.sub_right (Offset.sub_base B (by decide))).symm,
        Proof.Seed.blocksAt_frame hfr (p := bufAt B) (n := 16) (fun r hr => by
          rw [List.mem_singleton] at hr; subst hr; exact (stS.sub_right (Offset.sub_base B (by decide))).symm)
          (by decide)]
  obtain ⟨t₁₀, s₁₀, e₁₀, ⟨rd₁₀, wr₁₀, cs₁₀, f₁₀, res₁₀⟩, xmm₁₀, -⟩ := w
  refine WP.seq ⟨t₁₀, s₁₀, e₁₀, ?_⟩
  -- The three registers back.
  obtain ⟨u₁, q₁, v₁, p₁, n₁, rdu₁, wru₁, xu₁⟩ := Modes.X86_64.movqR_ok s₁₀ sb .xmm12
  obtain ⟨u₂, q₂, v₂, p₂, n₂, rdu₂, wru₂, xu₂⟩ := Modes.X86_64.movqR_ok u₁ .r12 .xmm13
  obtain ⟨u₃, q₃, v₃, p₃, n₃, rdu₃, wru₃, -⟩ := Modes.X86_64.movqR_ok u₂ .r13 .xmm14
  refine WP.of_runBlock ⟨u₃, by
    rw [show cryptTail = [.movqR sb .xmm12] ++ ([.movqR .r12 .xmm13] ++ [.movqR .r13 .xmm14]) from rfl,
      runBlock_app, q₁, Option.bind_some, runBlock_app, q₂, Option.bind_some, q₃], ?_⟩
  obtain xx : u₂.xmm = s₃.xmm := by rw [xu₂, xu₁, xmm₁₀, xmm₉]
  obtain mu : u₃.mem = s₁₀.mem := by rw [n₃, n₂, n₁]
  obtain rspu : u₃.gpr .rsp = s.gpr .rsp := by
    rw [p₃ _ (by decide), p₂ _ (by decide), p₁ _ (by decide), cs₁₀ .rsp (by decide), rsp₉]
  obtain fsched : ∀ r ∈ [(⟨bufAt B, 256⟩ : Region), ⟨B, 1088⟩, stkRegion (s.gpr .rsp) 8],
      Region.Disjoint ⟨schedAddr B, 128⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sched_buf B
    · exact sched_work B
    · exact (stS.sub_right (Offset.sub_base B (by decide))).symm
  refine ⟨?_, rspu, ?_, ?_, ⟨?_, by rw [rspu]; exact hst, by rw [rspu]; exact hsd⟩, ?_, fun j hj => ?_,
    by rw [rdu₃, rdu₂, rdu₁, rd₁₀, rd₉'], by rw [wru₃, wru₂, wru₁, wr₁₀, wr₉']⟩
  · rw [p₃ _ (by decide), p₂ _ (by decide), v₁, xmm₁₀, xmm₉, x₃₁₂, Modes.X86_64.extract_zero_append, hB]
  · rw [p₃ _ (by decide), v₂, xu₁, xmm₁₀, xmm₉, x₃₁₃, Modes.X86_64.extract_zero_append]
  · rw [v₃, xx, x₃₁₄, Modes.X86_64.extract_zero_append]
  · rw [mu, scheduleAt_frame f₁₀ fsched, mem₉]; exact hk
  · show Frame (coreRegion (dirCore d) B :: stkList (dirCore d) (s.gpr .rsp)) s.mem u₃.mem
    rw [stkList_dirCore, core_eq, mu, ← mem₉]
    refine f₁₀.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub_base B (by decide)⟩
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · have hj16 : j < 16 := by simp only [dirCore] at hj; exact hj
    obtain ea : blkAddr (dirCore d) B j = bufAt B + BitVec.ofNat 64 (16 * j) := by
      rw [blkAddr, bufAt, Offset.add_add]; simp only [dirCore, bufSlot]
    rw [dirCore_bw, show 8 * 2 = 16 from rfl, ea, dirCipher_bytes, bytesAt_eq, mu,
      blockAt_of_ecb res₁₀ hj16, mem₉, hk]

/-- SEED's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : BlockSpec (dirCore d) where
  Key := Spec.Seed.Schedule
  cipher := dirCipher d
  KeyArgs := ModeKeyArgs
  Ready := Ready
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Seed.cipher, Spec.Seed.invCipher]
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore, schedSlot, bufSlot]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore, schedSlot, bufSlot]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.X86_64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame := ready_frame
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.Seed.X86_64
