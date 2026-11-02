module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.VerifyMsgCT
import VerifiedGarbage.Proof.Ed25519.RISCV64.WindowRhs
import VerifiedGarbage.Proof.Ed25519.RISCV64.WindowCT
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Impl.Ed25519.RISCV64.VerifyWindow
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# `vg_ed25519_verify` on RISC-V, verified

The code meets `verifyContract` under `abi.withConsts bConsts` (the static of
the cached `-[1]B … -[15]B`, which `verify_equation` reads) with the frame
(34 doublewords, so aligned as the contract's `u64` buffers are) as one more
argument (`Sig.scratchContract`) and 208 bytes of stack for the callees'
frames: the proof against the contract's facts by register (`verC`: `verR`
without the static, and what the static adds), which it implies
(`bconsts_implies`), with the windows' proofs (`rhs_ok`, `rhs_ct`), and a
state satisfying it, with the static at `0x100000` (`bMem`). In a frame of
272 bytes on the stack (`Verified.stackScratchLC`), it meets the contract
itself.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole
open VG.Impl.Ed25519.RISCV64 (bSym bWords bConsts)
open VG.Proof.Ed25519.RISCV64 (bWords_length rhs_ok rhs_ct)

/-- A contract by register `kR` without the static implies the signature's contract under
`abi`; so does it with the static, under `abi.withConsts bConsts`. -/
theorem bconsts_implies {kR : Contract isa} {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {st : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (h : kR.Implies (sig.contract abi pre post wa st leak))
    (hpost : ∀ s s', kR.post s s' → kR.post (stripConsts bConsts s) s')
    (hpub : ∀ s₁ s₂, kR.pub (stripConsts bConsts s₁) (stripConsts bConsts s₂) → kR.pub s₁ s₂)
    (hsat : ∃ s, (sig.contract (abi.withConsts bConsts) pre post wa st leak).pre s) :
    Contract.Implies (M := isa)
      { pre := fun s => kR.pre (stripConsts bConsts s) ∧ ConstsOk bConsts st s
        post := kR.post
        pub := fun s₁ s₂ => kR.pub s₁ s₂ ∧ s₁.syms bSym = s₂.syms bSym }
      (sig.contract (abi.withConsts bConsts) pre post wa st leak) where
  pre _ hs := ⟨h.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (post_stripConsts.mp (h.post (stripConsts bConsts s) s'
    (pre_consts.mp hs).1 (hpost s s' hp)))
  pub s₁ s₂ h₁ h₂ hp := ⟨hpub _ _ (h.pub (stripConsts bConsts s₁) (stripConsts bConsts s₂)
      (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_stripConsts.mpr (pub_consts.mp hp).1)),
    (pub_consts.mp hp).2 _ List.mem_cons_self⟩
  sat := hsat

/-- A state satisfying the precondition, without the static. -/
def verSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | .a4 => 0x4000 | .a5 => 0x8000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 0⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x8000, 272⟩]

theorem verR_implies : verR.Implies (Sig.scratchContract RISCV64.abi Spec.Ed25519.verifySig "frame" .u64 34
    (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.verifyPost RISCV64.abi.ptrBits) true 208
    (some (Proof.Ed25519.WholeLocal.verifyLeak RISCV64.abi.ptrBits))) := by
  sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.verifySig,
    Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.verifyPost, Proof.Ed25519.WholeLocal.verifyLeak, verR,
    verResult, RISCV64.abi, RISCV64.argRegs] [verSat] using verSat

/-- The static at `0x100000`. -/
@[irreducible] def bMem : Mem := constMem 0x100000 bWords

theorem bMem_held : ∀ i < bWords.length,
    bMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0 := by
  have h := constMem_held 0x100000 bWords (by rw [bWords_length]; decide)
  unfold bMem
  exact h

/-- `verSat` with the static. -/
def verSatC : State :=
  { verSat with mem := bMem, rd := verSat.rd ++ [⟨0x100000, 1920⟩], syms := fun _ => 0x100000 }

theorem verC_sat : (Sig.scratchContract (RISCV64.abi.withConsts bConsts) Spec.Ed25519.verifySig "frame"
    .u64 34 (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.verifyPost RISCV64.abi.ptrBits) true
    208 (some (Proof.Ed25519.WholeLocal.verifyLeak RISCV64.abi.ptrBits))).pre verSatC := by
  have hl := bWords_length
  have held := bMem_held
  dsimp only [bConsts]
  generalize bWords = W' at hl held ⊢
  generalize e : verSatC = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.verifySig,
    Spec.Ed25519.scratchWords, RISCV64.abi, RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x4000, 8192⟩ : Region), ⟨0x8000, 272⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem verC_implies : verC.Implies (Sig.scratchContract (RISCV64.abi.withConsts bConsts)
    Spec.Ed25519.verifySig "frame" .u64 34 (Curry.const (fun _ => True) _)
    (Proof.Ed25519.WholeLocal.verifyPost RISCV64.abi.ptrBits) true 208
    (some (Proof.Ed25519.WholeLocal.verifyLeak RISCV64.abi.ptrBits))) :=
  bconsts_implies (kR := verR) verR_implies (fun _ _ h => h) (fun _ _ h => h) ⟨verSatC, verC_sat⟩

theorem verify_verified :
    Verified RISCV64.target verifyMessage (Sig.scratchContract (RISCV64.abi.withConsts bConsts)
      Spec.Ed25519.verifySig "frame" .u64 34 (Curry.const (fun _ => True) _)
      (Proof.Ed25519.WholeLocal.verifyPost RISCV64.abi.ptrBits) true 208
      (some (Proof.Ed25519.WholeLocal.verifyLeak RISCV64.abi.ptrBits))) :=
  Verified.of_correct (ver_ok rhs_ok) (ver_ct rhs_ok rhs_ct) verC_implies

/-- A state satisfying `vg_ed25519_verify`'s precondition, without the frame. -/
def verFrameSat : State := { verSatC with wr := [⟨0x4000, 8192⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Ed25519.verifyContract (RISCV64.abi.withConsts bConsts) (208 + 272)).pre s := by
  refine ⟨verFrameSat, ?_⟩
  have hl := bWords_length
  have held := bMem_held
  dsimp only [bConsts]
  generalize bWords = W' at hl held ⊢
  generalize e : verFrameSat = s
  sig_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig, Spec.Ed25519.scratchWords, RISCV64.abi,
    RISCV64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x4000, 8192⟩ : Region)] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 272 bytes. -/
theorem verify_framed :
    Verified RISCV64.target verifyCode (Spec.Ed25519.verifyContract (RISCV64.abi.withConsts bConsts) (208 + 272)) :=
  Verified.stackScratchLC (sig := Spec.Ed25519.verifySig) (nm := "frame") (e := .u64) (n := 34)
    (post := Proof.Ed25519.WholeLocal.verifyPost RISCV64.abi.ptrBits) (wa := true) (stack := 208) (bytes := 272)
    (leak := some (Proof.Ed25519.WholeLocal.verifyLeak RISCV64.abi.ptrBits)) verify_verified (by decide)
    (by decide) verFrameSat_pre

end VG.Proof.Ed25519.RISCV64.Whole
