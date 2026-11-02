module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.ByRegister
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.PublicKeyCT
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarBase
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Comb
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Whole
public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# `vg_ed25519_public_key` on RISC-V, verified

The code meets `publicKeyContract` under `abi.withConsts combConsts` (the
comb's table, which `vg_ed25519_scalar_base` reads) with the frame (18
doublewords, so aligned as the contract's `u64` buffers are) as one more
argument (`Sig.scratchContract`) and 208 bytes of stack for the callees'
frames: the proof against the contract's facts by register (`pkC`: `pkR`
without the table, and what the table adds), which it implies
(`consts_implies`), and a state satisfying it, with the table at `0x100000`
(`tblMem`). In a frame of 144 bytes on the stack whose first 136 it zeroes
before returning (`Verified.stackScratchWipedC`), it meets the contract
itself.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole
open VG.Impl.Ed25519.RISCV64 (combSym combWords combConsts)
open VG.Proof.Ed25519.RISCV64 (combWords_length)

/-- A state satisfying the precondition, without the table. -/
def pkSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x4000 | .a3 => 0x8000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩]

theorem pkR_implies : pkR.Implies (Sig.scratchContract RISCV64.abi Spec.Ed25519.publicKeySig "frame" .u64 18
    (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.publicKeyPost RISCV64.abi.ptrBits) true 208) := by
  sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.publicKeySig,
    Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.publicKeyPost, pkR, RISCV64.abi, RISCV64.argRegs]
    [pkSat] using pkSat

/-- The comb's table at `0x100000`. -/
@[irreducible] def tblMem : Mem := constMem 0x100000 combWords

theorem tblMem_held : ∀ i < combWords.length,
    tblMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  have h := constMem_held 0x100000 combWords (by rw [combWords_length]; decide)
  unfold tblMem
  exact h

/-- `pkSat` with the table. -/
def pkSatC : State :=
  { pkSat with mem := tblMem, rd := pkSat.rd ++ [⟨0x100000, 49152⟩], syms := fun _ => 0x100000 }

theorem pkC_sat : (Sig.scratchContract (RISCV64.abi.withConsts combConsts) Spec.Ed25519.publicKeySig "frame"
    .u64 18 (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.publicKeyPost RISCV64.abi.ptrBits) true
    208).pre pkSatC := by
  have hl := combWords_length
  have held := tblMem_held
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : pkSatC = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.publicKeySig,
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
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩, ⟨0x8000, 144⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem pkC_implies : pkC.Implies (Sig.scratchContract (RISCV64.abi.withConsts combConsts)
    Spec.Ed25519.publicKeySig "frame" .u64 18 (Curry.const (fun _ => True) _)
    (Proof.Ed25519.WholeLocal.publicKeyPost RISCV64.abi.ptrBits) true 208) :=
  consts_implies (kR := pkR) pkR_implies (fun _ _ h => h) (fun _ _ h => h) ⟨pkSatC, pkC_sat⟩

theorem publicKey_verified :
    Verified RISCV64.target publicKey (Sig.scratchContract (RISCV64.abi.withConsts combConsts)
      Spec.Ed25519.publicKeySig "frame" .u64 18 (Curry.const (fun _ => True) _)
      (Proof.Ed25519.WholeLocal.publicKeyPost RISCV64.abi.ptrBits) true 208) :=
  Verified.of_correct (pk_ok base_ok) (publicKey_ct fun _ _ _ _ ⟨⟨h0, h1, h2, h3, hsp⟩, hsy⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption, hsy⟩) pkC_implies

/-- A state satisfying `vg_ed25519_public_key`'s precondition, without the frame. -/
def pkFrameSat : State := { pkSatC with wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩] }

theorem pkFrameSat_pre : ∃ s, (Spec.Ed25519.publicKeyContract (RISCV64.abi.withConsts combConsts)
    (208 + 144)).pre s := by
  refine ⟨pkFrameSat, ?_⟩
  have hl := combWords_length
  have held := tblMem_held
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : pkFrameSat = s
  sig_pre [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig, Spec.Ed25519.scratchWords, RISCV64.abi,
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
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 144 bytes, whose first 136 it zeroes before returning. -/
theorem publicKey_framed :
    Verified RISCV64.target publicKeyCode
      (Spec.Ed25519.publicKeyContract (RISCV64.abi.withConsts combConsts) (208 + 144)) :=
  Verified.stackScratchWipedC (sig := Spec.Ed25519.publicKeySig) (nm := "frame") (e := .u64) (n := 18)
    (post := Proof.Ed25519.WholeLocal.publicKeyPost RISCV64.abi.ptrBits) (wa := true) (stack := 208) (bytes := 144)
    (words := 17) publicKey_verified (by decide) (by decide) (by decide)
    (Proof.Ed25519.WholeLocal.publicKeyPostOut_local _) pkFrameSat_pre

end VG.Proof.Ed25519.RISCV64.Whole
