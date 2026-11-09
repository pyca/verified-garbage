module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Seed.Contract
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Seed.X86.Ecb
meta import VerifiedGarbage.Proof.Seed.X86.Ecb
public import VerifiedGarbage.Proof.Seed.X86.Lit
meta import VerifiedGarbage.Proof.Seed.X86.Lit
public import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Seed.X86.Lanes
meta import VerifiedGarbage.Proof.Seed.X86.Lanes
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Aes.X86.Sbox
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Linear
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Seed.G16
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Seed.X86.Crypt8
meta import VerifiedGarbage.Proof.Aes.X86.Sbox
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Linear
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Seed.G16
meta import VerifiedGarbage.Proof.Seed.Memory
meta import VerifiedGarbage.Proof.Seed.X86.Crypt8

/-!
# SEED ECB on x86 (32-bit): correctness, and the rounds' taint summary

`ecb_correct`: `ecb dir`, `vg_seed_encrypt_blocks` and
`vg_seed_decrypt_blocks`, meets `ecbX86 dir` (`ecb_wp`). `roundsSum`: the
taint analysis of the loop of rounds, which both directions run, once, as a
summary. `wideContract` is `ecbX86` with the argument slots writable, which
`narrowRd` and `narrowWr` narrow back.
-/

@[expose] public section

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.Impl.Seed.X86
open VG.Proof.Seed (ecbX86)

/-- What is public at the loop of rounds: the stack pointer, the round keys'
and the scratch buffer's pointers, the flags, and the slots of the caller's
`esi` and `ebp` and of the group's data pointer. -/
def roundsTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp, .esi, .edi], flags := true, lens := [0, 4 * Impl.Seed.X86.wsSlots],
    bases := [(.edi, 1, 0)],
    slots := [(1, 4 * (Impl.Seed.X86.savedSlot + 1), 4), (1, 4 * (Impl.Seed.X86.savedSlot + 3), 8)], argLen := 20,
    argBases := [(8, 0), (16, 1)] }

/-! The loop of rounds, which both directions run, analysed once, as a summary. -/

taint_summary roundsSum : VG.X86.taint roundsTaint (.block Impl.Seed.X86.roundPair)

theorem ecb_correct (dir : Spec.Seed.Direction) (s : State) (hs : (ecbX86 dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbX86 dir).post s s' :=
  ecb_wp dir hs

/-- `ecbX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`narrowRd`, `narrowWr` narrow it to `ecbX86`). -/
def wideContract (dir : Spec.Seed.Direction) : Contract isa :=
  { ecbX86 dir with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
      let data : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * Impl.Seed.X86.wsSlots⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [sched] ∧ s.wr = [data, scratch, args] ∧
      sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 4 * Impl.Seed.X86.wsSlots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 16⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, 4 * Impl.Seed.X86.wsSlots⟩]

tactic_template "narrow_seed_x86_verified" : tactic => `(tactic| simp only [VG.Proof.Seed.ecbX86, VG.Proof.Seed.X86.wideContract,
                     VG.Proof.Seed.X86.narrowRd, VG.Proof.Seed.X86.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])
tactic_template "narrow_seed_x86_verified" loc:Lean.Parser.Tactic.location : tactic => `(tactic| simp only [VG.Proof.Seed.ecbX86, VG.Proof.Seed.X86.wideContract,
                     VG.Proof.Seed.X86.narrowRd, VG.Proof.Seed.X86.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $loc)

end VG.Proof.Seed.X86
