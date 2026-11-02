module

public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Checks of every instruction, on code without its displacements

What `lit_decide` checks of every instruction of a function (that nothing
writes `rsp`, that it loads no MXCSR, that its calls can be inlined) does not
depend on the instructions' displacements and immediates (`Code.erase`,
`Proof/Framework/X86_64/TaintErase.lean`). So the kernel can check it on
the function's erased literal of shared blocks (`materialize_shared`),
evaluating each repeated block once.
-/

@[expose] public section

namespace VG.X86_64

theorem Code.allInstrs_mapBlocks {p : Instr → Bool} {f : Instr → Instr} (hp : ∀ i, p (f i) = p i) :
    ∀ c : Prog isa, (c.mapBlocks f).allInstrs p = c.allInstrs p
  | .block is => by
    rw [Code.allInstrs_eq, Code.allInstrs_eq]
    simp only [Code.mapBlocks, instrs, KList.map_eq, List.all_map, Function.comp_def, hp]
  | .seq a b => by
    simp only [Code.mapBlocks, Code.allInstrs, Code.allInstrs_mapBlocks hp a, Code.allInstrs_mapBlocks hp b]
  | .ite _ t e => by
    simp only [Code.mapBlocks, Code.allInstrs, Code.allInstrs_mapBlocks hp t, Code.allInstrs_mapBlocks hp e]
  | .loop b _ => by simp only [Code.mapBlocks, Code.allInstrs, Code.allInstrs_mapBlocks hp b]
  | .call _ b => by simp only [Code.mapBlocks, Code.allInstrs, Code.allInstrs_mapBlocks hp b]
  | .frame _ b _ => by simp only [Code.mapBlocks, Code.allInstrs, Code.allInstrs_mapBlocks hp b]
  | .icall .. => rfl

theorem Code.noCalls_mapBlocks (f : Instr → Instr) : ∀ c : Prog isa, (c.mapBlocks f).noCalls = c.noCalls
  | .block _ => rfl
  | .seq a b => by simp only [Code.mapBlocks, Code.noCalls, Code.noCalls_mapBlocks f a, Code.noCalls_mapBlocks f b]
  | .ite _ t e => by simp only [Code.mapBlocks, Code.noCalls, Code.noCalls_mapBlocks f t, Code.noCalls_mapBlocks f e]
  | .loop b _ => by simp only [Code.mapBlocks, Code.noCalls, Code.noCalls_mapBlocks f b]
  | .call _ _ => rfl
  | .frame .. => rfl
  | .icall .. => rfl

theorem Taint.clobbers_erase (r : Reg) (i : Instr) : Taint.clobbers i.erase r = Taint.clobbers i r := by
  cases i <;> rfl

theorem loadsMxcsr_erase (i : Instr) : loadsMxcsr i.erase = loadsMxcsr i := by
  cases i <;> rfl

theorem Src.noRsp_erase (s : Src) : s.erase.noRsp = s.noRsp := by
  cases s <;> rfl

theorem Instr.rspFree_erase (i : Instr) : i.erase.rspFree = i.rspFree := by
  cases i <;> first | rfl | simp only [Instr.erase, Instr.rspFree, Src.noRsp_erase]

theorem Code.InlineOk_erase : ∀ c : Prog isa, (Code.erase c).InlineOk = c.InlineOk
  | .block is => by
    show KList.all (KList.map Instr.erase is) _ = KList.all is _
    simp only [KList.all_eq, KList.map_eq, List.all_map, Function.comp_def, Taint.clobbers_erase]
  | .seq a b => by
    show ((Code.erase a).InlineOk && (Code.erase b).InlineOk) = _
    rw [Code.InlineOk_erase a, Code.InlineOk_erase b]; rfl
  | .ite _ t e => by
    show ((Code.erase t).InlineOk && (Code.erase e).InlineOk) = _
    rw [Code.InlineOk_erase t, Code.InlineOk_erase e]; rfl
  | .loop b _ => Code.InlineOk_erase b
  | .call _ b => by
    show ((b.mapBlocks Instr.erase).noCalls && (b.mapBlocks Instr.erase).allInstrs Instr.rspFree) = _
    rw [Code.noCalls_mapBlocks, Code.allInstrs_mapBlocks Instr.rspFree_erase]; rfl
  | .frame .. => rfl
  | .icall .. => rfl

end VG.X86_64
