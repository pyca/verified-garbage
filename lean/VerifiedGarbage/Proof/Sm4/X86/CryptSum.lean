module

public import VerifiedGarbage.Proof.Sm4.X86.LayersLit
meta import VerifiedGarbage.Proof.Sm4.X86.LayersLit
public import VerifiedGarbage.Impl.Sm4.X86.Modes
meta import VerifiedGarbage.Impl.Sm4.X86.Modes
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The constant-time analysis of SM4's x86 core, once

Every mode's code contains the bitsliced core `crypt8` (the transposes and
the rounds), which OFB, CFB64 and CFB8 reach at the same taint (`τCrypt`),
CBC at another (`τCryptCbc`, their regions in another order) and ECB at a
third (`τCryptEcb`): the stack and the scratch buffer's base public, with the
buffer's word at 1424. The analyses of the core are summaries
(`taint_summary`), which the modes' checks use (`taint_decide_sum`, by the
code, `CodeEq`) in place of the analysis of the core in each.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86

/-- What OFB, CFB64 and CFB8 have public where they run the core. -/
def τCrypt : VG.X86.Taint.T :=
  { regs := .ofList [.esp, .ebp, .esi, .edi], flags := true, lens := [0, 16, 8 * 181],
    bases := [(.edi, 2, 0)], slots := ⟨[0, 0, 0xFF <<< 1424]⟩, argLen := 24,
    argBases := [(12, 0), (8, 1), (20, 2)] }

taint_summary cryptSum : taint τCrypt Impl.Sm4.X86.crypt8

/-- What CBC encryption and decryption have public where they run the core
(decryption has the flags too). -/
def τCryptCbc : VG.X86.Taint.T :=
  { regs := .ofList [.esp, .ebp, .esi, .edi], flags := false, lens := [0, 8 * 181],
    bases := [(.edi, 1, 0)], slots := ⟨[0, 0xFF <<< 1424]⟩, argLen := 24, argBases := [(12, 0), (20, 1)] }

taint_summary cryptSumCbc : taint τCryptCbc Impl.Sm4.X86.crypt8

/-- What ECB encryption and decryption have public where they run the core. -/
def τCryptEcb : VG.X86.Taint.T :=
  { regs := .ofList [.esp, .ebp, .esi, .edi], flags := true, lens := [0, 8 * 179],
    bases := [(.edi, 1, 0)], slots := ⟨[0, 0xFF <<< 1424]⟩, argLen := 20, argBases := [(8, 0), (16, 1)] }

taint_summary cryptSumEcb : taint τCryptEcb Impl.Sm4.X86.crypt8

end VG.Proof.Sm4.X86
