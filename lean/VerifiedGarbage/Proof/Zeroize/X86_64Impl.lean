module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
public import VerifiedGarbage.Proof.Zeroize.X86_64Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.ModeSim

/-!
# `vg_zeroize` on x86-64, for the functions that call it

`ZeroizeImpl`: an implementation of `vg_zeroize` that verified code calls
(`Code.call name code`), verified against `Spec.Zeroize.zeroizeContract`,
which never writes the stack pointer, never touches MXCSR and uses no stack: `scalar`
(`vg_zeroize`) or `avx` (`vg_zeroize_avx`). Its callers are generic over
them (`Variants/Zeroize/X86_64/`).
-/

@[expose] public section

namespace VG.Proof.Zeroize.X86_64

open VG VG.X86_64 VG.Impl.Zeroize.X86_64

/-- An implementation of `vg_zeroize` on x86-64, for the functions that call it. -/
structure ZeroizeImpl where
  /-- Its symbol and its code: the code of the artifact
  (`Artifacts/Zeroize/X86_64.lean`), called as an internal function of its
  own, `<artifact>_core`, since the artifact also clears what it leaves
  (`Proof.Zeroize.X86_64.zeroizeReg`), which its callers, which clear their
  own, do not need. -/
  name : String
  code : Prog isa
  verified : Verified target code (Spec.Zeroize.zeroizeContract abi)
  spSafe : code.all (fun i => !isa.writesSp i) = true
  /-- It never touches MXCSR, so its callers' runs need not agree on it
  (`Contract.mxFree`). -/
  noMx : code.allInstrs (fun i => !touchesMxcsr i) = true
  /-- It uses no stack. -/
  xd : code.x86_64Depth = 0
  /-- What the names of its callers' instances end with (`_avx`; nothing
  for the baseline). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The level of its vector instructions. -/
  level : Impl.Scrub.X86_64.VecLevel
  /-- What the cleanup of a function that calls it needs of its code, at
  that level (`X86_64.Scrub.calleeSide`), evaluated here, once. -/
  side : X86_64.Scrub.calleeSide code level.level 0 = true := by lit_decide

/-- `vg_zeroize`'s code. -/
def ZeroizeImpl.scalar : ZeroizeImpl where
  name := "vg_zeroize_core"
  code := zeroize
  verified := Proof.Zeroize.X86_64.verified
  spSafe := Code.all_of_allInstrs (by decide)
  noMx := by decide
  xd := rfl
  suffix := ""
  features := []
  level := .sse

/-- `vg_zeroize_avx`'s code. -/
def ZeroizeImpl.avx : ZeroizeImpl where
  name := "vg_zeroize_avx_core"
  code := zeroizeAvx
  verified := Proof.Zeroize.X86_64.verifiedAvx
  spSafe := Code.all_of_allInstrs (by decide)
  noMx := by decide
  xd := rfl
  suffix := "_avx"
  features := ["avx"]
  level := .avx

end VG.Proof.Zeroize.X86_64
