module

public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64.AbsorbF
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AES-CMAC's streaming functions on x86-64: the functions as emitted

Each function, over the implementations it calls, in the frame its
implementations' working space needs (`Impl.Aes.X86_64.Space`), then its
cleanup (`Impl.Scrub.X86_64.scrubAll v 0 n`): every vector register at the
level `v` and every caller-saved register cleared, and its whole frame
wiped.
-/

@[expose] public section

namespace VG.Impl.CmacAes.Stream.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)
open VG.Impl.Aes.X86_64 (Space Ctr32 ExpandKey)
open VG.Impl.StackScratch.X86_64 (withStackScratch)

/-- The bytes of stack `vg_cmac_aes_init`, `_absorb` and `_finish` use over
an implementation with the working space `sp`, `free` as given. -/
def stack (free : Nat) : Space → Nat
  | .free => free
  | .small => 1816
  | .full => 2328

/-- `Spec.Cmac.aesInitApi`'s function as emitted. -/
def init (v : VecLevel) (sp : Space) (e : ExpandKey) (c : Ctr32) (sfx : String) : Prog isa :=
  match sp with
  | .free => scrubAll v 0 184 (withStackScratch 168 .rcx (Stream.X86_64.initF .aesni c sfx))
  | .small => scrubAll v 0 1816 (withStackScratch 1800 .rcx (Stream.X86_64.initS e c sfx))
  | .full => scrubAll v 0 2328 (withStackScratch 2312 .rcx (Stream.X86_64.init e c sfx))

/-- `Spec.Cmac.aesFinishApi`'s function as emitted. -/
def finish (v : VecLevel) (sp : Space) (c : Ctr32) (sfx : String) : Prog isa :=
  match sp with
  | .free => scrubAll v 0 40 (withStackScratch 24 .r8 (Stream.X86_64.finishF c sfx))
  | .small => scrubAll v 0 1816 (withStackScratch 1800 .r8 (Stream.X86_64.finishS c sfx))
  | .full => scrubAll v 0 2328 (withStackScratch 2312 .r8 (Stream.X86_64.finish c sfx))

/-- `Spec.Cmac.aesAbsorbApi`'s function as emitted. -/
def absorb (v : VecLevel) (sp : Space) (u : Impl.CmacAes.X86_64.Update) : Prog isa :=
  match sp with
  | .free => scrubAll v 0 72 (withStackScratch 56 .r9 (Stream.X86_64.absorbF u))
  | .small => scrubAll v 0 1816 (withStackScratch 1800 .r9 (Stream.X86_64.absorbS u))
  | .full => scrubAll v 0 2328 (withStackScratch 2312 .r9 (Stream.X86_64.absorb u))

end VG.Impl.CmacAes.Stream.X86_64.Fn
