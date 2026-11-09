module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.Callee
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.Contract
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.CT
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: the instance it calls

Untrusted: everything here is checked by Lean. For the code of
`vg_chacha20_poly1305_seal_gather` that calls an instance of
`vg_chacha20_poly1305_seal` (`sealGatherWhole`): that instance (`sealFn`),
how many bytes at a time the code copies (`width`), and that only its
frames' pushes and pops write `rsp` (`sealGather_spSafe`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealGather

open VG.Proof.ChaCha20.X86_64 VG.Impl.StackScratch.X86_64 in
/-- The instance of `vg_chacha20_poly1305_seal` calling the implementation
`v` of `vg_chacha20_xor`, with its working space in a frame of its own. -/
def sealFn (v : XorImpl) : SealFn where
  name := Spec.ChaCha20Poly1305.sealApi.name ++ v.suffix
  code := Impl.ChaCha20Poly1305.X86_64.Shared.sealCode v.callee v.poly
  verified := Shared.seal_verified v
  sp := SpSafe.of_all (Shared.seal_sp v)
  depth := Shared.seal_depth v

open VG.Proof.ChaCha20.X86_64 in
/-- How many bytes at a time the instance for `v` copies: as many as the
CPUs of the instance of `vg_chacha20_poly1305_seal` it calls can. -/
def width (v : XorImpl) : Width := .ofBlocks v.poly

open VG.Proof.ChaCha20.X86_64 in
/-- No instruction of the code, or of the instance it calls, writes `rsp`
but its frames' pushes and pops. -/
theorem sealGather_spSafe (v : XorImpl) :
    (sealGatherWhole (width v) (sealFn v).name (sealFn v).code).all (fun i => !X86_64.isa.writesSp i) = true := by
  have hc : (sealFn v).code.all (fun i => !X86_64.isa.writesSp i) = true :=
    Shared.seal_sp v
  simp only [sealGatherWhole, Code.all, hc, Bool.and_true, Bool.true_and]
  cases width v <;> decide +kernel

end VG.Proof.ChaCha20Poly1305.X86_64.Gather.Whole
