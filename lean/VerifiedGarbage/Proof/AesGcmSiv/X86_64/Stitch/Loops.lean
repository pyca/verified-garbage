module

public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Stitch
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Spec
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.CryptCT
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# AES-GCM-SIV's loops on the groups: what `open` and `seal` need of them

Untrusted: everything here is checked by Lean. `open` and `seal`
(`Impl.AesGcmSiv.X86_64Stitch`) are proven for any loops
(`Impl.AesGcmSiv.X86_64Stitch.Loops`) that meet their contracts: the
interleaved loop `dec` (`SPre` to `DPost`), POLYVAL's `hash` (`HPre` to
`HPost`) and counter mode's `ctr` (`SPre` to `CPost`), each on a multiple of
16 blocks, and that pass the taint analysis from the registers holding their
public arguments (`LoopsOk`); and that load no MXCSR, leave `rsp` alone and
use no stack (`LoopsCode`), which the artifacts' frame needs.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.AesGcmSiv.X86_64Stitch (Loops)

/-- What `open`'s and `seal`'s proofs need of their loops. -/
structure LoopsOk (lp : Loops) : Prop where
  dec : ∀ {s₀ : State}, SPre s₀ → nb s₀ % 16 = 0 → WP isa lp.dec s₀ (DPost s₀)
  hash : ∀ {s₀ : State}, HPre s₀ → WP isa lp.hash s₀ (HPost s₀)
  ctr : ∀ {s₀ : State}, SPre s₀ → nb s₀ % 16 = 0 → WP isa lp.ctr s₀ (CPost s₀)
  decT : ∃ hc, (taint.check (sivT [.rdi, .rsi, .rdx, .rcx, .r8, .r11, .r12, .r9]) lp.dec hc).isSome = true
  hashT : ∃ hc, (taint.check (sivT [.rcx, .r8, .r11, .rdx, .r9]) lp.hash hc).isSome = true
  ctrT : ∃ hc, (taint.check (sivT [.rdi, .rsi, .rdx, .rcx, .r8, .r11, .r12, .r9]) lp.ctr hc).isSome = true

/-- What the artifacts' frame needs of the loops' code. -/
structure LoopsCode (lp : Loops) : Prop where
  decMx : lp.dec.allInstrs (fun i => !loadsMxcsr i) = true
  hashMx : lp.hash.allInstrs (fun i => !loadsMxcsr i) = true
  ctrMx : lp.ctr.allInstrs (fun i => !loadsMxcsr i) = true
  decSp : lp.dec.all (fun i => !X86_64.isa.writesSp i) = true
  hashSp : lp.hash.all (fun i => !X86_64.isa.writesSp i) = true
  ctrSp : lp.ctr.all (fun i => !X86_64.isa.writesSp i) = true
  decDepth : lp.dec.x86_64Depth = 0
  hashDepth : lp.hash.x86_64Depth = 0
  ctrDepth : lp.ctr.x86_64Depth = 0

end VG.Proof.AesGcmSiv.X86_64.Stitch
