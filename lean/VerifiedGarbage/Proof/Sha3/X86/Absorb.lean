module

public import VerifiedGarbage.Proof.Sha3.X86.Instances
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha3.PostOut
public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Impl.Sha3.X86.Instances
import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha3.X86.Instances
meta import VerifiedGarbage.Proof.Framework.X86.StackScratch
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha3.PostOut
meta import VerifiedGarbage.Spec.Sha3.Instances
meta import VerifiedGarbage.Impl.Sha3.X86.Instances
meta import VerifiedGarbage.Proof.Sha3.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-3's absorb on x86 (32-bit)

`vg_<f>_update` (`Spec.Sha3.updateApi`) is `update` with its working space
`scratch` in a frame of 664 bytes on the stack, passed as its stack argument
(`Impl.Sha3.X86.Instances.absorb`, `withStackScratch`): proven from
`update`'s proof (`X86.Verified.stackScratch`, the contract with `scratch`
being `updateScratchContract` by `rfl`), and returning without secret residue
(`update_sha3_224_scrubbed` and the others, of the code with its cleanup,
`Impl.Sha3.X86.Fn.update`, which zeroes the 704 bytes of stack below `esp`
that it and `update` use, and clears the registers a callee may change), so
that nothing is left in the caller's memory: `X86.Scrub.verifiedScrubbedAll`.
What the cleanup needs of the code (its stack use within the 704 bytes, no
indirect call, no MMX instruction) is one Boolean, `X86.Scrub.scrubFSide`,
which the kernel evaluates once (`lit_decide`).
-/

@[expose] public section

namespace VG.Proof.Sha3.X86.Absorb

open VG.X86 VG.X86.Scrub

-- The sponge's absorbing, which `update` calls, as a literal: the scrub's
-- side condition (`scrubFSide`) and the absence of writes of `esp` are
-- checked by evaluation (`lit_decide`).
materialize_code streamAbsorb := Impl.Sha3.X86.Stream.absorb

/-- Memory holding `absorb`'s arguments `0x1000, 0, 0x2000, 0` at `0x4004`. -/
def absorbSatMem : Mem := fun a => if a = 0x4005 then 0x10 else if a = 0x400D then 0x20 else 0

/-- A state satisfying `updateContract`'s precondition (with no data), with
704 bytes of stack. -/
def absorbSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := absorbSatMem
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x4004, 16⟩]

theorem absorbOut (rate stack : Nat) :
    PostOut (Spec.Sha3.updateContract abi rate stack) (Spec.Sha3.updateSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha3.PostOut.updatePost_out rate _)

theorem absorbSat_sha3_224 : ∃ s, (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_224.rate 704).pre s := by
  implies_sat [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Spec.Sha3.hashSha3_224]
    [absorbSat, absorbSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_sha3_224 : Verified X86.target (Impl.Sha3.X86.Instances.absorb Spec.Sha3.hashSha3_224.rate)
    (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_224.rate 704) :=
  X86.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.hashSha3_224.rate X86.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.hashSha3_224.rate X86.abi.ptrBits) (wa := true) (stack := 40)
    (bytes := 664) Proof.Sha3.X86.Instances.update_sha3_224 (by decide) (by lit_decide) (by lit_decide)
    (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_sha3_224

/-- `vg_sha3_224_update` as emitted (`Impl.Sha3.X86.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_sha3_224_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.X86.Fn.update Spec.Sha3.hashSha3_224.rate)
      (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_224.rate 704) 32 :=
  verifiedScrubbedAll (api := Spec.Sha3.updateSha3_224Api)
    { code := Impl.Sha3.X86.Instances.absorb Spec.Sha3.hashSha3_224.rate
      verified := absorb_sha3_224 }
    (absorbOut _ _)

theorem absorbSat_sha3_256 : ∃ s, (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_256.rate 704).pre s := by
  implies_sat [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Spec.Sha3.hashSha3_256]
    [absorbSat, absorbSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_sha3_256 : Verified X86.target (Impl.Sha3.X86.Instances.absorb Spec.Sha3.hashSha3_256.rate)
    (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_256.rate 704) :=
  X86.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.hashSha3_256.rate X86.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.hashSha3_256.rate X86.abi.ptrBits) (wa := true) (stack := 40)
    (bytes := 664) Proof.Sha3.X86.Instances.update_sha3_256 (by decide) (by lit_decide) (by lit_decide)
    (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_sha3_256

/-- `vg_sha3_256_update` as emitted (`Impl.Sha3.X86.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_sha3_256_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.X86.Fn.update Spec.Sha3.hashSha3_256.rate)
      (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_256.rate 704) 32 :=
  verifiedScrubbedAll (api := Spec.Sha3.updateSha3_256Api)
    { code := Impl.Sha3.X86.Instances.absorb Spec.Sha3.hashSha3_256.rate
      verified := absorb_sha3_256 }
    (absorbOut _ _)

theorem absorbSat_sha3_384 : ∃ s, (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_384.rate 704).pre s := by
  implies_sat [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Spec.Sha3.hashSha3_384]
    [absorbSat, absorbSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_sha3_384 : Verified X86.target (Impl.Sha3.X86.Instances.absorb Spec.Sha3.hashSha3_384.rate)
    (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_384.rate 704) :=
  X86.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.hashSha3_384.rate X86.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.hashSha3_384.rate X86.abi.ptrBits) (wa := true) (stack := 40)
    (bytes := 664) Proof.Sha3.X86.Instances.update_sha3_384 (by decide) (by lit_decide) (by lit_decide)
    (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_sha3_384

/-- `vg_sha3_384_update` as emitted (`Impl.Sha3.X86.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_sha3_384_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.X86.Fn.update Spec.Sha3.hashSha3_384.rate)
      (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_384.rate 704) 32 :=
  verifiedScrubbedAll (api := Spec.Sha3.updateSha3_384Api)
    { code := Impl.Sha3.X86.Instances.absorb Spec.Sha3.hashSha3_384.rate
      verified := absorb_sha3_384 }
    (absorbOut _ _)

theorem absorbSat_sha3_512 : ∃ s, (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_512.rate 704).pre s := by
  implies_sat [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Spec.Sha3.hashSha3_512]
    [absorbSat, absorbSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_sha3_512 : Verified X86.target (Impl.Sha3.X86.Instances.absorb Spec.Sha3.hashSha3_512.rate)
    (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_512.rate 704) :=
  X86.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.hashSha3_512.rate X86.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.hashSha3_512.rate X86.abi.ptrBits) (wa := true) (stack := 40)
    (bytes := 664) Proof.Sha3.X86.Instances.update_sha3_512 (by decide) (by lit_decide) (by lit_decide)
    (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_sha3_512

/-- `vg_sha3_512_update` as emitted (`Impl.Sha3.X86.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_sha3_512_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.X86.Fn.update Spec.Sha3.hashSha3_512.rate)
      (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_512.rate 704) 32 :=
  verifiedScrubbedAll (api := Spec.Sha3.updateSha3_512Api)
    { code := Impl.Sha3.X86.Instances.absorb Spec.Sha3.hashSha3_512.rate
      verified := absorb_sha3_512 }
    (absorbOut _ _)

theorem absorbSat_shake128 : ∃ s, (Spec.Sha3.updateContract X86.abi Spec.Sha3.xofShake128.rate 704).pre s := by
  implies_sat [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Spec.Sha3.xofShake128]
    [absorbSat, absorbSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_shake128 : Verified X86.target (Impl.Sha3.X86.Instances.absorb Spec.Sha3.xofShake128.rate)
    (Spec.Sha3.updateContract X86.abi Spec.Sha3.xofShake128.rate 704) :=
  X86.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.xofShake128.rate X86.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.xofShake128.rate X86.abi.ptrBits) (wa := true) (stack := 40)
    (bytes := 664) Proof.Sha3.X86.Instances.update_shake128 (by decide) (by lit_decide) (by lit_decide)
    (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_shake128

/-- `vg_shake128_update` as emitted (`Impl.Sha3.X86.Fn.update`) meets its contract in
constant time and returns without secret residue. -/
theorem update_shake128_scrubbed :
    VerifiedScrubbed target (Impl.Sha3.X86.Fn.update Spec.Sha3.xofShake128.rate)
      (Spec.Sha3.updateContract X86.abi Spec.Sha3.xofShake128.rate 704) 32 :=
  verifiedScrubbedAll (api := Spec.Sha3.updateShake128Api)
    { code := Impl.Sha3.X86.Instances.absorb Spec.Sha3.xofShake128.rate
      verified := absorb_shake128 }
    (absorbOut _ _)

end VG.Proof.Sha3.X86.Absorb
