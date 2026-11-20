module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesCtr.X86.Ctr32
public import VerifiedGarbage.Proof.AesCtr.X86.Final
public import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.Spec.Ctr.Final
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.AesCtr.X86.Final
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesCtr.X86.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.X86.Final
meta import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Spec.Ctr.Final
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.AesCtr.X86.Final

/-!
# AES-CTR on x86 (32-bit), without secret residue

`vg_aes_ctr` and `vg_aes_ctr_final` read the memory on return only within
the data and the counter block (`ctrOut`, `ctrFinalOut`), as on PPC64LE
(`Proof/Aes/PPC64LE/Scrub.lean`): what the scrub of their frames and calls
needs (`X86.Scrub.PostOut`).

Each as emitted (`Impl.AesCtr.X86.Fn`) zeroes the stack of its contract
below `esp` and clears the registers, and returns without secret residue
(`X86.Scrub.verifiedScrubbedF`: `ctr_scrubbed`, `ctrFinal_scrubbed`). What that needs of the code (`scrubFSide`) holds whatever the
implementation of AES (`crypt32_scrub`, `final_scrub`): from CTR's code with
a stub, whose code is `.block []`, which the kernel evaluates once
(`crypt32_side`, `final_side`), the implementation's own facts
(`Ctr32Impl.scrub`, `BlocksImpl.encScrub`, their stacks), and `Fill`, which
`fill_calls` proves by walking only CTR's code.
-/

@[expose] public section

namespace VG.Proof.AesCtr.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Aes.ScrubLocal

/-- A count of elements of `k` bytes, which the contract reads as its low 32
bits, spans at most the bytes of the buffer `Sig.bufs` gives it. -/
private theorem len_le (x : BitVec 64) (k : Nat) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k := by
  show (x.setWidth 32).toNat * k ≤ x.toNat * k
  rw [BitVec.toNat_setWidth]
  exact Nat.mul_le_mul_right _ (Nat.mod_le _ _)

private theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size := by
  have := len_le x 1
  rwa [Nat.mul_one] at this

theorem ctrOut (stack : Nat) :
    PostOut (Spec.Ctr.aesContract abi stack) (Spec.Ctr.aesSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ctr, dt, ln, sc], _ =>
      simp only [Spec.Ctr.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ctr 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrFinalOut (stack : Nat) :
    PostOut (Spec.Ctr.aesFinalContract abi stack) (Spec.Ctr.aesFinalSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ctr, dt, ln, sc], _ =>
      simp only [Spec.Ctr.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ctr 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## What the scrub needs of the code -/

open Impl.StackScratch.X86 (withStackScratchWiped)
open Proof.Aes.X86 (BlocksImpl Ctr32Impl)

/-- AES in counter mode with no code. -/
def stubCtr : Impl.Aes.X86.Ctr32 := ⟨"", .block []⟩

/-- A block function with no code. -/
def stubBlocks : Impl.Aes.X86.Blocks := ⟨"", .block []⟩

-- CTR's own code, with the stubs, as literals for the kernel's evaluation.
materialize_code crypt32Stub := Impl.AesCtr.X86.crypt32 stubCtr
materialize_code finalStub := withStackScratchWiped 64 6 8 (Impl.AesCtr.X86.cryptFinal stubBlocks "")

theorem crypt32_side : scrubFSide (Impl.AesCtr.X86.crypt32 stubCtr) [] 32 = true := by
  lit_decide

theorem final_side :
    scrubFSide (withStackScratchWiped 64 6 8 (Impl.AesCtr.X86.cryptFinal stubBlocks "")) [] 116 = true := by
  lit_decide

theorem crypt32_fill (c : Impl.Aes.X86.Ctr32) (hc : calleeSide c.code 0 = true) :
    Fill 0 (Impl.AesCtr.X86.crypt32 stubCtr) (Impl.AesCtr.X86.crypt32 c) := by
  fill_calls

theorem final_fill (b : Impl.Aes.X86.Blocks) (sfx : String) (hb : calleeSide b.code 0 = true) :
    Fill 0 (withStackScratchWiped 64 6 8 (Impl.AesCtr.X86.cryptFinal stubBlocks ""))
      (withStackScratchWiped 64 6 8 (Impl.AesCtr.X86.cryptFinal b sfx)) := by
  fill_calls

/-- `scrubFSide` of `vg_aes_ctr`, whatever the implementation. -/
theorem crypt32_scrub (v : Ctr32Impl) : scrubFSide (Impl.AesCtr.X86.crypt32 v.callee) [] 32 = true :=
  scrubFSide_of_fill (crypt32_fill _ (calleeSide_of_eq v.stack v.scrub)) crypt32_side

/-- `scrubFSide` of `vg_aes_ctr_final`, whatever the implementation. -/
theorem final_scrub (v : BlocksImpl) :
    scrubFSide (withStackScratchWiped 64 6 8 (Impl.AesCtr.X86.cryptFinal v.enc v.suffix)) [] 116 = true :=
  scrubFSide_of_fill (final_fill _ _ (calleeSide_of_eq v.encStack v.encScrub)) final_side

/-! ## The functions as emitted -/

/-- `vg_aes_ctr` over `v` as emitted (`Impl.AesCtr.X86.Fn.crypt32`)
meets its contract in constant time and returns without secret residue. -/
theorem ctr_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed X86.target (Impl.AesCtr.X86.Fn.crypt32 v.callee)
      (Spec.Ctr.aesContract X86.abi 32) 0 :=
  verifiedScrubbedF (api := Spec.Ctr.aesApi) {
      suffix := v.suffix
      code := Impl.AesCtr.X86.crypt32 v.callee
      verified := Proof.AesCtr.keyed (Ctr32.crypt32_verified v)
      spSafe := Ctr32.crypt32_spSafe v }
    (ctrOut _) (W := 32) (hs := crypt32_scrub v)

/-- `vg_aes_ctr_final` over `v` as emitted (`Impl.AesCtr.X86.Fn.cryptFinal`)
meets its contract in constant time and returns without secret residue. -/
theorem ctrFinal_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesCtr.X86.Fn.cryptFinal v.enc v.suffix)
      (Spec.Ctr.aesFinalContract X86.abi 116) 0 :=
  verifiedScrubbedF (api := Spec.Ctr.aesFinalApi) {
      suffix := v.suffix
      code := withStackScratchWiped 64 6 8 (Impl.AesCtr.X86.cryptFinal v.enc v.suffix)
      verified := Proof.AesCtr.final_keyed (cryptFinal_framed v)
      spSafe := cryptFinal_framed_spSafe v }
    (ctrFinalOut _) (W := 116) (hs := final_scrub v)

/-- `Impl.AesCtr.X86.Fn.crypt32` writes `esp` only in its frames and calls. -/
theorem ctr_fnSpSafe (v : Ctr32Impl) :
    (Impl.AesCtr.X86.Fn.crypt32 v.callee).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (Ctr32.crypt32_spSafe v)

/-- `Impl.AesCtr.X86.Fn.cryptFinal` writes `esp` only in its frames and calls. -/
theorem ctrFinal_fnSpSafe (v : BlocksImpl) :
    (Impl.AesCtr.X86.Fn.cryptFinal v.enc v.suffix).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (cryptFinal_framed_spSafe v)

end VG.Proof.AesCtr.X86.Scrub
