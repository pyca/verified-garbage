module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesOfb.X86.Verified
public import VerifiedGarbage.Proof.AesOfb.X86.Final
public import VerifiedGarbage.Spec.Ofb.Contract
public import VerifiedGarbage.Spec.Ofb.Final
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.AesOfb.X86.Final
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesOfb.X86.Verified
meta import VerifiedGarbage.Proof.AesOfb.X86.Final
meta import VerifiedGarbage.Spec.Ofb.Contract
meta import VerifiedGarbage.Spec.Ofb.Final
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.AesOfb.X86.Final

/-!
# AES-OFB on x86 (32-bit), without secret residue

`vg_aes_ofb` and `vg_aes_ofb_final` read the memory on return only within
the data and the IV (`ofbOut`, `ofbFinalOut`), as on PPC64LE
(`Proof/Aes/PPC64LE/Scrub.lean`): what the scrub of their frames and calls
needs (`X86.Scrub.PostOut`).

Each as emitted (`Impl.AesOfb.X86.Fn`) zeroes the stack of its contract
below `esp` and clears the registers, and returns without secret residue
(`X86.Scrub.verifiedScrubbedF`: `ofb_scrubbed`, `ofbFinal_scrubbed`). What that needs of the code (`scrubFSide`) holds whatever the
implementation of the block function (`crypt_scrub`, `final_scrub`): from
OFB's code with a stub block function, whose code is `.block []`, which the
kernel evaluates once (`crypt_side`, `final_side`), the implementation's own
facts (`BlocksImpl.encScrub`, its stack), and `Fill`, which `fill_calls`
proves by walking only OFB's code. `vg_aes_ofb_final` calls `vg_aes_ofb`'s
code as `vg_aes_ofb_core` (`Impl.AesOfb.X86.cryptFinal`), unscrubbed.
-/

@[expose] public section

namespace VG.Proof.AesOfb.X86.Scrub

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

theorem ofbOut (stack : Nat) :
    PostOut (Spec.Ofb.aesContract abi stack) (Spec.Ofb.aesSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Ofb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) :
    PostOut (Spec.Ofb.aesFinalContract abi stack) (Spec.Ofb.aesFinalSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Ofb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## What the scrub needs of the code -/

open Impl.StackScratch.X86 (withStackScratchWiped)
open Proof.Aes.X86 (BlocksImpl)

/-- A block function with no code. -/
def stubBlocks : Impl.Aes.X86.Blocks := ⟨"", .block []⟩

-- OFB's own code, with the stub, as literals for the kernel's evaluation.
materialize_code cryptStub := Impl.AesOfb.X86.crypt stubBlocks
materialize_code finalStub := withStackScratchWiped 48 6 4 (Impl.AesOfb.X86.cryptFinal stubBlocks "")

theorem crypt_side : scrubFSide (Impl.AesOfb.X86.crypt stubBlocks) [] 24 = true := by
  lit_decide

theorem final_side : scrubFSide (withStackScratchWiped 48 6 4 (Impl.AesOfb.X86.cryptFinal stubBlocks "")) [] 100 = true := by
  lit_decide

theorem crypt_fill (b : Impl.Aes.X86.Blocks) (hb : calleeSide b.code 0 = true) :
    Fill 0 (Impl.AesOfb.X86.crypt stubBlocks) (Impl.AesOfb.X86.crypt b) := by
  fill_calls

theorem final_fill (b : Impl.Aes.X86.Blocks) (sfx : String) (hb : calleeSide b.code 0 = true) :
    Fill 0 (withStackScratchWiped 48 6 4 (Impl.AesOfb.X86.cryptFinal stubBlocks ""))
      (withStackScratchWiped 48 6 4 (Impl.AesOfb.X86.cryptFinal b sfx)) := by
  fill_calls

/-- `scrubFSide` of `vg_aes_ofb`, whatever the implementation. -/
theorem crypt_scrub (v : BlocksImpl) : scrubFSide (Impl.AesOfb.X86.crypt v.enc) [] 24 = true :=
  scrubFSide_of_fill (crypt_fill _ (calleeSide_of_eq v.encStack v.encScrub)) crypt_side

/-- `scrubFSide` of `vg_aes_ofb_final`, whatever the implementation. -/
theorem final_scrub (v : BlocksImpl) :
    scrubFSide (withStackScratchWiped 48 6 4 (Impl.AesOfb.X86.cryptFinal v.enc v.suffix)) [] 100 = true :=
  scrubFSide_of_fill (final_fill _ _ (calleeSide_of_eq v.encStack v.encScrub)) final_side

/-! ## The functions as emitted -/

/-- `vg_aes_ofb` over `v` as emitted (`Impl.AesOfb.X86.Fn.crypt`)
meets its contract in constant time and returns without secret residue. -/
theorem ofb_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesOfb.X86.Fn.crypt v.enc)
      (Spec.Ofb.aesContract X86.abi 24) 0 :=
  verifiedScrubbedF (api := Spec.Ofb.aesApi) {
      suffix := v.suffix
      code := Impl.AesOfb.X86.crypt v.enc
      verified := Proof.AesOfb.keyed (crypt_verified v)
      spSafe := crypt_spSafe v }
    (ofbOut _) (W := 24) (hs := crypt_scrub v)

/-- `vg_aes_ofb_final` over `v` as emitted (`Impl.AesOfb.X86.Fn.cryptFinal`)
meets its contract in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesOfb.X86.Fn.cryptFinal v.enc v.suffix)
      (Spec.Ofb.aesFinalContract X86.abi 100) 0 :=
  verifiedScrubbedF (api := Spec.Ofb.aesFinalApi) {
      suffix := v.suffix
      code := withStackScratchWiped 48 6 4 (Impl.AesOfb.X86.cryptFinal v.enc v.suffix)
      verified := Proof.AesOfb.final_keyed (cryptFinal_framed v)
      spSafe := cryptFinal_framed_spSafe v }
    (ofbFinalOut _) (W := 100) (hs := final_scrub v)

/-- The code as emitted, `c` and then its cleanup, writes `esp` only in its
frames and calls, as `c` does. -/
theorem scrubF_spSafe {rb W : Nat} {c : Prog X86.isa} (h : c.all (fun i => !X86.isa.writesSp i) = true) :
    (Impl.Scrub.X86.scrubF rb W c).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [Impl.Scrub.X86.scrubF, Impl.Scrub.X86.wipeBelow, Code.all, h, zeroRegs_all, tail_all,
    Bool.true_and, Bool.and_true]
  exact wipe_all _

/-- `Impl.AesOfb.X86.Fn.crypt` writes `esp` only in its frames and calls. -/
theorem ofb_fnSpSafe (v : BlocksImpl) :
    (Impl.AesOfb.X86.Fn.crypt v.enc).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (crypt_spSafe v)

/-- `Impl.AesOfb.X86.Fn.cryptFinal` writes `esp` only in its frames and calls. -/
theorem ofbFinal_fnSpSafe (v : BlocksImpl) :
    (Impl.AesOfb.X86.Fn.cryptFinal v.enc v.suffix).all (fun i => !X86.isa.writesSp i) = true :=
  scrubF_spSafe (cryptFinal_framed_spSafe v)

end VG.Proof.AesOfb.X86.Scrub
