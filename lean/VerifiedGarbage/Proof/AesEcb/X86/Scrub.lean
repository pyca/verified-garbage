module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesEcb.X86
public import VerifiedGarbage.Spec.AesEcb.Contract
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.AesEcb.X86
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesEcb.X86
meta import VerifiedGarbage.Spec.AesEcb.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.AesEcb.X86

/-!
# AES-ECB on x86 (32-bit), without secret residue

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` read the memory on return only
within the data and `scratch` (`encryptOut`, `decryptOut`), as on PPC64LE
(`Proof/Aes/PPC64LE/Scrub.lean`): what the scrub of their frames and calls
needs (`X86.Scrub.PostOut`).

Which code is emitted for an implementation `v` of the block functions
(`Impl.AesEcb.X86.Fn.crypt`), with its stack (`ecbStack`): where `v`'s
block function writes nothing in `scratch` and calls nothing (AES-NI's),
that function's code, then the clearing of the registers
(`X86.Scrub.verifiedScrubbed`), with none; otherwise the call of it, then
of `vg_zeroize` on the bytes of `scratch` it writes
(`Impl.AesEcb.X86.wiped`), which also zeroes its 32 bytes of stack
(`X86.Scrub.verifiedScrubbedF`). `encrypt_scrubbed` and `decrypt_scrubbed`
prove each by cases. What that needs of the code (`scrubFSide`) holds
whatever the implementation (`wiped_scrub`): from the code with a stub,
whose block function's code and the instructions that pass `vg_zeroize`
its length, `zeroArgs`, are `.block []` (`wipedStub`), which the kernel
evaluates once, the implementation's own facts (`BlocksImpl.encScrub`, its
stack), and `Fill`, which `fill_calls` proves by walking only the call's
code.
-/

@[expose] public section

namespace VG.Proof.AesEcb.X86.Scrub

open VG.X86 VG.X86.Scrub
open Proof.Aes.X86 (BlocksImpl)
open Impl.CallWipe.X86 (frameSize copyArgs zeroArgs restoreRet)

/-! ## Postconditions -/

/-- The postcondition of `vg_aes_ecb_encrypt` reads the memory on return only
within the buffers. -/
theorem encryptOut (stack : Nat) :
    PostOut (Spec.AesEcb.encryptContract abi stack) (Spec.Aes.blocksSig.retBits 32) := by
  rw [Proof.AesEcb.encrypt_eq]
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · show Spec.Aes.statesAt m₂ c (d.setWidth abi.ptrBits).toNat = _
      have hd := agree_of hb.2.1
      rw [statesAt_congr fun i hi => hd i (by have := n_le (pb := abi.ptrBits) d; omega_using [hi, this])]
      exact h1 key hk
    · rw [← hb.2.2 z hz]
      exact h2 z hz

/-- The postcondition of `vg_aes_ecb_decrypt` reads the memory on return only
within the buffers. -/
theorem decryptOut (stack : Nat) :
    PostOut (Spec.AesEcb.decryptContract abi stack) (Spec.Aes.blocksSig.retBits 32) := by
  rw [Proof.AesEcb.decrypt_eq]
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · show Spec.Aes.statesAt m₂ c (d.setWidth abi.ptrBits).toNat = _
      have hd := agree_of hb.2.1
      rw [statesAt_congr fun i hi => hd i (by have := n_le (pb := abi.ptrBits) d; omega_using [hi, this])]
      exact h1 key hk
    · rw [← hb.2.2 z hz]
      exact h2 z hz

/-! ## What the scrub needs of the code -/

/-- `Impl.CallWipe.X86.callWipe 5 4 n` with a function of no code and no
name, and `.block []` where it passes `vg_zeroize` its length `n`. -/
def wipedStub : Prog isa :=
  .frame (.alloc (frameSize 5))
    (.seq (.block (copyArgs (frameSize 5) 5))
      (.seq (.call "" (.block []))
        (.seq (.block [])
          (.seq (.call "vg_zeroize" Impl.Zeroize.X86.zeroize) (.block (restoreRet 5))))))
    (.free (frameSize 5))

materialize_code wipedStubLit := wipedStub

theorem wiped_side : scrubFSide wipedStub [] 32 = true := by
  lit_decide

/-- The instructions that pass `vg_zeroize` its length, whatever it is. -/
theorem zeroArgs_side (n : Nat) : calleeSide (.block (zeroArgs 5 4 n)) 0 = true := rfl

theorem wiped_fill (b : Impl.Aes.X86.Blocks) (n : Nat) (hb : calleeSide b.code 0 = true)
    (hz : calleeSide (.block (zeroArgs 5 4 n)) 0 = true) :
    Fill 0 wipedStub (Impl.AesEcb.X86.wiped b n) := by
  fill_calls

/-- `scrubFSide` of the call of a block function `b`, then of `vg_zeroize`,
whatever `b`. -/
theorem wiped_scrub (b : Impl.Aes.X86.Blocks) (n : Nat) (hs : stackUse b.code = 0) (hc : calleeOk b.code = true) :
    scrubFSide (Impl.AesEcb.X86.wiped b n) [] 32 = true :=
  scrubFSide_of_fill (wiped_fill b n (calleeSide_of_eq hs hc) (zeroArgs_side n)) wiped_side

/-- `scrubSide` of a block function's code that calls nothing. -/
theorem free_scrub (b : Impl.Aes.X86.Blocks) (hn : b.code.noCalls = true) (hc : calleeOk b.code = true) :
    scrubSide b.code = true := by
  simp only [scrubSide, hn, ((calleeOk_iff _).mp hc).2, Bool.and_self]

/-! ## The functions as emitted -/

/-- Whether `vg_aes_ecb_encrypt` or `vg_aes_ecb_decrypt` over the block
function `b`, which writes the first `n` bytes of `scratch`, is `b`'s own
code (`Impl.AesEcb.X86.Fn.crypt`): where `b` writes nothing in `scratch`
and calls nothing. -/
def ecbFree (b : Impl.Aes.X86.Blocks) (n : Nat) : Bool := n == 0 && b.code.noCalls

/-- The stack of `vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` over `b`:
none for `b`'s own code, 32 bytes for the call wiping `scratch`. -/
def ecbStack (b : Impl.Aes.X86.Blocks) (n : Nat) : Nat := if ecbFree b n then 0 else 32

theorem ecbFree_iff {b : Impl.Aes.X86.Blocks} {n : Nat} : ecbFree b n = true ↔ n = 0 ∧ b.code.noCalls = true := by
  simp only [ecbFree, Bool.and_eq_true, beq_iff_eq]

/-- `vg_aes_ecb_encrypt` over `v` as emitted (`Impl.AesEcb.X86.Fn.crypt`)
meets its contract in constant time and returns without secret residue. -/
theorem encrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesEcb.X86.Fn.crypt (ecbFree v.enc v.encWritten) v.enc v.encWritten)
      (Spec.AesEcb.encryptContract X86.abi (ecbStack v.enc v.encWritten)) 0 := by
  unfold Impl.AesEcb.X86.Fn.crypt ecbStack
  by_cases hf : ecbFree v.enc v.encWritten = true
  · have h := ecbFree_iff.mp hf
    rw [ite_eq_left hf, ite_eq_left hf]
    exact verifiedScrubbed (api := Spec.AesEcb.encryptApi) {
      suffix := v.suffix
      code := v.enc.code
      verified := encrypt_free v h.1
      spSafe := v.encSpSafe } (free_scrub _ h.2 v.encScrub)
  · rw [ite_eq_right hf, ite_eq_right hf]
    exact verifiedScrubbedF (api := Spec.AesEcb.encryptApi) {
        suffix := v.suffix
        code := Impl.AesEcb.X86.wiped v.enc v.encWritten
        stack := 32
        verified := encrypt_verified v
        spSafe := encrypt_spSafe v }
      (encryptOut _) (W := 32) (hs := wiped_scrub _ _ v.encStack v.encScrub)

/-- `vg_aes_ecb_decrypt` over `v` as emitted (`Impl.AesEcb.X86.Fn.crypt`)
meets its contract in constant time and returns without secret residue. -/
theorem decrypt_scrubbed (v : BlocksImpl) :
    VerifiedScrubbed X86.target (Impl.AesEcb.X86.Fn.crypt (ecbFree v.dec v.decWritten) v.dec v.decWritten)
      (Spec.AesEcb.decryptContract X86.abi (ecbStack v.dec v.decWritten)) 0 := by
  unfold Impl.AesEcb.X86.Fn.crypt ecbStack
  by_cases hf : ecbFree v.dec v.decWritten = true
  · have h := ecbFree_iff.mp hf
    rw [ite_eq_left hf, ite_eq_left hf]
    exact verifiedScrubbed (api := Spec.AesEcb.decryptApi) {
      suffix := v.suffix
      code := v.dec.code
      verified := decrypt_free v h.1
      spSafe := v.decSpSafe } (free_scrub _ h.2 v.decScrub)
  · rw [ite_eq_right hf, ite_eq_right hf]
    exact verifiedScrubbedF (api := Spec.AesEcb.decryptApi) {
        suffix := v.suffix
        code := Impl.AesEcb.X86.wiped v.dec v.decWritten
        stack := 32
        verified := decrypt_verified v
        spSafe := decrypt_spSafe v }
      (decryptOut _) (W := 32) (hs := wiped_scrub _ _ v.decStack v.decScrub)

/-- `Impl.AesEcb.X86.Fn.crypt` writes `esp` only in its frames and calls, if
the block function and the call wiping `scratch` do. -/
theorem crypt_fnSpSafe {free : Bool} {b : Impl.Aes.X86.Blocks} {n : Nat} (hb : b.code.all (fun i => !X86.isa.writesSp i) = true)
    (hw : (Impl.AesEcb.X86.wiped b n).all (fun i => !X86.isa.writesSp i) = true) :
    (Impl.AesEcb.X86.Fn.crypt free b n).all (fun i => !X86.isa.writesSp i) = true := by
  unfold Impl.AesEcb.X86.Fn.crypt
  split
  · exact scrub_spSafe hb
  · exact scrubF_spSafe hw

/-- `vg_aes_ecb_encrypt` over `v` as emitted writes `esp` only in its frames and calls. -/
theorem encrypt_fnSpSafe (v : BlocksImpl) :
    (Impl.AesEcb.X86.Fn.crypt (ecbFree v.enc v.encWritten) v.enc v.encWritten).all
      (fun i => !X86.isa.writesSp i) = true :=
  crypt_fnSpSafe v.encSpSafe (encrypt_spSafe v)

/-- `vg_aes_ecb_decrypt` over `v` as emitted writes `esp` only in its frames and calls. -/
theorem decrypt_fnSpSafe (v : BlocksImpl) :
    (Impl.AesEcb.X86.Fn.crypt (ecbFree v.dec v.decWritten) v.dec v.decWritten).all
      (fun i => !X86.isa.writesSp i) = true :=
  crypt_fnSpSafe v.decSpSafe (decrypt_spSafe v)

end VG.Proof.AesEcb.X86.Scrub
