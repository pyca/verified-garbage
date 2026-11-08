module

public import VerifiedGarbage.Proof.AesCbc.Wipe
public import VerifiedGarbage.Proof.AesCbc.X86_64.Caller
public import VerifiedGarbage.Proof.AesCbc.X86_64.Vaes512Decrypt
public import VerifiedGarbage.Proof.Framework.X86_64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.X86_64Impl
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# AES-CBC on x86-64, zeroing the scratch it writes

Each implementation of `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` that
writes its `scratch` buffer is called by `callWipe`, as the internal function
`vg_aes_cbc_{en,de}crypt_unwiped<suffix>`, which then zeroes the bytes it may
write (`decWrites`: 224 for the loops in AES-NI or VAES registers, which
write nothing past them, all 2176 for the others) with an implementation of
`vg_zeroize` (`ZeroizeImpl`, `vg_zeroize_avx` for the code that needs AVX
already). The loop in AES-NI registers that encrypts writes none of
`scratch`, and is not wrapped.

Each implementation meets its contract and leaves each byte of `scratch`
unchanged or zero (`*_scrubbed`, the stronger contract the Spec will state
once every target's implementations prove it; the registrations take its
weakening, `*_verified`): the bytes it may write are zero
(`Verified.callWipeTail'`), and the others it did not write
(`Verified.cbc_tail_of_written`, from its `written` bound).
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86_64.Wiped

open VG VG.X86_64 VG.Proof.Aes.X86_64 VG.Proof.AesCbc.Wipe VG.Proof.Zeroize.X86_64

/-- A call of `name`, whose code is `body`, then of the zeroize function `z`
on the first `n` bytes of `scratch` (the sixth argument, in `r9`). -/
def wiped (z : ZeroizeImpl) (n : Nat) (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.X86_64.callWipe .r9 n name body z.name z.code

theorem wiped_spSafe {z : ZeroizeImpl} {n : Nat} {name : String} {body : Prog isa}
    (h : body.all (fun i => !isa.writesSp i) = true) :
    (wiped z n name body).all (fun i => !isa.writesSp i) = true :=
  callWipe_spSafe h z.spSafe

theorem sat (P : Spec.Cbc.aesSig.Post 64) :
    ∃ s, (Spec.Cbc.aesSig.contract abi (pre 64) P false 32 none).pre s := by
  implies_sat [Spec.Cbc.aesSig, pre, X86_64.abi, X86_64.argRegs] [Proof.AesCbc.X86_64.sat]
    using Proof.AesCbc.X86_64.sat

theorem args_length : ∀ s vals,
    abi.args ((Spec.Cbc.aesSig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some vals →
      (vals s).length = (Spec.Cbc.aesSig.words abi.ptrBits).length := by
  intro s vals hv
  obtain rfl := Option.some.inj (hv.symm.trans (rfl : abi.args _ = some (regArgs Spec.Cbc.aesSig)))
  exact regArgs_length Spec.Cbc.aesSig s (by decide)

/-- An implementation with 8 bytes of stack that writes nothing in
`scratch` from `w` on, wrapped to zero the rest. -/
theorem wiped_scrubbed {P : Spec.Cbc.aesSig.Post 64} {w : Nat} {name : String} {body : Prog isa}
    (z : ZeroizeImpl)
    (h : Verified target body (Spec.Cbc.aesSig.contract abi (pre 64) (tailPost 64 w P) false 8 none))
    (hsp : body.all (fun i => !isa.writesSp i) = true) (hd : body.x86_64Depth ≤ 8) (hw : w ≤ 2176)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (Spec.Cbc.aesSig.words 64).length →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words 64) P vs m₁ m' x → Curry.apply (Spec.Cbc.aesSig.words 64) P vs m₂ m' x)
    (hout : ∀ vs m m₁ m₂ x, vs.length = (Spec.Cbc.aesSig.words 64).length →
      (Sig.bufs Spec.Cbc.aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words 64) P vs m m₁ x → Curry.apply (Spec.Cbc.aesSig.words 64) P vs m m₂ x) :
    Verified target (wiped z w name body)
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 P) false 32 none) :=
  Verified.callWipeTail' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := [])
    (nm := "scratch") (e := .u64) (k := 272) (i := 5) h z.verified (by decide) rfl rfl rfl
    (by simp only [Elem.size]; omega) (by omega) (by decide) hsp hd z.spSafe (by rw [z.xd])
    (Nat.zero_le _) (pre_local 64) (tailPost_local 64 w P hpost) (tailPost_out 64 w P hout hw)
    (wipedTail 64 w P) (sat _)

/-! ## The implementations, wrapped -/

theorem decrypt_depth (v : BlocksImpl) : (Caller.decrypt v).x86_64Depth ≤ 8 := by
  unfold Caller.decrypt
  split
  · decide
  · split
    · decide
    · simp only [Impl.AesCbc.X86_64.decrypt, Impl.AesCbc.X86_64.batched, Impl.AesCbc.X86_64.groups,
        Impl.AesCbc.X86_64.decGroup, Impl.AesCbc.X86_64.decBody, Code.x86_64Depth, v.decNoStack, Nat.max_le]
      omega

theorem encrypt_depth (v : BlocksImpl) : (Caller.encrypt v).x86_64Depth ≤ 8 := by
  unfold Caller.encrypt
  split
  · decide
  · simp only [Impl.AesCbc.X86_64.encrypt, Impl.AesCbc.X86_64.whole, Impl.AesCbc.X86_64.encBody,
      Code.x86_64Depth, v.encNoStack, Nat.max_le]
    omega

/-- The bytes of `scratch` that `Caller.decrypt v` may write: 224 for the
loops in AES-NI or VAES registers, all of them for the others. -/
def decWrites (v : BlocksImpl) : Nat :=
  if Caller.vaes v then 224 else if Caller.hardware v then 224 else 2176

theorem decWrites_le (v : BlocksImpl) : decWrites v ≤ 2176 := by
  unfold decWrites; split
  · decide
  · split <;> decide

/-- `Caller.decrypt v` writes nothing in `scratch` from `decWrites v` on. -/
theorem decrypt_tail (v : BlocksImpl) :
    Verified target (Caller.decrypt v)
      (Spec.Cbc.aesSig.contract abi (pre 64) (tailPost 64 (decWrites v) (decPost 64)) false 8 none) := by
  have h : Verified target (Caller.decrypt v)
      (Spec.Cbc.aesSig.contract abi (pre 64) (decPost 64) false 8 none) :=
    Proof.AesCbc.decrypt_keyed (Caller.decryptVerified v)
  unfold decWrites
  split
  · rename_i hv
    exact Verified.cbc_tail_of_written h (fun s t s' hs he => by
      have hw := Caller.decWritten_ok v s t s' hs he
      rwa [Caller.decWritten, ite_eq_left hv] at hw) args_length
  · rename_i hv
    split
    · rename_i hh
      exact Verified.cbc_tail_of_written h (fun s t s' hs he => by
        have hw := Caller.decWritten_ok v s t s' hs he
        rwa [Caller.decWritten, ite_eq_right hv, ite_eq_left hh] at hw) args_length
    · exact Verified.cbc_tail_full h

/-- `vg_aes_cbc_decrypt` for `v`, wrapped with `z`. -/
def decrypt (v : BlocksImpl) (z : ZeroizeImpl) : Prog isa :=
  wiped z (decWrites v) ("vg_aes_cbc_decrypt_unwiped" ++ v.suffix) (Caller.decrypt v)

theorem decrypt_scrubbed (v : BlocksImpl) (z : ZeroizeImpl) :
    Verified target (decrypt v z)
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (decPost 64)) false 32 none) :=
  wiped_scrubbed z (decrypt_tail v) (Caller.decryptSpSafe v) (decrypt_depth v) (decWrites_le v)
    (decPost_local 64) (decPost_out 64)

theorem decrypt_verified (v : BlocksImpl) (z : ZeroizeImpl) :
    Verified target (decrypt v z) (Spec.Cbc.aesDecryptContract abi 32) :=
  Verified.of_scrubbed (decrypt_scrubbed v z)

theorem decrypt_spSafe (v : BlocksImpl) (z : ZeroizeImpl) :
    (decrypt v z).all (fun i => !isa.writesSp i) = true :=
  wiped_spSafe (Caller.decryptSpSafe v)

/-- `vg_aes_cbc_encrypt` for `v`, wrapped with `z`: for the baseline loop,
which may write all of `scratch`. -/
def encrypt (v : BlocksImpl) (z : ZeroizeImpl) : Prog isa :=
  wiped z 2176 ("vg_aes_cbc_encrypt_unwiped" ++ v.suffix) (Caller.encrypt v)

theorem encrypt_scrubbed (v : BlocksImpl) (z : ZeroizeImpl) :
    Verified target (encrypt v z)
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (encPost 64)) false 32 none) :=
  wiped_scrubbed z (Verified.cbc_tail_full (Proof.AesCbc.encrypt_keyed (Caller.verified v)))
    (Caller.spSafe v) (encrypt_depth v) (by decide) (encPost_local 64) (encPost_out 64)

theorem encrypt_verified (v : BlocksImpl) (z : ZeroizeImpl) :
    Verified target (encrypt v z) (Spec.Cbc.aesEncryptContract abi 32) :=
  Verified.of_scrubbed (encrypt_scrubbed v z)

theorem encrypt_spSafe (v : BlocksImpl) (z : ZeroizeImpl) :
    (encrypt v z).all (fun i => !isa.writesSp i) = true :=
  wiped_spSafe (Caller.spSafe v)

/-- The loop in AES-NI registers that encrypts writes nothing in `scratch`. -/
theorem encrypt_free_scrubbed (v : BlocksImpl) (h : Caller.hardware v = true) :
    Verified target (Caller.encrypt v)
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (encPost 64)) false 8 none) :=
  Verified.cbc_of_unwritten (Proof.AesCbc.encrypt_keyed (Caller.verified v))
    (fun s t s' hs he => by
      have hw := Caller.written_ok v s t s' hs he
      rwa [Caller.written, ite_eq_left h] at hw)
    args_length

/-- `vg_aes_cbc_decrypt_vaes_avx512`, wrapped. -/
def decryptVaes512 : Prog isa :=
  wiped .avx 224 "vg_aes_cbc_decrypt_unwiped_vaes_avx512" Impl.AesCbc.X86_64.Vaes512Decrypt.decrypt

theorem decryptVaes512_scrubbed :
    Verified target decryptVaes512
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (decPost 64)) false 32 none) :=
  wiped_scrubbed .avx (Verified.cbc_tail_of_written (Proof.AesCbc.decrypt_keyed Vaes512Decrypt.verified)
      Vaes512Decrypt.written args_length)
    Vaes512Decrypt.spSafe (by decide) (by decide) (decPost_local 64) (decPost_out 64)

theorem decryptVaes512_verified :
    Verified target decryptVaes512 (Spec.Cbc.aesDecryptContract abi 32) :=
  Verified.of_scrubbed decryptVaes512_scrubbed

theorem decryptVaes512_spSafe : decryptVaes512.all (fun i => !isa.writesSp i) = true :=
  wiped_spSafe Vaes512Decrypt.spSafe

end VG.Proof.AesCbc.X86_64.Wiped
