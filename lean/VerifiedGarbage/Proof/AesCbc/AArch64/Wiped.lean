module

public import VerifiedGarbage.Proof.AesCbc.Wipe
public import VerifiedGarbage.Proof.AesCbc.AArch64.Caller
public import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Verified
public import VerifiedGarbage.Proof.Framework.AArch64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.AArch64Wide
import VerifiedGarbage.Proof.AesEcb.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Depth

/-!
# AES-CBC on AArch64, zeroing the scratch it writes

Each implementation of `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` that
writes its `scratch` buffer (all but the encryption with the Cryptographic
Extension, `Encrypt.code`, and the decryption with SHA-3's `eor3`,
`Decrypt.code`) is called by `callWipe`, as the internal function
`vg_aes_cbc_{en,de}crypt_unwiped<suffix>`, which then zeroes the whole of
`scratch` with `vg_zeroize`. Each implementation meets its contract and
leaves each byte of `scratch` unchanged or zero (`*_scrubbed`, the stronger
contract the Spec will state once every target's implementations prove it;
the registrations take its weakening, `*_verified`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Wiped

open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.AesCbc.Wipe

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the
2176 bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.AArch64.callWipe .x5 2176 name body "vg_zeroize" Impl.Zeroize.AArch64.zeroizeWide

/-- `vg_aes_cbc_encrypt<suffix>`, wiping `scratch`. -/
def encrypt (v : BlocksImpl) : Prog isa :=
  wiped ("vg_aes_cbc_encrypt_unwiped" ++ v.suffix) (Caller.encrypt v)

/-- `vg_aes_cbc_decrypt<suffix>`, wiping `scratch`. -/
def decrypt (v : BlocksImpl) : Prog isa :=
  wiped ("vg_aes_cbc_decrypt_unwiped" ++ v.suffix) (Impl.AesCbc.AArch64.decrypt v.dec)

theorem sat (P : Spec.Cbc.aesSig.Post 64) :
    ∃ s, (Spec.Cbc.aesSig.contract abi (pre 64) P false 32 none).pre s := by
  implies_sat [Spec.Cbc.aesSig, pre, AArch64.abi, AArch64.argRegs] [Proof.AesCbc.AArch64.sat]
    using Proof.AesCbc.AArch64.sat

theorem wiped_verified {P : Spec.Cbc.aesSig.Post 64} {name : String} {body : Prog isa}
    (h : Verified target body (Spec.Cbc.aesSig.contract abi (pre 64) P false 0 none))
    (hd : body.aarch64Depth = 0)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (Spec.Cbc.aesSig.words 64).length →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words 64) P vs m₁ m' x → Curry.apply (Spec.Cbc.aesSig.words 64) P vs m₂ m' x)
    (hout : ∀ vs m m₁ m₂ x, vs.length = (Spec.Cbc.aesSig.words 64).length →
      (Sig.bufs Spec.Cbc.aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words 64) P vs m m₁ x → Curry.apply (Spec.Cbc.aesSig.words 64) P vs m m₂ x) :
    Verified target (wiped name body)
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 P) false 32 none) :=
  Verified.callWipe' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := [])
    (nm := "scratch") (e := .u64) (k := 272) (n := 2176) (i := 5) h Proof.Zeroize.AArch64.wideVerified
    (by decide) rfl rfl rfl (by decide) (by decide) (by rw [hd]) AesEcb.AArch64.zeroize_depth
    (Nat.zero_le _) (pre_local 64) hpost hout (Wipe.wiped 64 P) (sat _)

theorem encrypt_depth (v : BlocksImpl) : (Caller.encrypt v).aarch64Depth = 0 := by
  unfold Caller.encrypt
  split
  · exact AesEcb.AArch64.depth_of_noFrames (by decide)
  · simp only [Impl.AesCbc.AArch64.encrypt, Impl.AesCbc.AArch64.whole, Impl.AesCbc.AArch64.encBody,
      Code.aarch64Depth, AesEcb.AArch64.depth_of_noFrames v.encNoFrames, Nat.max_self]

theorem decrypt_depth (v : BlocksImpl) : (Impl.AesCbc.AArch64.decrypt v.dec).aarch64Depth = 0 := by
  simp only [Impl.AesCbc.AArch64.decrypt, Impl.AesCbc.AArch64.whole, Impl.AesCbc.AArch64.decBody,
    Code.aarch64Depth, AesEcb.AArch64.depth_of_noFrames v.decNoFrames, Nat.max_self]

theorem encrypt_scrubbed (v : BlocksImpl) :
    Verified target (encrypt v)
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (encPost 64)) false 32 none) :=
  wiped_verified (Proof.AesCbc.encrypt_keyed (Caller.verified v)) (encrypt_depth v)
    (encPost_local 64) (encPost_out 64)

theorem decrypt_scrubbed (v : BlocksImpl) :
    Verified target (decrypt v)
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (decPost 64)) false 32 none) :=
  wiped_verified (Proof.AesCbc.decrypt_keyed (Proof.AesCbc.AArch64.decrypt_verified v))
    (decrypt_depth v) (decPost_local 64) (decPost_out 64)

theorem encrypt_verified (v : BlocksImpl) :
    Verified target (encrypt v) (Spec.Cbc.aesEncryptContract abi 32) :=
  Verified.of_scrubbed (encrypt_scrubbed v)

theorem decrypt_verified (v : BlocksImpl) :
    Verified target (decrypt v) (Spec.Cbc.aesDecryptContract abi 32) :=
  Verified.of_scrubbed (decrypt_scrubbed v)

theorem args_length : ∀ s vals,
    abi.args ((Spec.Cbc.aesSig.words abi.ptrBits).map (·.bits abi.ptrBits)) = some vals →
      (vals s).length = (Spec.Cbc.aesSig.words abi.ptrBits).length := by
  intro s vals hv
  obtain rfl := Option.some.inj (hv.symm.trans (rfl : abi.args _ = some (regArgs Spec.Cbc.aesSig)))
  exact regArgs_length Spec.Cbc.aesSig s (by decide)

/-- With the Cryptographic Extension, encryption writes nothing in `scratch`. -/
theorem encrypt_free_scrubbed (v : BlocksImpl) (h : v.enc.name = "vg_aes_encrypt_blocks_aes") :
    Verified target (Caller.encrypt v)
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (encPost 64)) false 0 none) :=
  Verified.cbc_of_unwritten (Proof.AesCbc.encrypt_keyed (Caller.verified v))
    (fun s t s' hs he => by
      have hw := Caller.written_ok v s t s' hs he
      rwa [Caller.written, ite_eq_left h] at hw)
    args_length

/-- The decryption with SHA-3's `eor3` writes nothing in `scratch`. -/
theorem decryptSha3_scrubbed :
    Verified target Impl.AesCbc.AArch64.Decrypt.code
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (decPost 64)) false 0 none) :=
  Verified.cbc_of_unwritten (Proof.AesCbc.decrypt_keyed Proof.AesCbc.AArch64.Decrypt.verified)
    Proof.AesCbc.AArch64.Decrypt.written args_length

end VG.Proof.AesCbc.AArch64.Wiped
