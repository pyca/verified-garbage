module

public import VerifiedGarbage.Spec.Gcm.Contract

/-!
# The powers of AES-GCM's hash subkey

**Trusted** (as every file in `Spec/`). The powers `H¹ … H⁴⁸` of the hash
subkey (`hpow`), and where a 1024-byte key context holds them
(`PowersRepr`): after the key context of `vg_aes_gcm_init` (`KeyRepr`) in its
first 256 bytes, `Hᵏ` in bytes `256 + 16 (k - 1)` to `256 + 16 k - 1`, for
`k` from 1 to 48, each a block as GCM writes one (`blockAt`, as `H` is in
bytes 240–255). The prepared key contexts' contracts state them.
-/

@[expose] public section

namespace VG.Spec.Gcm

/-- The multiplicative identity of `GF(2¹²⁸)` (§6.3): the block whose
leftmost bit is 1, which stands for the polynomial 1. -/
def one : Block := 1 <<< 127

/-- `Hᵏ`: `H` multiplied by itself `k` times in `GF(2¹²⁸)` (`mul`, §6.3). -/
def hpow (h : Block) (k : Nat) : Block := Nat.repeat (fun y => mul y h) k one

/-- The key context at `p` holds the powers `H¹ … H⁴⁸` of its hash subkey:
`Hᵏ⁺¹` is the block at `p + 256 + 16 k`. -/
def PowersRepr (m : Mem) (p : Addr) : Prop :=
  ∀ k < 48, blockAt m (p + BitVec.ofNat 64 (256 + 16 * k)) = hpow (ctxH m p) (k + 1)

end VG.Spec.Gcm
