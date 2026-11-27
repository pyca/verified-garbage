module

public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE

/-!
# HMAC's `init` for a key of any length, with its working space as an argument: PPC64LE

`vg_hmac_<hash>_init_any_scratch(inner = r3, outer = r4, key = r5,
key_len = r6, scratch = r7)` (`Hash.initAny`), which the tables of `Hmac`
hold (`Proof/HmacTable/PPC64LE.lean`): for a key longer than a block of
`B = 2 ^ b` bytes (cold), `initLong`, which hashes the key into `scratch`
and calls `init` with its digest; otherwise `init` itself, inline, with the
same working space (`Hash.initEntry`, which compares `key_len` on entry).
`initLong` uses more of `scratch` (`Hash.lbytes` bytes) and 48 bytes more
of stack (its frame) than `init`. The key's digest stays in `scratch`, which
the caller wipes, as `vg_hmac_<hash>_init` (`initCode`, whose frame holds
its working space) wipes its own.
-/

@[expose] public section

namespace VG.Impl.Hmac.Stream.PPC64LE.Hash

open VG.PPC64LE

/-- HMAC's `init` for a key of any length, with its working space as an
argument, for `B = 2 ^ b`. -/
def initAny (H : Hash) (b : Nat) : Prog isa := initEntry b H.init H.initLong

end VG.Impl.Hmac.Stream.PPC64LE.Hash
-- separate module: the shared HMAC code (`Impl/Hmac/Stream/PPC64LE.lean`) is imported by every
-- PPC64LE HMAC, PBKDF2 and RSA proof, which a definition there would rebuild; only the tables use this.
