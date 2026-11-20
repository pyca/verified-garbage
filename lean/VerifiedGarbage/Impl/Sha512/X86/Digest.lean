module

public import VerifiedGarbage.Impl.Sha512.X86.Stream
public import VerifiedGarbage.Impl.MdStream.X86.Digest
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# The SHA-512 family's one-shot digests on x86 (32-bit), as emitted

`vg_<f>_digest` is the generic one-shot digest (`Impl.MdStream.X86.Digest`)
over SHA-512's streaming functions (`hash`), then its cleanup: the zeroing of
the 612 bytes of stack below `esp` that it and its callees use, and the
clearing of the registers a callee may change (`Impl.Scrub.X86.scrubF 0 612`),
so that it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Sha512.X86.Fn

open VG.X86

/-- SHA-512's streaming functions, as the one-shot digest of the first `D`
bytes of the final hash value from `iv` calls them: `init` as `initN`, and
`update` and `finalize` as `vg_sha512_update_scratch` and
`vg_sha512_finalize_scratch`. -/
def hash (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Impl.Pbkdf2.Stream.X86.Hash :=
  ⟨128, 192, D, 64, 34, initN, Stream.init iv, "vg_sha512_update_scratch", Stream.update,
    "vg_sha512_finalize_scratch", Stream.finalize⟩

/-- `vg_<f>_digest` of the first `D` bytes of the final hash value from `iv`, as emitted. -/
def digest (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Prog isa :=
  Impl.Scrub.X86.scrubF 0 612 (Impl.MdStream.X86.Digest.digest (hash D initN iv))

end VG.Impl.Sha512.X86.Fn
