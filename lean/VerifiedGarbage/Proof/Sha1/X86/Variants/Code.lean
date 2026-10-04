import VerifiedGarbage.Impl.Pbkdf2.Md.X86
import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
import VerifiedGarbage.Impl.Sha1.X86.Stream
import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# SHA-1 backends on x86: the code built on them

SHA-1 has backends on x86 (`Interface.lean`): implementations of its
compression function, each with the streaming `update` and `finalize` made
with it. HMAC and PBKDF2 are the code of every other hash function, at SHA-1
made with a backend: its streaming functions as the code calls them
(`hmacHash`), SHA-1 as a Merkle–Damgård hash function for HMAC's `init` and
`finalize` and PBKDF2's iteration, which call the compression function
(`mdHash`, `Impl/Pbkdf2/Md/X86.lean`), and the functions the whole of PBKDF2
calls (`fns`, `Impl/Pbkdf2/Whole/X86.lean`), by the names the generic
registration files give them (with the backend's suffix).
-/

namespace VG.Proof.Sha1.X86.Variants

open VG.X86

/-- SHA-1's streaming functions, with a backend's `update` and `finalize`
(`updC`, `finC`), which take their working space as an argument, named
`update_scratch` and `finalize_scratch` with its suffix: an 84-byte state, 20
words of working space and a 20-byte digest. -/
def hmacHash (suffix : String) (updC finC : Prog isa) : Impl.Pbkdf2.Stream.X86.Hash :=
  ⟨64, 84, 20, 20, 20, Spec.Sha1.initApi.name, Impl.Sha1.X86.Stream.init,
    Spec.Sha1.updateScratchApi.name ++ suffix, updC, Spec.Sha1.finalizeScratchApi.name ++ suffix,
    finC⟩

/-- SHA-1 as a Merkle–Damgård hash function, with a backend's compression
function `cmpN`/`cmpC` and the streaming functions calling it: a 20-byte hash
value, a big-endian 8-byte length field, and 112 bytes of scratch space for
the compression function. -/
def mdHash (suffix cmpN : String) (cmpC updC finC : Prog isa) : Impl.Pbkdf2.Md.X86.Hash :=
  ⟨hmacHash suffix updC finC, 20, 8, true, 112, cmpN, cmpC, Impl.Sha1.X86.Stream.params.out⟩

/-- The functions the whole of PBKDF2 calls for SHA-1 with a backend. -/
def fns (suffix cmpN : String) (cmpC updC finC : Prog isa) : Impl.Pbkdf2.Whole.X86.Fns where
  H := hmacHash suffix updC finC
  W := Spec.Hmac.sha1I.scratch
  hiN := Spec.Hmac.sha1I.initScratchApi.name ++ suffix
  hiC := (mdHash suffix cmpN cmpC updC finC).hmacInit
  hfN := Spec.Hmac.sha1I.finalizeScratchApi.name ++ suffix
  hfC := (mdHash suffix cmpN cmpC updC finC).hmacFin
  itN := Spec.Hmac.sha1I.iterateApi.name ++ suffix
  itC := (mdHash suffix cmpN cmpC updC finC).iterate

end VG.Proof.Sha1.X86.Variants
