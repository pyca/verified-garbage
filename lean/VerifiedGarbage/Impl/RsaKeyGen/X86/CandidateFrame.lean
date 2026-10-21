module

public import VerifiedGarbage.Impl.Mont.X86

/-! # One candidate frame supplies the shared round's workspace-length slot

The candidate API's eleventh argument is scratch_len; its second argument
is out_len. Entry copies scratch_len to header byte 40. A 28-byte private
frame puts its copy at ESP+24, the length slot read by the shared prepared
Montgomery call helper. It is allocated once around preparation and all
witnesses, rather than around every product.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.CandidateFrame
open VG VG.X86 VG.Impl.Mont.X86

def bytes : Nat := 28

def code (body : Prog isa) : Prog isa :=
  .seq (.block [.mov .edx (.mem (sc 40))])
    (.frame (.alloc bytes) (.seq (.block [.store (at_ .esp 24) .edx]) body) (.free bytes))

end VG.Impl.RsaKeyGen.X86.CandidateFrame
