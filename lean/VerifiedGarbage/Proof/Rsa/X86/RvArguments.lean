module

public import VerifiedGarbage.Proof.Rsa.X86.RvSlots
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall

/-! # Public cdecl arguments remain available throughout recovery -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys

theorem KS.argument {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) {i : Nat} {v : BitVec 32}
    (arg : CallArgument s0 g.B g.Z i v) : CallArgument s g.B g.Z i v :=
  arg.keep h.rest (by decide) (h.frame.mono (by decide) (by
    have := h.ws.hdr_le; unfold hdr at this; omega))

end VG.Proof.Rsa.X86.Recover
