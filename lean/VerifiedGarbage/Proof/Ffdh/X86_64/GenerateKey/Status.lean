module

public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH on x86-64: encode success or a degenerate-public-value rejection -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem status_ok {s : State} {B : Addr} {Z : Nat} {c : Bool}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hZ : 256 ≤ Z)
    (hF : word s.mem B (8 * sF) = BitVec.ofNat 64 c.toNat) :
    WP isa (.block status) s fun t =>
      (t.gpr .rax = BitVec.ofNat 64 (if c then 1 else 3) ∧ t.mem = s.mem) ∧ Keep [.rax, .rdx] s t := by
  refine WP.keep _ ?_ rfl
  unfold status
  xrun [State.ea, hdr, hd, hdrOff, hs.ld (d := 8 * sF) (by change 248 ≤ Z; omega), hF]
  cases c <;> rfl

end VG.Proof.Ffdh.X86_64.GenerateKey
