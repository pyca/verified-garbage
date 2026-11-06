module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# FFDH on AArch64: the stages across stores outside the working space

A key-generation attempt writes its results outside the working space while
it runs. Its data with other inputs (`FD.withSrcs`), whose octets are the stores'
results, and stores outside the working space (`outside_of_frame`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep)

/-- The run's data with the other inputs `ss`. -/
abbrev FD.withSrcs (D : FD) (ss : List (Addr × List Byte)) : FD := ⟨D.B, D.Z, D.k, D.dl, D.dp, D.dom, D.hs, ss⟩

/-- Memory below `Z` kept by stores outside it. -/
theorem outside_of_frame {B : Addr} {Z : Nat} {m m' : Mem} {op : Addr} {len : Nat}
    (hsep : ∀ j < len, Z ≤ ofs B (op + BitVec.ofNat 64 j))
    (hx : ∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → m' x = m x) : Outside B Z (2 ^ 64) m m' :=
  fun x hx' => hx x fun j hj he => by
    have := hsep j hj
    rw [← he] at this
    have : ofs B x < 2 ^ 64 := (x - B).isLt
    rcases hx' with h | h <;> omega

end VG.Proof.Ffdh.AArch64
