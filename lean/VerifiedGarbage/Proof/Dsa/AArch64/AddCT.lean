module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Constant time of DSA modular addition -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- The workspace of `addMod`, for some `-m⁻¹`. -/
def AddPre (L : Ws) (s : State) : Prop := GoodW L s ∧ 1 ≤ L.w ∧ L.w < 2 ^ 31

/-- Modular addition has a value-independent trace for either DSA schedule:
RSA's `addMod_ct`, given the taint check of its loads. -/
theorem addCode_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x9 (sArr a), ldh .x17 (sArr b),
      ldh .x10 (sArr Public.aN), ldh .x8 (sArr Public.aAcc), ldh .x6 (sArr Public.aTmp), ldh .x5 (sArr o),
      ldh .x12 sW, movi .x7 0, mov .x16 .x8, mov .x14 .x12, .adds .x .x3 .x7 .x7]) hc).isSome = true) :
    RelCT isa (Two AddPre) (addMod o a b) fun _ _ => True :=
  two_map id (fun _ _ h => h.1) (addMod_ct ho ha hb hT)

end VG.Proof.Dsa.AArch64
