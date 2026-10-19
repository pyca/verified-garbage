module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallResult
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallGeometry
import VerifiedGarbage.Proof.Framework.Offset

/-! The call instruction's return-address write does not change signing inputs. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

theorem random_callResult_plain {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hsp : t.gpr .rsp = randomBase s) :
    randomCallResult s t = Spec.Dsa.signBytes (s.gpr .r9).toNat (stackArg s 0).toNat
      (Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat)
      (Spec.Rsa.bytesAt t.mem (stackArg s 1) (stackArg s 2).toNat) := by
  have sR : Region.Sub ⟨randomBase s - 8, 8⟩ (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_callBase extra s]
    exact Offset.sub_base _ (by omega)
  have retain (p : Addr) (n : Nat) (hn : n < 2 ^ 64)
      (hd : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨p, n⟩) :
      Spec.Rsa.bytesAt t.callEntry.mem p n = Spec.Rsa.bytesAt t.mem p n :=
    random_callEntry_bytes hsp
      ((hd.sub_left sR).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)) hn
  have hq : (stackArg s 0).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  have hn : (⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩ : Region).Disjoint
      ⟨randomBase s - 8, 8⟩ :=
    Offset.disjoint_below _ (by change 8 + 200 + (stackArg s 0).toNat ≤ 2 ^ 64; omega)
  unfold randomCallResult
  rw [retain _ _ (s.gpr .r8).isLt h.stackKey, retain _ _ (stackArg s 2).isLt h.stackDigest,
    random_callEntry_bytes hsp (hn.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by omega)]

end VG.Proof.Dsa.X86_64
