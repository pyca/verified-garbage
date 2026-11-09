module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.KeyScalar

/-! # Combine a checked bit with the persistent RSA validity mask -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem maskFlag_preserves_e {m m' : Mem} {B : Addr} {n : Nat}
    (O : Keep B n [] [kFlag, kOk] m m') : val32 m' B kEv 2 = val32 m B kEv 2 := by
  apply O.val32 _ (by decide)
  intro r hr
  change r ∈ [] ++ [(kFlag, 4), (kOk, 4)] at hr
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  all_goals exact Or.inl (by decide)

end VG.Proof.RsaKeyGen.X86.Key
