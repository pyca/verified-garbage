module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Import the public exponent into a pair and a persistent native array -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Bignum.X86 (byteAddr)
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def loadExponentRanges (n : Nat) : List (Nat × Nat) := [(kEv, 8), (arr n aE, S n)]

theorem loadExponent_preserves_num {m m' : Mem} {B : Addr} {n j : Nat}
    (unchanged : j ≠ aE) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (loadExponentRanges n) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega)
  intro r hr
  simp only [loadExponentRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Or.inr (Nat.le_trans (by decide : kEv + 8 ≤ hdr) (Nat.le_add_right ..))
  · have D := arr_disj (w := n) unchanged
    unfold S at D ⊢
    omega

end VG.Proof.RsaKeyGen.X86.Key
