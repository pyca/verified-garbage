module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExponentFrame
import VerifiedGarbage.Proof.Rsa.WordRanges
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # Frames for preparing the quotient-based inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem exponent_mask_coefficient {m m' : Mem} {B : Addr} {n : Nat}
    (O : Keep B n [aT1, aT2] [kOk] m m') : num m' B 2 3 = num m B 2 3 := by
  change val32 m' B (arr 2 3) 2 = val32 m B (arr 2 3) 2
  apply O.val32 _ (by decide)
  intro r hr
  simp only [ranges, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  all_goals simp only [arr, S, aT1, aT2, hdr, kOk]
  all_goals omega

end VG.Proof.RsaKeyGen.X86.Key
