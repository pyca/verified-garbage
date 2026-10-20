module

public import VerifiedGarbage.Proof.Bignum.X86.CrtCheckedFrame
import VerifiedGarbage.Proof.Bignum.OutsFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! # Byte-level frame around the private RSA callee-save area -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.Proof.Mont

def bodyRegions (base out : Addr) (bytes len : Nat) : List Region :=
  [⟨base, 32⟩, ⟨off base 48, bytes - 48⟩, ⟨out, len⟩]

theorem body_frame {base out : Addr} {bytes len : Nat} {m m' : Mem}
    (O : Outs base (bodyRanges bytes) m m') (fit : bytes ≤ 2 ^ 64) :
    Frame (bodyRegions base out bytes len) m m' := by
  have F := VG.Proof.Bignum.outs_frame O (by
    intro r hr
    simp only [bodyRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> omega)
  apply F.mono
  simp only [bodyRanges, List.map_cons, List.map_nil, bodyRegions, List.mem_cons,
    List.not_mem_nil, or_false, off, BitVec.add_zero]
  intro r hr
  rcases hr with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem high_frame {base out : Addr} {bytes len : Nat} {m m' : Mem}
    (F : Frame [⟨off base 64, bytes - 64⟩, ⟨out, len⟩] m m') (low : 64 ≤ bytes)
    (fit : bytes ≤ 2 ^ 64) : Frame (bodyRegions base out bytes len) m m' := by
  apply F.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨⟨off base 48, bytes - 48⟩, by simp [bodyRegions], ?_⟩
    intro a ha
    have I := Offset.lt_iff a base (show 64 + (bytes - 64) ≤ 2 ^ 64 by omega)
    have J := Offset.lt_iff a base (show 48 + (bytes - 48) ≤ 2 ^ 64 by omega)
    change (a - off base 64).toNat < bytes - 64 ↔ 64 ≤ ofs base a ∧ ofs base a < 64 + (bytes - 64) at I
    change (a - off base 48).toNat < bytes - 48 ↔ 48 ≤ ofs base a ∧ ofs base a < 48 + (bytes - 48) at J
    change (a - off base 64).toNat + 1 ≤ bytes - 64 at ha
    change (a - off base 48).toNat + 1 ≤ bytes - 48
    have := I.mp (by omega)
    have := J.mpr (by omega)
    omega
  · exact ⟨⟨out, len⟩, by simp [bodyRegions], fun _ h => h⟩

end VG.Proof.Bignum.X86.Crt
