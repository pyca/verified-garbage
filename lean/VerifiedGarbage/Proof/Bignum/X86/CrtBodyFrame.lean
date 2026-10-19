module

public import VerifiedGarbage.Proof.Bignum.X86.CrtCheckedFrame
public import VerifiedGarbage.Proof.Bignum.OutsFrame

/-! # Byte-level frame around the private RSA callee-save area -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.Proof.Mont

/-- What the body writes: the bytes around its saved registers, the output and
the zone below `sp` its calls write. -/
def bodyRegions (base out : Addr) (bytes len : Nat) (sp : BitVec 32) : List Region :=
  [⟨base, 32⟩, ⟨off base 48, bytes - 48⟩, ⟨out, len⟩, VG.X86.below sp 20]

theorem body_frame {base out : Addr} {bytes len : Nat} {sp : BitVec 32} {m m' : Mem}
    (O : VG.Proof.Mont.X86.OutsZ base sp (bodyRanges bytes) m m') (fit : bytes ≤ 2 ^ 64) :
    Frame (bodyRegions base out bytes len sp) m m' := by
  intro a ha
  refine O a (fun r hr => ?_) (ha _ (by simp [bodyRegions]))
  have H : ¬ (⟨off base r.1, r.2⟩ : Region).Contains a 1 := by
    simp only [bodyRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := ha ⟨base, 32⟩ (by simp [bodyRegions])
      simpa only [off, BitVec.add_zero] using this
    · exact ha _ (by simp [bodyRegions])
  have I := Offset.lt_iff a base (show r.1 + r.2 ≤ 2 ^ 64 by
    simp only [bodyRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> omega)
  change ¬ ((a - off base r.1).toNat + 1 ≤ r.2) at H
  change (a - off base r.1).toNat < r.2 ↔ r.1 ≤ ofs base a ∧ ofs base a < r.1 + r.2 at I
  omega

theorem high_frame {base out : Addr} {bytes len : Nat} {sp : BitVec 32} {m m' : Mem}
    (F : Frame [⟨off base 64, bytes - 64⟩, ⟨out, len⟩] m m') (low : 64 ≤ bytes)
    (fit : bytes ≤ 2 ^ 64) : Frame (bodyRegions base out bytes len sp) m m' := by
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
