module

public import VerifiedGarbage.Impl.Bignum.X86.ModulusCheck
public import VerifiedGarbage.Proof.Bignum.X86.ByteOps
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion

/-! # Reading the first and last modulus bytes without crossing its buffer -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem modulusRead_ok (s : State) {k : Nat} (hk : 0 < k)
    (fit : (s.gpr .esi).toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr (s.gpr .esi)) k)
    (count : s.gpr .ecx = BitVec.ofNat 32 k) :
    WP isa (.block modulusRead) s fun t =>
      t.gpr .eax = (s.mem (byteAddr (s.gpr .esi))).setWidth 32 ∧
      t.gpr .edx = (s.mem (byteAddr (s.gpr .esi) + BitVec.ofNat 64 (k - 1))).setWidth 32 ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  have readable (i : Nat) (hi : i < k) :
      InRegions (s.rd ++ s.wr) (byteAddr (s.gpr .esi) + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := read
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  have first : InRegions (s.rd ++ s.wr) (byteAddr (s.gpr .esi)) 1 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using readable 0 hk
  unfold modulusRead
  refine wp_loadByte (by simp only [State.ea, BitVec.add_zero]; rfl)
    first fun s₁ u₁ => ?_
  refine wp_movS rfl fun s₂ u₂ _ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => ?_
  refine wp_subS rfl fun s₄ u₄ _ => ?_
  have K : Keeps [.eax, .ebx, .edx] s s₄ :=
    (((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps
  have ptr : s₄.gpr .ebx = s.gpr .esi + BitVec.ofNat 32 (k - 1) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other .esi (by decide),
      u₂.other .ecx (by decide), u₁.other .ecx (by decide), count]
    change s.gpr .esi + BitVec.ofNat 32 k - BitVec.ofNat 32 1 = _
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      Offset.ofNat_sub_ofNat (by omega)]
  have addr : s₄.ea ⟨.ebx, 0⟩ = byteAddr (s.gpr .esi) + BitVec.ofNat 64 (k - 1) := by
    simp only [State.ea, BitVec.add_zero]
    rw [ptr]
    exact byteAddr_add (by omega)
  refine wp_loadByte addr (by rw [K.2.1, K.2.2]; exact readable (k - 1) (by omega))
    fun t u₅ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, K.widen u₅.keeps⟩
  · rw [u₅.other .eax (by decide), u₄.other .eax (by decide), u₃.other .eax (by decide),
      u₂.other .eax (by decide), u₁.gpr]
  · rw [u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

end VG.Proof.Bignum.X86
