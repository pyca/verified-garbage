module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeBytes
public import VerifiedGarbage.Proof.Cast5.X86.Run

/-! # The padding string has the requested public length -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.X86
open VG.Proof.Cast5.X86 (wp_countdown)

theorem psStep_ok {s0 s : State} {k : Nat} {acc : List Byte}
    (buf : Buf s0 k) (hl : acc.length < k) (b : Byte) (h : W s0 acc s)
    (value : s.gpr .eax = b.setWidth 32) :
    WP isa (.block psStep) s fun t => W s0 (acc ++ [b]) t ∧ t.gpr .eax = b.setWidth 32 ∧
      t.gpr .ebx = s.gpr .ebx - 1 ∧ t.zf = some (s.gpr .ebx - 1 == 0) ∧
      Keeps [.edi, .ebx] s t := by
  unfold psStep
  have writable : InRegions s.wr (byteAddr (s.gpr .edi)) 1 := by
    rw [h.rest.2.2, h.cursor]
    exact buf.writable acc.length hl
  refine wp_storeByte (a := byteAddr (s.gpr .edi))
    (by change (s.gpr .edi + BitVec.ofNat 32 0).setWidth 64 = _
        simp only [BitVec.add_zero]; rfl) writable fun u U => ?_
  refine wp_addS rfl fun v V _ => ?_
  refine wp_subi fun t T _ zt => WP.block_nil ?_
  have rest : Keeps [.edi, .ebx] s t :=
    (U.keeps _).trans ((V.keeps.mono (by decide)).trans (T.keeps.mono (by decide)))
  refine ⟨⟨h.rest.trans (rest.mono (by decide)), ?_, ?_⟩, ?_, ?_, ?_, rest⟩
  · rw [T.mem, V.mem, U.mem]
    change s.mem.writeW (byteAddr (s.gpr .edi)) ((s.gpr .eax).setWidth 8) = _
    rw [value, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
    rw [h.mem, h.cursor, byteAddr_add (by have := buf.fit; omega)]
    exact (writeBytes_snoc _ _ _ _ (by have := buf.fit; omega)).symm
  · rw [T.other .edi (by decide), V.gpr, U.gpr, h.cursor]
    simp only [List.length_append, List.length_singleton]
    rw [BitVec.add_assoc]
    change s0.gpr .edi + (BitVec.ofNat 32 acc.length + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [T.other .eax (by decide), V.other .eax (by decide), U.gpr, value]
  · rw [T.gpr, V.other .ebx (by decide), U.gpr]
  · rw [zt, V.other .ebx (by decide), U.gpr]

theorem psLoop_ok {s0 s : State} {k n : Nat} {acc : List Byte}
    (buf : Buf s0 k) (hk : k ≤ 1024) (positive : 0 < n) (bound : acc.length + n ≤ k)
    (b : Byte) (h : W s0 acc s) (value : s.gpr .eax = b.setWidth 32)
    (count : s.gpr .ebx = BitVec.ofNat 32 n) :
    WP isa psLoop s fun t => W s0 (acc ++ List.replicate n b) t ∧ Keeps [.edi, .ebx] s t := by
  refine wp_countdown (cnt := .ebx) (by omega) positive
    (fun i t => W s0 (acc ++ List.replicate i b) t ∧ t.gpr .eax = b.setWidth 32 ∧ Keeps [.edi, .ebx] s t)
    ?_ (fun _ h => ⟨h.1, h.2.2⟩) ⟨by simpa using h, value, Keeps.refl _ _⟩ count
  intro i hi t ⟨hw, hv, hr⟩ _
  refine WP.mono (psStep_ok buf (by simp only [List.length_append, List.length_replicate]; omega) b hw hv)
    fun u ⟨hu, vu, cu, zu, ku⟩ => ?_
  exact ⟨⟨by simpa only [List.replicate_succ', ← List.append_assoc] using hu, vu, hr.trans ku⟩, cu, zu⟩

end VG.Proof.RsaPkcs1Sig.X86
