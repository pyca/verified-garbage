module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Encode
public import VerifiedGarbage.Proof.Bignum.X86.ByteOps

/-! # Mask one ciphertext byte with the branchless padding-validity mask -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.RsaPkcs1Enc.X86

theorem maskStep_ok (s : State) (p : Addr)
    (ptr : s.ea ⟨.esi, 0⟩ = p) (write : InRegions s.wr p 1) :
    WP isa (.block maskStep) s fun t =>
      t.mem = s.mem.writeW p (s.mem p &&& (s.gpr .edx).setWidth 8) ∧
      t.gpr .esi = s.gpr .esi + 1 ∧ t.gpr .ecx = s.gpr .ecx - 1 ∧
      t.zf = some (s.gpr .ecx - 1 == 0) ∧ Keeps [.eax, .esi, .ecx] s t := by
  unfold maskStep
  have read : InRegions (s.rd ++ s.wr) p 1 := by
    obtain ⟨r, hr, hc⟩ := write
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine wp_loadByte ptr read fun a A => ?_
  refine wp_logicS (Or.inl rfl) rfl fun b B => ?_
  refine wp_storeByte (a := p)
    (by change (b.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = p
        rw [B.other .esi (by decide), A.other .esi (by decide)]; exact ptr)
    (by rw [B.wr, A.wr]; exact write) fun c C => ?_
  refine wp_addS rfl fun d D _ => ?_
  refine wp_subi fun t T _ Z => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [T.mem, D.mem, C.mem, B.mem, A.mem]
    change s.mem.writeW p ((b.gpr .eax).setWidth 8) = _
    rw [B.gpr, A.gpr, A.other .edx (by decide)]
    simp only [ite_true, BitVec.setWidth_and,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
  · rw [T.other .esi (by decide), D.gpr, C.gpr, B.other .esi (by decide), A.other .esi (by decide)]
  · rw [T.gpr, D.other .ecx (by decide), C.gpr, B.other .ecx (by decide), A.other .ecx (by decide)]
  · rw [Z, D.other .ecx (by decide), C.gpr, B.other .ecx (by decide), A.other .ecx (by decide)]
  · exact (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans
      ((C.keeps _).trans ((D.keeps.mono (by decide)).trans (T.keeps.mono (by decide)))))

end VG.Proof.RsaPkcs1Enc.X86
