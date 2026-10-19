module

public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.ByteOps
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # A released byte is masked and its private temporary is immediately cleared -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Impl.Rsa.X86.PrivChecked

theorem releaseStep_ok (s : State) (src dst : Addr)
    (ps : s.ea ⟨.esi, 0⟩ = src) (pd : s.ea ⟨.edi, 0⟩ = dst)
    (readable : InRegions (s.rd ++ s.wr) src 1)
    (writable : InRegions s.wr dst 1) (clearable : InRegions s.wr src 1) :
    WP isa (.block releaseStep) s fun t =>
      t.mem = (s.mem.writeW dst (s.mem src &&& (s.gpr .edx).setWidth 8)).writeW src (0 : Byte) ∧
      t.gpr .edi = s.gpr .edi + 1 ∧ t.gpr .esi = s.gpr .esi + 1 ∧
      t.gpr .ecx = s.gpr .ecx - 1 ∧ t.zf = some (s.gpr .ecx - 1 == 0) ∧
      Keeps [.eax, .esi, .edi, .ecx] s t := by
  unfold releaseStep
  refine wp_loadByte ps readable fun a A => ?_
  refine wp_logicS (.inl rfl) rfl fun b B => ?_
  refine wp_storeByte (a := dst)
    (by change (b.gpr .edi + BitVec.ofNat 32 0).setWidth 64 = dst
        rw [B.other .edi (by decide), A.other .edi (by decide)]; exact pd)
    (by rw [B.wr, A.wr]; exact writable) fun c C => ?_
  refine wp_movS rfl fun d D _ => ?_
  refine wp_storeByte (a := src)
    (by change (d.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = src
        rw [D.other .esi (by decide), C.gpr, B.other .esi (by decide), A.other .esi (by decide)]; exact ps)
    (by rw [D.wr, C.wr, B.wr, A.wr]; exact clearable) fun e E => ?_
  refine wp_addS rfl fun f F _ => ?_
  refine wp_addS rfl fun g G _ => ?_
  refine wp_subS rfl fun h H _ => ?_
  refine wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [T.mem, H.mem, G.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]
    change (s.mem.writeW dst ((b.gpr .eax).setWidth 8)).writeW src ((d.gpr .eax).setWidth 8) = _
    rw [D.gpr, B.gpr, A.gpr, A.other .edx (by decide), ite_eq_left rfl, BitVec.setWidth_and,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
    rfl
  · rw [T.gpr, H.other .edi (by decide), G.gpr, F.other .edi (by decide), E.gpr,
      D.other .edi (by decide), C.gpr, B.other .edi (by decide), A.other .edi (by decide)]
  · rw [T.gpr, H.other .esi (by decide), G.other .esi (by decide), F.gpr, E.gpr,
      D.other .esi (by decide), C.gpr, B.other .esi (by decide), A.other .esi (by decide)]
  · rw [T.gpr, H.gpr, G.other .ecx (by decide), F.other .ecx (by decide), E.gpr,
      D.other .ecx (by decide), C.gpr, B.other .ecx (by decide), A.other .ecx (by decide)]
  · rw [Z, H.gpr, G.other .ecx (by decide), F.other .ecx (by decide), E.gpr,
      D.other .ecx (by decide), C.gpr, B.other .ecx (by decide), A.other .ecx (by decide)]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  · exact (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans ((C.keeps _).trans
      ((D.keeps.mono (by decide)).trans ((E.keeps _).trans ((F.keeps.mono (by decide)).trans
      ((G.keeps.mono (by decide)).trans ((H.keeps.mono (by decide)).trans (T.keeps _))))))))

end VG.Proof.Rsa.X86.PrivChecked
