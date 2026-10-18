module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Encode
public import VerifiedGarbage.Proof.RsaPkcs1Enc.ByteZero
public import VerifiedGarbage.Proof.Bignum.X86.ByteOps

/-! # Copy one encryption padding byte and accumulate its zero test -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.RsaPkcs1Enc.X86

theorem psStep_ok (s : State) (src dst : Addr)
    (ps : s.ea ⟨.esi, 0⟩ = src) (pd : s.ea ⟨.edi, 0⟩ = dst)
    (read : InRegions (s.rd ++ s.wr) src 1) (write : InRegions s.wr dst 1) :
    WP isa (.block psStep) s fun t =>
      t.mem = s.mem.writeW dst (s.mem src) ∧ t.gpr .esi = s.gpr .esi + 1 ∧
      t.gpr .edi = s.gpr .edi + 1 ∧ t.gpr .ebp = s.gpr .ebp - 1 ∧
      t.gpr .ebx = s.gpr .ebx ||| BitVec.ofNat 32 (decide (s.mem src = 0)).toNat ∧
      t.zf = some (s.gpr .ebp - 1 == 0) ∧ Keeps [.eax, .ebx, .esi, .edi, .ebp] s t := by
  unfold psStep
  refine wp_loadByte ps read fun a A => ?_
  refine wp_storeByte (a := dst)
    (by change (a.gpr .edi + BitVec.ofNat 32 0).setWidth 64 = dst
        rw [A.other .edi (by decide)]; exact pd)
    (by rw [A.wr]; exact write) fun b B => ?_
  refine wp_subS rfl fun c C _ => ?_
  refine wp_shr (by decide) fun d D _ => ?_
  refine wp_orS rfl fun e E => ?_
  refine wp_addS rfl fun f F _ => ?_
  refine wp_addS rfl fun g G _ => ?_
  refine wp_subi fun t T _ Z => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [T.mem, G.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]
    change s.mem.writeW dst ((a.gpr .eax).setWidth 8) = _
    rw [A.gpr, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
  · rw [T.other .esi (by decide), G.other .esi (by decide), F.gpr,
      E.other .esi (by decide), D.other .esi (by decide), C.other .esi (by decide), B.gpr, A.other .esi (by decide)]
  · rw [T.other .edi (by decide), G.gpr, F.other .edi (by decide), E.other .edi (by decide),
      D.other .edi (by decide), C.other .edi (by decide), B.gpr, A.other .edi (by decide)]
  · rw [T.gpr, G.other .ebp (by decide), F.other .ebp (by decide), E.other .ebp (by decide),
      D.other .ebp (by decide), C.other .ebp (by decide), B.gpr, A.other .ebp (by decide)]
  · rw [T.other .ebx (by decide), G.other .ebx (by decide), F.other .ebx (by decide), E.gpr,
      D.other .ebx (by decide), C.other .ebx (by decide), B.gpr, A.other .ebx (by decide),
      D.gpr, C.gpr, B.gpr, A.gpr, VG.Proof.RsaPkcs1Enc.byte_zero32]
  · rw [Z, G.other .ebp (by decide), F.other .ebp (by decide), E.other .ebp (by decide),
      D.other .ebp (by decide), C.other .ebp (by decide), B.gpr, A.other .ebp (by decide)]
  · exact (A.keeps.mono (by decide)).trans ((B.keeps _).trans ((C.keeps.mono (by decide)).trans
      ((D.keeps.mono (by decide)).trans ((E.keeps.mono (by decide)).trans ((F.keeps.mono (by decide)).trans
      ((G.keeps.mono (by decide)).trans (T.keeps.mono (by decide))))))))

end VG.Proof.RsaPkcs1Enc.X86
