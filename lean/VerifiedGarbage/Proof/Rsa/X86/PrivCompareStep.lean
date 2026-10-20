module

public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.ByteOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # One byte-pair comparison preserves memory and accumulates all mismatches -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Impl.Rsa.X86.PrivChecked

theorem compareStep_ok (s : State) (a b : Addr)
    (pa : s.ea ⟨.esi, 0⟩ = a) (pb : s.ea ⟨.edi, 0⟩ = b)
    (ra : InRegions (s.rd ++ s.wr) a 1) (rb : InRegions (s.rd ++ s.wr) b 1) :
    WP isa (.block compareStep) s fun t => t.mem = s.mem ∧
      t.gpr .esi = s.gpr .esi + 1 ∧ t.gpr .edi = s.gpr .edi + 1 ∧
      t.gpr .ebp = s.gpr .ebp ||| ((s.mem a).setWidth 32 ^^^ (s.mem b).setWidth 32) ∧
      t.gpr .ecx = s.gpr .ecx - 1 ∧ t.zf = some (s.gpr .ecx - 1 == 0) ∧
      Keeps [.esi, .edi, .ebp, .eax, .edx, .ecx] s t := by
  unfold compareStep
  refine wp_loadByte pa ra fun s1 U1 => ?_
  refine wp_loadByte (a := b)
    (by change (s1.gpr .edi + BitVec.ofNat 32 0).setWidth 64 = b
        rw [U1.other .edi (by decide)]; exact pb)
    (by rw [U1.rd, U1.wr]; exact rb) fun s2 U2 => ?_
  refine wp_logicS (.inr rfl) rfl fun s3 U3 => ?_
  refine wp_orS rfl fun s4 U4 => ?_
  refine wp_addS rfl fun s5 U5 _ => ?_
  refine wp_addS rfl fun s6 U6 _ => ?_
  refine wp_subS rfl fun s7 U7 _ => ?_
  refine wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨T.mem.trans (U7.mem.trans (U6.mem.trans (U5.mem.trans (U4.mem.trans
    (U3.mem.trans (U2.mem.trans U1.mem)))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [T.gpr, U7.other .esi (by decide), U6.other .esi (by decide), U5.gpr,
      U4.other .esi (by decide), U3.other .esi (by decide), U2.other .esi (by decide), U1.other .esi (by decide)]
  · rw [T.gpr, U7.other .edi (by decide), U6.gpr, U5.other .edi (by decide),
      U4.other .edi (by decide), U3.other .edi (by decide), U2.other .edi (by decide), U1.other .edi (by decide)]
  · rw [T.gpr, U7.other .ebp (by decide), U6.other .ebp (by decide), U5.other .ebp (by decide), U4.gpr,
      U3.other .ebp (by decide), U2.other .ebp (by decide), U1.other .ebp (by decide),
      U3.gpr, U2.other .eax (by decide), U1.gpr, U2.gpr, U1.mem, ite_eq_right (by decide)]
  · rw [T.gpr, U7.gpr, U6.other .ecx (by decide), U5.other .ecx (by decide), U4.other .ecx (by decide),
      U3.other .ecx (by decide), U2.other .ecx (by decide), U1.other .ecx (by decide)]
  · rw [Z, U7.gpr, U6.other .ecx (by decide), U5.other .ecx (by decide), U4.other .ecx (by decide),
      U3.other .ecx (by decide), U2.other .ecx (by decide), U1.other .ecx (by decide)]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  · exact (U1.keeps.mono (by decide)).trans ((U2.keeps.mono (by decide)).trans
      ((U3.keeps.mono (by decide)).trans ((U4.keeps.mono (by decide)).trans
      ((U5.keeps.mono (by decide)).trans ((U6.keeps.mono (by decide)).trans
      ((U7.keeps.mono (by decide)).trans (T.keeps _)))))))

end VG.Proof.Rsa.X86.PrivChecked
