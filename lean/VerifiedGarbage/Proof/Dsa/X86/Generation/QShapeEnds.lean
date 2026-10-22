module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ForceByte
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Set the first candidate byte's top bit and the last byte's low bit -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem q_shape_ends {s : State} {dst : BitVec 32} {n : Nat}
    (hn : 2 ≤ n) (fit : dst.toNat + n ≤ 2 ^ 32)
    (first : s.gpr .ebp = dst) (past : s.gpr .ebx = dst + BitVec.ofNat 32 n)
    (read0 : InRegions (s.rd ++ s.wr) (byteAddr dst) 1)
    (readLast : InRegions (s.rd ++ s.wr) (off (byteAddr dst) (n - 1)) 1)
    (write0 : InRegions s.wr (byteAddr dst) 1)
    (writeLast : InRegions s.wr (off (byteAddr dst) (n - 1)) 1) :
    WP isa (.seq (.block (forceByte .ebp 128))
      (.block ([.alu .sub .ebx (.imm 1)] ++ forceByte .ebx 1))) s fun t =>
      t.mem = (s.mem.writeW (byteAddr dst) (s.mem (byteAddr dst) ||| (128 : BitVec 8))).writeW
        (off (byteAddr dst) (n - 1)) (s.mem (off (byteAddr dst) (n - 1)) ||| (1 : BitVec 8)) ∧
      Keeps [.eax, .ebx] s t := by
  have address : s.ea (at_ .ebp 0) = byteAddr dst := by
    simp only [State.ea, at_, BitVec.add_zero, first, byteAddr]
  refine WP.seq (WP.mono (force_byte (r := .ebp) 128 (by decide) address read0 write0) ?_)
  rintro u ⟨memory, K⟩
  refine wp_subS rfl fun v V _ => ?_
  have lastPtr : v.gpr .ebx = dst + BitVec.ofNat 32 (n - 1) := by
    rw [V.gpr, K.1 .ebx (by decide), past, BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  have lastAddress : v.ea (at_ .ebx 0) = off (byteAddr dst) (n - 1) := by
    simp only [State.ea, at_, BitVec.add_zero, lastPtr]
    exact byteAddr_add (by omega)
  refine WP.mono (force_byte (r := .ebx) 1 (by decide) lastAddress
    (by rw [V.rd, V.wr, K.2.1, K.2.2]; exact readLast)
    (by rw [V.wr, K.2.2]; exact writeLast)) ?_
  rintro t ⟨lastMemory, L⟩
  refine ⟨?_, ((K.mono (by decide)).trans (V.keeps.mono (by decide))).trans (L.mono (by decide))⟩
  rw [lastMemory, V.mem, memory]
  rw [WriteBytes.writeW8_apply, ite_eq_right ?_]
  simpa only [off, BitVec.add_zero] using Offset.add_ofNat_ne (byteAddr dst)
    (by omega : n - 1 < 2 ^ 64) (by decide : 0 < 2 ^ 64) (by omega : n - 1 ≠ 0)

end VG.Proof.Dsa.X86.Generation
