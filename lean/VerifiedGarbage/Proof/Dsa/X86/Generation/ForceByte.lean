module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.QShape
public import VerifiedGarbage.Proof.Bignum.X86.ByteOps
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Set endpoint bits with one verified byte read and write -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem force_byte {s : State} {r : Reg} {a : Addr} (mask : BitVec 8)
    (ne : r ≠ .eax) (address : s.ea (at_ r 0) = a)
    (read : InRegions (s.rd ++ s.wr) a 1) (write : InRegions s.wr a 1) :
    WP isa (.block (forceByte r mask)) s fun t =>
      t.mem = s.mem.writeW a (s.mem a ||| mask) ∧ Keeps [.eax] s t := by
  unfold forceByte
  refine wp_loadByte address read fun u U => wp_orS rfl fun v V => ?_
  refine wp_storeByte (a := a) ?_ (by rw [V.wr, U.wr]; exact write) fun t T => WP.block_nil ?_
  · change (v.gpr r + BitVec.ofNat 32 0).setWidth 64 = a
    rw [V.other r ne, U.other r ne]
    exact address
  · refine ⟨?_, (U.keeps.trans V.keeps).trans (T.keeps _)⟩
    rw [T.mem]
    change v.mem.writeW a ((v.gpr .eax).setWidth 8) = _
    rw [V.gpr, U.gpr, V.mem, U.mem]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]

end VG.Proof.Dsa.X86.Generation
