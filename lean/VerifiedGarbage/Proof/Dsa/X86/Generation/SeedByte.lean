module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SeedAdd
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.RandomScan

/-! # Carry propagation for one wrapped-seed byte on i686 -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86

theorem seedAddByte_ok {s : State} {rp op : BitVec 32} {i carry : Nat} {b : Byte}
    (hc : carry < 2 ^ 24) (hrp : s.gpr .esi = rp) (hop : s.gpr .edi = op)
    (hrfit : rp.toNat + i < 2 ^ 32) (hofit : op.toNat + i < 2 ^ 32)
    (hcarry : s.gpr .eax = BitVec.ofNat 32 carry)
    (hrd : InRegions (s.rd ++ s.wr) (off (rp.setWidth 64) i) 1)
    (hwr : InRegions s.wr (off (op.setWidth 64) i) 1)
    (hb : s.mem (off (rp.setWidth 64) i) = b) :
    WP isa (.block (Impl.Dsa.X86.Generation.seedAddByte i)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 ((b.toNat + carry) / 256) ∧
      t.mem = s.mem.writeW (off (op.setWidth 64) i) (BitVec.ofNat 8 (b.toNat + carry)) ∧
      Keeps [.eax, .ecx] s t := by
  have hbfit := b.isLt
  have src : s.ea (at_ .esi i) = off (rp.setWidth 64) i := by
    change (s.gpr .esi + BitVec.ofNat 32 i).setWidth 64 = _
    rw [hrp]; exact addr_eq hrfit
  unfold Impl.Dsa.X86.Generation.seedAddByte
  refine wp_load8 src hrd fun u su _ _ => wp_addS rfl fun v uv _ => ?_
  have val : v.gpr .eax = BitVec.ofNat 32 (b.toNat + carry) := by
    rw [uv.gpr, su.other _ (by decide), hcarry, su.gpr, hb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    omega
  have dst : v.ea (at_ .edi i) = off (op.setWidth 64) i := by
    change (v.gpr .edi + BitVec.ofNat 32 i).setWidth 64 = _
    rw [uv.other _ (by decide), su.other _ (by decide), hop]; exact addr_eq hofit
  refine wp_store8 dst (by rw [uv.wr, su.wr]; exact hwr) fun w vw =>
    wp_shr (by decide) fun t wt _ => WP.block_nil ?_
  have mem : t.mem = s.mem.writeW (off (op.setWidth 64) i) (BitVec.ofNat 8 (b.toNat + carry)) := by
    rw [wt.mem, vw.mem, show Reg8.al.reg = Reg.eax from rfl, val, uv.mem, su.mem]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  refine ⟨?_, mem, (((su.keeps.mono (by decide)).trans (uv.keeps.mono (by decide))).trans
    (vw.keeps _)).trans (wt.keeps.mono (by decide))⟩
  rw [wt.gpr, vw.gpr, val]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega
end VG.Proof.Dsa.X86.Generation
