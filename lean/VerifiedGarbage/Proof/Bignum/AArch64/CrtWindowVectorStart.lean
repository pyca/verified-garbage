module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorHead
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorScan
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorClear
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block

/-! Initialize the complete invariant for a 32-row vector scan. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs)

theorem startScan_ok {s : State} {P : Addr} {w b v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 64 * b))
    (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v)) (h24 : s.v .v24 = dup2 1) :
    WP isa (.block (blockHead ++ accs.map fun r => .vop (.movi0 r))) s fun t =>
      t.gpr .x14 = BitVec.ofNat 64 32 ∧
      ScanInv t (off P (slot w 8 + 64 * b)) (8 * (w + 2)) v 0 t ∧
      t.mem = s.mem ∧ Keep [.x16,.x3,.x14] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (blockHead_ok hc ht hp) fun u ⟨⟨h16,h14,hv,hm⟩, ku⟩ => ?_
  refine WP.mono (clearAccs_ok u) fun t ⟨hz, kt⟩ => ?_
  have keep : Keep [] u t := ⟨fun r _ => congrFun kt.gpr r, kt.rd, kt.wr, kt.sp,
    fun r hr => congrArg (fun x : BitVec 128 => x.extractLsb' 0 64)
      (kt.v r ((by decide : ∀ r ∈ preservedV, r ∉ accs) r hr))⟩
  refine ⟨by rw [kt.gpr, h14], ⟨rfl, Keep.refl _ _, ?_, ?_, ?_, ?_, ?_⟩,
    kt.mem.trans hm, (ku.trans keep).mono (by decide)⟩
  · simpa only [Nat.mul_zero, BitVec.add_zero, kt.gpr] using h16
  · rw [kt.v .v23 (by decide), hv, RegUpd.v_setV_self]
    rfl
  · rw [kt.v .v22 (by decide), hv, RegUpd.v_setV_of_ne _ _ (by decide)]
    exact h22
  · rw [kt.v .v24 (by decide), hv, RegUpd.v_setV_of_ne _ _ (by decide)]
    exact h24
  · intro i hi
    simpa only [Nat.not_lt_zero, ite_false] using hz i hi

end VG.Proof.Bignum.AArch64.WindowVector
