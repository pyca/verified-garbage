module

public import VerifiedGarbage.Impl.Bignum.Arm.ExportBE
public import VerifiedGarbage.Proof.Bignum.Arm.Bases
import VerifiedGarbage.Proof.Bignum.Arm.LoadArray
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Set the source end pointer and output length for I2OSP -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov wp_dp op2_reg op2_imm dpVal)

theorem exportBETail_ok (s : State) {k : Nat} (hk : 0 < k) (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (.block exportBETail) s fun t => t.gpr .r0 = s.gpr .r4 ∧
      t.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (k - 1) ∧ t.gpr .lr = BitVec.ofNat 32 k ∧
      t.gpr .r5 = s.gpr .r0 ∧ t.mem = s.mem ∧ Rest [.r0, .r1, .r5, .lr] s t := by
  unfold exportBETail
  refine wp_mov (op2_reg _ _) fun u a => ?_
  refine wp_mov (op2_reg _ _) fun v b => ?_
  refine wp_dp (op2_reg _ _) fun z c => ?_
  refine wp_dp (op2_imm (by decide)) fun q d => ?_
  refine wp_mov (op2_reg _ _) fun t e => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem))),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans ((c.rest (by simp)).trans
      ((d.rest (by simp)).trans (e.rest (by simp)))))⟩
  · rw [e.gpr, d.other .r4 (by decide), c.other .r4 (by decide), b.other .r4 (by decide), a.other .r4 (by decide)]
  · rw [e.other .r1 (by decide), d.gpr, dpVal, c.gpr, dpVal, b.other .r1 (by decide),
      a.other .r1 (by decide), b.other .r6 (by decide), a.other .r6 (by decide), count]
    change s.gpr .r1 + BitVec.ofNat 32 k - BitVec.ofNat 32 1 = _
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  · rw [e.other .lr (by decide), d.other .lr (by decide), c.other .lr (by decide), b.gpr,
      a.other .r6 (by decide), count]
  · rw [e.other .r5 (by decide), d.other .r5 (by decide), c.other .r5 (by decide), b.other .r5 (by decide), a.gpr]

theorem exportBEArgs_ok (s : State) {base : BitVec 32} {size w o k : Nat}
    {arr : Nat → Nat} {inv : BitVec 32}
    (ws : Workspace s base size) (fit : 128 ≤ size) (header : NativeHeader s.mem base w arr inv)
    (ho : o < 8) (hk : 0 < k) (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o)
    (count : s.gpr .r6 = BitVec.ofNat 32 k) :
    WP isa (.block exportBEArgs) s fun t =>
      t.gpr .r0 = s.gpr .r4 ∧ t.gpr .r1 = base + BitVec.ofNat 32 (arr o) + BitVec.ofNat 32 (k - 1) ∧
      t.gpr .lr = BitVec.ofNat 32 k ∧ t.gpr .r5 = base ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r5, .lr] s t := by
  rw [exportBEArgs, WP.block_append_iff]
  refine WP.mono (loadArray_ok s .r1 .r2 ws (by omega) ptr index (header.array o ho)) ?_
  rintro u ⟨array, mem, rest⟩
  refine WP.mono (exportBETail_ok u hk ((rest.gpr .r6 (by simp)).trans count)) ?_
  rintro t ⟨out, src, countT, saved, memT, keep⟩
  rw [array] at src
  exact ⟨out.trans (rest.gpr .r4 (by simp)), src, countT, saved.trans ((rest.gpr .r0 (by simp)).trans ptr),
    memT.trans mem, (rest.mono (by simp)).trans (keep.mono (by simp))⟩

end VG.Proof.Bignum.Arm
