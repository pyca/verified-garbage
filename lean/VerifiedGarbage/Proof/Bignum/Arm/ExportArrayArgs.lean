module

public import VerifiedGarbage.Impl.Bignum.Arm.ExportArray
public import VerifiedGarbage.Proof.Bignum.Arm.Bases
import VerifiedGarbage.Proof.Bignum.Arm.LoadArray
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Address and byte-count setup for RSA array export -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov op2_reg op2_lsl)

theorem exportArrayTail_ok (s : State) {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : 52 ≤ size) (ptr : s.gpr .r0 = base)
    (width : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa (.block exportArrayTail) s fun t =>
      t.gpr .lr = BitVec.ofNat 32 (8 * w) ∧ t.gpr .r5 = base ∧ t.gpr .r0 = s.gpr .r4 ∧
      t.mem = s.mem ∧ Rest [.r0, .r5, .lr] s t := by
  unfold exportArrayTail
  refine wp_mov (op2_reg _ _) fun u h => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [h.other .r0 (by decide), ptr]; exact addr_add (by have := ws.nowrap; omega))
    (by rw [h.rd, h.wr]; exact ws.read fit) fun v j => ?_
  refine wp_mov (op2_lsl (by decide)) fun z l => ?_
  refine wp_mov (op2_reg _ _) fun t q => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, q.mem.trans (l.mem.trans (j.mem.trans h.mem)),
    (h.rest (by decide)).trans ((j.rest (by decide)).trans ((l.rest (by decide)).trans (q.rest (by decide))))⟩
  · rw [q.other .lr (by decide), l.gpr, j.gpr, h.mem, width, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 w * BitVec.ofNat 32 8 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  · rw [q.other .r5 (by decide), l.other .r5 (by decide), j.other .r5 (by decide), h.gpr, ptr]
  · rw [q.gpr, l.other .r4 (by decide), j.other .r4 (by decide), h.other .r4 (by decide)]

theorem exportArrayArgs_ok (s : State) {base : BitVec 32} {size w o : Nat}
    {arr : Nat → Nat} {inv : BitVec 32}
    (ws : Workspace s base size) (fit : 128 ≤ size) (header : NativeHeader s.mem base w arr inv)
    (ho : o < 8) (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o) :
    WP isa (.block exportArrayArgs) s fun t =>
      t.gpr .r0 = s.gpr .r4 ∧ t.gpr .r1 = base + BitVec.ofNat 32 (arr o) ∧
      t.gpr .lr = BitVec.ofNat 32 (8 * w) ∧ t.gpr .r5 = base ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r5, .lr] s t := by
  rw [exportArrayArgs, WP.block_append_iff]
  refine WP.mono (loadArray_ok s .r1 .r2 ws (by omega) ptr index (header.array o ho)) ?_
  rintro u ⟨array, mem, rest⟩
  refine WP.mono (exportArrayTail_ok u (ws.congr rest.wr) (by omega)
    ((rest.gpr .r0 (by decide)).trans ptr) (by rw [mem]; exact header.count)) ?_
  rintro t ⟨count, saved, out, memT, keep⟩
  exact ⟨out.trans (rest.gpr .r4 (by decide)), (keep.gpr .r1 (by decide)).trans array,
    count, saved, memT.trans mem, (rest.mono (by decide)).trans (keep.mono (by decide))⟩

end VG.Proof.Bignum.Arm
