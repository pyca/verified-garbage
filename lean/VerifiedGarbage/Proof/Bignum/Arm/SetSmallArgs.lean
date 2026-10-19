module

public import VerifiedGarbage.Impl.Bignum.Arm.SetSmallFn
public import VerifiedGarbage.Proof.Bignum.Arm.Bases
import VerifiedGarbage.Proof.Bignum.Arm.LoadArray
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Read an array pointer and native-word count from the shared header -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov op2_reg op2_imm dpVal)

theorem setSmallTail_ok (s : State) {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : 52 ≤ size) (ptr : s.gpr .r0 = base)
    (width : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa (.block setSmallTail) s fun t =>
      t.gpr .lr = BitVec.ofNat 32 (2 * w) ∧ t.gpr .r3 = 0 ∧ t.gpr .r0 = s.gpr .r4 ∧
      t.mem = s.mem ∧ Rest [.r0, .r3, .lr] s t := by
  have nowrap := ws.nowrap
  unfold setSmallTail
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [ptr]; exact addr_add (by omega)) (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_reg _ _) fun t u4 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u4.other .lr (by decide), u3.other .lr (by decide), u2.gpr, dpVal, u1.gpr, width,
      ← BitVec.ofNat_add, Nat.two_mul]
  · rw [u4.other .r3 (by decide), u3.gpr]
  · rw [u4.gpr, u3.other .r4 (by decide), u2.other .r4 (by decide), u1.other .r4 (by decide)]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
      ((u3.rest (by simp)).trans (u4.rest (by simp))))

theorem setSmallArgs_ok (s : State) {base : BitVec 32} {size w o : Nat} {arr : Nat → Nat} {inv : BitVec 32}
    (ws : Workspace s base size) (fit : 128 ≤ size) (header : NativeHeader s.mem base w arr inv)
    (ho : o < 8) (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o) :
    WP isa (.block setSmallArgs) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 (arr o) ∧ t.gpr .r4 = base + BitVec.ofNat 32 (arr o) ∧
      t.gpr .lr = BitVec.ofNat 32 (2 * w) ∧ t.gpr .r3 = 0 ∧
      t.mem = s.mem ∧ Rest [.r0, .r2, .r3, .r4, .lr] s t := by
  rw [setSmallArgs, WP.block_append_iff]
  refine WP.mono (loadArray_ok s .r4 .r2 ws (by omega) ptr index (header.array o ho)) ?_
  rintro u ⟨array, mem, rest⟩
  refine WP.mono (setSmallTail_ok u (ws.congr rest.wr) (by omega)
    ((rest.gpr .r0 (by simp)).trans ptr) (by rw [mem]; exact header.count)) ?_
  rintro t ⟨count, zero, out, memT, keep⟩
  exact ⟨out.trans array, (keep.gpr .r4 (by simp)).trans array, count, zero, memT.trans mem,
    (rest.mono (by simp)).trans (keep.mono (by simp))⟩

end VG.Proof.Bignum.Arm
