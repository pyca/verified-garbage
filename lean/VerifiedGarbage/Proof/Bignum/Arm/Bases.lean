module
public import VerifiedGarbage.Proof.Bignum.Arm.MontInit
public import VerifiedGarbage.Impl.Bignum.Arm.MontFn

import VerifiedGarbage.Proof.Bignum.Arm.LoadArray
import VerifiedGarbage.Proof.Bignum.Arm.BasesTail
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Native register arguments from RSA's public indices and workspace header -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure NativeHeader (mem : Mem) (base : BitVec 32) (w : Nat) (arr : Nat → Nat) (inv : BitVec 32) : Prop where
  count : mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w
  inverse : mem.readW (off (State.addr base) 56) 32 = inv
  array : ∀ j < 8, mem.readW (off (State.addr base) (64 + 8 * j)) 32 = base + BitVec.ofNat 32 (arr j)

theorem bases_ok (s : State) {base : BitVec 32} {size w o a b : Nat} {arr : Nat → Nat} {inv : BitVec 32}
    (ws : Workspace s base size) (fit : 128 ≤ size) (header : NativeHeader s.mem base w arr inv)
    (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ptr : s.gpr .r0 = base) (po : s.gpr .r2 = BitVec.ofNat 32 o)
    (pa : s.gpr .r3 = BitVec.ofNat 32 a) (pb : s.gpr .r12 = BitVec.ofNat 32 b) :
    WP isa (.block MontFn.bases) s fun t =>
      InitRegs t base (arr o) (arr 3) (arr a) (arr b) (arr 0) (arr 2) (2 * w) inv ∧
      t.mem = s.mem ∧ Rest roundClobbers s t := by
  unfold MontFn.bases
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadArray_ok s .r10 .r2 ws (by omega) ptr po (header.array o ho)) ?_
  rintro s1 ⟨o1, m1, k1⟩
  have w1 := ws.congr k1.wr
  have p1 := (k1.gpr .r0 (by decide)).trans ptr
  rw [WP.block_append_iff]
  refine WP.mono (loadArray_ok s1 .r8 .r3 w1 (by omega) p1
    ((k1.gpr .r3 (by decide)).trans pa) (by rw [m1]; exact header.array a ha)) ?_
  rintro s2 ⟨a2, m2, k2⟩
  have w2 := w1.congr k2.wr
  have p2 := (k2.gpr .r0 (by decide)).trans p1
  rw [WP.block_append_iff]
  refine WP.mono (loadArray_ok s2 .r9 .r12 w2 (by omega) p2
    ((k2.gpr .r12 (by decide)).trans ((k1.gpr .r12 (by decide)).trans pb))
    (by rw [m2, m1]; exact header.array b hb)) ?_
  rintro s3 ⟨b3, m3, k3⟩
  have w3 := w2.congr k3.wr
  have p3 := (k3.gpr .r0 (by decide)).trans p2
  refine WP.mono (basesTail_ok s3 (tmp := arr 3) (acc := arr 2) (mod := arr 0) (w := w) (inv := inv) w3 (by omega) p3
    ((k3.gpr .r8 (by decide)).trans a2) b3
    ((k3.gpr .r10 (by decide)).trans ((k2.gpr .r10 (by decide)).trans o1)) ?_ ?_ ?_ ?_ ?_) ?_
  · rw [m3, m2, m1]; exact header.array 3 (by decide)
  · rw [m3, m2, m1]; exact header.array 2 (by decide)
  · rw [m3, m2, m1]; exact header.count
  · rw [m3, m2, m1]; exact header.array 0 (by decide)
  · rw [m3, m2, m1]; exact header.inverse
  · rintro t ⟨regs, mem, keep⟩
    exact ⟨regs, mem.trans (m3.trans (m2.trans m1)),
      (k1.mono (by decide)).trans ((k2.mono (by decide)).trans
        ((k3.mono (by decide)).trans (keep.mono (by decide))))⟩

end VG.Proof.Bignum.Arm
