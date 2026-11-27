module

public import VerifiedGarbage.Proof.Bignum.Arm.MontInit
public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

/-! ### `Bignum.Arm.BasesTail`, which this module and modules that import it used -/

section

/-! # Recover Montgomery's fixed pointers and double the RSA word count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp op2_reg dpVal)

theorem basesTail_ok (s : State) {base : BitVec 32} {size out tmp a b mod acc w : Nat} {inv : BitVec 32}
    (ws : Workspace s base size) (fit : 92 ≤ size) (ptr : s.gpr .r0 = base)
    (pa : s.gpr .r8 = base + BitVec.ofNat 32 a) (pb : s.gpr .r9 = base + BitVec.ofNat 32 b)
    (po : s.gpr .r10 = base + BitVec.ofNat 32 out)
    (mt : s.mem.readW (off (State.addr base) 88) 32 = base + BitVec.ofNat 32 tmp)
    (mc : s.mem.readW (off (State.addr base) 80) 32 = base + BitVec.ofNat 32 acc)
    (mw : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (mm : s.mem.readW (off (State.addr base) 64) 32 = base + BitVec.ofNat 32 mod)
    (mi : s.mem.readW (off (State.addr base) 56) 32 = inv) :
    WP isa (.block MontFn.basesTail) s fun t =>
      InitRegs t base out tmp a b mod acc (2 * w) inv ∧ t.mem = s.mem ∧
      Rest [.r5, .r6, .r7, .r11, .r12] s t := by
  have p0 : s.gpr .r0 = base + BitVec.ofNat 32 0 := by simpa using ptr
  unfold MontFn.basesTail
  refine wp_ldr (by decide) (ws.ea p0 (by omega_using [fit])) (ws.read (by omega_using [fit])) fun s1 u1 => ?_
  have p1 := (u1.other .r0 (by decide)).trans p0
  have w1 := ws.congr u1.wr
  refine wp_ldr (by decide) (w1.ea p1 (by omega_using [fit])) (w1.read (by omega_using [fit])) fun s2 u2 => ?_
  have p2 := (u2.other .r0 (by decide)).trans p1
  have w2 := w1.congr u2.wr
  refine wp_ldr (by decide) (w2.ea p2 (by omega_using [fit])) (w2.read (by omega_using [fit])) fun s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  have p4 := (u4.other .r0 (by decide)).trans ((u3.other .r0 (by decide)).trans p2)
  have w4 := (w2.congr u3.wr).congr u4.wr
  refine wp_ldr (by decide) (w4.ea p4 (by omega_using [fit])) (w4.read (by omega_using [fit])) fun s5 u5 => ?_
  have p5 := (u5.other .r0 (by decide)).trans p4
  have w5 := w4.congr u5.wr
  refine wp_ldr (by decide) (w5.ea p5 (by omega_using [fit])) (w5.read (by omega_using [fit])) fun t u6 => WP.block_nil ?_
  have keep : Rest [.r5, .r6, .r7, .r11, .r12] s t :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  refine ⟨⟨?_, ?_, ?_, (keep.gpr .r8 (by decide)).trans pa, (keep.gpr .r9 (by decide)).trans pb,
    (keep.gpr .r10 (by decide)).trans po, ?_, ?_⟩, ?_, keep⟩
  · rw [u6.other .r5 (by decide), u5.other .r5 (by decide), u4.other .r5 (by decide),
      u3.other .r5 (by decide), u2.other .r5 (by decide), u1.gpr, mt]
  · rw [u6.other .r6 (by decide), u5.other .r6 (by decide), u4.other .r6 (by decide),
      u3.other .r6 (by decide), u2.gpr, u1.mem, mc]
  · rw [u6.other .r7 (by decide), u5.other .r7 (by decide), u4.gpr, dpVal, u3.gpr, u2.mem, u1.mem, mw]
    rw [← BitVec.ofNat_add, show w + w = 2 * w by omega_using []]
  · rw [u6.other .r11 (by decide), u5.gpr, u4.mem, u3.mem, u2.mem, u1.mem, mm]
  · rw [u6.gpr, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, mi]
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.LoadArray`, which this module and modules that import it used -/

section

/-! # Load an array pointer using a public RSA array index -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_dp wp_ldr op2_lsl dpVal)

theorem loadArray_ok (s : State) (d i : Reg) {base : BitVec 32} {size j a : Nat}
    (ws : Workspace s base size) (fit : 64 + 8 * j + 4 ≤ size)
    (ptr : s.gpr .r0 = base) (index : s.gpr i = BitVec.ofNat 32 j)
    (header : s.mem.readW (off (State.addr base) (64 + 8 * j)) 32 = base + BitVec.ofNat 32 a) :
    WP isa (.block (MontFn.loadArray d i)) s fun t =>
      t.gpr d = base + BitVec.ofNat 32 a ∧ t.mem = s.mem ∧ Rest [i, d] s t := by
  have nowrap := ws.nowrap
  have shift : BitVec.ofNat 32 j <<< 3 = BitVec.ofNat 32 (8 * j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega_using [fit, nowrap] : j < 2 ^ 32)]
    congr 1
    omega_using []
  unfold MontFn.loadArray
  refine wp_dp (op2_lsl (by decide)) fun u hu => ?_
  have pu : u.gpr i = base + BitVec.ofNat 32 (8 * j) := by
    rw [hu.gpr, dpVal, ptr, index, shift]
  have wu := ws.congr hu.wr
  refine wp_ldr (by decide) (wu.ea pu (by omega_using [fit])) (wu.read (by omega_using [fit])) fun t ht => WP.block_nil ?_
  refine ⟨?_, ht.mem.trans hu.mem, (hu.rest (by simp)).trans (ht.rest (by simp))⟩
  rw [ht.gpr, hu.mem, show 8 * j + 64 = 64 + 8 * j by omega_using [], header]

end VG.Proof.Bignum.Arm

end

end

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
  refine WP.mono (loadArray_ok s .r10 .r2 ws (by omega_using [fit, ho]) ptr po (header.array o ho)) ?_
  rintro s1 ⟨o1, m1, k1⟩
  have w1 := ws.congr k1.wr
  have p1 := (k1.gpr .r0 (by decide)).trans ptr
  rw [WP.block_append_iff]
  refine WP.mono (loadArray_ok s1 .r8 .r3 w1 (by omega_using [fit, ha]) p1
    ((k1.gpr .r3 (by decide)).trans pa) (by rw [m1]; exact header.array a ha)) ?_
  rintro s2 ⟨a2, m2, k2⟩
  have w2 := w1.congr k2.wr
  have p2 := (k2.gpr .r0 (by decide)).trans p1
  rw [WP.block_append_iff]
  refine WP.mono (loadArray_ok s2 .r9 .r12 w2 (by omega_using [fit, hb]) p2
    ((k2.gpr .r12 (by decide)).trans ((k1.gpr .r12 (by decide)).trans pb))
    (by rw [m2, m1]; exact header.array b hb)) ?_
  rintro s3 ⟨b3, m3, k3⟩
  have w3 := w2.congr k3.wr
  have p3 := (k3.gpr .r0 (by decide)).trans p2
  refine WP.mono (basesTail_ok s3 (tmp := arr 3) (acc := arr 2) (mod := arr 0) (w := w) (inv := inv) w3 (by omega_using [fit]) p3
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
