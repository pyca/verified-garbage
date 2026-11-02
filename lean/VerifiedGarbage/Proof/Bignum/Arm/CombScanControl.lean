module

public import VerifiedGarbage.Impl.Bignum.Arm.CombScan
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.WindowCtl
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! The dense comb scan changes only its two public cursor words. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombScan
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov wp_str wp_cmp op2_reg op2_imm op2_lsl op2_lsr dpVal)

private theorem mask32 : ∀ d<32, ∀ j<32,
    ((BitVec.ofNat 32 d ^^^ BitVec.ofNat 32 j)-1)>>>31 = if d=j then (1:BitVec 32) else 0 := by
  decide +kernel

private theorem index32 : ∀ j<32,
    (BitVec.ofNat 32 (j+1)-32 == 0)=decide (j+1=32) := by
  decide +kernel

private theorem stride_value (w : Nat) :
    BitVec.ofNat 32 w <<< 3=BitVec.ofNat 32 (8*w) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 32 w * BitVec.ofNat 32 8=_
  rw [←BitVec.ofNat_mul,Nat.mul_comm]

theorem bit_ok (s : State) {base : BitVec 32} {len w d j : Nat}
    (h : ArithmeticReady base len w s) (hd : d < 32) (hj : j < 32)
    (digit : s.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 d)
    (index : s.mem.readW (off (State.addr base) 228) 32 = BitVec.ofNat 32 j) :
    WP isa (.block scanBit) s fun t =>
      t.gpr .r11 = (if d = j then 1 else 0) ∧ t.mem = s.mem ∧ Rest [.r1, .r2, .r11] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have addr (d : Nat) (hd : d + 4 ≤ 8 * len) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega)
  unfold scanBit
  refine wp_ldr (a := off (State.addr base) 196) (by decide) (addr 196 (by omega))
    (h.workspace.read (by omega)) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) 228) (by decide)
    (by rw [a.other .r0 (by decide)]; exact addr 228 (by omega))
    (by rw [a.rd, a.wr]; exact h.workspace.read (by omega)) fun v b => ?_
  refine wp_dp (op2_reg _ _) fun z c => ?_
  refine wp_dp (op2_imm (by decide)) fun q e => ?_
  refine wp_mov (op2_lsr (by decide)) fun t f => WP.block_nil ?_
  refine ⟨?_, f.mem.trans (e.mem.trans (c.mem.trans (b.mem.trans a.mem))),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans ((c.rest (by simp)).trans
      ((e.rest (by simp)).trans (f.rest (by simp)))))⟩
  rw [f.gpr, e.gpr, dpVal, c.gpr, dpVal, b.other .r1 (by decide), a.gpr, digit, b.gpr, a.mem, index]
  exact mask32 d hd j hj

theorem next_ok (s : State) {base table : BitVec 32} {len w j : Nat}
    (h : ArithmeticReady base len w s) (hj : j < 32)
    (entry : s.mem.readW (off (State.addr base) 220) 32 = table + BitVec.ofNat 32 (8*w*j))
    (index : s.mem.readW (off (State.addr base) 228) 32 = BitVec.ofNat 32 j) :
    WP isa (.block VG.Impl.Bignum.Arm.CombScan.next) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr base) 220)
        (table + BitVec.ofNat 32 (8*w*(j+1)))).writeW
          (off (State.addr base) 228) (BitVec.ofNat 32 (j + 1)) ∧
      t.z = decide (j + 1 = 32) ∧ Rest [.r1, .r2] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have addr (d : Nat) (hd : d + 4 ≤ 8 * len) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega)
  unfold VG.Impl.Bignum.Arm.CombScan.next
  refine wp_ldr (a := off (State.addr base) 220) (by decide) (addr 220 (by omega))
    (h.workspace.read (by omega)) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [a.other .r0 (by decide)]; exact addr 48 (by omega))
    (by rw [a.rd, a.wr]; exact h.workspace.read (by omega)) fun v b => ?_
  refine wp_dp (op2_lsl (by decide)) fun q d => ?_
  have r0q : q.gpr .r0 = s.gpr .r0 := by
    rw [d.other .r0 (by decide), b.other .r0 (by decide), a.other .r0 (by decide)]
  have next : q.gpr .r1 = table + BitVec.ofNat 32 (8*w*(j+1)) := by
    rw [d.gpr, dpVal, b.other .r1 (by decide), a.gpr, entry,
      b.gpr, a.mem, header.count]
    rw [stride_value,Offset.add_add]
    congr 1

  refine wp_str (a := off (State.addr base) 220) (by decide) (by rw [r0q]; exact addr 220 (by omega))
    (by rw [d.wr, b.wr, a.wr]; exact h.workspace.write (by omega)) fun y e => ?_
  have memY : y.mem = s.mem.writeW (off (State.addr base) 220)
      (table + BitVec.ofNat 32 (8*w*(j+1))) := by
    rw [e.mem, d.mem, b.mem, a.mem, next]
  have outsideY := writeW32_outside s.mem (State.addr base) (d := 220)
    (table + BitVec.ofNat 32 (8*w*(j+1))) (by decide)
  rw [← memY] at outsideY
  refine wp_ldr (a := off (State.addr base) 228) (by decide)
    (by rw [congrFun e.gpr .r0, r0q]; exact addr 228 (by omega))
    (by rw [e.rd, e.wr, d.rd, d.wr, b.rd, b.wr, a.rd, a.wr]; exact h.workspace.read (by omega))
    fun g f => ?_
  refine wp_dp (op2_imm (by decide)) fun g2 f2 => ?_
  have value : g2.gpr .r1 = BitVec.ofNat 32 (j + 1) := by
    rw [f2.gpr, dpVal, f.gpr, outside_read32 outsideY (d := 228) (by decide) (by decide), index]
    exact (BitVec.ofNat_add _ _).symm
  refine wp_str (a := off (State.addr base) 228) (by decide)
    (by rw [f2.other .r0 (by decide), f.other .r0 (by decide), congrFun e.gpr .r0, r0q]; exact addr 228 (by omega))
    (by rw [f2.wr, f.wr, e.wr, d.wr, b.wr, a.wr]; exact h.workspace.write (by omega)) fun g3 f3 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t f4 zz => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [f4.mem, f3.mem, f2.mem, f.mem, memY, value]
  · rw [zz, congrFun f3.gpr .r1, value]
    exact index32 j hj
  · exact (a.rest (by simp)).trans ((b.rest (by simp)).trans
      ((d.rest (by simp)).trans ((e.rest _).trans ((f.rest (by simp)).trans ((f2.rest (by simp)).trans
        ((f3.rest _).trans (f4.rest _)))))))

theorem init_ok (s : State) {base table : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s)
    (saved : s.mem.readW (off (State.addr base) 232) 32=table) :
    WP isa (.block VG.Impl.Bignum.Arm.CombScan.init) s fun t =>
      t.mem=(s.mem.writeW (off (State.addr base) 220) table).writeW
        (off (State.addr base) 228) (BitVec.ofNat 32 0) ∧ Rest [.r1,.r12] s t := by
  have fits : arrAt w 8≤8*len := h.width ▸ h.layout.2.2.1
  have size : 256≤8*len := by simp only [arrAt,Proof.Rsa.Mont.hdrBytes] at fits; omega
  have addr (d : Nat) (hd : d+4≤8*len) :
      State.addr (s.gpr .r0+BitVec.ofNat 32 d)=off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega)
  unfold VG.Impl.Bignum.Arm.CombScan.init
  refine wp_ldr (a := off (State.addr base) 232) (by decide) (addr 232 (by omega)) (h.workspace.read (by omega)) fun u a => ?_
  refine wp_str (a := off (State.addr base) 220) (by decide) (by rw [a.other .r0 (by decide)]; exact addr 220 (by omega))
    (by rw [a.wr]; exact h.workspace.write (by omega)) fun v b => ?_
  refine wp_mov (op2_imm (by decide)) fun z c => ?_
  refine wp_str (a := off (State.addr base) 228) (by decide)
    (by rw [c.other .r0 (by decide),congrFun b.gpr .r0,a.other .r0 (by decide)]; exact addr 228 (by omega))
    (by rw [c.wr,b.wr,a.wr]; exact h.workspace.write (by omega)) fun t d => WP.block_nil ?_
  refine ⟨?_,(a.rest (by simp)).trans ((b.rest _).trans ((c.rest (by simp)).trans (d.rest _)))⟩
  rw [d.mem,c.mem,b.mem,a.mem,c.gpr,a.gpr,saved]
  rfl

theorem args_ok (s : State) {base entryPtr : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s)
    (entry : s.mem.readW (off (State.addr base) 220) 32 = entryPtr) :
    WP isa (.block scanArgs) s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 (arrAt w 1) ∧ t.gpr .r10 = base + BitVec.ofNat 32 (arrAt w 1) ∧
      t.gpr .r12 = entryPtr ∧ t.gpr .lr = BitVec.ofNat 32 (2 * w) ∧
      t.mem = s.mem ∧ Rest [.r0, .r10, .r12, .lr] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have addr (d : Nat) (hd : d + 4 ≤ 8 * len) :
      State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega)
  unfold scanArgs
  refine wp_ldr (a := off (State.addr base) 72) (by decide) (addr 72 (by omega))
    (h.workspace.read (by omega)) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) 220) (by decide)
    (by rw [a.other .r0 (by decide)]; exact addr 220 (by omega))
    (by rw [a.rd, a.wr]; exact h.workspace.read (by omega)) fun v b => ?_
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 48 (by omega))
    (by rw [b.rd, b.wr, a.rd, a.wr]; exact h.workspace.read (by omega)) fun z c => ?_
  refine wp_dp (op2_reg _ _) fun q d => ?_
  refine wp_ldr (a := off (State.addr base) 72) (by decide)
    (by rw [d.other .r0 (by decide), c.other .r0 (by decide), b.other .r0 (by decide),
      a.other .r0 (by decide)]; exact addr 72 (by omega))
    (by rw [d.rd, d.wr, c.rd, c.wr, b.rd, b.wr, a.rd, a.wr]; exact h.workspace.read (by omega))
    fun t e => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem))),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans ((c.rest (by simp)).trans
      ((d.rest (by simp)).trans (e.rest (by simp)))))⟩
  · rw [e.gpr, d.mem, c.mem, b.mem, a.mem]
    exact header.array 1 (by decide)
  · rw [e.other .r10 (by decide), d.other .r10 (by decide), c.other .r10 (by decide),
      b.other .r10 (by decide), a.gpr]
    exact header.array 1 (by decide)
  · rw [e.other .r12 (by decide), d.other .r12 (by decide), c.other .r12 (by decide), b.gpr, a.mem, entry]
  · rw [e.other .lr (by decide), d.gpr, dpVal, c.gpr, b.mem, a.mem, header.count,
      ← BitVec.ofNat_add, show w + w = 2 * w by omega]

end VG.Proof.Bignum.Arm.CombScan
