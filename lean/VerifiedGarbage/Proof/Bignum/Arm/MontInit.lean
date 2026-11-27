module

import VerifiedGarbage.Proof.Bignum.Arm.Zero
public import VerifiedGarbage.Proof.Bignum.Arm.MontCoreCT
public import VerifiedGarbage.Impl.Bignum.Arm.MontInit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.RoundMeta
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! ### `Bignum.Arm.PrepareZero`, which this module and modules that import it used -/

section

/-! # Set the accumulator pointer and its extended word count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_dp op2_reg op2_imm dpVal)

theorem prepareZero_ok (s : State) {n : Nat} (count : s.gpr .r7 = BitVec.ofNat 32 n) :
    WP isa (.block prepareZero) s fun t => t.gpr .r0 = s.gpr .r6 ∧
      t.gpr .lr = BitVec.ofNat 32 (n + 2) ∧ t.gpr .r3 = 0 ∧ t.mem = s.mem ∧
      Rest [.r0, .r3, .lr] s t := by
  unfold prepareZero
  refine wp_mov (op2_reg _ _) fun s1 u1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u4 => WP.block_nil ?_
  refine ⟨?_, ?_, u4.gpr, ?_, ?_⟩
  · rw [u4.other .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide), u1.gpr]
  · rw [u4.other .lr (by decide), u3.gpr, dpVal, u2.gpr, u1.other .r7 (by decide), count]
    change BitVec.ofNat 32 n + BitVec.ofNat 32 2 = _
    rw [← BitVec.ofNat_add]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
      ((u3.rest (by simp)).trans (u4.rest (by simp))))

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.InitMetaMemory`, which this module and modules that import it used -/

section

/-! # Metadata stores establish the first round and preserve other workspace bytes -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/InitMeta.lean`, which only this module imported.
section

/-! # Eight bounded stores initialize the Montgomery metadata -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

def initMetaMem (s : State) (base : Addr) (tmp : Nat) : Mem :=
  ((((((((s.mem.writeW (off base (tmp + 0)) (s.gpr .r7)).writeW
     (off base (tmp + 4)) (s.gpr .r9)).writeW
     (off base (tmp + 8)) (s.gpr .r11)).writeW
     (off base (tmp + 12)) (s.gpr .r12)).writeW
     (off base (tmp + 16)) (s.gpr .r8)).writeW
     (off base (tmp + 20)) (s.gpr .r7)).writeW
     (off base (tmp + 24)) (s.gpr .r10)).writeW
     (off base (tmp + 28)) (s.gpr .r6))

theorem initMeta_ok (s : State) {base : BitVec 32} {size tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 32 ≤ size)
    (ptr : s.gpr .r5 = base + BitVec.ofNat 32 tmp) :
    WP isa (.block initMeta) s fun t =>
      t.mem = initMetaMem s (State.addr base) tmp ∧ Rest [] s t := by
  unfold initMeta
  refine wp_str (by decide) (ws.ea ptr (by omega_using [fit])) (ws.write (by omega_using [fit])) fun s1 u1 => ?_
  obtain w1 := ws.congr u1.wr
  obtain p1 := (congrFun u1.gpr .r5).trans ptr
  refine wp_str (by decide) (w1.ea p1 (by omega_using [fit])) (w1.write (by omega_using [fit])) fun s2 u2 => ?_
  obtain w2 := w1.congr u2.wr
  obtain p2 := (congrFun u2.gpr .r5).trans p1
  refine wp_str (by decide) (w2.ea p2 (by omega_using [fit])) (w2.write (by omega_using [fit])) fun s3 u3 => ?_
  obtain w3 := w2.congr u3.wr
  obtain p3 := (congrFun u3.gpr .r5).trans p2
  refine wp_str (by decide) (w3.ea p3 (by omega_using [fit])) (w3.write (by omega_using [fit])) fun s4 u4 => ?_
  obtain w4 := w3.congr u4.wr
  obtain p4 := (congrFun u4.gpr .r5).trans p3
  refine wp_str (by decide) (w4.ea p4 (by omega_using [fit])) (w4.write (by omega_using [fit])) fun s5 u5 => ?_
  obtain w5 := w4.congr u5.wr
  obtain p5 := (congrFun u5.gpr .r5).trans p4
  refine wp_str (by decide) (w5.ea p5 (by omega_using [fit])) (w5.write (by omega_using [fit])) fun s6 u6 => ?_
  obtain w6 := w5.congr u6.wr
  obtain p6 := (congrFun u6.gpr .r5).trans p5
  refine wp_str (by decide) (w6.ea p6 (by omega_using [fit])) (w6.write (by omega_using [fit])) fun s7 u7 => ?_
  obtain w7 := w6.congr u7.wr
  obtain p7 := (congrFun u7.gpr .r5).trans p6
  refine wp_str (by decide) (w7.ea p7 (by omega_using [fit])) (w7.write (by omega_using [fit])) fun s8 u8 => WP.block_nil ?_
  refine ⟨?_, ?_⟩
  · simp only [initMetaMem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  · exact (u1.rest []).trans ((u2.rest []).trans ((u3.rest []).trans ((u4.rest []).trans ((u5.rest []).trans ((u6.rest []).trans ((u7.rest []).trans ((u8.rest []))))))))

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem initMeta_header (s : State) {base : BitVec 32} {size tmp a b mod acc out n : Nat} {inv : BitVec 32}
    (nowrap : base.toNat + size ≤ 2 ^ 32) (fit : tmp + 32 ≤ size)
    (count : s.gpr .r7 = BitVec.ofNat 32 n)
    (pa : s.gpr .r8 = base + BitVec.ofNat 32 a) (pb : s.gpr .r9 = base + BitVec.ofNat 32 b)
    (pm : s.gpr .r11 = base + BitVec.ofNat 32 mod) (pi : s.gpr .r12 = inv)
    (po : s.gpr .r10 = base + BitVec.ofNat 32 out) (pc : s.gpr .r6 = base + BitVec.ofNat 32 acc) :
    RoundMeta (initMetaMem s (State.addr base) tmp) base tmp a b mod acc n 0 inv ∧
    (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 24)) 32 =
      base + BitVec.ofNat 32 out := by
  obtain hb : (State.addr base).toNat + size ≤ 2 ^ 32 := by
    rw [VG.Proof.X25519.Arm.addr_toNat]; exact nowrap
  obtain h0 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 0)) 32 = s.gpr .r7 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 0) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_self]
  obtain h1 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 4)) 32 = s.gpr .r9 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 4) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_self]
  obtain h2 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 8)) 32 = s.gpr .r11 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 8) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_self]
  obtain h3 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 12)) 32 = s.gpr .r12 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 12) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_self]
  obtain h4 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 16)) 32 = s.gpr .r8 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 16) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_self]
  obtain h5 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 20)) 32 = s.gpr .r7 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 20) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_self]
  obtain h6 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 24)) 32 = s.gpr .r10 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 24) = _
    unfold initMetaMem
    rw [w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using [])]
    rw [w32_write_self]
  obtain h7 : (initMetaMem s (State.addr base) tmp).readW (off (State.addr base) (tmp + 28)) 32 = s.gpr .r6 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (initMetaMem s (State.addr base) tmp) (State.addr base) (tmp + 28) = _
    unfold initMetaMem
    rw [w32_write_self]
  refine ⟨⟨h0.trans count, h1.trans pb, h2.trans pm, h3.trans pi, ?_, ?_, h7.trans pc⟩, h6.trans po⟩
  · simpa only [Nat.mul_zero, Nat.add_zero] using h4.trans pa
  · simpa only [Nat.sub_zero] using h5.trans count

theorem initMeta_outside (s : State) {base : Addr} {tmp : Nat} (fit : tmp + 32 ≤ 2 ^ 64) :
    Outside base tmp 32 s.mem (initMetaMem s base tmp) := by
  let m0 := s.mem
  let m1 := m0.writeW (off base (tmp + 0)) (s.gpr .r7)
  obtain h0 : Outside base tmp 32 m0 m1 :=
    (writeW32_outside m0 base (d := tmp + 0) (s.gpr .r7) (by omega_using [fit])).mono
      (by omega_using []) (by omega_using [])
  let m2 := m1.writeW (off base (tmp + 4)) (s.gpr .r9)
  obtain h1 : Outside base tmp 32 m1 m2 :=
    (writeW32_outside m1 base (d := tmp + 4) (s.gpr .r9) (by omega_using [fit])).mono
      (by omega_using []) (by omega_using [])
  let m3 := m2.writeW (off base (tmp + 8)) (s.gpr .r11)
  obtain h2 : Outside base tmp 32 m2 m3 :=
    (writeW32_outside m2 base (d := tmp + 8) (s.gpr .r11) (by omega_using [fit])).mono
      (by omega_using []) (by omega_using [])
  let m4 := m3.writeW (off base (tmp + 12)) (s.gpr .r12)
  obtain h3 : Outside base tmp 32 m3 m4 :=
    (writeW32_outside m3 base (d := tmp + 12) (s.gpr .r12) (by omega_using [fit])).mono
      (by omega_using []) (by omega_using [])
  let m5 := m4.writeW (off base (tmp + 16)) (s.gpr .r8)
  obtain h4 : Outside base tmp 32 m4 m5 :=
    (writeW32_outside m4 base (d := tmp + 16) (s.gpr .r8) (by omega_using [fit])).mono
      (by omega_using []) (by omega_using [])
  let m6 := m5.writeW (off base (tmp + 20)) (s.gpr .r7)
  obtain h5 : Outside base tmp 32 m5 m6 :=
    (writeW32_outside m5 base (d := tmp + 20) (s.gpr .r7) (by omega_using [fit])).mono
      (by omega_using []) (by omega_using [])
  let m7 := m6.writeW (off base (tmp + 24)) (s.gpr .r10)
  obtain h6 : Outside base tmp 32 m6 m7 :=
    (writeW32_outside m6 base (d := tmp + 24) (s.gpr .r10) (by omega_using [fit])).mono
      (by omega_using []) (by omega_using [])
  let m8 := m7.writeW (off base (tmp + 28)) (s.gpr .r6)
  obtain h7 : Outside base tmp 32 m7 m8 :=
    (writeW32_outside m7 base (d := tmp + 28) (s.gpr .r6) (by omega_using [fit])).mono
      (by omega_using []) (by omega_using [])
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7)))))))

end VG.Proof.Bignum.Arm

end

end

/-! # Initialize the complete Montgomery core without changing its operands -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

structure InitRegs (s : State) (base : BitVec 32) (out tmp a b mod acc n : Nat) (inv : BitVec 32) : Prop where
  tmpPtr : s.gpr .r5 = base + BitVec.ofNat 32 tmp
  accPtr : s.gpr .r6 = base + BitVec.ofNat 32 acc
  count : s.gpr .r7 = BitVec.ofNat 32 n
  aPtr : s.gpr .r8 = base + BitVec.ofNat 32 a
  bPtr : s.gpr .r9 = base + BitVec.ofNat 32 b
  outPtr : s.gpr .r10 = base + BitVec.ofNat 32 out
  mPtr : s.gpr .r11 = base + BitVec.ofNat 32 mod
  inverse : s.gpr .r12 = inv

theorem montInit_ok (s : State) {base : BitVec 32} {size out tmp a b mod acc n : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (regs : InitRegs s base out tmp a b mod acc n inv)
    (hB : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n)
    (hInv : (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa montInit s fun t => CoreReady base size out tmp a b mod acc n t ∧
      Outs (State.addr base) [(acc, 4 * (n + 2)), (tmp, 32)] s.mem t.mem ∧ Rest roundClobbers s t := by
  have nowrap := ctx.workspace.nowrap
  have fits := ctx.tmpFits
  have layout := ctx.layout
  rw [montInit, WP.seq_iff]
  refine WP.mono (initMeta_ok s ctx.workspace fits regs.tmpPtr) ?_
  rintro u ⟨memU, restU⟩
  obtain ⟨headerU, outputU⟩ := initMeta_header s nowrap fits regs.count regs.aPtr regs.bPtr
    regs.mPtr regs.inverse regs.outPtr regs.accPtr
  rw [← memU] at headerU outputU
  have outsideU := initMeta_outside s (base := State.addr base) (by omega_using [nowrap, fits] : tmp + 32 ≤ 2 ^ 64)
  rw [← memU] at outsideU
  rw [WP.seq_iff]
  refine WP.mono (prepareZero_ok u ((restU.gpr .r7 (by decide)).trans regs.count)) ?_
  rintro v ⟨ptrV, countV, zeroV, memV, restV⟩
  have cv : ZeroCtx v base size acc (n + 2) := ⟨nowrap, ctx.accFits, by
    rw [restV.wr, restU.wr]; exact ⟨_, ctx.workspace.writable, Region.contains_self _ _⟩⟩
  have pv : v.gpr .r0 = base + BitVec.ofNat 32 acc :=
    ptrV.trans ((restU.gpr .r6 (by decide)).trans regs.accPtr)
  rw [WP.seq_iff]
  refine WP.mono (zero_ok v cv (by omega_using []) pv countV zeroV) ?_
  intro w zw
  refine wp_mov (op2_reg _ _) fun t ut => WP.block_nil ?_
  have outsideW := zw.outside
  rw [memV] at outsideW
  have headerW := headerU.of_outside outsideW (by omega_using [layout]) (by omega_using [nowrap, fits])
  have outputW := outside_read32 outsideW (d := tmp + 24) (by omega_using [layout]) (by omega_using [nowrap, fits])
  have kept : Rest roundClobbers s t := (restU.mono (by decide)).trans
    ((restV.mono (by decide)).trans
      ((zw.rest.mono (by decide)).trans (ut.rest (by decide))))
  have outside : Outs (State.addr base) [(acc, 4 * (n + 2)), (tmp, 32)] s.mem t.mem := by
    rw [ut.mem]
    exact (Outs.of_outside outsideU (by simp)).trans (Outs.of_outside outsideW (by simp))
  have mFits := ctx.mFits
  have bFits := ctx.bFits
  have accM := ctx.accM
  have accB := ctx.accB
  have tmpM := ctx.tmpM
  have tmpB := ctx.tmpB
  have oldM := outside.val32 (d := mod) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [nowrap, mFits])
  have oldB := outside.val32 (d := b) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [nowrap, bFits])
  refine ⟨⟨⟨ctx.congr kept.wr, ⟨inv, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩, outside, kept⟩
  · rw [ut.mem]; exact headerW
  · rw [oldM]; exact hInv
  · rw [ut.gpr, zw.rest.gpr .r5 (by decide), restV.gpr .r5 (by decide), restU.gpr .r5 (by decide), regs.tmpPtr]
  · rw [oldM, ut.mem, zw.value]
    omega_using [hB]
  · rw [oldB, oldM]; exact hB
  · rw [ut.mem, outputW]; exact outputU
  · rw [ut.mem]; exact zw.value

end VG.Proof.Bignum.Arm
