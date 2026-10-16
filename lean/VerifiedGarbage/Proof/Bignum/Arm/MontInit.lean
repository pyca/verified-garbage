module

public import VerifiedGarbage.Proof.Bignum.Arm.InitMetaMemory
public import VerifiedGarbage.Proof.Bignum.Arm.PrepareZero
public import VerifiedGarbage.Proof.Bignum.Arm.Zero
public import VerifiedGarbage.Proof.Bignum.Arm.MontCoreCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
  have outsideU := initMeta_outside s (base := State.addr base) (by omega : tmp + 32 ≤ 2 ^ 64)
  rw [← memU] at outsideU
  rw [WP.seq_iff]
  refine WP.mono (prepareZero_ok u ((restU.gpr .r7 (by simp)).trans regs.count)) ?_
  rintro v ⟨ptrV, countV, zeroV, memV, restV⟩
  have cv : ZeroCtx v base size acc (n + 2) := ⟨nowrap, ctx.accFits, by
    rw [restV.wr, restU.wr]; exact ⟨_, ctx.workspace.writable, Region.contains_self _ _⟩⟩
  have pv : v.gpr .r0 = base + BitVec.ofNat 32 acc :=
    ptrV.trans ((restU.gpr .r6 (by simp)).trans regs.accPtr)
  rw [WP.seq_iff]
  refine WP.mono (zero_ok v cv (by omega) pv countV zeroV) ?_
  intro w zw
  refine wp_mov (op2_reg _ _) fun t ut => WP.block_nil ?_
  have outsideW := zw.outside
  rw [memV] at outsideW
  have headerW := headerU.of_outside outsideW (by omega) (by omega)
  have outputW := outside_read32 outsideW (d := tmp + 24) (by omega) (by omega)
  have kept : Rest roundClobbers s t := (restU.mono (by simp [roundClobbers])).trans
    ((restV.mono (by simp [roundClobbers])).trans
      ((zw.rest.mono (by simp [roundClobbers])).trans (ut.rest (by simp [roundClobbers]))))
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
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  have oldB := outside.val32 (d := b) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  refine ⟨⟨⟨ctx.congr kept.wr, ⟨inv, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩, outside, kept⟩
  · rw [ut.mem]; exact headerW
  · rw [oldM]; exact hInv
  · rw [ut.gpr, zw.rest.gpr .r5 (by simp), restV.gpr .r5 (by simp), restU.gpr .r5 (by simp), regs.tmpPtr]
  · rw [oldM, ut.mem, zw.value]
    omega
  · rw [oldB, oldM]; exact hB
  · rw [ut.mem, outputW]; exact outputU
  · rw [ut.mem]; exact zw.value

end VG.Proof.Bignum.Arm
