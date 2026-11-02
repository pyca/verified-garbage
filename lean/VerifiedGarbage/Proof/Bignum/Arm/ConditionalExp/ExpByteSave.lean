module

public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBits
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Install an exponent byte and initialize its eight-bit loop -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (Rest wp_str wp_mov op2_imm)

theorem expByteSave_ready (s : State) {base : BitVec 32} {len w M x E v : Nat}
    (h : ExpState ok base len w M x E s) (hv : v < 256) (value : s.gpr .r1 = BitVec.ofNat 32 v) :
    WP isa (.block expByteSave) s fun t => ExpBitState ok base len w M x E v 0 t ∧
      (∀ d, d + 4 ≤ 192 → t.mem.readW (off (State.addr base) d) 32 = s.mem.readW (off (State.addr base) d) 32) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest [.r1] s t := by
  have size : 256 ≤ 8 * len := by
    have := h.ready.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  have addr (d : Nat) (hd : d ≤ 252) : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ready.ptr]; exact addr_add (by have := h.ready.workspace.nowrap; omega)
  unfold expByteSave
  refine wp_str (a := off (State.addr base) 200) (by decide) (addr 200 (by decide))
    (h.ready.workspace.write (by omega)) fun u a => ?_
  have memU : u.mem = s.mem.writeW (off (State.addr base) 200) (BitVec.ofNat 32 v) := by rw [a.mem, value]
  obtain ⟨stateU, frameU⟩ := h.after_header (d := 200) (by decide) (by decide) memU (a.rest [.r1])
    (by rw [a.gpr]; exact h.ready.ptr)
  refine wp_mov (op2_imm (by decide)) fun z b => ?_
  have stateZ := stateU.of_mem b.mem (b.rest (ws := [.r1]) (by simp))
    ((b.other .r0 (by decide)).trans stateU.ready.ptr)
  refine wp_str (a := off (State.addr base) 192) (by decide)
    (by rw [b.other .r0 (by decide), a.gpr]; exact addr 192 (by decide))
    (by rw [b.wr, a.wr]; exact h.ready.workspace.write (by omega)) fun t c => WP.block_nil ?_
  have memT : t.mem = z.mem.writeW (off (State.addr base) 192) (BitVec.ofNat 32 8) := by rw [c.mem, b.gpr]; rfl
  obtain ⟨stateT, frameT⟩ := stateZ.after_header (d := 192) (by decide) (by decide) memT (c.rest [.r1])
    (by rw [c.gpr]; exact stateZ.ready.ptr)
  have outsideU := writeW32_outside s.mem (State.addr base) (d := 200) (BitVec.ofNat 32 v) (by decide)
  have outsideT := writeW32_outside z.mem (State.addr base) (d := 192) (BitVec.ofNat 32 8) (by decide)
  rw [← memU] at outsideU
  rw [← memT] at outsideT
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, (a.rest _).trans ((b.rest (by simp)).trans (c.rest _))⟩
  · simpa only [Nat.pow_zero, Nat.mul_one, Nat.sub_zero, show 2 ^ 8 = 256 from rfl,
      Nat.div_eq_of_lt hv, Nat.add_zero] using stateT
  · simp only [Nat.pow_zero, Nat.mul_one]
    rw [outside_read32 outsideT (d := 200) (by decide) (by decide), b.mem, memU, Mem.readW_writeW_self32]
  · rw [memT, Mem.readW_writeW_self32]
  · intro d hd
    rw [outside_read32 outsideT (d := d) (by omega) (by omega), b.mem,
      outside_read32 outsideU (d := d) (by omega) (by omega)]
  · rw [b.mem] at frameT
    exact frameU.trans frameT

end VG.Proof.Bignum.Arm.ConditionalExp
