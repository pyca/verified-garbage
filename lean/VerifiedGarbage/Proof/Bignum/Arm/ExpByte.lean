module

public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Bignum.Arm.ExpState
public import VerifiedGarbage.Proof.Bignum.Words

import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHead
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
/-! # One exponent-buffer byte appends eight bits to the proved power -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/ExpByteNext.lean`, which only this module imported.
section

/-! # Advance the exponent pointer and remaining-byte counter -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str wp_subs op2_imm dpVal ofNat_beq_zero)

theorem expByteNext_ok (s : State) {base ep : BitVec 32} {len w M x E c : Nat}
    (h : ExpState base len w M x E s) (hc : 0 < c) (hc' : c < 2 ^ 32)
    (pointer : s.mem.readW (off (State.addr base) 128) 32 = ep)
    (count : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 c) :
    WP isa (.block expByteNext) s fun t => ExpState base len w M x E t ∧
      t.mem.readW (off (State.addr base) 128) 32 = ep + 1 ∧
      t.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 (c - 1) ∧
      t.z = decide (c = 1) ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest [.r1] s t := by
  have size : 256 ≤ 8 * len := by
    have := h.ready.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  have addr (d : Nat) (hd : d ≤ 252) : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ready.ptr]; exact addr_add (by have := h.ready.workspace.nowrap; omega)
  unfold expByteNext
  refine wp_ldr (a := off (State.addr base) 128) (by decide) (addr 128 (by decide))
    (h.ready.workspace.read (by omega)) fun u a => ?_
  refine wp_dp (op2_imm (by decide)) fun v b => ?_
  refine wp_str (a := off (State.addr base) 128) (by decide)
    (by rw [b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 128 (by decide))
    (by rw [b.wr, a.wr]; exact h.ready.workspace.write (by omega)) fun z d => ?_
  have memZ : z.mem = s.mem.writeW (off (State.addr base) 128) (ep + 1) := by
    rw [d.mem, b.mem, a.mem, b.gpr, dpVal, a.gpr, pointer]
  have restZ : Rest [.r1] s z := (a.rest (by simp)).trans ((b.rest (by simp)).trans (d.rest _))
  obtain ⟨stateZ, frameZ⟩ := h.after_header (d := 128) (by decide) (by decide) memZ restZ
    ((restZ.gpr .r0 (by simp)).trans h.ready.ptr)
  have outsideZ := writeW32_outside s.mem (State.addr base) (d := 128) (ep + 1) (by decide)
  rw [← memZ] at outsideZ
  have countZ : z.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 c := by
    rw [outside_read32 outsideZ (d := 132) (by decide) (by decide)]
    exact count
  refine wp_ldr (a := off (State.addr base) 132) (by decide)
    (by rw [restZ.gpr .r0 (by simp)]; exact addr 132 (by decide))
    (by rw [restZ.rd, restZ.wr]; exact h.ready.workspace.read (by omega)) fun q e => ?_
  refine wp_subs (op2_imm (by decide)) fun r f zero => ?_
  refine wp_str_z (a := off (State.addr base) 132) (by decide)
    (by rw [f.other .r0 (by decide), e.other .r0 (by decide), restZ.gpr .r0 (by simp)]; exact addr 132 (by decide))
    (by rw [f.wr, e.wr, restZ.wr]; exact h.ready.workspace.write (by omega)) fun t g zeroT => WP.block_nil ?_
  have value : r.gpr .r1 = BitVec.ofNat 32 (c - 1) := by
    rw [f.gpr, e.gpr, countZ]
    change BitVec.ofNat 32 c - BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
  have memT : t.mem = z.mem.writeW (off (State.addr base) 132) (BitVec.ofNat 32 (c - 1)) := by
    rw [g.mem, f.mem, e.mem, value]
  have restT : Rest [.r1] z t := (e.rest (by simp)).trans ((f.rest (by simp)).trans (g.rest _))
  obtain ⟨stateT, frameT⟩ := stateZ.after_header (d := 132) (by decide) (by decide) memT restT
    ((restT.gpr .r0 (by simp)).trans stateZ.ready.ptr)
  refine ⟨stateT, ?_, ?_, ?_, frameZ.trans frameT, restZ.trans restT⟩
  · have outsideT := writeW32_outside z.mem (State.addr base) (d := 132) (BitVec.ofNat 32 (c - 1)) (by decide)
    rw [← memT] at outsideT
    rw [outside_read32 outsideT (d := 128) (by decide) (by decide), memZ, Mem.readW_writeW_self32]
  · rw [memT, Mem.readW_writeW_self32]
  · rw [zeroT, zero, ← f.gpr, value, ofNat_beq_zero (by omega)]
    exact decide_eq_decide.mpr (by omega)

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem expByte_ok (s : State) {base ep : BitVec 32} {len w M x E c : Nat}
    (h : ExpState base len w M x E s) (hc : 0 < c) (hc' : c < 2 ^ 32)
    (pointer : s.mem.readW (off (State.addr base) 128) 32 = ep)
    (count : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 c)
    (read : InRegions (s.rd ++ s.wr) (State.addr ep) 1) :
    WP isa (.seq expByteHead (.seq expBits (.block expByteNext))) s fun t =>
      ExpState base len w M x (256 * E + (s.mem (State.addr ep)).toNat) t ∧
      t.mem.readW (off (State.addr base) 128) 32 = ep + 1 ∧
      t.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 (c - 1) ∧
      t.z = decide (c = 1) ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (expByteHead_ok s h pointer read) ?_
  rintro u ⟨ready, headerU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (expBits_ok u ready (s.mem (State.addr ep)).isLt) ?_
  rintro v ⟨power, headerV, frameV, restV⟩
  refine WP.mono (expByteNext_ok v power hc hc'
    ((headerV 128 (by decide)).trans ((headerU 128 (by decide)).trans pointer))
    ((headerV 132 (by decide)).trans ((headerU 132 (by decide)).trans count))) ?_
  rintro t ⟨final, ptr, counter, zero, frameT, restT⟩
  exact ⟨final, ptr, counter, zero, frameU.trans (frameV.trans frameT),
    (restU.mono (by decide)).trans (restV.trans (restT.mono (by decide)))⟩

end VG.Proof.Bignum.Arm
