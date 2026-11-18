module

public import VerifiedGarbage.Proof.Bignum.Arm.RoundMeta
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Bignum.Arm.RoundFinish`, which the modules that import this one used -/

section

/-! ### `Bignum.Arm.RoundFinishSteps`, which this module and modules that import it used -/

section

/-! # Clear the high word and advance the Montgomery round's temporary state -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_mov wp_dp wp_subs op2_imm dpVal)

theorem clearTop_ok (s : State) {base : BitVec 32} {size top : Nat}
    (ws : Workspace s base size) (fit : top + 4 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 top) :
    WP isa (.block clearTop) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) top) (0 : BitVec 32) ∧
      t.gpr .r0 = base + BitVec.ofNat 32 (top + 12) ∧ Rest [.r0, .r3] s t := by
  unfold clearTop
  refine wp_mov (op2_imm (by decide)) fun u hu => ?_
  have wu := ws.congr hu.wr
  have pu := (hu.other .r0 (by decide)).trans ptr
  refine wp_str (a := off (State.addr base) top) (by decide) (wu.ea pu (by omega_using [fit]))
    (wu.write fit) fun v hv => ?_
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [ht.mem, hv.mem, hu.mem, hu.gpr]
  · rw [ht.gpr, dpVal, hv.gpr, pu]
    change base + BitVec.ofNat 32 top + BitVec.ofNat 32 12 = _
    rw [Offset.add_add]
  · exact (hu.rest (by simp)).trans ((hv.rest _).trans (ht.rest (by simp)))

theorem advanceOperand_ok (s : State) {base : BitVec 32} {size tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 20 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp) :
    WP isa (.block advanceOperand) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (tmp + 16))
        (s.mem.readW (off (State.addr base) (tmp + 16)) 32 + 4) ∧ Rest [.r4] s t := by
  unfold advanceOperand
  refine wp_ldr (by decide) (ws.ea ptr (by omega_using [fit])) (ws.read fit) fun u hu => ?_
  refine wp_dp (op2_imm (by decide)) fun v hv => ?_
  have wv := (ws.congr hu.wr).congr hv.wr
  have pv := (hv.other .r0 (by decide)).trans ((hu.other .r0 (by decide)).trans ptr)
  refine wp_str (by decide) (wv.ea pv (by omega_using [fit])) (wv.write fit) fun t ht => WP.block_nil ?_
  refine ⟨?_, ?_⟩
  · rw [ht.mem, hv.mem, hu.mem, hv.gpr, dpVal, hu.gpr]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (ht.rest _))

theorem decrementRounds_ok (s : State) {base : BitVec 32} {size tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 24 ≤ size)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp) :
    WP isa (.block decrementRounds) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (tmp + 20))
        (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 1) ∧
      t.z = (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 1 == 0) ∧ Rest [.lr] s t := by
  unfold decrementRounds
  refine wp_ldr (by decide) (ws.ea ptr (by omega_using [fit])) (ws.read fit) fun u hu => ?_
  refine wp_subs (op2_imm (by decide)) fun v hv hz => ?_
  have wv := (ws.congr hu.wr).congr hv.wr
  have pv := (hv.other .r0 (by decide)).trans ((hu.other .r0 (by decide)).trans ptr)
  refine wp_str_z (by decide) (wv.ea pv (by omega_using [fit])) (wv.write fit) fun t ht htz => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [ht.mem, hv.mem, hu.mem, hv.gpr, hu.gpr]
  · rw [htz, hz, hu.gpr]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (ht.rest _))

end VG.Proof.Bignum.Arm

end

end

/-! # Exact stores and public loop condition at the end of a Montgomery round -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem roundFinish_ok (s : State) {base : BitVec 32} {size top tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 24 ≤ size) (htmp : tmp = top + 12)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 top) :
    WP isa (.block roundFinish) s fun t =>
      t.mem = ((s.mem.writeW (off (State.addr base) top) (0 : BitVec 32)).writeW
        (off (State.addr base) (tmp + 16)) (s.mem.readW (off (State.addr base) (tmp + 16)) 32 + 4)).writeW
        (off (State.addr base) (tmp + 20)) (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 1) ∧
      t.gpr .r0 = base + BitVec.ofNat 32 tmp ∧
      t.z = (s.mem.readW (off (State.addr base) (tmp + 20)) 32 - 1 == 0) ∧
      Rest [.r0, .r3, .r4, .lr] s t := by
  have hn := ws.nowrap
  rw [roundFinish, List.append_assoc]
  apply WP.block_append_iff.mpr
  refine WP.mono (clearTop_ok s ws (by omega_using [fit, htmp]) ptr) ?_
  rintro u ⟨mem1, ptr1, keep1⟩
  rw [← htmp] at ptr1
  have wr1 := writeW32_outside s.mem (State.addr base) (d := top) (0 : BitVec 32) (by omega)
  rw [← mem1] at wr1
  have oldPtr := outside_read32 wr1 (d := tmp + 16) (by omega_using [htmp]) (by omega_using [fit, hn])
  have oldCount := outside_read32 wr1 (d := tmp + 20) (by omega_using [htmp]) (by omega_using [fit, hn])
  apply WP.block_append_iff.mpr
  refine WP.mono (advanceOperand_ok u (ws.congr keep1.wr) (by omega_using [fit]) ptr1) ?_
  rintro v ⟨mem2, keep2⟩
  have wr2 := writeW32_outside u.mem (State.addr base) (d := tmp + 16)
    (u.mem.readW (off (State.addr base) (tmp + 16)) 32 + 4) (by omega_using [fit, hn])
  rw [← mem2] at wr2
  have oldCount2 := (outside_read32 wr2 (d := tmp + 20) (by omega_using []) (by omega_using [fit, hn])).trans oldCount
  refine WP.mono (decrementRounds_ok v ((ws.congr keep1.wr).congr keep2.wr) fit
    ((keep2.gpr .r0 (by simp)).trans ptr1)) ?_
  rintro t ⟨mem3, zero, keep3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem3, oldCount2, mem2, oldPtr, mem1]
  · rw [keep3.gpr .r0 (by simp), keep2.gpr .r0 (by simp), ptr1]
  · rw [zero, oldCount2]
  · exact (keep1.mono (by simp_all)).trans
      ((keep2.mono (by simp_all)).trans (keep3.mono (by simp_all)))

end VG.Proof.Bignum.Arm

end

end

/-! # The three finishing stores update only the high word and loop state -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

def finishMem (mem : Mem) (base : Addr) (top tmp : Nat) : Mem :=
  ((mem.writeW (off base top) (0 : BitVec 32)).writeW (off base (tmp + 16))
    (mem.readW (off base (tmp + 16)) 32 + 4)).writeW (off base (tmp + 20))
    (mem.readW (off base (tmp + 20)) 32 - 1)

theorem finish_meta {mem : Mem} {base : BitVec 32} {size top tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (nowrap : base.toNat + size ≤ 2 ^ 32) (fit : tmp + 32 ≤ size) (htmp : tmp = top + 12)
    (hdr : RoundMeta mem base tmp a b mod acc n i inv) (hi : i < n) :
    RoundMeta (finishMem mem (State.addr base) top tmp) base tmp a b mod acc n (i + 1) inv := by
  have hb : (State.addr base).toNat + size ≤ 2 ^ 32 := by
    rw [VG.Proof.X25519.Arm.addr_toNat]
    exact nowrap
  have stable (d : Nat) (hd : d + 4 ≤ 32) (sep : d + 4 ≤ 16 ∨ 24 ≤ d) :
      (finishMem mem (State.addr base) top tmp).readW (off (State.addr base) (tmp + d)) 32 =
        mem.readW (off (State.addr base) (tmp + d)) 32 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (finishMem mem (State.addr base) top tmp) (State.addr base) (tmp + d) =
      w32 mem (State.addr base) (tmp + d)
    rw [finishMem, w32_write_ne hb (by omega_using [fit]) (by omega_using [fit, hd]) (by omega_using [sep]),
      w32_write_ne hb (by omega_using [fit]) (by omega_using [fit, hd]) (by omega_using [sep]),
      w32_write_ne hb (by omega_using [fit, htmp]) (by omega_using [fit, hd]) (by omega_using [htmp])]
  have ap : (finishMem mem (State.addr base) top tmp).readW (off (State.addr base) (tmp + 16)) 32 =
      mem.readW (off (State.addr base) (tmp + 16)) 32 + 4 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (finishMem mem (State.addr base) top tmp) (State.addr base) (tmp + 16) = _
    rw [finishMem, w32_write_ne hb (by omega_using [fit]) (by omega_using [fit]) (by omega_using []), w32_write_self]
  have count : (finishMem mem (State.addr base) top tmp).readW (off (State.addr base) (tmp + 20)) 32 =
      mem.readW (off (State.addr base) (tmp + 20)) 32 - 1 := by
    rw [finishMem, Mem.readW_writeW_self32]
  refine ⟨(stable 0 (by decide) (by decide)).trans hdr.count,
    (stable 4 (by decide) (by decide)).trans hdr.bPtr,
    (stable 8 (by decide) (by decide)).trans hdr.mPtr,
    (stable 12 (by decide) (by decide)).trans hdr.inverse, ?_, ?_,
    (stable 28 (by decide) (by decide)).trans hdr.accPtr⟩
  · rw [ap, hdr.aPtr]
    change base + BitVec.ofNat 32 (a + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, hdr.remaining]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi])]
    congr 1

theorem finish_value {mem : Mem} {base : Addr} {size acc top tmp n : Nat}
    (nowrap : base.toNat + size ≤ 2 ^ 32) (fit : tmp + 24 ≤ size)
    (htop : top = acc + 4 * (n + 1)) (htmp : tmp = top + 12) :
    val32 (finishMem mem base top tmp) base acc (n + 2) = val32 mem base acc (n + 1) ∧
      Outs base [(acc, 4 * (n + 2)), (tmp + 16, 8)] mem (finishMem mem base top tmp) := by
  have k1 := writeW32_outside mem base (d := top) (0 : BitVec 32) (by omega)
  have k2 := writeW32_outside (mem.writeW (off base top) (0 : BitVec 32)) base (d := tmp + 16)
    (mem.readW (off base (tmp + 16)) 32 + 4) (by omega_using [nowrap, fit])
  have k3 := writeW32_outside ((mem.writeW (off base top) (0 : BitVec 32)).writeW
    (off base (tmp + 16)) (mem.readW (off base (tmp + 16)) 32 + 4)) base (d := tmp + 20)
    (mem.readW (off base (tmp + 20)) 32 - 1) (by omega_using [nowrap, fit])
  have low1 := k1.val32 (d := acc) (k := n + 1) (by omega_using [htop]) (by omega)
  have low2 := k2.val32 (d := acc) (k := n + 1) (by omega_using [htop, htmp]) (by omega)
  have low3 := k3.val32 (d := acc) (k := n + 1) (by omega_using [htop, htmp]) (by omega)
  have hi2 := k2.w32 (d := top) (by omega_using [htmp]) (by omega)
  have hi3 := k3.w32 (d := top) (by omega_using [htmp]) (by omega)
  refine ⟨?_, ?_⟩
  · rw [show n + 2 = (n + 1) + 1 by omega_using [], val32_succ, finishMem, low3, low2, low1,
      ← htop, hi3, hi2, w32_write_self]
    simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  · exact (Outs.of_outside (k1.mono (o' := acc) (n' := 4 * (n + 2)) (by omega_using [htop]) (by omega_using [htop])) (by simp)).trans
      ((Outs.of_outside (k2.mono (o' := tmp + 16) (n' := 8) (by omega_using []) (by omega_using [])) (by simp)).trans
        (Outs.of_outside (k3.mono (o' := tmp + 16) (n' := 8) (by omega_using []) (by omega_using [])) (by simp)))

end VG.Proof.Bignum.Arm
