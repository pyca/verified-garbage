module

public import VerifiedGarbage.Proof.Bignum.Arm.SelectReadState
import VerifiedGarbage.Proof.Bignum.Arm.SelectStep
import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Bignum.Arm.Select

/-! One masked word selection accepts its separate source as read-only. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem selectRead_slice {rs : List Region} {p : Addr} {n d : Nat}
    (h : InRegions rs p n) (hd : d + 4 ≤ n) (bound : d < 2 ^ 64) :
    InRegions rs (off p d) 4 := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  have le : (off p d - r.base).toNat ≤ (p - r.base).toNat + d := by
    rw [off, Offset.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    exact Nat.mod_le _ _
  simp only [Region.Contains] at hc ⊢
  omega

theorem selectReadBody_ok {s0 s : State} {dst src : BitVec 32} {n i : Nat}
    (ctx : SelectReadCtx s0 dst src n) (inv : SelectReadInv s0 dst src n i s) (hi : i < n)
    (hc : (s0.gpr .r11).toNat ≤ 1) :
    WP isa selectBody s fun t => SelectReadInv s0 dst src n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have hn := ctx.countFit
  have hd := ctx.dstFit
  have hs := ctx.srcFit
  have addr {r : Reg} {p : BitVec 32} (hp : s.gpr r = p + BitVec.ofNat 32 (4 * i))
      (fit : p.toNat + 4 * n ≤ 2 ^ 32) :
      State.addr (s.gpr r + BitVec.ofNat 32 0) = off (State.addr p) (4 * i) := by
    rw [hp, BitVec.add_zero]
    exact VG.Arm.addr_add (by omega)
  have writable : InRegions s.wr (off (State.addr dst) (4 * i)) 4 := by
    rw [inv.rest.wr]
    exact selectRead_slice ctx.write (by omega) (by omega)
  have readableA : InRegions (s.rd ++ s.wr) (off (State.addr dst) (4 * i)) 4 := by
    obtain ⟨r, hr, h⟩ := writable
    exact ⟨r, List.mem_append_right _ hr, h⟩
  have readableB : InRegions (s.rd ++ s.wr) (off (State.addr src) (4 * i)) 4 := by
    rw [inv.rest.rd, inv.rest.wr]
    exact selectRead_slice ctx.read (by omega) (by omega)
  rw [selectBody, WP.seq_iff]
  refine WP.mono (selectStep_ok s _ _ _ (addr inv.outPtr hd) (addr inv.aPtr hd)
    (addr inv.bPtr hs) writable readableA readableB
    (by rw [inv.rest.gpr .r11 (by simp [selectLoopClobbers])]; exact hc) inv.mask) ?_
  rintro u ⟨mem, keep⟩
  obtain ⟨outside, frame, value⟩ := selectRead_value_step ctx inv hi mem
  refine WP.mono (subAdvance_ok u) ?_
  rintro t ⟨p0, p10, p12, count, zero, mem2, keep2⟩
  have uc : u.gpr .lr = BitVec.ofNat 32 (n - i) :=
    (keep.gpr .lr (by simp [selectClobbers])).trans inv.count
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [p0, keep.gpr .r0 (by simp [selectClobbers]), inv.outPtr]
    change dst + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [p10, keep.gpr .r10 (by simp [selectClobbers]), inv.aPtr]
    change dst + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [p12, keep.gpr .r12 (by simp [selectClobbers]), inv.bPtr]
    change src + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, uc]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [mem2]; exact outside
  · rw [mem2]; exact frame
  · rw [mem2]; exact value
  · rw [keep2.gpr .r4 (by simp), keep.gpr .r4 (by simp [selectClobbers]),
      keep2.gpr .r11 (by simp), keep.gpr .r11 (by simp [selectClobbers])]
    exact inv.mask
  · refine inv.rest.trans ((keep.mono ?_).trans (keep2.mono ?_))
    all_goals decide
  · rw [zero, uc]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

end VG.Proof.Bignum.Arm
