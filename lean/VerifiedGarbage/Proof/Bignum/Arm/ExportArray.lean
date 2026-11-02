module

import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Impl.Bignum.Arm.ExportArray
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Exact packed-word export from a shared RSA array -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf Layout)
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

theorem exportArray_ok (s : State) {base dst : BitVec 32} {len w o : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ho : o < 8)
    (dstFit : dst.toNat + 8 * w ≤ 2 ^ 32) (write : InRegions s.wr (State.addr dst) (8 * w))
    (sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, 8 * w⟩)
    (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o) (output : s.gpr .r4 = dst) :
    WP isa exportArray s fun t =>
      t.mem.read (State.addr dst) (8 * w) = s.mem.read (off (State.addr base) (arrAt w o)) (8 * w) ∧
      Frame [⟨State.addr dst, 8 * w⟩] s.mem t.mem ∧
      t.gpr .r0 = base ∧ t.gpr .r4 = dst ∧ Rest roundClobbers s t := by
  have nowrap := ws.nowrap
  have hw : 2 ≤ w := width ▸ layout.1
  have fits : arrAt w 8 ≤ 8 * len := width ▸ layout.2.2.1
  have bound := Nat.le_trans (array_end_le ho) fits
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  let src := base + BitVec.ofNat 32 (arrAt w o)
  have srcAddr : State.addr src = off (State.addr base) (arrAt w o) := addr_add (by omega)
  have srcNat : src.toNat = base.toNat + arrAt w o := by
    simp only [src, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : arrAt w o < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : base.toNat + arrAt w o < 2 ^ 32)]
  have header := nativeHeader_of_layout s.mem base nowrap (Nat.le_refl _) layout
  rw [width] at header
  rw [exportArray, WP.seq_iff]
  refine WP.mono (exportArrayArgs_ok s ws size header ho ptr index) ?_
  rintro u ⟨p0, p1, count, saved, mem, rest⟩
  have read : InRegions (u.rd ++ u.wr) (State.addr src) (8 * w) := by
    rw [rest.rd, rest.wr, srcAddr]
    exact ⟨_, List.mem_append_right _ ws.writable, Offset.contains_base _ (by omega) (by omega)⟩
  have sepSrc : Region.Disjoint ⟨State.addr src, 8 * w⟩ ⟨State.addr dst, 8 * w⟩ := by
    apply sep.sub_left
    intro a ha
    rw [srcAddr] at ha
    change (a - off (State.addr base) (arrAt w o)).toNat + 1 ≤ 8 * w at ha
    have hi : (a - off (State.addr base) (arrAt w o)).toNat < 8 * w := by omega
    rw [Offset.lt_iff a (State.addr base) (by omega)] at hi
    change (a - State.addr base).toNat + 1 ≤ 8 * len
    omega
  rw [WP.seq_iff]
  refine WP.mono (copyBuffer_ok u (by omega) (by rw [srcNat]; omega) dstFit (by omega)
    read (by rw [rest.wr]; exact write) sepSrc (p0.trans output) p1 count) ?_
  rintro v ⟨value, frame, _, keep⟩
  refine wp_mov (op2_reg _ _) fun t moved => WP.block_nil ?_
  rw [srcAddr, mem] at value
  rw [mem] at frame
  refine ⟨by rw [moved.mem]; exact value, by rw [moved.mem]; exact frame, ?_, ?_, ?_⟩
  · rw [moved.gpr, keep.gpr .r5 (by decide), saved]
  · rw [moved.other .r4 (by decide), keep.gpr .r4 (by decide), rest.gpr .r4 (by decide), output]
  · exact (rest.mono (by decide)).trans
      ((keep.mono (by decide)).trans (moved.rest (by decide)))

end VG.Proof.Bignum.Arm
