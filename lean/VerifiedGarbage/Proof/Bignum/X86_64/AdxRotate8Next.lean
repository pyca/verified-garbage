import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8MiddleBody

/-! Public block pointers and loop endpoint. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem nextBlock_ok {s : State} {B : Addr} {Z w eU j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hj : j + 8 ≤ w)
    (hp : s.gpr .rbp = off B (slot w aN + 8 * j))
    (ho : s.gpr .rsi = off B (eU + 8 * j)) :
    WP isa (.block AdxRotate8.nextBlock) s fun t =>
      t.gpr .rbp = off B (slot w aN + 8 * (j + 8)) ∧
      t.gpr .rsi = off B (eU + 8 * (j + 8)) ∧
      t.zf = some (decide (j + 8 = w)) ∧ t.mem = s.mem ∧ Keep [.rbp, .rsi, .rax] s t := by
  have hn := hs.nowrap
  have hN := slot_le (w := w) (show aN < 8 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have a8 (e : Nat) : off B (e + 8 * j) + 64 = off B (e + 8 * (j + 8)) := by
    change off (off B (e + 8 * j)) 64 = off B (e + 8 * (j + 8))
    rw [off_off]
    congr 1
  have w8 : ((BitVec.ofNat 64 w + BitVec.ofNat 64 w) +
      (BitVec.ofNat 64 w + BitVec.ofNat 64 w)) +
      ((BitVec.ofNat 64 w + BitVec.ofNat 64 w) + (BitVec.ofNat 64 w + BitVec.ofNat 64 w)) = BitVec.ofNat 64 (8 * w) := by
    simp only [← BitVec.ofNat_add]; congr 1; omega
  have ep : BitVec.ofNat 64 (8 * w) + off B (slot w aN) = off B (slot w aN + 8 * w) := by
    rw [BitVec.add_comm]
    exact off_off B (slot w aN) (8 * w)
  have hz : ((off B (slot w aN + 8 * (j + 8)) - off B (slot w aN + 8 * w)) == 0) = decide (j + 8 = w) := by
    rw [off_sub_beq B (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  refine WP.mono (WP.keep [.rbp, .rsi, .rax] (Q := fun t =>
      t.gpr .rbp = off B (slot w aN + 8 * (j + 8)) ∧
      t.gpr .rsi = off B (eU + 8 * (j + 8)) ∧
      t.zf = some (decide (j + 8 = w)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold AdxRotate8.nextBlock
  xrun [State.ea, hdr, hdi, hdrOff, hp, ho, a8, hl sW (by decide),
    show BitVec.signExtend 64 (64 : BitVec 32) = (64 : BitVec 64) from rfl, hl (sArr aN) (by decide), hH.hw, hH.harr aN (by decide), w8, ep, hz]
end VG.Proof.Bignum.X86_64.AdxRotate8
