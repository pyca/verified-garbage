module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: drawing the candidate

`loadC_ok`: the first `8 w` octets of `rand` (at `R`, in `r26`) into array 0,
most significant first, its low bit and its two top bits set: array 0 holds
`RsaKeyGen.candidate (64 w) x` (`wv_candidate`), and `r28 := 8 w`, the octets
read.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (loadC)
open VG.Proof.MillerRabin.PPC64LE (Env)
open VG.Proof.Bignum (slot wv)

/-- The registers `loadC` writes. -/
def lcRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r12, .r14, .r15, .r16, .r17, .r28]

theorem top2_eq : (BitVec.signExtend 64 ((49152 : BitVec 16) ++ (0 : BitVec 16)) <<< 32 : BitVec 64) =
    13835058055282163712#64 := by
  decide

theorem loadC_ok {s : State} {B R : Addr} {Z w : Nat} (h : Env s B Z w) (h26 : s.gpr .r26 = R)
    (h24 : s.gpr .r24 = BitVec.ofNat 64 (8 * w)) (hR : ∀ i < 8 * w, InRegions (s.rd ++ s.wr) (off R i) 1)
    (hsep : ∀ i < 8 * w, ∀ x, ofs B x < Z → off R i ≠ x) :
    WP isa loadC s fun t =>
      (wv t.mem B (slot w 0) w = Spec.RsaKeyGen.candidate (64 * w)
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem R (8 * w))) ∧
        t.gpr .r28 = BitVec.ofNat 64 (8 * w) ∧ Outside B (slot w 0) (8 * w) s.mem t.mem) ∧
        Keep lcRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h.hZ
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have h0 : slot w 0 = 256 := by rw [es, Nat.zero_mul, Nat.add_zero]
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ Z := by rw [← es]; exact hZ
  unfold loadC
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r12 .r26 0, .addi .r6 .r24 0]) s fun u =>
      (u.gpr .r12 = off R 0 ∧ u.gpr .r6 = BitVec.ofNat 64 (8 * w) ∧ u.mem = s.mem) ∧ Keep [.r6, .r12] s u := by
    refine WP.keep _ ?_ (by decide)
    prun [h26, h24]
    exact BitVec.add_zero _
  refine WP.mono hpre fun u ⟨⟨u12, u6, um⟩, ku⟩ => ?_
  have eu := h.keep ku (by decide)
  refine WP.seq (WP.mono (loadN_ok eu.hs eu.h10 u12 u6 eu.h11 (by omega) (Nat.le_refl _) (by omega)
    (by rw [h0]; decide) (by rw [h0]; omega) (fun i hi => by rw [ku.rd, ku.wr]; exact hR i hi) hsep)
    fun v ⟨vv, vout, kv⟩ => ?_)
  rw [um] at vv vout
  have ev := eu.keep kv (by decide)
  have hsv := ev.hs
  -- The candidate's bits.
  have hw0 := hsv.ld (d := slot w 0) (n := 8) (by omega)
  have hwt := hsv.ld (d := slot w 0 + 8 * (w - 1)) (n := 8) (by omega)
  have hs0 := hsv.st (d := slot w 0) (n := 8) (by omega)
  have hst := hsv.st (d := slot w 0 + 8 * (w - 1)) (n := 8) (by omega)
  have e5 : (BitVec.ofNat 64 (2 * w) <<< 2) + off B (slot w 0) - BitVec.ofNat 64 8 = off B (slot w 0 + 8 * (w - 1)) := by
    have e8 : BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    rw [e8, BitVec.add_comm, off_add, Offset.add_ofNat_sub _ (show 8 ≤ slot w 0 + 8 * w by omega),
      show slot w 0 + 8 * w - 8 = slot w 0 + 8 * (w - 1) by omega]
  have r24 : v.gpr .r24 = BitVec.ofNat 64 (8 * w) := by rw [kv.gpr _ (by decide), ku.gpr _ (by decide), h24]
  refine WP.mono (WP.keep [.r3, .r4, .r5, .r28] (Q := fun t =>
      t.mem = (v.mem.writeW (off B (slot w 0)) (word v.mem B (slot w 0) ||| BitVec.ofNat 64 1)).writeW
        (off B (slot w 0 + 8 * (w - 1))) (word v.mem B (slot w 0 + 8 * (w - 1)) ||| BitVec.ofNat 64 (3 * 2 ^ 62)) ∧
      t.gpr .r28 = BitVec.ofNat 64 (8 * w)) ?_ (by decide)) fun t ⟨⟨tm, t28⟩, kt⟩ => ⟨⟨?_, t28, ?_⟩, ?_⟩
  · prun [ev.h10, ev.h11, r24, hw0, hs0, e5, hwt, hst, exec_lis, top2_eq]
    refine ⟨?_, BitVec.add_zero _⟩
    rw [Mem.readW_writeW_sep (Offset.sep B (d := slot w 0 + 8 * (w - 1)) (n := 8) (e := slot w 0) (k := 8)
      (by omega) (by omega) (by omega)) (by decide)]
  · have sep : ∀ d e : Nat, d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ Z → e + 8 ≤ Z → ∀ (m : Mem) (x : BitVec 64),
        (m.writeW (off B e) x).readW (off B d) 64 = m.readW (off B d) 64 := fun d e h1 h2 h3 m x =>
      Mem.readW_writeW_sep (Offset.sep B h1 (by omega) (by omega)) (by decide)
    rw [VG.Proof.RsaKeyGen.wv_candidate (m := v.mem) (by omega) ?_ ?_ ?_, ← Pre.val32_eq_wv, vv]
    · show t.mem.readW _ 64 = _
      rw [tm, sep _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]; rfl
    · show t.mem.readW _ 64 = _
      rw [tm, Mem.readW_writeW_self64]
    · intro j hj0 hj
      show t.mem.readW _ 64 = v.mem.readW _ 64
      rw [tm, sep _ _ (by omega) (by omega) (by omega), sep _ _ (by omega) (by omega) (by omega)]
  · have o1 := writeW_outside v.mem B (d := slot w 0) (word v.mem B (slot w 0) ||| BitVec.ofNat 64 1) (by omega)
    have o2 := writeW_outside (v.mem.writeW (off B (slot w 0)) (word v.mem B (slot w 0) ||| BitVec.ofNat 64 1)) B
      (d := slot w 0 + 8 * (w - 1)) (word v.mem B (slot w 0 + 8 * (w - 1)) ||| BitVec.ofNat 64 (3 * 2 ^ 62))
      (by omega)
    rw [tm]
    exact (vout.trans (o1.mono (by omega) (by omega))).trans (o2.mono (by omega) (by omega))
  · exact ((ku.trans kv).trans kt).mono (by simp [lcRegs])

end VG.Proof.RsaKeyGen.PPC64LE.Cand
