module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Phase
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordCut
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Prep

/-!
# An FFDH parameter candidate on PPC64LE: the candidate p

`shapeP_ok`: in p's working space (`Ph p bits`), the first `out_len` octets
of the tape into array 0 (`loadN_ok`), its top word cut to `bits` bits with
its top bit set, and its low bit set: `candidateOf bits` of their number
(`wv_shape`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE

/-- The registers `shapeP` writes. -/
def shRegs : List Reg := [.r0, .r4, .r5, .r6, .r12, .r14, .r15, .r16, .r17]

theorem shapeP_ok {p : PP} {s : State} (h : St p s) (hp : Ph p p.bits s) (hrl : p.L ≤ p.r.length) :
    WP isa shapeP s fun t =>
      (wv t.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) =
          Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)) ∧
        Frm p.B [(slot (wOf p.bits) 0, 8 * wOf p.bits)] s.mem t.mem) ∧ Keep shRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hn := h.dims.n
  have hnw := h.scr.nowrap
  have h10 := hp.r10
  have h11 := hp.r11
  have htop := hp.topW
  generalize hwd : wOf p.bits = w at h10 h11 htop ⊢
  have hw8 : 8 ≤ w := by simp only [wOf] at hwd; omega
  have hw128 : w ≤ 128 := by simp only [wOf] at hwd; omega
  have hLw : p.L ≤ 8 * w := by simp only [wOf, PP.L] at hwd ⊢; omega
  have hZ : slot w 0 + 8 * w ≤ p.Z := by simp only [slot, hdrBytes, PP.Z, PP.L] at hn ⊢; omega
  have hL1 : 1 ≤ p.L := by simp only [PP.L]; omega
  unfold shapeP
  refine WP.seq (WP.mono (WP.keep [.r6, .r12] (Q := fun u => u.gpr .r12 = off p.rp 0 ∧
      u.gpr .r6 = BitVec.ofNat 64 p.L ∧ u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨u12, u6, um⟩, ku⟩ => ?_)
  · simp only [ldh, hRand, hLen]
    prun [h.r31, h.ld (d := 136) (by decide), h.ld (d := 24) (by decide), h.args.rand', h.args.len',
      BitVec.add_zero]
  have hrd : ∀ i < p.L, InRegions (u.rd ++ u.wr) (off p.rp i) 1 := fun i hi => by
    rw [ku.rd, ku.wr]; exact h.bufs.rdR i (by omega)
  refine WP.seq (WP.mono (loadN_ok (h.scr.congr ku.wr) ((ku.gpr .r10 (by decide)).trans h10) u12 u6
    ((ku.gpr .r11 (by decide)).trans h11) hL1 hLw (by omega) (by simp [slot, hdrBytes]) hZ hrd
    (fun i hi => h.bufs.sepR i (by omega))) fun v ⟨vv, vo, kv⟩ => ?_)
  have kuv := ku.trans kv
  rw [um, Pre.val32_eq_wv, h.take_bytes hrl] at vv
  have h0 : slot w 0 = 256 := by simp [slot, hdrBytes]
  -- The top word's mask, from the header.
  have hk1 : 1 ≤ p.bits + 64 - 64 * w := by simp only [wOf] at hwd; omega
  have hk2 : p.bits + 64 - 64 * w ≤ 64 := by simp only [wOf] at hwd; omega
  generalize hkd : p.bits + 64 - 64 * w = k at htop hk1 hk2
  have tv : v.mem.readW (p.B + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 (2 ^ k - 1) := by
    show word v.mem p.B 192 = _
    rw [Outside.word vo (by omega) (by omega), um]; exact htop
  have e5 : off p.B (slot w 0 + 8 * w) - BitVec.ofNat 64 8 = off p.B (slot w 0 + 8 * (w - 1)) := by
    simp only [off]; rw [Offset.add_ofNat_sub _ (by omega)]; congr 2; omega
  have sT : InRegions v.wr (off p.B (slot w 0 + 8 * (w - 1))) 8 := by
    rw [kuv.wr]; exact h.scr.st (by omega)
  have lT : InRegions (v.rd ++ v.wr) (off p.B (slot w 0 + 8 * (w - 1))) 8 := by
    rw [kuv.rd, kuv.wr]; exact h.scr.ld (by omega)
  have sA : InRegions v.wr (off p.B (slot w 0)) 8 := by rw [kuv.wr]; exact h.scr.st (by omega)
  have lA : InRegions (v.rd ++ v.wr) (off p.B (slot w 0)) 8 := by
    rw [kuv.rd, kuv.wr]; exact h.scr.ld (by omega)
  have eA : ∀ x : BitVec 64, (v.mem.writeW (off p.B (slot w 0 + 8 * (w - 1))) x).readW (off p.B (slot w 0)) 64 =
      v.mem.readW (off p.B (slot w 0)) 64 := fun x => rw_off _ _ _ (by omega) (by omega) (by omega)
  have ebit : (BitVec.ofNat 64 (2 ^ k - 1)) >>> 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 (2 ^ (k - 1)) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.pow_succ]
    have : 2 ^ j ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    generalize 2 ^ j = P at *
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega
  have l192 : InRegions (v.rd ++ v.wr) (p.B + BitVec.ofNat 64 192) 8 := by
    rw [kuv.rd, kuv.wr]; exact h.ld (d := 192) (by decide)
  refine WP.mono (WP.keep [.r4, .r5, .r6] (Q := fun t => t.mem =
      (v.mem.writeW (off p.B (slot w 0 + 8 * (w - 1)))
        ((v.mem.readW (off p.B (slot w 0 + 8 * (w - 1))) 64 &&& BitVec.ofNat 64 (2 ^ k - 1)) |||
          BitVec.ofNat 64 (2 ^ (k - 1)))).writeW (off p.B (slot w 0))
        (v.mem.readW (off p.B (slot w 0)) 64 ||| BitVec.ofNat 64 1)) ?_ (by decide))
    fun t ⟨tm, kt⟩ => ⟨⟨?_, ?_⟩, (kuv.trans kt).mono (by decide)⟩
  · simp only [ldh, hTop]
    prun [(kuv.gpr .r10 (by decide)).trans h10, (kuv.gpr .r11 (by decide)).trans h11,
      (kuv.gpr .r31 (by decide)).trans h.r31, Proof.MillerRabin.PPC64LE.shl2_ofNat, e5, sT, lT, sA, lA, eA,
      l192, tv, ebit, BitVec.add_zero]
  · have hb : 64 * (w - 1) + k = p.bits := by simp only [wOf] at hwd; omega
    rw [← hb, ← vv]
    refine Proof.Ffdh.ParameterCandidate.wv_shape (by omega) hk1 hk2 ?_ ?_ fun j hj0 hj => ?_
    · simp only [word, off] at tm ⊢; rw [tm, rw_self]; rfl
    · simp only [word, off] at tm ⊢
      rw [tm, rw_off _ _ _ (by omega) (by omega) (by omega), rw_self]
    · simp only [word, off] at tm ⊢
      rw [tm, rw_off _ _ _ (by omega) (by omega) (by omega), rw_off _ _ _ (by omega) (by omega) (by omega)]
  · rw [um] at vo
    have hr : ∀ a, a + 8 ≤ 8 * w → ∃ r ∈ [(slot w 0, 8 * w)], r.1 ≤ slot w 0 + a ∧ slot w 0 + a + 8 ≤ r.1 + r.2 :=
      fun a ha => ⟨_, List.mem_singleton_self _, by dsimp only; omega, by dsimp only; omega⟩
    simp only [off] at tm
    rw [tm]
    have f1 := frm_writeW (Frm.of_outside vo (List.mem_singleton_self _)) (a := slot w 0 + 8 * (w - 1))
      ((v.mem.readW (p.B + BitVec.ofNat 64 (slot w 0 + 8 * (w - 1))) 64 &&& BitVec.ofNat 64 (2 ^ k - 1)) |||
        BitVec.ofNat 64 (2 ^ (k - 1))) (hr _ (by omega)) (by omega)
    have f2 := frm_writeW f1 (a := slot w 0 + 0)
      (v.mem.readW (p.B + BitVec.ofNat 64 (slot w 0)) 64 ||| BitVec.ofNat 64 1) (hr _ (by omega)) (by omega)
    simpa only [Nat.add_zero] using f2

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
