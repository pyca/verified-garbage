module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Pow
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyComb
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Comb.Pow

/-!
# DSA signing on PPC64LE: `g^k mod p`

`gk_ok`: in the P space with p in array 0 and `R² mod p` in array 8, `g^k mod
p` (k the nonce's `q_len` octets) to the buffer's first `p_len` octets.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot)

/-- k, from the nonce at `nonce`. -/
def kOf (m : Mem) (L : Lay) (nonce : Addr) : Nat := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m nonce L.ql)

/-- The registers `gk` writes. -/
def gkRegs : List Reg := [.r24, .r0, .r6, .r12] ++ combPowRegs ++ storeRegs

/-- `gk`: `g^k mod p` to the buffer's first `p_len` octets. Memory changes
only in the P space's arrays 1–7 and the buffer's first `p_len` octets. -/
theorem gk_ok {s : State} {L : Lay} {key nonce dig : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key nonce dig) (hin : InP s L) (hk : Src s L key (3 * L.pl + 2 * L.ql))
    (hn : Src s L nonce L.ql)
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 8 = 2 ^ (128 * L.wp) % p) :
    WP isa gk s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.pl) = gOf s.mem L key ^ kOf s.mem L nonce % p ∧
        InP t L ∧ Body L s.mem t.mem ∧ Outside L.Q 1600 (2 ^ 64 - 1600) s.mem t.mem ∧
        arrP t.mem L 0 = arrP s.mem L 0 ∧ arrP t.mem L 8 = arrP s.mem L 8 ∧
        word t.mem L.S (slot L.wp 0 + 8 * L.wp) = word s.mem L.S (slot L.wp 0 + 8 * L.wp)) ∧
        Keep gkRegs s t := by
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hql := hL.ql
  have hpl := hL.pl
  have hbe := hL.buf_end
  have hqZ : L.qOff + 1600 ≤ L.Z := by simp only [Lay.bOff] at hbe; omega
  have e0 := Lay.slot_eq L.wp 0; have e1 := Lay.slot_eq L.wp 1; have e4 := Lay.slot_eq L.wp 4
  have e8 := Lay.slot_eq L.wp 8; have e9 := Lay.slot_eq L.wp 9; have e28 := Lay.slot_eq L.wp 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  unfold gk
  -- The pointers: the nonce into `r24`, g's octets into `r12`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r24] (Q := fun u => u.gpr .r24 = nonce ∧ u.mem = s.mem)
    (by prun [hr.r28, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a24, m1⟩, k1⟩ => ?_
  refine WP.mono (ptrG_ok (hr.keep k1)) fun s₂ ⟨⟨b12, _, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  -- `g^k mod p` into array 4.
  refine WP.seq (WP.mono (powSrc_ok (N := off key (L.pl + L.ql)) (E := nonce) (p := p) hL
      (hr.keep k12) (hin.keep k12 (by decide))
      ((hk.keep k12.rd k12.wr).sub (o := L.pl + L.ql) (k := L.pl) (by omega)) b12 (hn.keep k12.rd k12.wr)
      ((k2.gpr .r24 (by decide)).trans a24) (by rw [hm2]; exact hp0) hp hpo (by rw [hm2]; exact hrr))
    fun s₃ ⟨⟨v4, in3, o3⟩, k3⟩ => ?_)
  rw [hm2] at v4 o3
  have k13 := k12.trans k3
  -- The buffer and `p_len`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (bufBase_ok hL (hr.keep k13) (rd := .r12) (t := .r0) (by decide)) fun s₄ ⟨⟨c12, m4⟩, k4⟩ => ?_
  refine WP.mono (getP_ok ((hr.keep k13).keep k4) .r6) fun s₅ ⟨⟨c6, m5⟩, k5⟩ => ?_
  have k35 := k4.trans k5
  have hm5 : s₅.mem = s₃.mem := by rw [m5, m4]
  refine WP.mono (storeBE_ok (j := 4) (O := L.Buf) (k := L.pl) (in3.env.keep k35 (by decide)) (by decide)
    (ScrL.bufN (hs.congr (k13.trans k35).wr) hL (by omega)) ((k5.gpr .r12 (by decide)).trans c12) c6
    (by omega) (by omega) (combBufPastP hL)) fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [hm5] at vt ot
  have hplt : p < 2 ^ (8 * L.pl) := by
    rw [← hp0, ← hw8, show 8 * (8 * L.wp) = 32 * (2 * L.wp) by omega]; exact val32_lt _ _ _ _
  have v4' : val32 s₃.mem L.S (slot L.wp 4) (2 * L.wp) = gOf s.mem L key ^ kOf s.mem L nonce % p := v4
  have oP : Outside L.S L.qOff (2 ^ 64 - L.qOff) s₃.mem t.mem := by
    intro x hx
    have hlt := (x - L.S).isLt
    rcases hx with hx | hx
    · refine ot x ?_
      by_contra hc
      have := combBufPastP hL x (by simp only [ofs] at hc ⊢; omega)
      simp only [ofs] at hx this; omega
    · simp only [ofs] at hx; omega
  have kall := (k13.trans k35).trans kt
  refine ⟨⟨?_, ⟨in3.env.keep (k35.trans kt) (by decide), (kall.gpr .r21 (by decide)).trans hin.h21,
      (kall.gpr .r23 (by decide)).trans hin.h23⟩, (Body.ofP hL o3 (by omega) (by omega)).trans (Body.ofBuf hL ot (by omega)),
    (comb_pbody_keepQ hL (o3.mono (by omega) (by omega))).trans (combBufKeepQ ot (by omega)), ?_, ?_, ?_⟩,
    kall.mono (by decide)⟩
  · rw [vt, read_low (w := L.wp) _ _ (by omega) (by rw [v4']; exact Nat.lt_trans (Nat.mod_lt _ (by omega)) hplt), v4']
  · show val32 t.mem L.S (slot L.wp 0) (2 * L.wp) = val32 s.mem L.S (slot L.wp 0) (2 * L.wp)
    rw [Outside.val32 oP (by omega) (by omega), Outside.val32 o3 (by omega) (by omega)]
  · show val32 t.mem L.S (slot L.wp 8) (2 * L.wp) = val32 s.mem L.S (slot L.wp 8) (2 * L.wp)
    rw [Outside.val32 oP (by omega) (by omega), Outside.val32 o3 (by omega) (by omega)]
  · rw [Outside.word oP (by omega) (by omega), Outside.word o3 (by omega) (by omega)]

end VG.Proof.Dsa.PPC64LE
