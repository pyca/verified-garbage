module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Pow
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Comb.Pow

/-!
# DSA signing on PPC64LE: the key pair

`keyPair_ok`: in the P space with p in array 0 and `R² mod p` in array 8,
`g^x mod p` (x the key's last `q_len` octets) compared with y, the mask into
the header's word `hMask`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot)

/-- x, from the key at `key`. -/
def xOf (m : Mem) (L : Lay) (key : Addr) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off key (3 * L.pl + L.ql)) L.ql)

/-- `ptrX`: the key plus `3 p_len + q_len`, `q_len`. -/
theorem ptrX_ok {s : State} {L : Lay} {key sig dig : Addr} (hr : Regs s L key sig dig) :
    WP isa (.block ptrX) s fun t =>
      (t.gpr .r12 = off key (3 * L.pl + L.ql) ∧ t.gpr .r6 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧
        Keep [.r0, .r6, .r12] s t := by
  unfold ptrX
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ptrY_ok hr) fun t ⟨⟨a12, a6, m⟩, k⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = off key (3 * L.pl + L.ql) ∧ u.mem = t.mem) ?_
    (by decide)) fun u ⟨⟨b12, mu⟩, ku⟩ => ?_
  · prun [a12, a6]
    rw [off, show 2 * L.pl + L.ql + L.pl = 3 * L.pl + L.ql by omega]
  · refine WP.mono (getQ_ok ((hr.keep k).keep ku) .r6) fun v ⟨⟨c6, mv⟩, kv⟩ =>
      ⟨⟨(kv.gpr .r12 (by decide)).trans b12, c6, by rw [mv, mu, m]⟩, ((k.trans ku).trans kv).mono (by decide)⟩

/-- The registers `keyPair` writes. -/
def keyPairRegs : List Reg := [.r0, .r6, .r12, .r24] ++ combPowRegs ++ loadRegs ++ eqRegs .r3

/-- `keyPair`: the mask of `g^x mod p = y` into `hMask`. Memory changes only
before the P space's array 8, but for its array 0 and the saved registers. -/
theorem keyPair_ok {s : State} {L : Lay} {key sig dig : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hin : InP s L) (hk : Src s L key (3 * L.pl + 2 * L.ql))
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 8 = 2 ^ (128 * L.wp) % p) :
    WP isa keyPair s fun t =>
      (word t.mem L.S hMask = mask (decide (gOf s.mem L key ^ xOf s.mem L key % p = yOf s.mem L key)) ∧
        InP t L ∧ Outside L.S 0 (slot L.wp 8) s.mem t.mem ∧ arrP t.mem L 0 = arrP s.mem L 0 ∧
        word t.mem L.S (slot L.wp 0 + 8 * L.wp) = word s.mem L.S (slot L.wp 0 + 8 * L.wp) ∧
        (∀ i < 19, word t.mem L.S (saveOff i) = word s.mem L.S (saveOff i)) ∧
        word t.mem L.S hOut = word s.mem L.S hOut) ∧ Keep keyPairRegs s t := by
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hql := hL.ql
  have hbe := hL.buf_end
  have hqZ : L.qOff + 1600 ≤ L.Z := by simp only [Lay.bOff] at hbe; omega
  have e0 := Lay.slot_eq L.wp 0; have e1 := Lay.slot_eq L.wp 1; have e4 := Lay.slot_eq L.wp 4
  have e5 := Lay.slot_eq L.wp 5
  have e8 := Lay.slot_eq L.wp 8; have e28 := Lay.slot_eq L.wp 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  unfold keyPair
  -- The pointers: x's octets into `r24`, g's into `r12`.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ptrX_ok hr) fun s₁ ⟨⟨a12, _, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.r24] (Q := fun u => u.gpr .r24 = off key (3 * L.pl + L.ql) ∧ u.mem = s₁.mem)
    (by prun [a12, BitVec.add_zero]) (by decide)) fun s₂ ⟨⟨a24, m2⟩, k2⟩ => ?_
  refine WP.mono (ptrG_ok ((hr.keep k1).keep k2)) fun s₃ ⟨⟨b12, b6, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  have hm3 : s₃.mem = s.mem := by rw [m3, m2, m1]
  -- `g^x mod p` into array 4.
  refine WP.seq (WP.mono (powSrc_ok (N := off key (L.pl + L.ql)) (E := off key (3 * L.pl + L.ql)) (p := p) hL
      (hr.keep k13) (hin.keep k13 (by decide))
      ((hk.keep k13.rd k13.wr).sub (o := L.pl + L.ql) (k := L.pl) (by omega)) b12
      ((hk.keep k13.rd k13.wr).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega))
      ((k3.gpr .r24 (by decide)).trans a24) (by rw [hm3]; exact hp0) hp hpo (by rw [hm3]; exact hrr))
    fun s₄ ⟨⟨v4, in4, o4⟩, k4⟩ => ?_)
  rw [hm3] at v4 o4
  -- y into array 5.
  refine WP.seq (WP.mono (ptrY_ok ((hr.keep k13).keep k4)) fun s₅ ⟨⟨c12, c6, m5⟩, k5⟩ => ?_)
  have k15 := (k13.trans k4).trans k5
  refine WP.seq (WP.mono (loadArr_ok (in4.env.keep k5 (by decide)) (j := 5) (by decide) c12 c6 (by omega) (by omega)
      (fun i hi => by rw [k15.rd, k15.wr]; exact (hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)).rd i hi)
      (fun i hi x hx => (hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)).sep i hi x (by omega)))
    fun s₆ ⟨⟨v5, _, o6, a10⟩, k6⟩ => ?_)
  rw [m5] at v5 o6
  have en6 := env_keep10 (in4.env.keep k5 (by decide)) k6 (by decide) a10
  -- The comparison, and the mask to the header.
  refine WP.seq (WP.mono (eqMask_ok en6 .r3 (a := 4) (b := 5) (by decide) (by decide))
    fun s₇ ⟨⟨c3, m7⟩, k7⟩ => ?_)
  have k17 := (k15.trans k6).trans k7
  have h21 : s₇.gpr .r21 = L.S := (k17.gpr .r21 (by decide)).trans hr.r21
  have hst : InRegions s₇.wr (L.S + BitVec.ofNat 64 hMask) 8 := (hs.congr k17.wr).st (by simp only [hMask]; omega)
  have he : exec (.store .d .r3 .r21 hMask) s₇ =
      some { s₇ with mem := s₇.mem.writeW (L.S + BitVec.ofNat 64 hMask) (s₇.gpr .r3) } := by
    rw [exec_std (by decide) (by rw [h21]; exact hst), h21]
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = s₇.mem.writeW (L.S + BitVec.ofNat 64 hMask) (s₇.gpr .r3))
    (by prun [he]) (by decide)) fun t ⟨mt, kt⟩ => ?_
  have wo : Outside L.S 0 8 s₆.mem t.mem := by
    rw [mt, m7]; exact writeW_outside s₆.mem L.S (d := 0) _ (by omega)
  have o6' : Outside L.S (slot L.wp 5) (8 * (L.wp + 1)) s₄.mem s₆.mem := o6
  have x4 : val32 s₆.mem L.S (slot L.wp 4) (2 * L.wp) = arrP s₄.mem L 4 :=
    Outside.val32 o6' (by omega) (by omega)
  have y5 : Spec.Rsa.bytesAt s₄.mem (off key (2 * L.pl + L.ql)) L.pl =
      Spec.Rsa.bytesAt s.mem (off key (2 * L.pl + L.ql)) L.pl :=
    (hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)).bytes (Body.ofP hL o4 (by omega) (by omega)) hZ
  rw [x4, v4, v5, y5] at c3
  have kall := k17.trans kt
  refine ⟨⟨?_, ⟨en6.keep (k7.trans kt) (by decide), (kall.gpr .r21 (by decide)).trans hin.h21,
      (kall.gpr .r23 (by decide)).trans hin.h23⟩, ?_, ?_, ?_, fun i hi => ?_, ?_⟩, kall.mono (by decide)⟩
  · rw [mt]
    exact (word_writeW_self s₇.mem L.S hMask _).trans c3
  · exact ((o4.mono (Nat.zero_le _) (by omega)).trans (o6'.mono (Nat.zero_le _) (by omega))).trans
      (wo.mono (Nat.zero_le _) (by omega))
  · show val32 t.mem L.S (slot L.wp 0) (2 * L.wp) = val32 s.mem L.S (slot L.wp 0) (2 * L.wp)
    rw [Outside.val32 wo (by omega) (by omega), Outside.val32 o6' (by omega) (by omega),
      Outside.val32 o4 (by omega) (by omega)]
  · rw [Outside.word wo (by omega) (by omega), Outside.word o6' (by omega) (by omega),
      Outside.word o4 (by omega) (by omega)]
  · rw [Outside.word wo (by simp only [saveOff]; omega) (by simp only [saveOff]; omega),
      Outside.word o6' (by simp only [saveOff]; omega) (by simp only [saveOff]; omega),
      Outside.word o4 (by simp only [saveOff]; omega) (by simp only [saveOff]; omega)]
  · rw [Outside.word wo (by simp only [hOut]; omega) (by simp only [hOut]; omega),
      Outside.word o6' (by simp only [hOut]; omega) (by simp only [hOut]; omega),
      Outside.word o4 (by simp only [hOut]; omega) (by simp only [hOut]; omega)]

end VG.Proof.Dsa.PPC64LE
