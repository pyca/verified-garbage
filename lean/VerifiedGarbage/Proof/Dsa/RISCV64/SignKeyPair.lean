module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCommon
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
public import VerifiedGarbage.Impl.Dsa.RISCV64.Sign
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA signing on RISC-V: the key pair's check

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/KeyPair.lean`). `keyPair_ok`: in the
P space with p in array 0 and `R² mod p` in array 24, the mask of
`g^x mod p = y` into the header's word `hMask`; the P space's arrays 1–23
change.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Sign
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- x, from the key at `key`. -/
def xOf (m : Mem) (L : Lay) (key : Addr) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off key (3 * L.pl + L.ql)) L.ql)

/-- `ptrX`: the key plus `3 p_len + q_len`, `q_len`. -/
theorem ptrX_ok {s : State} {L : Lay} {key sig : Addr} (hs : ScrL s L) (hL : L.Ok) (hr : Regs s L key sig) :
    WP isa (.block ptrX) s fun t =>
      (t.gpr .s7 = off key (3 * L.pl + L.ql) ∧ t.gpr .s8 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧
        Keep ptrRegs s t := by
  unfold ptrX
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ptrY_ok hs hL hr) fun t ⟨⟨a7, a8, m⟩, k⟩ => ?_
  refine WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = off key (3 * L.pl + L.ql) ∧ u.mem = t.mem) ?_
    (by rfl) (by rfl)) fun u ⟨⟨b7, mu⟩, ku⟩ => ?_
  · brun [a7, a8, off_off]
    rw [show 2 * L.pl + L.ql + L.pl = 3 * L.pl + L.ql by omega]
  · refine WP.mono (getQ_ok (hs.congr (k.trans ku).2.2) hL ((hr.keepM k m).keepM ku mu) .s8) fun v ⟨⟨c8, mv⟩, kv⟩ =>
      ⟨⟨(kv.gpr (by decide)).trans b7, c8, by rw [mv, mu, m]⟩, ((k.trans ku).trans kv).mono (by decide)⟩

/-- The registers `keyPair` writes. -/
def keyPairRegs : List Reg := ptrRegs ++ [.s9] ++ ptrRegs ++ powPRegs ++ ptrRegs ++ loadRegs ++ eqRegs .a0

/-- A change in the P space's arrays 1–23. -/
abbrev PLow (L : Lay) (m m' : Mem) : Prop := Outside L.S (slot L.wp 1) (23 * (8 * (L.wp + 2))) m m'

theorem PLow.parr {L : Lay} {m m' : Mem} (h : PLow L m m') : PArr L m m' :=
  PArr.of h (Nat.le_refl _) (by simp only [Lay.slot_eq]; omega)

theorem PLow.arr {L : Lay} (hL : L.Ok) {m m' : Mem} (h : PLow L m m') {j : Nat} (hj : j < 28)
    (hj' : j = 0 ∨ 24 ≤ j) : arrP m' L j = arrP m L j := by
  have := slot_lt (w := L.wp) hj
  have hb := hL.buf_end
  have hn := hL.nowrap
  have e1 := Lay.slot_eq L.wp 1; have e24 := Lay.slot_eq L.wp 24; have ej := Lay.slot_eq L.wp j
  rcases hj' with rfl | hj'
  · exact h.wordsVal (Or.inl (by simp only [Lay.slot_eq]; omega)) (by simp only [Lay.bOff, Lay.qOff] at hb; omega)
  · exact h.wordsVal (Or.inr (by have := slot_mono (w := L.wp) hj'; omega))
      (by simp only [Lay.bOff, Lay.qOff] at hb; omega)

theorem PLow.word0 {L : Lay} (hL : L.Ok) {m m' : Mem} (h : PLow L m m') :
    word m' L.S (slot L.wp 0) = word m L.S (slot L.wp 0) := by
  have hw := hL.wp_ge
  exact h.word (Or.inl (by simp only [Lay.slot_eq]; omega)) (by simp only [Lay.slot_eq]; omega)

theorem mask_word0 {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.S hMask 8 m m') :
    word m' L.S (slot L.wp 0) = word m L.S (slot L.wp 0) := by
  have hw := hL.wp_ge
  exact h.word (Or.inr (by simp only [hMask, Lay.slot_eq]; omega)) (by simp only [Lay.slot_eq]; omega)

theorem kp_a4 (L : Lay) (hL : L.Ok) {m m' : Mem} (h : Outside L.S (slot L.wp 5) (8 * (L.wp + 1)) m m') :
    wordsVal m' L.S (slot L.wp 4) L.wp = wordsVal m L.S (slot L.wp 4) L.wp := by
  have hw := hL.wp_ge
  exact h.wordsVal (Or.inl (by simp only [Lay.slot_eq]; omega)) (by simp only [Lay.slot_eq]; omega)

theorem kp_o5 (L : Lay) {m m' : Mem} (h : Outside L.S (slot L.wp 5) (8 * (L.wp + 1)) m m') : PLow L m m' :=
  h.mono (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega)

theorem PLow.body {L : Lay} (hL : L.Ok) {m m' : Mem} (h : PLow L m m') : Body L m m' :=
  h.parr.pbody.body hL

theorem PLow.keepQ {L : Lay} (hL : L.Ok) {m m' : Mem} (h : PLow L m m') : Outside L.Q 1600 (2 ^ 64 - 1600) m m' :=
  h.parr.pbody.keepQ hL

/-- `keyPair`: the mask of `g^x mod p = y` into `hMask`. Memory changes only
in `hMask` and in the P space's arrays 1–23. -/
theorem keyPair_ok {s : State} {L : Lay} {key sig : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hin : InP s L) (hi : PInv s L) (hk : Src s L key (3 * L.pl + 2 * L.ql))
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa keyPair s fun t =>
      (word t.mem L.S hMask = mask (decide (gOf s.mem L key ^ xOf s.mem L key % p = yOf s.mem L key)) ∧
        InP t L ∧ PInv t L ∧ ∃ m, PLow L s.mem m ∧ Outside L.S hMask 8 m t.mem) ∧ Keep keyPairRegs s t := by
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hql := hL.ql
  unfold keyPair
  -- The pointers: x's octets into `s9`, g's into `s7`.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ptrX_ok hs hL hr) fun s₁ ⟨⟨a7, _, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = off key (3 * L.pl + L.ql) ∧ u.mem = s₁.mem)
    (by brun [a7, BitVec.add_zero]) (by decide) (by rfl)) fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  refine WP.mono (ptrG_ok (hs.congr k12.2.2) hL (hr.keepM k12 hm2)) fun s₃ ⟨⟨b7, b8, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  have hm3 : s₃.mem = s.mem := by rw [m3, hm2]
  -- `g^x mod p` into array 4.
  refine WP.seq (WP.mono (powSrc_ok (N := off key (L.pl + L.ql)) (E := off key (3 * L.pl + L.ql)) (p := p) hL
      (hs.congr k13.2.2) (hr.keepM k13 hm3) (hin.keep k13) (by
        show ((word s₃.mem L.S (slot L.wp 0)).toNat * (s₃.gpr .t1).toNat + 1) % 2 ^ 64 = 0
        rw [hm3, k13.gpr (by decide)]; exact hi)
      ((hk.keep k13.2.1 k13.2.2).sub (o := L.pl + L.ql) (k := L.pl) (by omega)) b7
      ((hk.keep k13.2.1 k13.2.2).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega))
      ((k3.gpr (by decide)).trans a9) (by rw [hm3]; exact hp0) hp hpo (by rw [hm3]; exact hrr))
    fun s₄ ⟨⟨v4, in4, i4, o4⟩, k4⟩ => ?_)
  rw [hm3] at v4 o4
  -- y into array 5.
  have k14 := k13.trans k4
  have hr4 : Regs s₄ L key sig := hr.keep k14 (PLow.body hL o4)
  refine WP.seq (WP.mono (ptrY_ok (hs.congr k14.2.2) hL hr4) fun s₅ ⟨⟨c7, c8, m5⟩, k5⟩ => ?_)
  have k15 := k14.trans k5
  have hY := (hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega))
  refine WP.seq (WP.mono (loadArr_ok (in4.env.keep k5) (j := 5) (N := off key (2 * L.pl + L.ql)) (by decide)
      (by rw [c7]; exact (BitVec.add_zero _).symm) c8 (by omega) (by omega)
      (fun i hi => by rw [k15.2.1, k15.2.2]; exact hY.rd i hi)
      (fun i hi x hx => hY.sep i hi x (by
        have := hL.buf_end; simp only [Lay.bOff] at this; omega)))
    fun s₆ ⟨⟨v5, _, o6, a76⟩, k6⟩ => ?_)
  rw [m5] at v5 o6
  have en5 := in4.env.keep k5
  have en6 : Env s₆ L.S L.qOff L.wp := ⟨en5.hs.congr k6.2.2, a76, (k6.gpr (by decide)).trans en5.s5,
    (k6.gpr (by decide)).trans en5.t0, en5.w2, en5.w48, en5.hZ⟩
  -- The comparison, and the mask to the header.
  refine WP.seq (WP.mono (eqMask_ok en6 (j := 4) (k := 5) (rd := .a0) (by decide) (by decide) (by decide))
    fun s₇ ⟨⟨c0, m7⟩, k7⟩ => ?_)
  have k17 := (k15.trans k6).trans k7
  obtain ⟨_, hal0⟩ := ScrL.hdr (hs.congr k17.2.2) hL (d := 0) (by decide) (by decide)
  have hst : InRegions s₇.wr (off L.S 0) 8 := (hs.congr k17.2.2).st (by omega)
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = s₇.mem.writeW (off L.S 0) (s₇.gpr .a0))
    (by brun [hMask, (k17.gpr (r := .s6) (by decide)).trans hr.s6, hst, hal0]) (by decide) (by rfl))
    fun t ⟨mt, kt⟩ => ?_
  have wo : Outside L.S hMask 8 s₆.mem t.mem := by
    rw [mt, m7]; exact writeW_outside s₆.mem L.S _ (by simp only [hMask]; omega)
  have o6' : Outside L.S (slot L.wp 5) (8 * (L.wp + 1)) s₄.mem s₆.mem := o6
  have o46 : PLow L s.mem s₆.mem := o4.trans (kp_o5 L o6')
  have x4 : wordsVal s₆.mem L.S (slot L.wp 4) L.wp = arrP s₄.mem L 4 := kp_a4 L hL o6'
  have y5 : Spec.Rsa.bytesAt s₄.mem (off key (2 * L.pl + L.ql)) L.pl =
      Spec.Rsa.bytesAt s.mem (off key (2 * L.pl + L.ql)) L.pl :=
    hY.bytes (PLow.body hL o4) (by omega)
  rw [x4, v4, v5, y5] at c0
  have kall := k17.trans kt
  refine ⟨⟨?_, ⟨en6.keep (k7.trans kt), (kall.gpr (by decide)).trans hin.s6⟩, ?_, ⟨s₆.mem, o46, wo⟩⟩, ?_⟩
  · rw [mt]
    exact (word_writeW_self s₇.mem L.S hMask _).trans c0
  · show ((word t.mem L.S (slot L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [mask_word0 hL wo, (kp_o5 L o6').word0 hL, (((k5.trans k6).trans k7).trans kt).gpr (by decide)]
    exact i4
  · simp only [keyPairRegs, List.append_assoc] at kall ⊢
    exact kall.mono (by decide)

end VG.Proof.Dsa.RISCV64
