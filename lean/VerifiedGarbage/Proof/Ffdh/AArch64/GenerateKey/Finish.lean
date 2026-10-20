module

public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Tail
import VerifiedGarbage.Proof.Rsa.AArch64.CvFail
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.Stages
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_ffdh_generate_key` on AArch64: the results

With the key's flag `F` in the outer `sF`: x and y masked by it, and
`3 − 2 F` returned (`T12` … `T15`); and with the scalar out of range, zeros
to both and 2 returned (`fail2_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.GenerateKey

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- In the outer workspace, with the outer header's slots the results use. -/
structure Fz (p : GkP) (t : State) : Prop where
  scr : Scr t p.B p.Z
  x0 : t.gpr .x0 = p.B
  hZ : 128 * p.k + 256 ≤ p.Z
  k1 : 64 ≤ p.k
  k2 : p.k ≤ 1024
  wX : word t.mem p.B (8 * sX) = p.xp
  wY : word t.mem p.B (8 * sY) = p.yp
  wK : word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k

theorem Fz.of_pa {p : GkP} {rb : List Byte} {ss : List (Addr × List Byte)} {mi : BitVec 64} {t : State}
    (h : Pa ((p.D₀ rb).withSrcs ss) mi t) : Fz p t := by
  have hb := h.1
  have hs := h.2.2.2.2.1
  exact ⟨hb.scr, h.2.2.2.2.2.2, hb.hZ, hb.k1, hb.k2, hs.get (i := sX) (v := p.xp) (by simp [GkP.D₀]),
    hs.get (i := sY) (v := p.yp) (by simp [GkP.D₀]), hs.get (i := sK) (by simp)⟩

theorem Fz.out {p : GkP} {t u : State} (h : Fz p t) (hout : Outside p.B p.Z (2 ^ 64) t.mem u.mem)
    (hwr : u.wr = t.wr) (h0 : u.gpr .x0 = t.gpr .x0) : Fz p u := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  have e : ∀ i < 32, word u.mem p.B (8 * i) = word t.mem p.B (8 * i) := fun i hi =>
    hout.word (Or.inl (by omega)) (by omega)
  exact ⟨h.scr.congr hwr, h0.trans h.x0, h.hZ, h.k1, h.k2, (e _ (by decide)).trans h.wX, (e _ (by decide)).trans h.wY,
    (e _ (by decide)).trans h.wK⟩

/-- x's octets, masked by `c`. -/
abbrev Xm (p : GkP) (rb : List Byte) (c : Bool) (m : Mem) : Prop :=
  ∀ i < p.k, m (p.xp + BitVec.ofNat 64 i) = if c then (p.xo rb).getD i 0 else 0

/-- y's octets, masked by `c`. -/
abbrev Ym (p : GkP) (rb : List Byte) (c : Bool) (m : Mem) : Prop :=
  ∀ i < p.k, m (p.yp + BitVec.ofNat 64 i) = if c then (p.yo rb).getD i 0 else 0

/-- The mask of the flag in `x15`. -/
def T12 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  Fz p t ∧ word t.mem p.B (8 * sF) = bit (p.F rb) ∧ t.gpr .x15 = mask (decide (p.F rb)) ∧
    Xm p rb true t.mem ∧ Ym p rb true t.mem ∧ Ok p rb ∧ p.pv = true

theorem mBlk_ok {t : State} {B : Addr} {f : BitVec 64} (h0 : t.gpr .x0 = B) (hF : word t.mem B (8 * sF) = f)
    (hl : InRegions (t.rd ++ t.wr) (off B (8 * sF)) 8) :
    WP isa (.block [ldh .x9 sF, movi .x7 0, .sub .x .x15 .x7 .x9]) t fun u =>
      (u.gpr .x15 = 0 - f ∧ u.mem = t.mem) ∧ Keep [.x7, .x9, .x15] t u :=
  WP.keep _ (by brun [h0, hdr_enc (show sF < 32 by decide), hl, hF]; rfl) (by decide) (by decide) (by decide +kernel)

theorem t11_t12 (p : GkP) (rb : List Byte) (t : State) (h : T11 p rb t) :
    WP isa (.block [ldh .x9 sF, movi .x7 0, .sub .x .x15 .x7 .x9]) t fun u => T12 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hF⟩, ho, hpv⟩ := h
  have hb := hP.1
  have hO := hP.outer
  have hz : Fz p t := Fz.of_pa (rb := rb) hP
  have hx : Src t p.B p.Z p.xp (p.xo rb) := hb.srcs (p.xp, p.xo rb) (by simp)
  obtain ⟨hyl, -, hy⟩ := yo_facts hb hP.2.2.2.2.2.1
  have hxl := xo_length p rb hb.bl_lt ho
  refine WP.mono (mBlk_ok hO.x0 hF (hO.ld (by decide))) fun u ⟨⟨h15, hm⟩, k⟩ =>
    ⟨⟨hz.out (by rw [hm]; exact Outside.refl _ _ _ _) k.wr (k.gpr .x0 (by decide)), by rw [hm]; exact hF,
      by rw [h15, Exchange.bit_mask], fun i hi => ?_, fun i hi => ?_, ho, hpv⟩, k.mono (by decide)⟩
  · rw [hm, hx.val i (by rw [hxl]; exact hi)]
    simp only [↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hxl]; exact hi),
      Option.getD_some]
  · rw [hm, hy.val i (by rw [hyl]; exact hi)]
    simp only [↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hyl]; exact hi),
      Option.getD_some]

/-- After x masked. -/
def T13 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  Fz p t ∧ word t.mem p.B (8 * sF) = bit (p.F rb) ∧ t.gpr .x15 = mask (decide (p.F rb)) ∧
    Xm p rb (decide (p.F rb)) t.mem ∧ Ym p rb true t.mem ∧ Ok p rb ∧ p.pv = true

theorem fz_word {p : GkP} {t u : State} (h : Fz p t) (hout : Outside p.B p.Z (2 ^ 64) t.mem u.mem) {i : Nat}
    (hi : i < 32) : word u.mem p.B (8 * i) = word t.mem p.B (8 * i) := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  exact hout.word (Or.inl (by omega)) (by omega)

theorem t12_t13 (p : GkP) (rb : List Byte) (t : State) (h : T12 p rb t) (hd : Dst p t) :
    WP isa (GenerateKey.maskOut sX) t fun u => T13 p rb u ∧ KX t u := by
  obtain ⟨hz, hF, h15, hX, hY, ho, hpv⟩ := h
  obtain ⟨-, ⟨gXY, -, -, -, nX, nY, -, -⟩, -⟩ := id ho
  have hk1 := hz.k1
  have hk2 := hz.k2
  have hZ := hz.hZ
  refine WP.mono (maskOut_ok hz.scr hz.x0 (by omega) (show sX < 32 by decide) hz.wX hz.wK (by omega) (by omega) h15
    (fun i hi => (hd i hi).1.1)) fun u ⟨hb, hfr, k⟩ => ?_
  have hout := outside_of_frame (fun j hj => (hd j hj).1.2) hfr
  refine ⟨⟨hz.out hout k.wr (k.gpr .x0 (by decide)), by rw [fz_word hz hout (by decide)]; exact hF,
    (k.gpr .x15 (by decide)).trans h15, fun i hi => ?_, fun i hi => ?_, ho, hpv⟩, k.mono (by decide)⟩
  · rw [hb i hi, hX i hi]; simp only [↓reduceIte]
  · rw [hfr _ fun j hj => (ne_of_disj gXY nX nY hj hi).symm]; exact hY i hi

/-- After x and y masked. -/
def T14 (p : GkP) (rb : List Byte) (t : State) : Prop :=
  Fz p t ∧ word t.mem p.B (8 * sF) = bit (p.F rb) ∧ Xm p rb (decide (p.F rb)) t.mem ∧
    Ym p rb (decide (p.F rb)) t.mem ∧ Ok p rb ∧ p.pv = true

theorem t13_t14 (p : GkP) (rb : List Byte) (t : State) (h : T13 p rb t) (hd : Dst p t) :
    WP isa (GenerateKey.maskOut sY) t fun u => T14 p rb u ∧ KX t u := by
  obtain ⟨hz, hF, h15, hX, hY, ho, hpv⟩ := h
  obtain ⟨-, ⟨gXY, -, -, -, nX, nY, -, -⟩, -⟩ := id ho
  have hk1 := hz.k1
  have hk2 := hz.k2
  have hZ := hz.hZ
  refine WP.mono (maskOut_ok hz.scr hz.x0 (by omega) (show sY < 32 by decide) hz.wY hz.wK (by omega) (by omega) h15
    (fun i hi => (hd i hi).2.1)) fun u ⟨hb, hfr, k⟩ => ?_
  have hout := outside_of_frame (fun j hj => (hd j hj).2.2) hfr
  refine ⟨⟨hz.out hout k.wr (k.gpr .x0 (by decide)), by rw [fz_word hz hout (by decide)]; exact hF,
    fun i hi => ?_, fun i hi => ?_, ho, hpv⟩, k.mono (by decide)⟩
  · rw [hfr _ fun j hj => ne_of_disj gXY nX nY hi hj]; exact hX i hi
  · rw [hb i hi, hY i hi]; simp only [↓reduceIte]

/-- The status from the flag. -/
theorem fBlk_ok {t : State} {B : Addr} {f : BitVec 64} (h0 : t.gpr .x0 = B) (hF : word t.mem B (8 * sF) = f)
    (hl : InRegions (t.rd ++ t.wr) (off B (8 * sF)) 8) :
    WP isa (.block [ldh .x9 sF, movi .x0 3, .lsl .x .x9 .x9 1, .sub .x .x0 .x0 .x9]) t fun u =>
      (u.gpr .x0 = BitVec.ofNat 64 3 - (f <<< 1) ∧ u.mem = t.mem) ∧ Keep [.x0, .x9] t u :=
  WP.keep _ (by brun [h0, hdr_enc (show sF < 32 by decide), hl, hF]; rfl) (by decide) (by decide)
    (by decide +kernel)

/-- Zeros to x and y, and `r` returned. -/
theorem fail_ok (p : GkP) (rb : List Byte) {r : Nat} (hr : r < 65536) (t : State) (hz : Fz p t) (hd : Dst p t)
    (ho : Ok p rb) :
    WP isa (GenerateKey.fail r) t fun u =>
      (u.gpr .x0 = BitVec.ofNat 64 r ∧ Xm p rb false u.mem ∧ Ym p rb false u.mem) ∧ KX t u := by
  obtain ⟨-, ⟨gXY, -, -, -, nX, nY, -, -⟩, -⟩ := id ho
  have hk1 := hz.k1
  have hk2 := hz.k2
  have hZ := hz.hZ
  unfold GenerateKey.fail
  simp only [seqs]
  refine WP.seq (WP.mono (VG.Proof.Rsa.AArch64.zeroOut_ok hz.scr hz.x0 (by omega) (by decide) (by decide) hz.wX
    hz.wK (by omega) (by omega) ⟨fun i hi => (hd i hi).1.1, fun i hi => (hd i hi).1.2⟩)
    fun t₁ ⟨hb₁, hfr₁, k₁⟩ => ?_)
  have hout₁ := outside_of_frame (fun j hj => (hd j hj).1.2) hfr₁
  have hz₁ : Fz p t₁ := hz.out hout₁ k₁.wr (k₁.gpr .x0 (by decide))
  refine WP.seq (WP.mono (VG.Proof.Rsa.AArch64.zeroOut_ok hz₁.scr hz₁.x0 (by omega) (by decide) (by decide) hz₁.wY
    hz₁.wK (by omega) (by omega) ⟨fun i hi => by rw [k₁.wr]; exact (hd i hi).2.1, fun i hi => (hd i hi).2.2⟩)
    fun t₂ ⟨hb₂, hfr₂, k₂⟩ => ?_)
  refine WP.mono (ret_ok t₂ hr) fun u ⟨⟨h0, hm⟩, k⟩ => ⟨⟨h0, fun i hi => ?_, fun i hi => ?_⟩,
    keep_trans (k₁.mono (by decide)) (keep_trans (k₂.mono (by decide)) (k.mono (by decide)))⟩
  · rw [hm, hfr₂ _ fun j hj => ne_of_disj gXY nX nY hi hj, hb₁ i hi]; rfl
  · rw [hm, hb₂ i hi]; rfl

end VG.Proof.Ffdh.AArch64.GenerateKey
