module

public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRows
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSave
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRaw
import VerifiedGarbage.Proof.Bignum.AArch64.WideZero

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem saved_lane_exists : ∀ r ∈ VG.Impl.Bignum.AArch64.ProductEight.regs,
    ∃ v, (r, v, 0) ∈ savedLanes := by
  have h : ∀ r ∈ VG.Impl.Bignum.AArch64.ProductEight.regs,
      (r, ((savedLanes.find? (·.1 == r)).map (·.2.1)).getD .v0, 0) ∈ savedLanes := by
    decide +kernel
  exact fun r hr => ⟨_, h r hr⟩

/-- Exact full product in the existing scratch arrays, with every saved
scalar register restored before returning. No arithmetic input bound is needed. -/
theorem raw_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B (8 * k) minv)
    (hZ : slot (8 * k) 8 ≤ Z) (hk : 0 < k) (hk' : k < 2 ^ 56)
    {a b : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    (hb1 : b ≠ Public.aAcc) (hb2 : b ≠ Public.aTmp) :
    WP isa (VG.Impl.Bignum.AArch64.ProductEight.raw a b) s fun t =>
      wv t.mem B (productBase k) (16 * k + 2) =
        wv s.mem B (slot (8 * k) a) (8 * k) * wv s.mem B (slot (8 * k) b) (8 * k) ∧
      Outside B (productBase k) (8 * (16 * k + 2)) s.mem t.mem ∧
      t.gpr .x8 = off B (productBase k) ∧ t.gpr .x10 = off B (slot (8 * k) Public.aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 (8 * k) ∧ t.gpr .x15 = minv ∧ t.gpr .x7 = 0 ∧
      Keep mmRegs s t := by
  have hn := hs.nowrap
  have hP : productBase k + 8 * (16 * k + 2) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega_arith
  have sep : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp →
      slot (8 * k) j + 64 * k ≤ productBase k ∨
        productBase k + 8 * (16 * k + 2) ≤ slot (8 * k) j := by
    intro j hj hj1 hj2
    have := slot_sep (w := 8 * k) hj1
    have := slot_sep (w := 8 * k) hj2
    unfold productBase slot Public.aAcc Public.aTmp at *
    omega_arith
  unfold VG.Impl.Bignum.AArch64.ProductEight.raw
  refine WP.seq (WP.mono (Square.squareSetup_ok hs h0 hH hZ ha)
    fun u ⟨⟨hu8, _, _, hu12, _, hu7, hum⟩, ku⟩ => ?_)
  refine WP.seq (WP.mono (WideLoops.zero_ok (hs.congr ku.wr) hu8 hu7 hu12 hP hk hk')
    fun v ⟨hv0, hvo, kv⟩ => ?_)
  have ksv := ku.trans kv
  have hvs : Outside B (productBase k) (8 * (16 * k + 2)) s.mem v.mem := by
    intro x hx
    exact (hvo x hx).trans (congrArg (fun m : Mem => m x) hum)
  have hHv : Hdr v.mem B (8 * k) minv :=
    (Square.scratch_arrays (by simpa only [productBase, show 2 * (8 * k) = 16 * k by omega_arith] using hvs)).hdr hH
  refine WP.seq (WP.block_append ?_)
  refine WP.mono (saves_ok v) fun v0 ⟨⟨hv0m, lanes⟩, ks⟩ => ?_
  refine WP.mono (start_ok (hs.congr (ks.wr.trans ksv.wr))
    ((ks.gpr .x0 (by decide)).trans ((ksv.gpr .x0 (by decide)).trans h0))
    (hv0m ▸ hHv) hZ ha hk'
    ((ks.gpr .x12 (by decide)).trans ((kv.gpr .x12 (by decide)).trans hu12)))
    fun v1 ⟨⟨hv18, hv112, hv1m, hv1v⟩, kstart⟩ => ?_
  have kpre := (ksv.trans ks).trans kstart
  have hv1zero : wv v1.mem B (productBase k) (16 * k + 2) = 0 := by
    rw [hv1m, hv0m]
    exact hv0
  have hv1H : Hdr v1.mem B (8 * k) minv := by rw [hv1m, hv0m]; exact hHv
  refine WP.seq (WP.mono (productRows_ok (hs.congr kpre.wr)
    ((kpre.gpr .x0 (by decide)).trans h0)
    ((kstart.gpr .x7 (by decide)).trans ((ks.gpr .x7 (by decide)).trans
      ((kv.gpr .x7 (by decide)).trans hu7))) hv1H hZ hv18 hv112 ha hb hk hk'
    (sep a ha ha1 ha2) (sep b hb hb1 hb2) hv1zero)
    fun v2 ⟨hr, hvec⟩ => ?_)
  apply WP.block_append
  refine WP.mono (restores_ok v2) fun v3 ⟨⟨hv3m, restored⟩, kr⟩ => ?_
  have kv3 := (kpre.trans hr.keep).trans kr
  have hvs3 : Outside B (productBase k) (8 * (16 * k + 2)) s.mem v3.mem := by
    have hvs1 : Outside B (productBase k) (8 * (16 * k + 2)) s.mem v1.mem := by
      intro x hx
      exact (congrArg (fun m : Mem => m x) (hv1m.trans hv0m)).trans (hvs x hx)
    intro x hx
    exact (congrArg (fun m : Mem => m x) hv3m).trans ((hvs1.trans hr.frame) x hx)
  have hHv3 : Hdr v3.mem B (8 * k) minv :=
    (Square.scratch_arrays (by simpa only [productBase, show 2 * (8 * k) = 16 * k by omega_arith] using hvs3)).hdr hH
  refine WP.mono (Square.squareSetup_ok (hs.congr kv3.wr)
    ((kv3.gpr .x0 (by decide)).trans h0) hHv3 hZ ha)
    fun t ⟨⟨ht8, _, ht10, ht12, ht15, ht7, htm⟩, kt⟩ => ?_
  have kout := kv3.trans kt
  refine ⟨?_, ?_, ht8, ht10, ht12, ht15, ht7, ?_⟩
  · have hread : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp →
        wv v1.mem B (slot (8 * k) j) (8 * k) = wv s.mem B (slot (8 * k) j) (8 * k) := by
      intro j hj hj1 hj2
      have hjZ := slot_le (w := 8 * k) hj
      rw [hv1m, hv0m]
      exact hvs.wv (by have := sep j hj hj1 hj2; omega_arith) (by omega_arith)
    rw [htm, hv3m, hr.value, hread a ha ha1 ha2, hread b hb hb1 hb2]
  · intro x hx
    exact (congrArg (fun m : Mem => m x) htm).trans (hvs3 x hx)
  · refine ⟨?_, kout.rd, kout.wr, kout.sp, kout.vcs⟩
    intro r hrmm
    by_cases hrs : r ∈ VG.Impl.Bignum.AArch64.ProductEight.regs
    · obtain ⟨vreg, hvreg⟩ := saved_lane_exists r hrs
      have hkr := restored (r, vreg, 0) hvreg
      have hvsaved := lanes (r, vreg, 0) hvreg
      have hLane : laneOf v2 vreg 0 = laneOf v0 vreg 0 := by
        unfold laneOf
        rw [hvec, hv1v]
      have hrv : v.gpr r = s.gpr r := ksv.gpr r (by
        intro h
        exact hrmm (by exact (show ∀ r ∈ [.x8, .x9, .x10, .x12, .x15, .x7] ++ [.x14, .x16], r ∈ mmRegs by decide) r h))
      exact (kt.gpr r (by intro h; exact hrmm ((show ∀ r ∈ [.x8, .x9, .x10, .x12, .x15, .x7], r ∈ mmRegs by decide) r h))).trans
        (hkr.trans (hLane.trans (hvsaved.trans hrv)))
    · exact kout.gpr r (by
        intro h
        have hsub : ∀ r ∈
            ((([.x8, .x9, .x10, .x12, .x15, .x7] ++ [.x14, .x16]) ++ []) ++ [.x8, .x12]) ++
              rawRegs ++ VG.Impl.Bignum.AArch64.ProductEight.regs ++ [.x8, .x9, .x10, .x12, .x15, .x7],
            r ∈ mmRegs ∨ r ∈ VG.Impl.Bignum.AArch64.ProductEight.regs := by decide +kernel
        exact (hsub r h).elim hrmm hrs)


theorem low_value {m : Mem} {B : Addr} {e n pad x : Nat}
    (h : wv m B e (n + pad) = x) (hx : x < 2 ^ (64 * n)) : wv m B e n = x := by
  have hp := wv_add m B e n pad
  have hu : wv m B (e + 8 * n) pad = 0 := by
    by_contra hz
    have hle := Nat.mul_le_mul_left (2 ^ (64 * n)) (show 1 ≤ wv m B (e + 8 * n) pad by omega_arith)
    simp only [Nat.mul_one] at hle
    omega_arith
  rw [hu, Nat.mul_zero, Nat.add_zero] at hp
  exact hp.symm.trans h

/-- The public-width form used by Montgomery callers, including the low
product needed by reduction and the full scratch frame. -/
theorem raw_width_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw : 16 ≤ w) (hw' : w < 2 ^ 31) (hmod : w % 8 = 0)
    {a b : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    (hb1 : b ≠ Public.aAcc) (hb2 : b ≠ Public.aTmp) :
    WP isa (VG.Impl.Bignum.AArch64.ProductEight.raw a b) s fun t =>
      wv t.mem B (slot w Public.aAcc + 16) (2 * w) =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w ∧
      Outside B (slot w Public.aAcc + 16) (8 * (2 * w + 2)) s.mem t.mem ∧
      t.gpr .x8 = off B (slot w Public.aAcc + 16) ∧ t.gpr .x10 = off B (slot w Public.aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x15 = minv ∧ t.gpr .x7 = 0 ∧ Keep mmRegs s t := by
  have he : w = 8 * (w / 8) := by omega_arith
  have hH' : Hdr s.mem B (8 * (w / 8)) minv := he ▸ hH
  have hZ' : slot (8 * (w / 8)) 8 ≤ Z := he ▸ hZ
  refine WP.mono (raw_ok hs h0 hH' hZ' (by omega_arith) (by omega_arith) ha hb ha1 ha2 hb1 hb2)
    fun t ⟨hv, ho, h8, h10, h12, h15, h7, kt⟩ => ?_
  have hlen : 16 * (w / 8) + 2 = 2 * w + 2 := by omega_arith
  simp only [productBase, ← he, hlen] at hv ho h8 h10 h12
  refine ⟨low_value hv ?_, ho, h8, h10, h12, h15, h7, kt⟩
  have hp := Nat.mul_lt_mul'' (wv_lt s.mem B (slot w a) w) (wv_lt s.mem B (slot w b) w)
  rw [← Nat.pow_add, show 64 * w + 64 * w = 64 * (2 * w) by omega_arith] at hp
  exact hp

end VG.Proof.Bignum.AArch64.ProductEight
