import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.LadderLayout
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages

/-! # secp256k1 multiplication by the base point -/

namespace VG.Proof.Ecdsa.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.Secp256k1
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

abbrev gSlots : List Nat := [EXPP, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
  T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP]

theorem ladderG_ok (hc : BaseCfgOk secp256k1) (hC : Law secp256k1.C)
    {base : Addr} {g : Reg → BitVec 64} {s : State} (hs : Scr s base size)
    (F : Fixed secp256k1 base g s.mem) {k : Nat} (hkl : k < 2 ^ (64 * secp256k1.n))
    (hrx : sv secp256k1 base s RX = 0) (hry : sv secp256k1 base s RY = secp256k1.mont 1)
    (hrz : sv secp256k1 base s RZ = 0)
    (hb3 : sv secp256k1 base s EXPP = secp256k1.mont (3 * secp256k1.C.b))
    (ht₀ : ∀ t < 64 * secp256k1.n, s.mem (off base (bitsAt secp256k1.n 0 + t)) = if k.testBit t then 1 else 0) :
    WP isa (ladder ladderCfg) s fun s' => KeepRegs (powClob 4) s s' ∧
      Unch base (ladW ladderCfg) s.mem s'.mem ∧ ModOkA secp256k1.MP' size secp256k1.C.p s'.mem base ∧
      (∀ x ∈ [secp256k1.sl RX, secp256k1.sl RY, secp256k1.sl RZ], wordsVal s'.mem base x 4 < secp256k1.C.p) ∧
      Rep secp256k1.C (tmv secp256k1.C 4 base s' (secp256k1.sl RX))
        (tmv secp256k1.C 4 base s' (secp256k1.sl RY))
        (tmv secp256k1.C 4 base s' (secp256k1.sl RZ)) (mul k (G secp256k1.C)) := by
  have hpR := unitMod_pow_two hc.p_odd (64 * secp256k1.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, secp256k1.mont x < secp256k1.C.p := fun x => Nat.mod_lt _ (by omega)
  have hlt : ∀ x ∈ ladR ladderCfg, wordsVal s.mem base x secp256k1.MP'.n < secp256k1.C.p := by
    intro x hx
    have hx' : x ∈ [AP, EXPP, GX, GY, ONEP, RX, RY, RZ].map secp256k1.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv secp256k1 _ s i < secp256k1.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F.ap (hmont _)
    · exact lt_of_eq_of_lt hb3 (hmont _)
    · exact lt_of_eq_of_lt F.gx (hmont _)
    · exact lt_of_eq_of_lt F.gy (hmont _)
    · exact lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega))
    · exact lt_of_eq_of_lt hrx (by omega)
    · exact lt_of_eq_of_lt hry (hmont _)
    · exact lt_of_eq_of_lt hrz (by omega)
  have hG : Rep secp256k1.C (tmv secp256k1.C secp256k1.n base s (secp256k1.sl GX)) (tmv secp256k1.C secp256k1.n base s (secp256k1.sl GY))
      (tmv secp256k1.C secp256k1.n base s (secp256k1.sl ONEP)) (G secp256k1.C) := by
    show Rep secp256k1.C (toM _ _ (wordsVal s.mem _ (secp256k1.sl GX) secp256k1.n)) (toM _ _ (wordsVal s.mem _ (secp256k1.sl GY) secp256k1.n))
      (toM _ _ (wordsVal s.mem _ (secp256k1.sl ONEP) secp256k1.n)) (G secp256k1.C)
    rw [F.gx, F.gy, F.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
    exact rep_affine' hC _ _
  have hR : Rep secp256k1.C (tmv secp256k1.C secp256k1.n base s (secp256k1.sl RX)) (tmv secp256k1.C secp256k1.n base s (secp256k1.sl RY))
      (tmv secp256k1.C secp256k1.n base s (secp256k1.sl RZ)) (mul (k >>> (64 * secp256k1.n)) (G secp256k1.C)) := by
    show Rep secp256k1.C (toM _ _ (sv secp256k1 _ s RX)) (toM _ _ (sv secp256k1 _ s RY)) (toM _ _ (sv secp256k1 _ s RZ)) _
    rw [hrx, hry, hrz, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
    exact rep_infinity' hC
  have hstep := step_rep (L := ladderCfg) (k := k) hC hc.onG (by
      show toM secp256k1.C.p (2 ^ (64 * secp256k1.n)) (wordsVal s.mem _ (secp256k1.sl AP) secp256k1.n) = _
      rw [F.ap]; exact toM_cmont hc _)
    (by
      show toM secp256k1.C.p (2 ^ (64 * secp256k1.n)) (sv secp256k1 base s EXPP) = _
      rw [hb3]; exact toM_cmont hc _) hG
  exact WP.mono (ladder_ok ladLay ladA hpR hs (modP_of hc F.mp) hlt hstep hR ht₀)
    fun _ ⟨K, U, M, L, R⟩ => ⟨K, U, M, L, by rw [Nat.shiftRight_zero] at R; exact R⟩

theorem gMul_ok (hc : BaseCfgOk secp256k1) (hC : Law secp256k1.C)
    {base : Addr} {g : Reg → BitVec 64} {s : State} (hs : Scr s base size)
    (F : Fixed secp256k1 base g s.mem) {k : Nat} (hkl : k < 2 ^ (64 * secp256k1.n))
    (hrx : sv secp256k1 base s RX = 0) (hry : sv secp256k1 base s RY = secp256k1.mont 1)
    (hrz : sv secp256k1 base s RZ = 0)
    (ht₀ : ∀ t < 64 * secp256k1.n, s.mem (off base (bitsAt secp256k1.n 0 + t)) = if k.testBit t then 1 else 0) :
    WP isa gMul s fun s' => KeepRegs (powClob 4) s s' ∧
      Unch base (slW secp256k1 gSlots) s.mem s'.mem ∧ ModOkA secp256k1.MP' size secp256k1.C.p s'.mem base ∧
      (∀ x ∈ [secp256k1.sl RX, secp256k1.sl RY, secp256k1.sl RZ], wordsVal s'.mem base x 4 < secp256k1.C.p) ∧
      Rep secp256k1.C (tmv secp256k1.C 4 base s' (secp256k1.sl RX))
        (tmv secp256k1.C 4 base s' (secp256k1.sl RY))
        (tmv secp256k1.C 4 base s' (secp256k1.sl RZ)) (mul k (G secp256k1.C)) := by
  have hn := hs.nowrap
  refine WP.seq (WP.mono (setConst_ok hs (n := 4) (o := secp256k1.sl EXPP)
    (x := secp256k1.mont (3 * secp256k1.C.b)) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨b₁, K₁, O₁⟩ => ?_)
  have U₁ : Unch base (slW secp256k1 [EXPP]) s.mem s₁.mem := O₁.unch
  have hs₁ := hs.of_keepRegs K₁ (by decide)
  have F₁ := F.unch hc.n10 hn (fixedOk_slW (l := [EXPP]) (by decide)) U₁
  have e₁ : ∀ {i}, i < 45 → i ≠ EXPP → sv secp256k1 base s₁ i = sv secp256k1 base s i :=
    fun hi he => sv_unch U₁ hc.n10 hn hi (apart_slW (by simpa using he))
  have ht₁ : ∀ t < 64 * secp256k1.n, s₁.mem (off base (bitsAt secp256k1.n 0 + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    rw [tbl_unch U₁ hc.n10 (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t)]
    exact ht₀ t ht
  refine WP.mono (ladderG_ok hc hC hs₁ F₁ hkl
    ((e₁ (by decide) (by decide)).trans hrx) ((e₁ (by decide) (by decide)).trans hry)
    ((e₁ (by decide) (by decide)).trans hrz) b₁ ht₁) fun s' ⟨K, U, M, L, R⟩ =>
      ⟨(K₁.mono (by decide)).trans K, ?_, M, L, R⟩
  rw [ladW_eq] at U
  exact U₁.trans U

end VG.Proof.Ecdsa.AArch64.Secp256k1
