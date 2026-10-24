module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Front
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFn
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA domain checks on PPC64LE: the function

`checkParameters_correct`: `vg_dsa_check_parameters` meets `pcContract`.
After `entry` (`pfront_ok`), `checkParams` leaves 1 or 0 as the domain
passes `ParamsOk` or not (`checkParams_ok`), which is the specification's
`checkParametersBytes` (`checkParameters_spec`, by `Proof/Dsa/Derive.lean`'s
`checkParametersBytes_eq`), and `restore` gives back the nonvolatile
registers (`finish_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- The specification's domain checks, on the domain's values. -/
theorem checkParameters_spec {m : Mem} {L : Lay} {key : Addr} (hv : Spec.Dsa.lengthsValid L.pl L.ql) :
    Spec.Dsa.checkParametersBytes L.pl L.ql (Spec.Rsa.bytesAt m key (2 * L.pl + L.ql)) =
      decide (ParamsOk m L key) := by
  rw [VG.Proof.Dsa.checkParametersBytes_eq hv (VG.Proof.Bignum.bytesAt_length _ _ _)]
  have ep : (Spec.Rsa.bytesAt m key (2 * L.pl + L.ql)).take L.pl = Spec.Rsa.bytesAt m key L.pl := by
    have := VG.Proof.Dsa.bytesAt_slice m key (offset := 0) (len := L.pl) (total := 2 * L.pl + L.ql) (by omega)
    simp only [List.drop_zero, BitVec.add_zero] at this
    exact this
  have eq : ((Spec.Rsa.bytesAt m key (2 * L.pl + L.ql)).drop L.pl).take L.ql =
      Spec.Rsa.bytesAt m (off key L.pl) L.ql :=
    VG.Proof.Dsa.bytesAt_slice m key (by omega)
  have eg : ((Spec.Rsa.bytesAt m key (2 * L.pl + L.ql)).drop (L.pl + L.ql)).take L.pl =
      Spec.Rsa.bytesAt m (off key (L.pl + L.ql)) L.pl :=
    VG.Proof.Dsa.bytesAt_slice m key (by omega)
  simp only [VG.Proof.Dsa.paramsBytes_eq, ep, eq, eg, VG.Proof.Dsa.powMod_eq]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff (p := ParamsOk m L key)]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_true]
  unfold ParamsOk VG.Proof.Dsa.shapeValid pOf qOf gOf
  constructor
  · rintro ⟨⟨hs, hp, hq⟩, hgq, hd, hg, -⟩
    exact ⟨⟨hs, hq, hp⟩, hg, hd, hgq⟩
  · rintro ⟨⟨hs, hq, hp⟩, hg, hd, hgq⟩
    exact ⟨⟨hs, hp, hq⟩, hgq, hd, hg, hg⟩

/-- The domain, readable and apart from `scratch`. -/
theorem pre_psrc {s : State} (h : pcContract.pre s) {t : State} (hr : t.rd = s.rd) (hw : t.wr = s.wr) :
    Src t (playOf s) (s.gpr .r3) (2 * (playOf s).pl + (playOf s).ql) := by
  obtain ⟨hrd, -, dPS, -, -, -, hpl, -⟩ := h
  have hn := (s.gpr .r4).isLt
  have e : 2 * (playOf s).pl + (playOf s).ql = (s.gpr .r4).toNat := by simp only [playOf]; omega
  exact ⟨fun i hi => ⟨_, by rw [hr, hw, hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
    Offset.contains_base _ (by omega) (by omega)⟩,
    fun i hi => Pub.ne_of_disjoint dPS (by omega) i (by omega)⟩

theorem checkParameters_correct (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa Params.checkParameters s tr t ∧ abiPreserved s t ∧ pcContract.post s t := by
  show WP isa Params.checkParameters s fun t => abiPreserved s t ∧ pcContract.post s t
  have hL := playOf_ok h
  have hZ := hL.z256
  have hpre := h
  obtain ⟨-, -, -, -, -, hv, hpl, -⟩ := h
  have hplq : 2 * (playOf s).pl + (playOf s).ql = (s.gpr .r4).toNat := by simp only [playOf]; omega
  have hspec : Spec.Dsa.checkParametersBytes (s.gpr .r5).toNat (s.gpr .r6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) = decide (ParamsOk s.mem (playOf s) (s.gpr .r3)) := by
    rw [← hplq]; exact checkParameters_spec hv
  unfold Params.checkParameters
  refine WP.seq (WP.mono (pfront_ok hpre) fun s₁ ⟨⟨hr₁, scr₁, r2₁, sav₁, out₁⟩, k₁⟩ => ?_)
  have hwr' : ∀ u : State, ScrL u (playOf s) → ∀ i < 19, InRegions u.wr (off (savW (s.gpr .r7)) (8 * i)) 8 :=
    fun u hu i hi => by rw [← saveOff_eq]; exact hu.st (d := 104 + 8 * i) (by simp only [playOf] at hZ ⊢; omega)
  have hsav' : ∀ u : State, Kept (playOf s) s₁.mem u.mem → ∀ i < 19,
      word u.mem (s.gpr .r7) (saveOff i) = s.gpr (saved i) := fun u hu i hi => (hu.sav i hi).trans (sav₁ i hi)
  have Out₁ : Outside (playOf s).S 0 (playOf s).Z s.mem s₁.mem :=
    out₁.mono (Nat.le_refl _) (by simp only [playOf] at hZ ⊢; omega)
  obtain ⟨ep₁, eq₁, eg₁⟩ := params_kept (pre_psrc hpre rfl rfl) Out₁
  have hPs : ParamsOk s₁.mem (playOf s) (s.gpr .r3) ↔ ParamsOk s.mem (playOf s) (s.gpr .r3) := by
    simp only [ParamsOk, ep₁, eq₁, eg₁]
  -- `r3 := c`, then `restore`.
  have ret : ∀ (t : State) (c : Nat), Kept (playOf s) s₁.mem t.mem → t.gpr .r21 = (playOf s).S →
      ScrL t (playOf s) → Keep ckRegs s₁ t → c < 2 → writesOnly [.r3] (.block [.li .r3 c]) = true →
      WP isa (.block [.li .r3 c]) t fun u => WP isa (.block restore) u fun w =>
        abiPreserved s w ∧ ((w.gpr .r3).setWidth 32).toNat = c := fun t c hkp h21 scrt kc hc hwo => by
    refine WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 c ∧ u.mem = t.mem)
      (by prun [show c < 2 ^ 15 by omega]) hwo) fun u ⟨⟨u3, um⟩, ku⟩ => ?_
    refine WP.mono (finish_ok ((ku.gpr .r21 (by decide)).trans h21) (hwr' u (scrt.congr ku.wr))
      (hsav' u (by rw [um]; exact hkp)) ((k₁.trans kc).trans ku)) fun w ⟨hab, w3⟩ => ⟨hab, ?_⟩
    rw [w3, u3, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine WP.seq (checkParams_ok hL scr₁ hr₁ r2₁ (by decide) (pre_psrc hpre k₁.rd k₁.wr)
    (fun t hP hc hkp kc => ?_) (fun t hn hkp hrt scrt kc => ?_))
  · refine WP.mono (ret t 1 (Kept.ofBody hL hkp) hc.regs.r21 hc.scr kc (by decide) (by decide)) fun u hu =>
      WP.mono hu fun w ⟨hab, w3⟩ => ⟨hab, ?_⟩
    show ((w.gpr .r3).setWidth 32).toNat = _
    rw [w3, hspec, decide_eq_true (hPs.mp hP)]
    rfl
  · refine WP.mono (ret t 0 (Kept.ofBody hL hkp) hrt.r21 scrt kc (by decide) (by decide)) fun u hu =>
      WP.mono hu fun w ⟨hab, w3⟩ => ⟨hab, ?_⟩
    show ((w.gpr .r3).setWidth 32).toNat = _
    rw [w3, hspec, decide_eq_false (fun hx => hn (hPs.mpr hx))]
    rfl

end VG.Proof.Dsa.PPC64LE
