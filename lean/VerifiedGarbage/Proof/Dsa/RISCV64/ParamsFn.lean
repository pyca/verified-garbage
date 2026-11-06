module

public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFront
public import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA domain checks on RISC-V: the function

As on PPC64LE (`Proof/Dsa/PPC64LE/Params/Fn.lean`). `checkParameters_correct`:
`vg_dsa_check_parameters` meets `pcContract`. After `entry`,
`checkParams` leaves 1 or 0 as the domain passes `ParamsOk` or not
(`checkParams_ok`), which is the specification's `checkParametersBytes`
(`checkParameters_spec`), and `restore` gives back the callee-saved
registers (`finish_ok`). `checkLike_ok` is this for any check `X`
(`checkKey` for the validation of a public key).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Dsa.RISCV64

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

/-- The buffer at `a0` (`a1` octets), the only one read, apart from `scratch`: its first `n` octets. -/
theorem psrc_of {s : State} {n : Nat} (hrd : s.rd = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩])
    (dPS : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a4, (s.gpr .a5).toNat * 8⟩)
    (hn : n ≤ (s.gpr .a1).toNat) {t : State} (hr : t.rd = s.rd) (hw : t.wr = s.wr) :
    Src t (playOf s) (s.gpr .a0) n := by
  have := (s.gpr .a1).isLt
  exact ⟨fun i hi => ⟨_, by rw [hr, hw, hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
    Offset.contains_base _ (by omega) (by omega)⟩,
    fun i hi => Pub.ne_of_disjoint dPS (by omega) i (by omega)⟩

/-- `a0 := c`, then `restore`. -/
theorem pret_ok {s t : State} {c : Nat} (hc : c = 0 ∨ c = 1) (hL : (playOf s).Ok)
    (h6 : t.gpr .s6 = (playOf s).S) (scrt : ScrL t (playOf s))
    (hsav : ∀ i < 13, word t.mem (s.gpr .a4) (saveOff i) = s.gpr (saved i)) :
    WP isa (.block [.li .a0 c]) t fun u => WP isa (.block restore) u fun w =>
      ((∀ r ∈ preserved, w.gpr r = s.gpr r) ∧ w.gpr .ra = s.gpr .ra) ∧
        ((w.gpr .a0).setWidth 32).toNat = c := by
  have hZ := hL.z256
  have hli : WP isa (.block [.li .a0 c]) t fun u =>
      (u.gpr .a0 = BitVec.ofNat 64 c ∧ u.mem = t.mem) ∧ Keep [.a0] t u := by
    rcases hc with rfl | rfl
    · exact WP.keep _ (by brun [exec_li_zero]) (by decide) (by rfl)
    · exact WP.keep _ (by brun [exec_li_lit (show 1 < 2048 by decide)]) (by decide) (by rfl)
  refine WP.mono hli fun u ⟨⟨u0, um⟩, ku⟩ => ?_
  have scru : ScrL u (playOf s) := scrt.congr ku.2.2
  refine WP.mono (finish_ok ((ku.gpr (by decide)).trans h6)
    (fun i hi => by rw [← saveOff_eq]; exact scru.st (d := saveOff i) (by simp only [saveOff, playOf] at hZ ⊢; omega_arith))
    (fun i hi => by
      rw [← saveOff_eq]
      exact scru.al8 (d := saveOff i) (by simp only [saveOff, playOf] at hZ ⊢; omega_arith)
        (by simp only [saveOff]; omega))
    (fun i hi => by rw [um]; exact hsav i hi)) fun w ⟨hab, w0⟩ => ⟨hab, ?_⟩
  rw [w0, u0, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- A check by `X` (`checkParams` or `checkKey`) of the octets at `a0` after
`Params.entry`, which leaves 1 or 0 as they pass `Ok` or not, then `restore`. -/
theorem checkLike_ok {X : Prog isa → Prog isa → Prog isa} {Ok : Mem → Lay → Addr → Prop}
    [∀ m L k, Decidable (Ok m L k)] {rs : List Reg} {s : State} {n : Nat}
    (hL : (playOf s).Ok) (hwr : s.wr = [⟨s.gpr .a4, (s.gpr .a5).toNat * 8⟩])
    (nw : (s.gpr .a4).toNat + (s.gpr .a5).toNat * 8 ≤ 2 ^ 64) (alS : (s.gpr .a4).toNat % 8 = 0)
    (hsrc : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → Src t (playOf s) (s.gpr .a0) n)
    (hOk : ∀ {m' : Mem}, Outside (playOf s).S 0 (playOf s).Z s.mem m' →
      (Ok m' (playOf s) (s.gpr .a0) ↔ Ok s.mem (playOf s) (s.gpr .a0)))
    (hX : ∀ {u : State} {Q : State → Prop} {rest fail : Prog isa}, ScrL u (playOf s) →
      Regs u (playOf s) (s.gpr .a0) 0 →
      word u.mem (playOf s).S hLens = pack (playOf s).pl (playOf s).ql 0 0 →
      Src u (playOf s) (s.gpr .a0) n →
      (∀ t, Ok u.mem (playOf s) (s.gpr .a0) → Checked u t (playOf s) (s.gpr .a0) 0 0 →
        Kept (playOf s) u.mem t.mem → Keep rs u t → WP isa rest t Q) →
      (∀ t, ¬ Ok u.mem (playOf s) (s.gpr .a0) → Kept (playOf s) u.mem t.mem →
        Regs t (playOf s) (s.gpr .a0) 0 → ScrL t (playOf s) → Keep rs u t → WP isa fail t Q) →
      WP isa (X rest fail) u Q) :
    WP isa (.seq (.block Params.entry) (.seq (X (.block [.li .a0 1]) (.block [.li .a0 0])) (.block restore))) s
      fun w => ((∀ r ∈ preserved, w.gpr r = s.gpr r) ∧ w.gpr .ra = s.gpr .ra) ∧
        ((w.gpr .a0).setWidth 32).toNat = if Ok s.mem (playOf s) (s.gpr .a0) then 1 else 0 := by
  have hZ := hL.z256
  refine WP.seq (WP.mono (pfront_ok_of hL hwr nw alS) fun s₁ ⟨F, k₁⟩ => ?_)
  have hsav' : ∀ u : State, Kept (playOf s) s₁.mem u.mem → ∀ i < 13,
      word u.mem (s.gpr .a4) (saveOff i) = s.gpr (saved i) := fun u hu i hi =>
    (hu.word (Or.inr ⟨by simp only [saveOff, hLens]; omega, by simp only [saveOff]; omega⟩)).trans (F.sav i hi)
  have Out₁ : Outside (playOf s).S 0 (playOf s).Z s.mem s₁.mem :=
    F.out.mono (Nat.le_refl _) (by simp only [playOf] at hZ ⊢; omega)
  have hPs := hOk Out₁
  refine WP.seq (hX F.scr F.regs F.lens (hsrc k₁.2.1 k₁.2.2) (fun t hP hc hkp kc => ?_)
    (fun t hn hkp hrt scrt kc => ?_))
  · refine WP.mono (pret_ok (c := 1) (Or.inr rfl) hL hc.regs.s6 hc.scr (hsav' t hkp)) fun u hu =>
      WP.mono hu fun w ⟨hab, w0⟩ => ⟨hab, by rw [w0, ite_eq_left (hPs.mp hP)]⟩
  · refine WP.mono (pret_ok (c := 0) (Or.inl rfl) hL hrt.s6 scrt (hsav' t hkp)) fun u hu =>
      WP.mono hu fun w ⟨hab, w0⟩ => ⟨hab, by rw [w0, ite_eq_right (fun hx => hn (hPs.mpr hx))]⟩

theorem checkParameters_correct (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa Params.checkParameters s tr t ∧ abiPreserved s t ∧ pcContract.post s t := by
  show WP isa Params.checkParameters s fun t => abiPreserved s t ∧ pcContract.post s t
  have hL := playOf_ok h
  have hpre := h
  obtain ⟨hrd, hwr, dPS, -, nw, hv, hpl, -, alS, -⟩ := h
  have hplq : 2 * (playOf s).pl + (playOf s).ql = (s.gpr .a1).toNat := by simp only [playOf]; omega
  have hspec : Spec.Dsa.checkParametersBytes (s.gpr .a2).toNat (s.gpr .a3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) = decide (ParamsOk s.mem (playOf s) (s.gpr .a0)) := by
    rw [← hplq]; exact checkParameters_spec hv
  have src : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr →
      Src t (playOf s) (s.gpr .a0) (2 * (playOf s).pl + (playOf s).ql) :=
    fun hr hw => psrc_of hrd dPS (Nat.le_of_eq hplq) hr hw
  unfold Params.checkParameters
  refine WP.mono (WP.rdwr (checkLike_ok (X := checkParams) (Ok := ParamsOk) hL hwr nw alS src (fun Out => ?_)
    (fun hs hr h2 hk hrest hfail => checkParams_ok hL hs hr h2 (by decide) hk hrest hfail)))
    fun w ⟨⟨⟨hp, hra⟩, w0⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, ?_⟩
  · have hk := src rfl rfl
    simp only [ParamsOk, pOf, qOf, gOf]
    rw [(hk.take (k := (playOf s).pl) (by omega)).bytes Out (by omega),
      (hk.sub (o := (playOf s).pl) (k := (playOf s).ql) (by omega)).bytes Out (by omega),
      (hk.sub (o := (playOf s).pl + (playOf s).ql) (k := (playOf s).pl) (by omega)).bytes Out (by omega)]
  · show ((w.gpr .a0).setWidth 32).toNat = _
    rw [w0, hspec]
    simp only [decide_eq_true_eq]

end VG.Proof.Dsa.RISCV64
