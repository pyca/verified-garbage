module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFront
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Save

/-!
# DSA verification on PPC64LE: the function

`verify_correct`: `vg_dsa_verify` meets `vContract`. After `entry`
(`front_ok`), `checkKey` either runs `body` (`body_ok`) or leaves 0, and
`restore` gives back the nonvolatile registers (`finish_ok`); the result is
the specification's by `Proof/Dsa/Accepted.lean`'s `verifyBytes_compute`.
`verifyLike_ok` states this for any check of the key in place of
`checkKey` that behaves as it does (for prevalidated verification).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- The bytes of a buffer apart from `scratch`, kept by a change in its first `n` bytes. -/
theorem Src.bytesOut {s : State} {L : Lay} {D : Addr} {k : Nat} (h : Src s L D k) {m m' : Mem} {n : Nat}
    (ho : Outside L.S 0 n m m') (hn : n ≤ L.Z) : Spec.Rsa.bytesAt m' D k = Spec.Rsa.bytesAt m D k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ho _ (Or.inr ?_)
  have hi := List.mem_range.mp hi
  by_contra hc
  exact h.sep i hi (D + BitVec.ofNat 64 i) (by omega) rfl

theorem ret_ofNat (c : Prop) [Decidable c] :
    ((BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32).toNat = if c then 1 else 0 := by
  split <;> rfl

theorem saved_all : ∀ r ∈ preserved, ∃ i < 19, r = saved i := by decide

/-- `restore`, from a state with `S` in `r21` and `s`'s nonvolatile registers
in the saved words. -/
theorem finish_ok {s u : State} {S : Addr} {rs : List Reg} (h21 : u.gpr .r21 = S)
    (hwr : ∀ i < 19, InRegions u.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 19, word u.mem S (saveOff i) = s.gpr (saved i)) (hk : Keep rs s u) :
    WP isa (.block restore) u fun w => abiPreserved s w ∧ w.gpr .r3 = u.gpr .r3 := by
  refine WP.mono (restore_ok u (v := fun i => s.gpr (saved i)) h21 hwr fun i hi => ?_)
    fun w ⟨wrs, wot, _, _, _, wsp, wlr⟩ => ⟨⟨fun r hr => ?_, by rw [wsp, hk.sp], by rw [wlr, hk.lr]⟩,
      wot .r3 (by decide)⟩
  · rw [← hsav i hi]
    show u.mem.readW (S + BitVec.ofNat 64 104 + BitVec.ofNat 64 (8 * i)) 64 = u.mem.readW (S + BitVec.ofNat 64 (104 + 8 * i)) 64
    rw [Offset.add_add]
  · obtain ⟨i, hi, rfl⟩ := saved_all r hr
    exact wrs i hi

/-- The specification, on the key's values, r, s and the digest. -/
theorem verify_spec {pl ql : Nat} {key sg dg : List Byte} {p q g y : Nat}
    (widths : Spec.Dsa.lengthsValid pl ql) (hkl : key.length = 3 * pl + ql) (hsl : sg.length = 2 * ql)
    (hkey : Spec.Dsa.publicKeyBytes pl ql key = ⟨⟨p, q, g⟩, y, none⟩) :
    Spec.Dsa.verifyBytes pl ql key sg dg = decide ((VG.Proof.Dsa.shapeValid p q ∧
      VG.Proof.Dsa.publicChecks p q g y) ∧
      ((0 < Spec.Dsa.decodeBE (sg.take ql) ∧ Spec.Dsa.decodeBE (sg.take ql) < q) ∧
        (0 < Spec.Dsa.decodeBE (sg.drop ql) ∧ Spec.Dsa.decodeBE (sg.drop ql) < q)) ∧
      vComp p q g y (Spec.Dsa.decodeBE (dg.take (Spec.Dsa.bitLength q / 8))) (Spec.Dsa.decodeBE (sg.take ql))
        (Spec.Dsa.decodeBE (sg.drop ql)) = Spec.Dsa.decodeBE (sg.take ql)) := by
  by_cases hs : VG.Proof.Dsa.shapeValid p q
  · have h8 : Spec.Dsa.bitLength q = 8 * (Spec.Dsa.bitLength q / 8) := by
      have := hs.1; unfold Spec.Dsa.supportedSizes at this; omega
    rw [VG.Proof.Dsa.verifyBytes_compute widths hs hkl hsl hkey rfl rfl h8]
    simp only [hs, true_and, vComp, Nat.mod_mul_mod, and_assoc]
  · rw [VG.Proof.Dsa.verifyBytes_invalid_shape (by rw [hkey]; exact hs)]
    simp only [hs, false_and, decide_false]

/-- Verification after `Verify.entry`, with the check of the key by `X`:
`checkKey`, or, when `V` gives `KeyOk`, a setup of the working spaces that
assumes it. -/
theorem verifyLike_ok {X : Prog isa → Prog isa → Prog isa} {V : Prop}
    (hX : ∀ {u : State} {L : Lay} {key sig dig : Addr} {d : Nat} {Q : State → Prop} {rest fail : Prog isa},
      L.Ok → ScrL u L → Regs u L key sig dig → u.gpr .r2 = pack L.pl L.ql 0 d → d < 2 ^ 16 →
      Src u L key (3 * L.pl + L.ql) → (V → KeyOk u.mem L key) →
      (∀ t, KeyOk u.mem L key → Checked u t L key sig dig d → Body L u.mem t.mem → Keep ckRegs u t →
        WP isa rest t Q) →
      (∀ t, ¬ KeyOk u.mem L key → Body L u.mem t.mem → Regs t L key sig dig → ScrL t L → Keep ckRegs u t →
        WP isa fail t Q) →
      WP isa (X rest fail) u Q)
    {s : State} (h : vContract.pre s) (hV : V → KeyOk s.mem (layOf s) (s.gpr .r3)) :
    WP isa (.seq (.block Verify.entry) (.seq (X Verify.body (.block [.li .r3 0])) (.block restore))) s
      fun t => abiPreserved s t ∧ vContract.post s t := by
  have hL := layOf_ok h
  have hZ := hL.z256
  have hpre := h
  obtain ⟨-, hrd, hwr, dKS, dGS, dDS, -, nwK, nwG, nwD, -, hv, hkl, hsl, -⟩ := h
  have mkSrc : ∀ {A : Addr} {n k : Nat}, (⟨A, n⟩ : Region) ∈ s.rd →
      (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ → A.toNat + n ≤ 2 ^ 64 → n < 2 ^ 64 →
      k ≤ n → ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (layOf s) A k :=
    fun hm hd hnw hn hk t hr hw => ⟨fun i hi => ⟨_, by rw [hr, hw]; exact List.mem_append_left _ hm,
      Offset.contains_base _ (by omega) (by omega)⟩, fun i hi => Pub.ne_of_disjoint hd (by omega) i (by omega)⟩
  have hplq : 3 * (layOf s).pl + (layOf s).ql = (s.gpr .r4).toNat := by simp only [layOf]; omega
  have srcK := mkSrc (A := s.gpr .r3) (k := 3 * (layOf s).pl + (layOf s).ql) (by rw [hrd]; simp) dKS nwK
    (s.gpr .r4).isLt (by omega)
  have srcG := mkSrc (A := s.gpr .r7) (k := 2 * (layOf s).ql) (by rw [hrd]; simp) dGS nwG
    (s.gpr .r8).isLt (by simp only [layOf]; omega)
  have srcD := mkSrc (A := s.gpr .r9) (k := (s.gpr .r10).toNat) (by rw [hrd]; simp) dDS nwD
    (s.gpr .r10).isLt (Nat.le_refl _)
  -- The specification's values.
  have hkey := VG.Proof.Dsa.publicKeyBytes_at s.mem (s.gpr .r3) (pLen := (layOf s).pl) (qLen := (layOf s).ql)
    (Nat.le_of_eq hplq)
  have hsg0 : (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat).take (s.gpr .r6).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r7) (layOf s).ql := by
    have := VG.Proof.Dsa.bytesAt_slice s.mem (s.gpr .r7) (offset := 0) (len := (layOf s).ql)
      (total := (s.gpr .r8).toNat) (by simp only [layOf]; omega)
    simp only [List.drop_zero, BitVec.add_zero] at this
    exact this
  have hsg1 : (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat).drop (s.gpr .r6).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r7 + BitVec.ofNat 64 (layOf s).ql) (layOf s).ql := by
    rw [← VG.Proof.Dsa.bytesAt_slice s.mem (s.gpr .r7) (offset := (layOf s).ql) (len := (layOf s).ql)
      (total := (s.gpr .r8).toNat) (by simp only [layOf]; omega)]
    refine (List.take_of_length_le ?_).symm
    simp only [List.length_drop, VG.Proof.Bignum.bytesAt_length, layOf]; omega
  refine WP.seq (WP.mono (front_ok hpre) fun s₁ ⟨⟨hr₁, scr₁, r2₁, sav₁, out₁⟩, k₁⟩ => ?_)
  have hwr' : ∀ u : State, ScrL u (layOf s) → ∀ i < 19, InRegions u.wr (off (savW (stackArg s 0)) (8 * i)) 8 :=
    fun u hu i hi => by rw [← saveOff_eq]; exact hu.st (d := 104 + 8 * i) (by simp only [layOf] at hZ ⊢; omega)
  have hsav' : ∀ u : State, Kept (layOf s) s₁.mem u.mem → ∀ i < 19,
      word u.mem (stackArg s 0) (saveOff i) = s.gpr (saved i) := fun u hu i hi => (hu.sav i hi).trans (sav₁ i hi)
  have Out₁ : Outside (layOf s).S 0 (layOf s).Z s.mem s₁.mem :=
    out₁.mono (Nat.le_refl _) (by simp only [layOf] at hZ ⊢; omega)
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := key_kept (srcK s rfl rfl) Out₁
  have hKs : KeyOk s₁.mem (layOf s) (s.gpr .r3) ↔ KeyOk s.mem (layOf s) (s.gpr .r3) := by
    simp only [KeyOk, ep₁, eq₁, eg₁, ey₁]
  have hspec := fun dg => verify_spec (sg := Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (dg := dg) hv
    (by rw [VG.Proof.Bignum.bytesAt_length]; exact hplq.symm)
    (by rw [VG.Proof.Bignum.bytesAt_length]; exact hsl) hkey
  rw [hsg0, hsg1] at hspec
  refine WP.seq (hX hL scr₁ hr₁ r2₁ (by omega) (srcK s₁ k₁.rd k₁.wr) (fun hv => hKs.mpr (hV hv))
    (fun t hK hc hkp kc => ?_)
    (fun t hn hkp hrt scrt kc => ?_))
  · have hkp := Kept.ofBody hL hkp
    have kt := k₁.trans kc
    have hKt := hKs.mp hK
    have hn32 : Spec.Dsa.bitLength (qOf s.mem (layOf s) (s.gpr .r3)) / 8 ≤ 32 := by
      have := hKt.1.1; unfold Spec.Dsa.supportedSizes at this; omega
    refine WP.mono (body_ok hL hK hc hkp (srcK t kt.rd kt.wr) (srcG t kt.rd kt.wr) (by omega)
      ((srcD t kt.rd kt.wr).take (Nat.min_le_left _ _))) fun u ⟨⟨r3, Ku, h21u, scru⟩, ku⟩ => ?_
    refine WP.mono (finish_ok h21u (hwr' u scru) (hsav' u (hkp.trans Ku)) (kt.trans ku))
      fun w ⟨hab, w3⟩ => ⟨hab, ?_⟩
    show ((w.gpr .r3).setWidth 32).toNat = _
    rw [w3, r3, ret_ofNat, hspec, bytesAt_take]
    simp only [decide_eq_true_eq]
    refine ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl)
    have Ot : Outside (layOf s).S 0 (layOf s).Z s.mem t.mem := Out₁.trans hkp.out
    obtain ⟨er, es, ed⟩ := sig_kept (srcG s rfl rfl) (srcD s rfl rfl) Ot
      (k := min (min (s.gpr .r10).toNat 64) (Spec.Dsa.bitLength (qOf s₁.mem (layOf s) (s.gpr .r3)) / 8))
      (by omega)
    rw [er, es, ed, ep₁, eq₁, eg₁, ey₁]
    rw [show min (min (s.gpr .r10).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (layOf s) (s.gpr .r3)) / 8) =
      min (s.gpr .r10).toNat (Spec.Dsa.bitLength (qOf s.mem (layOf s) (s.gpr .r3)) / 8) by omega]
    exact ⟨fun h => ⟨hKt, h⟩, fun h => h.2⟩
  · have hkp := Kept.ofBody hL hkp
    refine WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = 0#64 ∧ u.mem = t.mem) (by prun) (by decide))
      fun u ⟨⟨u3, um⟩, ku⟩ => ?_
    refine WP.mono (finish_ok ((ku.gpr .r21 (by decide)).trans hrt.r21) (hwr' u (scrt.congr ku.wr))
      (hsav' u (by rw [um]; exact hkp)) ((k₁.trans kc).trans ku)) fun w ⟨hab, w3⟩ => ⟨hab, ?_⟩
    show ((w.gpr .r3).setWidth 32).toNat = _
    rw [w3, u3, hspec, decide_eq_false (fun hx => hn (hKs.mpr hx.1))]
    rfl

theorem verify_correct (s : State) (h : vContract.pre s) :
    ∃ tr t, Exec isa Verify.verify s tr t ∧ abiPreserved s t ∧ vContract.post s t := by
  show WP isa Verify.verify s fun t => abiPreserved s t ∧ vContract.post s t
  unfold Verify.verify
  exact verifyLike_ok (X := checkKey) (V := False)
    (fun hL hs hr h2 hd hk _ hrest hfail => checkKey_ok hL hs hr h2 hd hk hrest hfail) h False.elim

end VG.Proof.Dsa.PPC64LE
