module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFront
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA verification on RISC-V: the function

As on PPC64LE (`Proof/Dsa/PPC64LE/VerifyFn.lean`). `verify_correct`:
`vg_dsa_verify` meets `vContract`. After `entry` (`front_ok`), `checkKey`
either runs `body` (`body_ok`) or leaves 0, and `restore` gives back the
callee-saved registers and `ra` (`finish_ok`); the result is the
specification's by `Proof/Dsa/Accepted.lean`'s `verifyBytes_compute`.
`verifyLike_ok` states this for any check of the key in place of
`checkKey` that behaves as it does (for prevalidated verification).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Dsa.RISCV64

theorem ret_ofNat (c : Prop) [Decidable c] :
    ((BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32).toNat = if c then 1 else 0 := by
  split <;> rfl

theorem saved_all : ∀ r ∈ preserved, ∃ i < 13, r = saved i := by decide

/-- `restore`, from a state with `S` in `s6` and `s`'s callee-saved registers
and `ra` in the saved words. -/
theorem finish_ok {s u : State} {S : Addr} (h6 : u.gpr .s6 = S)
    (hwr : ∀ i < 13, InRegions u.wr (off (savW S) (8 * i)) 8)
    (hal : ∀ i < 13, (off (savW S) (8 * i)).toNat % 8 = 0)
    (hsav : ∀ i < 13, word u.mem S (saveOff i) = s.gpr (saved i)) :
    WP isa (.block restore) u fun w =>
      ((∀ r ∈ preserved, w.gpr r = s.gpr r) ∧ w.gpr .ra = s.gpr .ra) ∧ w.gpr .a0 = u.gpr .a0 := by
  refine WP.mono (restore_ok u (v := fun i => s.gpr (saved i)) h6 hwr hal fun i hi => ?_)
    fun w ⟨wrs, wot, _⟩ => ⟨⟨fun r hr => ?_, wrs 11 (by decide)⟩, wot .a0 (by decide)⟩
  · rw [← hsav i hi]
    show u.mem.readW (off (savW S) (8 * i)) 64 = u.mem.readW (S + BitVec.ofNat 64 (saveOff i)) 64
    rw [saveOff_eq]
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
      have := hs.1; unfold Spec.Dsa.supportedSizes at this; omega_arith
    rw [VG.Proof.Dsa.verifyBytes_compute widths hs hkl hsl hkey rfl rfl h8]
    simp only [hs, true_and, vComp, Nat.mod_mul_mod, and_assoc]
  · rw [VG.Proof.Dsa.verifyBytes_invalid_shape (by rw [hkey]; exact hs)]
    simp only [hs, false_and, decide_false]

/-- The key's values, kept by a change in `scratch`. -/
theorem keyVals_kept {s : State} {L : Lay} {key : Addr} (hk : Src s L key (3 * L.pl + L.ql)) {m m' : Mem}
    (h : Outside L.S 0 L.Z m m') :
    pOf m' L key = pOf m L key ∧ qOf m' L key = qOf m L key ∧ gOf m' L key = gOf m L key ∧
      yOf m' L key = yOf m L key := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [pOf]; rw [(hk.take (k := L.pl) (by omega)).bytes h (by omega)]
  · simp only [qOf]; rw [(hk.sub (o := L.pl) (k := L.ql) (by omega)).bytes h (by omega)]
  · simp only [gOf]; rw [(hk.sub (o := L.pl + L.ql) (k := L.pl) (by omega)).bytes h (by omega)]
  · simp only [yOf]; rw [(hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)).bytes h (by omega)]

/-- Verification after `Verify.entry`, with the check of the key by `X`:
`checkKey`, or, when `V` gives `KeyOk`, a setup of the working spaces that
assumes it. -/
theorem verifyLike_ok {X : Prog isa → Prog isa → Prog isa} {V : Prop}
    (hX : ∀ {u : State} {L : Lay} {key sig : Addr} {d : Nat} {Q : State → Prop} {rest fail : Prog isa},
      L.Ok → ScrL u L → Regs u L key sig → word u.mem L.S hLens = pack L.pl L.ql 0 d → d < 2 ^ 16 →
      Src u L key (3 * L.pl + L.ql) → (V → KeyOk u.mem L key) →
      (∀ t, KeyOk u.mem L key → Checked u t L key sig d → Kept L u.mem t.mem → Keep ckRegs u t →
        WP isa rest t Q) →
      (∀ t, ¬ KeyOk u.mem L key → Kept L u.mem t.mem → Regs t L key sig → ScrL t L → Keep ckRegs u t →
        WP isa fail t Q) →
      WP isa (X rest fail) u Q)
    {s : State} (h : vContract.pre s) (hV : V → KeyOk s.mem (layOf s) (s.gpr .a0)) :
    WP isa (.seq (.block Verify.entry) (.seq (X Verify.body (.block [.li .a0 0])) (.block restore))) s
      fun t => ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ vContract.post s t := by
  have hL := layOf_ok h
  have hZ := hL.z256
  have hpre := h
  obtain ⟨hrd, hwr, dKS, dGS, dDS, -, nwK, nwG, nwD, -, hv, hkl, hsl, -, -, -⟩ := h
  have mkSrc : ∀ {A : Addr} {n k : Nat}, (⟨A, n⟩ : Region) ∈ s.rd →
      (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ → A.toNat + n ≤ 2 ^ 64 → n < 2 ^ 64 →
      k ≤ n → ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (layOf s) A k :=
    fun hm hd hnw hn hk t hr hw => ⟨fun i hi => ⟨_, by rw [hr, hw]; exact List.mem_append_left _ hm,
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
      fun i hi => Pub.ne_of_disjoint hd (by omega_arith) i (by omega_arith)⟩
  have hplq : 3 * (layOf s).pl + (layOf s).ql = (s.gpr .a1).toNat := by simp only [layOf]; omega_arith
  have srcK := mkSrc (A := s.gpr .a0) (k := 3 * (layOf s).pl + (layOf s).ql) (by rw [hrd]; simp) dKS nwK
    (s.gpr .a1).isLt (by omega_arith)
  have srcG := mkSrc (A := s.gpr .a4) (k := 2 * (layOf s).ql) (by rw [hrd]; simp) dGS nwG
    (s.gpr .a5).isLt (by simp only [layOf]; omega_arith)
  have srcD := mkSrc (A := s.gpr .a6) (k := (s.gpr .a7).toNat) (by rw [hrd]; simp) dDS nwD
    (s.gpr .a7).isLt (Nat.le_refl _)
  -- The specification's values.
  have hkey := VG.Proof.Dsa.publicKeyBytes_at s.mem (s.gpr .a0) (pLen := (layOf s).pl) (qLen := (layOf s).ql)
    (Nat.le_of_eq hplq)
  have hsg0 : (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat).take (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a4) (layOf s).ql := by
    have := VG.Proof.Dsa.bytesAt_slice s.mem (s.gpr .a4) (offset := 0) (len := (layOf s).ql)
      (total := (s.gpr .a5).toNat) (by simp only [layOf]; omega_arith)
    simp only [List.drop_zero, BitVec.add_zero] at this
    exact this
  have hsg1 : (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat).drop (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a4 + BitVec.ofNat 64 (layOf s).ql) (layOf s).ql := by
    rw [← VG.Proof.Dsa.bytesAt_slice s.mem (s.gpr .a4) (offset := (layOf s).ql) (len := (layOf s).ql)
      (total := (s.gpr .a5).toNat) (by simp only [layOf]; omega_arith)]
    refine (List.take_of_length_le ?_).symm
    simp only [List.length_drop, VG.Proof.Bignum.bytesAt_length, layOf]; omega_arith
  refine WP.seq (WP.mono (front_ok hpre) fun s₁ ⟨F, k₁⟩ => ?_)
  have hwr' : ∀ u : State, ScrL u (layOf s) → ∀ i < 13, InRegions u.wr (off (savW (stackArg s 0)) (8 * i)) 8 :=
    fun u hu i hi => by
      rw [← saveOff_eq]; exact hu.st (d := saveOff i) (by simp only [saveOff, layOf] at hZ ⊢; omega_arith)
  have hal' : ∀ u : State, ScrL u (layOf s) → ∀ i < 13, (off (savW (stackArg s 0)) (8 * i)).toNat % 8 = 0 :=
    fun u hu i hi => by
      rw [← saveOff_eq]
      exact hu.al8 (d := saveOff i) (by simp only [saveOff, layOf] at hZ ⊢; omega_arith)
        (by simp only [saveOff]; omega)
  have hsav' : ∀ u : State, Kept (layOf s) s₁.mem u.mem → ∀ i < 13,
      word u.mem (stackArg s 0) (saveOff i) = s.gpr (saved i) := fun u hu i hi =>
    (hu.word (Or.inr ⟨by simp only [saveOff, hLens]; omega, by simp only [saveOff]; omega⟩)).trans (F.sav i hi)
  have Out₁ : Outside (layOf s).S 0 (layOf s).Z s.mem s₁.mem :=
    F.out.mono (Nat.le_refl _) (by simp only [layOf] at hZ ⊢; omega_arith)
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := keyVals_kept (srcK s rfl rfl) Out₁
  have hKs : KeyOk s₁.mem (layOf s) (s.gpr .a0) ↔ KeyOk s.mem (layOf s) (s.gpr .a0) := by
    simp only [KeyOk, ep₁, eq₁, eg₁, ey₁]
  have hspec := fun dg => verify_spec (sg := Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (dg := dg) hv
    (by rw [VG.Proof.Bignum.bytesAt_length]; exact hplq.symm)
    (by rw [VG.Proof.Bignum.bytesAt_length]; exact hsl) hkey
  rw [hsg0, hsg1] at hspec
  refine WP.seq (hX hL F.scr F.regs F.lens (by omega_arith) (srcK s₁ k₁.2.1 k₁.2.2) (fun hv => hKs.mpr (hV hv))
    (fun t hK hc hkp kc => ?_)
    (fun t hn hkp hrt scrt kc => ?_))
  · have kt := k₁.trans kc
    have hKt := hKs.mp hK
    refine WP.mono (body_ok hL hK hc hkp (srcK t kt.2.1 kt.2.2) (srcG t kt.2.1 kt.2.2) (by omega_arith)
      ((srcD t kt.2.1 kt.2.2).take (Nat.min_le_left _ _))
      (by rw [hkp.word (Or.inl (by simp only [hDigest, hLens]; omega))]; exact F.dig))
      fun u ⟨⟨a0u, Ku, h6u, scru⟩, ku⟩ => ?_
    refine WP.mono (finish_ok h6u (hwr' u scru) (hal' u scru) fun i hi =>
        (Ku.word (by simp only [saveOff]; omega) (by simp only [saveOff]; omega)).trans (hsav' t hkp i hi))
      fun w ⟨hab, w0⟩ => ⟨hab, ?_⟩
    show ((w.gpr .a0).setWidth 32).toNat = _
    rw [w0, a0u, ret_ofNat, hspec, VG.Proof.Dsa.RISCV64.bytesAt_take]
    simp only [decide_eq_true_eq]
    refine ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl)
    have Ot : Outside (layOf s).S 0 (layOf s).Z s.mem t.mem := Out₁.trans hkp.out
    obtain ⟨er, es, ed⟩ := sig_kept (srcG s rfl rfl) (srcD s rfl rfl) Ot
      (k := min (min (s.gpr .a7).toNat 64) (Spec.Dsa.bitLength (qOf s₁.mem (layOf s) (s.gpr .a0)) / 8))
      (by omega_arith)
    rw [er, es, ed, ep₁, eq₁, eg₁, ey₁]
    rw [show min (min (s.gpr .a7).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (layOf s) (s.gpr .a0)) / 8) =
      min (s.gpr .a7).toNat (Spec.Dsa.bitLength (qOf s.mem (layOf s) (s.gpr .a0)) / 8) by
        have := hKt.1.1; unfold Spec.Dsa.supportedSizes at this; omega_arith]
    exact ⟨fun h => ⟨hKt, h⟩, fun h => h.2⟩
  · refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = 0 ∧ u.mem = t.mem) (by brun [exec_li_zero])
      (by decide) (by rfl)) fun u ⟨⟨u0, um⟩, ku⟩ => ?_
    refine WP.mono (finish_ok ((ku.gpr (by decide)).trans hrt.s6) (hwr' u (scrt.congr ku.2.2))
      (hal' u (scrt.congr ku.2.2)) fun i hi => by rw [um]; exact hsav' t hkp i hi) fun w ⟨hab, w0⟩ => ⟨hab, ?_⟩
    show ((w.gpr .a0).setWidth 32).toNat = _
    rw [w0, u0, hspec, decide_eq_false (fun hx => hn (hKs.mpr hx.1))]
    rfl

end VG.Proof.Dsa.RISCV64
