module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Front
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Save
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Body
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.CheckKey
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Zero
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFn
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA signing on PPC64LE: the function

`sign_correct`: `vg_dsa_sign` meets `sContract`. After `entry`
(`sfront_ok`), `checkKey` either runs `body` (`sbody_ok`) or `zeroOut`
(`zeroOut_ok`), and `restore` gives back the nonvolatile registers
(`sfinish_ok`); the result is the specification's by
`Proof/Dsa/Accepted.lean`'s `signBytes_compute`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE
open VG.Impl.Dsa.PPC64LE.Sign (hOut)

/-- `restore`, as `finish_ok`, keeping memory. -/
theorem sfinish_ok {s u : State} {S : Addr} {rs : List Reg} (h21 : u.gpr .r21 = S)
    (hwr : ∀ i < 19, InRegions u.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 19, word u.mem S (saveOff i) = s.gpr (saved i)) (hk : Keep rs s u) :
    WP isa (.block restore) u fun w => abiPreserved s w ∧ w.gpr .r3 = u.gpr .r3 ∧ w.mem = u.mem := by
  refine WP.mono (restore_ok u (v := fun i => s.gpr (saved i)) h21 hwr fun i hi => ?_)
    fun w ⟨wrs, wot, wm, _, _, wsp, wlr⟩ => ⟨⟨fun r hr => ?_, by rw [wsp, hk.sp], by rw [wlr, hk.lr]⟩,
      wot .r3 (by decide), wm⟩
  · rw [← hsav i hi]
    show u.mem.readW (S + BitVec.ofNat 64 104 + BitVec.ofNat 64 (8 * i)) 64 = u.mem.readW (S + BitVec.ofNat 64 (104 + 8 * i)) 64
    rw [Offset.add_add]
  · obtain ⟨i, hi, rfl⟩ := saved_all r hr
    exact wrs i hi

theorem signStatus_ite (c : Prop) [Decidable c] (v : List Byte) :
    Spec.Dsa.signStatus (if c then some v else none) = if c then 1 else 0 := by
  split <;> rfl

theorem sign_correct (s : State) (h : sContract.pre s) :
    ∃ tr t, Exec isa Sign.sign s tr t ∧ abiPreserved s t ∧ sContract.post s t := by
  show WP isa Sign.sign s fun t => abiPreserved s t ∧ sContract.post s t
  have hL := slayOf_ok h
  have hZ := hL.z256
  have hql := hL.ql
  have hpre := h
  obtain ⟨-, hrd, hwr, -, -, -, dOS, -, dKS, dNS, dDS, -, nwO, nwK, nwN, nwD, -, hv, hol, hkl, -⟩ := h
  have mkSrc : ∀ {A : Addr} {n k : Nat}, (⟨A, n⟩ : Region) ∈ s.rd ++ s.wr →
      (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ → A.toNat + n ≤ 2 ^ 64 → n < 2 ^ 64 →
      k ≤ n → ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (slayOf s) A k :=
    fun hm hd hnw hn hk t hr hw => ⟨fun i hi => ⟨_, by rw [hr, hw]; exact hm,
      Offset.contains_base _ (by omega) (by omega)⟩, fun i hi => Pub.ne_of_disjoint hd (by omega) i (by omega)⟩
  have h4 : (s.gpr .r4).toNat = 2 * (slayOf s).ql := hol
  have h6 : (s.gpr .r6).toNat = 3 * (slayOf s).pl + 2 * (slayOf s).ql := hkl
  have srcK := mkSrc (A := s.gpr .r5) (k := 3 * (slayOf s).pl + 2 * (slayOf s).ql)
    (List.mem_append_left _ (by rw [hrd]; simp)) dKS nwK (s.gpr .r6).isLt (by omega)
  have srcK3 : ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (slayOf s) (s.gpr .r5) (3 * (slayOf s).pl + (slayOf s).ql) :=
    fun t hr hw => (srcK t hr hw).take (by omega)
  have srcN := mkSrc (A := s.gpr .r8) (k := (slayOf s).ql) (List.mem_append_left _ (by rw [hrd]; simp)) dNS nwN
    (s.gpr .r9).isLt (Nat.le_refl _)
  have srcD := mkSrc (A := s.gpr .r10) (k := (stackArg s 0).toNat) (List.mem_append_left _ (by rw [hrd]; simp))
    dDS nwD (stackArg s 0).isLt (Nat.le_refl _)
  have srcO := mkSrc (A := s.gpr .r3) (k := 2 * (slayOf s).ql) (List.mem_append_right _ (by rw [hwr]; simp)) dOS nwO
    (s.gpr .r4).isLt (by omega)
  have scrO : ∀ t : State, t.wr = s.wr → Scr t (s.gpr .r3) (2 * (slayOf s).ql) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr, ← h4]; simp) (by omega)
  -- A change in `out` keeps the saved registers.
  have outSep : ∀ {m m' : Mem}, Outside (s.gpr .r3) 0 (2 * (slayOf s).ql) m m' → ∀ i < 19,
      word m' (slayOf s).S (saveOff i) = word m (slayOf s).S (saveOff i) := fun ho i hi =>
    Outside.word_sep (Zp := 2 * (slayOf s).ql) ho (fun x hx => by
        by_contra hc
        exact (srcO s rfl rfl).sep (VG.Proof.Bignum.ofs (s.gpr .r3) x)
          (by simp only [VG.Proof.Bignum.ofs] at hc ⊢; omega) x hx (off_ofs _ x))
      (by omega) (by simp only [saveOff]; omega) hL.nowrap
  -- The specification's values.
  have hkey : Spec.Dsa.privateKeyBytes (s.gpr .r7).toNat (s.gpr .r9).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) =
      ⟨⟨pOf s.mem (slayOf s) (s.gpr .r5), qOf s.mem (slayOf s) (s.gpr .r5), gOf s.mem (slayOf s) (s.gpr .r5)⟩,
        yOf s.mem (slayOf s) (s.gpr .r5), some (xOf s.mem (slayOf s) (s.gpr .r5))⟩ := by
    rw [VG.Proof.Dsa.privateKeyBytes_at s.mem (s.gpr .r5) (by simp only [slayOf] at h6; omega),
      VG.Proof.Dsa.publicKeyBytes_at s.mem (s.gpr .r5) (by simp only [slayOf] at h6; omega)]
    rfl
  have hspec : ∀ {n : Nat}, VG.Proof.Dsa.shapeValid (pOf s.mem (slayOf s) (s.gpr .r5)) (qOf s.mem (slayOf s) (s.gpr .r5)) →
      Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) = 8 * n →
      sRes s = if VG.Proof.Dsa.publicChecks (pOf s.mem (slayOf s) (s.gpr .r5)) (qOf s.mem (slayOf s) (s.gpr .r5))
            (gOf s.mem (slayOf s) (s.gpr .r5)) (yOf s.mem (slayOf s) (s.gpr .r5)) ∧
          SignOk (pOf s.mem (slayOf s) (s.gpr .r5)) (qOf s.mem (slayOf s) (s.gpr .r5))
            (gOf s.mem (slayOf s) (s.gpr .r5)) (yOf s.mem (slayOf s) (s.gpr .r5))
            (xOf s.mem (slayOf s) (s.gpr .r5)) (kOf s.mem (slayOf s) (s.gpr .r8))
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (min (stackArg s 0).toNat n)))
        then some (Spec.Dsa.encodeBE (slayOf s).ql (sigR (pOf s.mem (slayOf s) (s.gpr .r5))
              (qOf s.mem (slayOf s) (s.gpr .r5)) (gOf s.mem (slayOf s) (s.gpr .r5)) (kOf s.mem (slayOf s) (s.gpr .r8))) ++
            Spec.Dsa.encodeBE (slayOf s).ql (sigS (qOf s.mem (slayOf s) (s.gpr .r5)) (xOf s.mem (slayOf s) (s.gpr .r5))
              (kOf s.mem (slayOf s) (s.gpr .r8))
              (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (min (stackArg s 0).toNat n)))
              (sigR (pOf s.mem (slayOf s) (s.gpr .r5)) (qOf s.mem (slayOf s) (s.gpr .r5))
                (gOf s.mem (slayOf s) (s.gpr .r5)) (kOf s.mem (slayOf s) (s.gpr .r8)))))
        else none := fun {n} hs hq8 => by
    have hc := VG.Proof.Dsa.signBytes_compute (n := n) (k := kOf s.mem (slayOf s) (s.gpr .r8))
      (nonce := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (digest := Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat) hv hs
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact h6) (VG.Proof.Bignum.bytesAt_length _ _ _) hkey rfl hq8
    dsimp only at hc
    unfold sRes
    rw [hc, bytesAt_take]
    rfl
  unfold Sign.sign
  refine WP.seq (WP.mono (sfront_ok hpre) fun s₁ ⟨⟨hr₁, scr₁, r2₁, hout₁, sav₁, out₁⟩, k₁⟩ => ?_)
  have hwr' : ∀ u : State, ScrL u (slayOf s) → ∀ i < 19, InRegions u.wr (off (savW (stackArg s 1)) (8 * i)) 8 :=
    fun u hu i hi => by
      rw [← saveOff_eq]; exact hu.st (d := 104 + 8 * i) (by simp only [slayOf] at hZ ⊢; omega)
  have Out₁ : Outside (slayOf s).S 0 (slayOf s).Z s.mem s₁.mem :=
    out₁.mono (Nat.le_refl _) (by simp only [slayOf] at hZ ⊢; omega)
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := key_kept (srcK3 s rfl rfl) Out₁
  have hKs : KeyOk s₁.mem (slayOf s) (s.gpr .r5) ↔ KeyOk s.mem (slayOf s) (s.gpr .r5) := by
    simp only [KeyOk, ep₁, eq₁, eg₁, ey₁]
  refine WP.seq (checkKeyB_ok hL scr₁ hr₁ r2₁ (by omega) (srcK3 s₁ k₁.rd k₁.wr) (fun t hK hc Bd kc => ?_)
    (fun t hn Bd hrt scrt kc => ?_))
  · have kt := k₁.trans kc
    have Kd := Kept.ofBody hL Bd
    have hKt := hKs.mp hK
    have Ot : Outside (slayOf s).S 0 (slayOf s).Z s.mem t.mem := Out₁.trans Kd.out
    have hq8 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) =
        8 * (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8) := by
      have := hKt.1.1; unfold Spec.Dsa.supportedSizes at this; omega
    have hn32 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8 ≤ 32 := by
      have := hKt.1.1; unfold Spec.Dsa.supportedSizes at this; omega
    refine WP.mono (sbody_ok hL hK hc Kd (srcK t kt.rd kt.wr) (srcN t kt.rd kt.wr) (by omega)
      ((srcD t kt.rd kt.wr).take (Nat.min_le_left _ _)) ((Body.hOut Bd).trans hout₁) (scrO t kt.wr)
      (srcO t kt.rd kt.wr)) fun u ⟨⟨ob, r3u, ⟨m, Km, Om⟩, h21u, scru⟩, ku⟩ => ?_
    refine WP.mono (sfinish_ok h21u (hwr' u scru)
      (fun i hi => ((outSep Om i hi).trans (Km.sav i hi)).trans ((Kd.sav i hi).trans (sav₁ i hi)))
      (kt.trans ku)) fun w ⟨hab, w3, wm⟩ => ⟨hab, ?_⟩
    have ex : xOf t.mem (slayOf s) (s.gpr .r5) = xOf s.mem (slayOf s) (s.gpr .r5) := by
      simp only [xOf]
      rw [((srcK s rfl rfl).sub (o := 3 * (slayOf s).pl + (slayOf s).ql) (k := (slayOf s).ql) (by omega)).kept Ot]
    have ek : kOf t.mem (slayOf s) (s.gpr .r8) = kOf s.mem (slayOf s) (s.gpr .r8) := by
      simp only [kOf]; rw [(srcN s rfl rfl).kept Ot]
    rw [ep₁, eq₁, eg₁, ey₁, ex, ek] at ob r3u
    have ed : Spec.Rsa.bytesAt t.mem (s.gpr .r10)
        (min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8)) =
        Spec.Rsa.bytesAt s.mem (s.gpr .r10)
          (min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8)) := by
      rw [show min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8) =
        min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8) by omega]
      exact ((srcD s rfl rfl).take (Nat.min_le_left _ _)).kept Ot
    rw [ed] at ob r3u
    have hres := hspec hKt.1 hq8
    simp only [hKt.2, true_and] at hres
    refine ⟨?_, ?_⟩
    · show ((w.gpr .r3).setWidth 32).toNat = _
      rw [w3, r3u, ret_ofNat, hres, signStatus_ite]
    · rw [wm, h4, ob, hres]
      split <;> rfl
  · have kt := k₁.trans kc
    have Kd := Kept.ofBody hL Bd
    refine WP.mono (zeroOut_ok hL scrt hrt ((Body.hOut Bd).trans hout₁) (scrO t kt.wr))
      fun u ⟨⟨ub, uo, u3⟩, ku⟩ => ?_
    refine WP.mono (sfinish_ok ((ku.gpr .r21 (by decide)).trans hrt.r21) (hwr' u (scrt.congr ku.wr))
      (fun i hi => ((outSep uo i hi).trans (Kd.sav i hi)).trans (sav₁ i hi)) (kt.trans ku))
      fun w ⟨hab, w3, wm⟩ => ⟨hab, ?_⟩
    have hn' : ¬ KeyOk s.mem (slayOf s) (s.gpr .r5) := fun hx => hn (hKs.mpr hx)
    have hres : sRes s = none := by
      by_cases hs : VG.Proof.Dsa.shapeValid (pOf s.mem (slayOf s) (s.gpr .r5)) (qOf s.mem (slayOf s) (s.gpr .r5))
      · have hq8 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) =
            8 * (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8) := by
          have := hs.1; unfold Spec.Dsa.supportedSizes at this; omega
        rw [hspec hs hq8]
        split
        · rename_i hx; exact absurd ⟨hs, hx.1⟩ hn'
        · rfl
      · exact VG.Proof.Dsa.signBytes_invalid_shape (by rw [hkey]; exact hs)
    refine ⟨?_, ?_⟩
    · show ((w.gpr .r3).setWidth 32).toNat = _
      rw [w3, u3, hres]; rfl
    · rw [wm, h4, ub, hres]; rfl

end VG.Proof.Dsa.PPC64LE
