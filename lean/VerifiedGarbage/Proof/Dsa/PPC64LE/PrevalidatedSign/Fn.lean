module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.Contract
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Save
public import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Setup
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Body
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
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
# DSA prevalidated signing on PPC64LE: the function

`psign_correct`: `vg_dsa_sign_prevalidated` meets `spContract`. The key
passes validation (`validatePrivate_spec`), so after `Sign.entry`
(`sfront_ok`), `Prevalidated.setup` leaves what `checkKey` would
(`setup_ok`), `Sign.body` signs (`sbody_ok`, with `g^x mod p = y`), and
`restore` gives back the nonvolatile registers (`sfinish_ok`); the result is
the specification's by `Proof/Dsa/Accepted.lean`'s `signBytes_compute`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE
open VG.Impl.Dsa.PPC64LE.Sign (hOut)

theorem psign_correct (s : State) (h' : spContract.pre s) :
    ∃ tr t, Exec isa PrevalidatedSign.sign s tr t ∧ abiPreserved s t ∧ spContract.post s t := by
  show WP isa PrevalidatedSign.sign s fun t => abiPreserved s t ∧ sContract.post s t
  obtain ⟨h, hval⟩ := h'
  have hL := slayOf_ok h
  have hZ := hL.z256
  have hql := hL.ql
  have hpre := h
  obtain ⟨-, hrd, hwr, -, -, -, dOS, -, dKS, dNS, dDS, -, nwO, nwK, nwN, nwD, -, hv, hol, hkl, -⟩ := h
  have mkSrc : ∀ {A : Addr} {n k : Nat}, (⟨A, n⟩ : Region) ∈ s.rd ++ s.wr →
      (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ → A.toNat + n ≤ 2 ^ 64 → n < 2 ^ 64 →
      k ≤ n → ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (slayOf s) A k :=
    fun hm hd hnw hn hk t hr hw => ⟨fun i hi => ⟨_, by rw [hr, hw]; exact hm,
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩, fun i hi => Pub.ne_of_disjoint hd (by omega_arith) i (by omega_arith)⟩
  have h4 : (s.gpr .r4).toNat = 2 * (slayOf s).ql := hol
  have h6 : (s.gpr .r6).toNat = 3 * (slayOf s).pl + 2 * (slayOf s).ql := hkl
  have srcK := mkSrc (A := s.gpr .r5) (k := 3 * (slayOf s).pl + 2 * (slayOf s).ql)
    (List.mem_append_left _ (by rw [hrd]; simp)) dKS nwK (s.gpr .r6).isLt (by omega_arith)
  have srcK3 : ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (slayOf s) (s.gpr .r5) (3 * (slayOf s).pl + (slayOf s).ql) :=
    fun t hr hw => (srcK t hr hw).take (by omega_arith)
  have srcN := mkSrc (A := s.gpr .r8) (k := (slayOf s).ql) (List.mem_append_left _ (by rw [hrd]; simp)) dNS nwN
    (s.gpr .r9).isLt (Nat.le_refl _)
  have srcD := mkSrc (A := s.gpr .r10) (k := (stackArg s 0).toNat) (List.mem_append_left _ (by rw [hrd]; simp))
    dDS nwD (stackArg s 0).isLt (Nat.le_refl _)
  have srcO := mkSrc (A := s.gpr .r3) (k := 2 * (slayOf s).ql) (List.mem_append_right _ (by rw [hwr]; simp)) dOS nwO
    (s.gpr .r4).isLt (by omega_arith)
  have scrO : ∀ t : State, t.wr = s.wr → Scr t (s.gpr .r3) (2 * (slayOf s).ql) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr, ← h4]; simp) (by omega_arith)
  -- A change in `out` keeps the saved registers.
  have outSep : ∀ {m m' : Mem}, Outside (s.gpr .r3) 0 (2 * (slayOf s).ql) m m' → ∀ i < 19,
      word m' (slayOf s).S (saveOff i) = word m (slayOf s).S (saveOff i) := fun ho i hi =>
    Outside.word_sep (Zp := 2 * (slayOf s).ql) ho (fun x hx => by
        by_contra hc
        exact (srcO s rfl rfl).sep (VG.Proof.Bignum.ofs (s.gpr .r3) x)
          (by simp only [VG.Proof.Bignum.ofs] at hc ⊢; omega_arith) x hx (off_ofs _ x))
      (by omega_arith) (by simp only [saveOff]; omega_arith) hL.nowrap
  -- The specification's values.
  have hkey : Spec.Dsa.privateKeyBytes (s.gpr .r7).toNat (s.gpr .r9).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) =
      ⟨⟨pOf s.mem (slayOf s) (s.gpr .r5), qOf s.mem (slayOf s) (s.gpr .r5), gOf s.mem (slayOf s) (s.gpr .r5)⟩,
        yOf s.mem (slayOf s) (s.gpr .r5), some (xOf s.mem (slayOf s) (s.gpr .r5))⟩ := by
    rw [VG.Proof.Dsa.privateKeyBytes_at s.mem (s.gpr .r5) (by simp only [slayOf] at h6; omega_arith),
      VG.Proof.Dsa.publicKeyBytes_at s.mem (s.gpr .r5) (by simp only [slayOf] at h6; omega_arith)]
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
  have hP : PrivOk s.mem (slayOf s) (s.gpr .r5) := by
    have e := validatePrivate_spec (m := s.mem) (L := slayOf s) (key := s.gpr .r5) hv
    rw [show 3 * (slayOf s).pl + 2 * (slayOf s).ql = (s.gpr .r6).toNat from h6.symm] at e
    exact of_decide_eq_true (e.symm.trans hval)
  unfold PrevalidatedSign.sign
  refine WP.seq (WP.mono (sfront_ok hpre) fun s₁ ⟨⟨hr₁, scr₁, r2₁, hout₁, sav₁, out₁⟩, k₁⟩ => ?_)
  have hwr' : ∀ u : State, ScrL u (slayOf s) → ∀ i < 19, InRegions u.wr (off (savW (stackArg s 1)) (8 * i)) 8 :=
    fun u hu i hi => by
      rw [← saveOff_eq]; exact hu.st (d := 104 + 8 * i) (by simp only [slayOf] at hZ ⊢; omega_arith)
  have Out₁ : Outside (slayOf s).S 0 (slayOf s).Z s.mem s₁.mem :=
    out₁.mono (Nat.le_refl _) (by simp only [slayOf] at hZ ⊢; omega_arith)
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := key_kept (srcK3 s rfl rfl) Out₁
  have hKs : KeyOk s₁.mem (slayOf s) (s.gpr .r5) ↔ KeyOk s.mem (slayOf s) (s.gpr .r5) := by
    simp only [KeyOk, ep₁, eq₁, eg₁, ey₁]
  refine WP.seq (setup_ok hL scr₁ hr₁ r2₁ (by omega_arith) (srcK3 s₁ k₁.rd k₁.wr) (hKs.mpr hP.1)
    fun t hK hc Bd kc => ?_)
  have kt := k₁.trans kc
  have Kd := Kept.ofBody hL Bd
  have hKt := hKs.mp hK
  have Ot : Outside (slayOf s).S 0 (slayOf s).Z s.mem t.mem := Out₁.trans Kd.out
  have hq8 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) =
      8 * (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8) := by
    have := hKt.1.1; unfold Spec.Dsa.supportedSizes at this; omega_arith
  have hn32 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8 ≤ 32 := by
    have := hKt.1.1; unfold Spec.Dsa.supportedSizes at this; omega_arith
  have ex : xOf t.mem (slayOf s) (s.gpr .r5) = xOf s.mem (slayOf s) (s.gpr .r5) := by
    simp only [xOf]
    rw [((srcK s rfl rfl).sub (o := 3 * (slayOf s).pl + (slayOf s).ql) (k := (slayOf s).ql) (by omega_arith)).kept Ot]
  have hgx : gOf s₁.mem (slayOf s) (s.gpr .r5) ^ xOf t.mem (slayOf s) (s.gpr .r5) % pOf s₁.mem (slayOf s) (s.gpr .r5) =
      yOf s₁.mem (slayOf s) (s.gpr .r5) := by
    rw [ep₁, eg₁, ey₁, ex]; exact hP.2.2
  refine WP.mono (sbody_ok hL hK hgx hc Kd (srcK t kt.rd kt.wr) (srcN t kt.rd kt.wr) (by omega_arith)
    ((srcD t kt.rd kt.wr).take (Nat.min_le_left _ _)) ((Body.hOut Bd).trans hout₁) (scrO t kt.wr)
    (srcO t kt.rd kt.wr)) fun u ⟨⟨ob, r3u, ⟨m, Km, Om⟩, h21u, scru⟩, ku⟩ => ?_
  refine WP.mono (sfinish_ok h21u (hwr' u scru)
    (fun i hi => ((outSep Om i hi).trans (Km.sav i hi)).trans ((Kd.sav i hi).trans (sav₁ i hi)))
    (kt.trans ku)) fun w ⟨hab, w3, wm⟩ => ⟨hab, ?_⟩
  have ek : kOf t.mem (slayOf s) (s.gpr .r8) = kOf s.mem (slayOf s) (s.gpr .r8) := by
    simp only [kOf]; rw [(srcN s rfl rfl).kept Ot]
  rw [ep₁, eq₁, eg₁, ey₁, ex, ek] at ob r3u
  have ed : Spec.Rsa.bytesAt t.mem (s.gpr .r10)
      (min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8)) =
      Spec.Rsa.bytesAt s.mem (s.gpr .r10)
        (min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8)) := by
    rw [show min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8) =
      min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8) by omega_arith]
    exact ((srcD s rfl rfl).take (Nat.min_le_left _ _)).kept Ot
  rw [ed] at ob r3u
  have hres := hspec hKt.1 hq8
  simp only [hKt.2, true_and] at hres
  refine ⟨?_, ?_⟩
  · show ((w.gpr .r3).setWidth 32).toNat = _
    rw [w3, r3u, ret_ofNat, hres, signStatus_ite]
  · rw [wm, h4, ob, hres]
    split <;> rfl

end VG.Proof.Dsa.PPC64LE
