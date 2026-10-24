module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Front
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Body
import VerifiedGarbage.Proof.Dsa.PPC64LE.Save
import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Zero
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFn
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# DSA key derivation on PPC64LE: the function

`deriveKey_correct`: `vg_dsa_derive_key` meets `dContract`. After `entry`
(`dfront_ok`), `checkParams` either runs `body` (`dbody_ok`) or `zeroOut`
(`dzero_ok`), and `restore` gives back the nonvolatile registers
(`sfinish_ok`); the result is the specification's by `deriveKey_spec`, from
`Proof/Dsa/Derive.lean`'s `deriveKeyBytes_eq`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- The specification's derivation, on the domain's and x's values. -/
theorem deriveKey_spec {m : Mem} {L : Lay} {key x : Addr} (hv : Spec.Dsa.lengthsValid L.pl L.ql) :
    Spec.Dsa.deriveKeyBytes L.pl L.ql (Spec.Rsa.bytesAt m key (2 * L.pl + L.ql)) (Spec.Rsa.bytesAt m x L.ql) =
      if ParamsOk m L key ∧ DeriveOk (pOf m L key) (qOf m L key) (gOf m L key) (kOf m L x) then
        some (Spec.Rsa.bytesAt m key (2 * L.pl + L.ql) ++
          Spec.Dsa.encodeBE L.pl (gOf m L key ^ kOf m L x % pOf m L key) ++ Spec.Rsa.bytesAt m x L.ql)
      else none := by
  rw [VG.Proof.Dsa.deriveKeyBytes_eq hv (VG.Proof.Bignum.bytesAt_length _ _ _)
    (VG.Proof.Bignum.bytesAt_length _ _ _)]
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
  change (if _ then some (_ ++ Spec.Dsa.encodeBE L.pl (gOf m L key ^ kOf m L x % pOf m L key) ++ _) else none) = _
  split <;> rename_i h₁ <;> split <;> rename_i h₂
  · rfl
  · simp only [Bool.and_eq_true, decide_eq_true_eq, and_true] at h₁
    obtain ⟨⟨hs, hp, hq⟩, hgq, hd, ⟨hy, -⟩, hg, hx⟩ := h₁
    exact absurd ⟨⟨⟨hs, hq, hp⟩, hg, hd, hgq⟩, hy, hx⟩ h₂
  · obtain ⟨⟨⟨hs, hq, hp⟩, hg, hd, hgq⟩, hy, hx⟩ := h₂
    have B := VG.Proof.Dsa.supported_bounds hs
    refine absurd ?_ h₁
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_true]
    exact ⟨⟨hs, hp, hq⟩, hgq, hd, ⟨hy, Nat.mod_lt _ (show 0 < pOf m L key by omega)⟩, hg, hx⟩
  · rfl

theorem deriveKey_correct (s : State) (h : dContract.pre s) :
    ∃ tr t, Exec isa Derive.derive s tr t ∧ abiPreserved s t ∧ dContract.post s t := by
  show WP isa Derive.derive s fun t => abiPreserved s t ∧ dContract.post s t
  have hL := dlayOf_ok h
  have hZ := hL.z256
  have hql := hL.ql
  have hpre := h
  obtain ⟨-, hrd, hwr, dOP, dOX, dOS, -, dPS, dXS, -, nwO, nwP, nwX, -, hv, hol, hpl, -⟩ := h
  have mkSrc : ∀ {A : Addr} {n k : Nat}, (⟨A, n⟩ : Region) ∈ s.rd ++ s.wr →
      (⟨A, n⟩ : Region).Disjoint ⟨s.gpr .r10, (stackArg s 0).toNat * 8⟩ → A.toNat + n ≤ 2 ^ 64 → n < 2 ^ 64 →
      k ≤ n → ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (dlayOf s) A k :=
    fun hm hd hnw hn hk t hr hw => ⟨fun i hi => ⟨_, by rw [hr, hw]; exact hm,
      Offset.contains_base _ (by omega) (by omega)⟩, fun i hi => Pub.ne_of_disjoint hd (by omega) i (by omega)⟩
  have h4 : (s.gpr .r4).toNat = 3 * (dlayOf s).pl + 2 * (dlayOf s).ql := hol
  have h6 : (s.gpr .r6).toNat = 2 * (dlayOf s).pl + (dlayOf s).ql := hpl
  have srcK := mkSrc (A := s.gpr .r5) (k := 2 * (dlayOf s).pl + (dlayOf s).ql)
    (List.mem_append_left _ (by rw [hrd]; simp)) dPS nwP (s.gpr .r6).isLt (by omega)
  have srcX := mkSrc (A := s.gpr .r8) (k := (dlayOf s).ql) (List.mem_append_left _ (by rw [hrd]; simp)) dXS nwX
    (s.gpr .r9).isLt (Nat.le_refl _)
  have srcO := mkSrc (A := s.gpr .r3) (k := 3 * (dlayOf s).pl + 2 * (dlayOf s).ql)
    (List.mem_append_right _ (by rw [hwr]; simp)) dOS nwO (s.gpr .r4).isLt (by omega)
  have scrO : ∀ t : State, t.wr = s.wr → Scr t (s.gpr .r3) (3 * (dlayOf s).pl + 2 * (dlayOf s).ql) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr, ← h4]; simp) (by omega)
  have hko : ∀ i < 2 * (dlayOf s).pl + (dlayOf s).ql, ∀ y, ofs (s.gpr .r3) y < 3 * (dlayOf s).pl + 2 * (dlayOf s).ql →
      off (s.gpr .r5) i ≠ y := fun i hi y hy =>
    Pub.ne_of_disjoint (Region.Disjoint.symm dOP) (by omega) i (by omega) y (by rw [h4]; exact hy)
  have hxo : ∀ i < (dlayOf s).ql, ∀ y, ofs (s.gpr .r3) y < 3 * (dlayOf s).pl + 2 * (dlayOf s).ql →
      off (s.gpr .r8) i ≠ y := fun i hi y hy =>
    Pub.ne_of_disjoint (Region.Disjoint.symm dOX) (by omega) i (by simp only [dlayOf] at hi ⊢; omega) y
      (by rw [h4]; exact hy)
  -- A change in `out` keeps the saved registers.
  have outSep : ∀ {m m' : Mem}, Outside (s.gpr .r3) 0 (3 * (dlayOf s).pl + 2 * (dlayOf s).ql) m m' → ∀ i < 19,
      word m' (dlayOf s).S (saveOff i) = word m (dlayOf s).S (saveOff i) := fun ho i hi =>
    Outside.word_sep (Zp := 3 * (dlayOf s).pl + 2 * (dlayOf s).ql) ho (fun x hx => by
        by_contra hc
        exact (srcO s rfl rfl).sep (VG.Proof.Bignum.ofs (s.gpr .r3) x)
          (by simp only [VG.Proof.Bignum.ofs] at hc ⊢; omega) x hx (off_ofs _ x))
      (by omega) (by simp only [saveOff]; omega) hL.nowrap
  have hspec : dRes s = if ParamsOk s.mem (dlayOf s) (s.gpr .r5) ∧ DeriveOk (pOf s.mem (dlayOf s) (s.gpr .r5))
        (qOf s.mem (dlayOf s) (s.gpr .r5)) (gOf s.mem (dlayOf s) (s.gpr .r5)) (kOf s.mem (dlayOf s) (s.gpr .r8))
      then some (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (2 * (dlayOf s).pl + (dlayOf s).ql) ++
        Spec.Dsa.encodeBE (dlayOf s).pl (gOf s.mem (dlayOf s) (s.gpr .r5) ^ kOf s.mem (dlayOf s) (s.gpr .r8) %
          pOf s.mem (dlayOf s) (s.gpr .r5)) ++ Spec.Rsa.bytesAt s.mem (s.gpr .r8) (dlayOf s).ql)
      else none := by
    unfold dRes
    rw [h6]
    exact deriveKey_spec hv
  unfold Derive.derive
  refine WP.seq (WP.mono (dfront_ok hpre) fun s₁ ⟨⟨hr₁, scr₁, r2₁, sav₁, out₁⟩, k₁⟩ => ?_)
  have hwr' : ∀ u : State, ScrL u (dlayOf s) → ∀ i < 19, InRegions u.wr (off (savW (s.gpr .r10)) (8 * i)) 8 :=
    fun u hu i hi => by
      rw [← saveOff_eq]; exact hu.st (d := 104 + 8 * i) (by simp only [dlayOf] at hZ ⊢; omega)
  have Out₁ : Outside (dlayOf s).S 0 (dlayOf s).Z s.mem s₁.mem :=
    out₁.mono (Nat.le_refl _) (by simp only [dlayOf] at hZ ⊢; omega)
  obtain ⟨ep₁, eq₁, eg₁⟩ := params_kept (srcK s rfl rfl) Out₁
  have ek₁ : kOf s₁.mem (dlayOf s) (s.gpr .r8) = kOf s.mem (dlayOf s) (s.gpr .r8) := by
    simp only [kOf]; rw [(srcX s rfl rfl).kept Out₁]
  have eb₁ : Spec.Rsa.bytesAt s₁.mem (s.gpr .r5) (2 * (dlayOf s).pl + (dlayOf s).ql) =
      Spec.Rsa.bytesAt s.mem (s.gpr .r5) (2 * (dlayOf s).pl + (dlayOf s).ql) := (srcK s rfl rfl).kept Out₁
  have ex₁ : Spec.Rsa.bytesAt s₁.mem (s.gpr .r8) (dlayOf s).ql = Spec.Rsa.bytesAt s.mem (s.gpr .r8) (dlayOf s).ql :=
    (srcX s rfl rfl).kept Out₁
  have hPs : ParamsOk s₁.mem (dlayOf s) (s.gpr .r5) ↔ ParamsOk s.mem (dlayOf s) (s.gpr .r5) := by
    simp only [ParamsOk, ep₁, eq₁, eg₁]
  refine WP.seq (checkParams_ok hL scr₁ hr₁ r2₁ (by decide) (srcK s₁ k₁.rd k₁.wr) (fun t hP hc Bd kc => ?_)
    (fun t hn Bd hrt scrt kc => ?_))
  · have kt := k₁.trans kc
    have Kd := Kept.ofBody hL Bd
    refine WP.mono (dbody_ok hL hP hc Kd (srcK t kt.rd kt.wr) (srcX t kt.rd kt.wr) (scrO t kt.wr)
      (srcO t kt.rd kt.wr) hko hxo) fun u ⟨⟨ob, r3u, ⟨m, Km, Om⟩, h21u, scru⟩, ku⟩ => ?_
    refine WP.mono (sfinish_ok h21u (hwr' u scru)
      (fun i hi => ((outSep Om i hi).trans (Km.sav i hi)).trans ((Kd.sav i hi).trans (sav₁ i hi)))
      (kt.trans ku)) fun w ⟨hab, w3, wm⟩ => ⟨hab, ?_⟩
    simp only [ep₁, eq₁, eg₁, ek₁, eb₁, ex₁] at ob r3u
    have hres := hspec
    simp only [hPs.mp hP, true_and] at hres
    refine ⟨?_, ?_⟩
    · show ((w.gpr .r3).setWidth 32).toNat = _
      rw [w3, r3u, ret_ofNat, hres, signStatus_ite]
    · rw [wm, h4, ob, hres]
      split <;> rfl
  · have kt := k₁.trans kc
    have Kd := Kept.ofBody hL Bd
    refine WP.mono (dzero_ok hL hrt (scrO t kt.wr)) fun u ⟨⟨ub, uo, u3⟩, ku⟩ => ?_
    refine WP.mono (sfinish_ok ((ku.gpr .r21 (by decide)).trans hrt.r21) (hwr' u (scrt.congr ku.wr))
      (fun i hi => ((outSep uo i hi).trans (Kd.sav i hi)).trans (sav₁ i hi)) (kt.trans ku))
      fun w ⟨hab, w3, wm⟩ => ⟨hab, ?_⟩
    have hres : dRes s = none := by
      rw [hspec]
      exact ite_eq_right_iff.mpr fun hx => absurd (hPs.mpr hx.1) hn
    refine ⟨?_, ?_⟩
    · show ((w.gpr .r3).setWidth 32).toNat = _
      rw [w3, u3, hres]; rfl
    · rw [wm, h4, ub, hres]; rfl

end VG.Proof.Dsa.PPC64LE
