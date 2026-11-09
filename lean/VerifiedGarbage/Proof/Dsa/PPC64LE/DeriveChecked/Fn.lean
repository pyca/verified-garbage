module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Front
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Body
import VerifiedGarbage.Proof.Dsa.PPC64LE.Save
import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Zero
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
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
import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Fn
public import VerifiedGarbage.Proof.Dsa.PPC64LE.DeriveChecked.Check

/-!
# DSA key derivation for a checked domain on PPC64LE: the function

`dcContract`: `vg_dsa_derive_key_checked`, `Derive.deriveChecked`, with
`vg_dsa_derive_key`'s arguments, result and public data (`dContract`), for a
domain whose exact octets pass the specification's `checkParametersBytes`.
`deriveChecked_correct`: it meets `dcContract`. The proof is
`deriveKey_correct`'s with `checkDomain_ok` for `checkParams_ok`: the
precondition gives the domain's checks (`ParamsOk`, by
`checkParameters_spec`), which `checkDomain` leaves out of g's.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- `vg_dsa_derive_key_checked`, on the registers and the stack: `dContract`
for a domain that passes the specification's checks. -/
def dcContract : Contract isa where
  pre s := dContract.pre s ∧ Spec.Dsa.checkParametersBytes (s.gpr .r7).toNat (s.gpr .r9).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) = true
  post := dContract.post
  pub := dContract.pub

theorem deriveChecked_correct (s : State) (h : dcContract.pre s) :
    ∃ tr t, Exec isa Derive.deriveChecked s tr t ∧ abiPreserved s t ∧ dcContract.post s t := by
  show WP isa Derive.deriveChecked s fun t => abiPreserved s t ∧ dContract.post s t
  obtain ⟨h, hchk⟩ := h
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
  -- The domain passes the checks, by the precondition.
  have hP₀ : ParamsOk s.mem (dlayOf s) (s.gpr .r5) := by
    have e := checkParameters_spec (m := s.mem) (L := dlayOf s) (key := s.gpr .r5) hv
    rw [← h6] at e
    exact of_decide_eq_true (e.symm.trans hchk)
  unfold Derive.deriveChecked
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
  refine WP.seq (checkDomain_ok hL scr₁ hr₁ r2₁ (by decide) (srcK s₁ k₁.rd k₁.wr) (fun t _ hc Bd kc => ?_)
    (fun t hn Bd hrt scrt kc => ?_))
  · have kt := k₁.trans kc
    have Kd := Kept.ofBody hL Bd
    refine WP.mono (dbody_ok hL (hPs.mpr hP₀) hc Kd (srcK t kt.rd kt.wr) (srcX t kt.rd kt.wr) (scrO t kt.wr)
      (srcO t kt.rd kt.wr) hko hxo) fun u ⟨⟨ob, r3u, ⟨m, Km, Om⟩, h21u, scru⟩, ku⟩ => ?_
    refine WP.mono (sfinish_ok h21u (hwr' u scru)
      (fun i hi => ((outSep Om i hi).trans (Km.sav i hi)).trans ((Kd.sav i hi).trans (sav₁ i hi)))
      (kt.trans ku)) fun w ⟨hab, w3, wm⟩ => ⟨hab, ?_⟩
    simp only [ep₁, eq₁, eg₁, ek₁, eb₁, ex₁] at ob r3u
    have hres := hspec
    simp only [hP₀, true_and] at hres
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
      exact ite_eq_right_iff.mpr fun hx => absurd (hPs.mpr hx.1).domainOk hn
    refine ⟨?_, ?_⟩
    · show ((w.gpr .r3).setWidth 32).toNat = _
      rw [w3, u3, hres]; rfl
    · rw [wm, h4, ub, hres]; rfl

end VG.Proof.Dsa.PPC64LE
