module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignFront
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignBody
public import VerifiedGarbage.Impl.Dsa.RISCV64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedFn
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
import VerifiedGarbage.Proof.Dsa.RISCV64.Elem
import VerifiedGarbage.Proof.Dsa.RISCV64.Arr
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveOutput
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA prevalidated signing on RISC-V: the function

`spContract`: `vg_dsa_sign_prevalidated`, with `vg_dsa_sign`'s arguments,
result and public data (`sContract`), for a key whose exact octets pass
`validatePrivateKeyBytes`. `signPre_correct`: after `vg_dsa_sign`'s entry
(`sfront_ok`), `Prevalidated.setup` sets up the working spaces
(`setup_ok`, for a key that passes `KeyOk`, which validation implies), then
`setMask` puts in `hMask` the mask `keyPair` would (`setMask_KPOk`: all
ones, as `g^x mod p = y`), and signing's `tail` runs as in `vg_dsa_sign`
(`sbodyWith_ok`). The result is the specification's by `signBytes_compute`,
whose public-key checks validation makes true.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- `vg_dsa_sign_prevalidated`, on the registers and the stack. -/
abbrev spContract : Contract isa := sContractWith Spec.Dsa.validatePrivateKeyBytes

/-- Validation of a packed private key, on its values. -/
theorem validatePrivate_eq {pLen qLen p q g y x : Nat} {key : List Byte}
    (widths : Spec.Dsa.lengthsValid pLen qLen) (keyLen : key.length = 3 * pLen + 2 * qLen)
    (keyValue : Spec.Dsa.privateKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, some x⟩) :
    Spec.Dsa.validatePrivateKeyBytes pLen qLen key =
      decide (VG.Proof.Dsa.shapeValid p q ∧ VG.Proof.Dsa.publicChecks p q g y ∧ (0 < x ∧ x < q) ∧
        g ^ x % p = y) := by
  unfold Spec.Dsa.validatePrivateKeyBytes
  simp only [widths, decide_true, Bool.not_true, keyLen, bne_self_eq_false, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, keyValue]
  by_cases hs : VG.Proof.Dsa.shapeValid p q
  · have e := VG.Proof.Dsa.privateChecks_spec (g := g) (y := y) (x := x) hs
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, hs, true_and, e]
  · have hp : ¬ Spec.Dsa.parametersValid ⟨p, q, g⟩ := fun P => hs (VG.Proof.Dsa.parametersValid_shape P)
    simp only [hp, hs, decide_false, Bool.false_and, false_and]

/-- `setMask` is a first step of signing for a key with `g^x mod p = y`. -/
theorem setMask_KPOk {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hin : InP s L) (hi : PInv s L)
    (hv : gOf s.mem L key ^ xOf s.mem L key % arrP s.mem L 0 = yOf s.mem L key) :
    KPOk (.block PrevalidatedSign.setMask) s L key := by
  intro p p0 _ _ _
  subst p0
  have hZ := hL.z256
  obtain ⟨_, hal0⟩ := ScrL.hdr hs hL (d := 0) (by decide) (by decide)
  have hst : InRegions s.wr (off L.S 0) 8 := hs.st (by omega)
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.mem = s.mem.writeW (off L.S 0) (mask true))
    (by brun [PrevalidatedSign.setMask, exec_li (show imm12 (-1) by decide), hMask, hr.s6, hst, hal0]; rfl)
    (by decide) (by rfl)) fun t ⟨mt, kt⟩ => ?_
  have wo : Outside L.S hMask 8 s.mem t.mem := by
    rw [mt]; exact writeW_outside s.mem L.S _ (by simp only [hMask]; omega)
  refine ⟨⟨?_, ⟨hin.env.keep kt, (kt.gpr (by decide)).trans hin.s6⟩, ?_, ⟨s.mem, fun _ _ => rfl, wo⟩⟩,
    kt.mono (by decide)⟩
  · rw [mt]; refine (word_writeW_self s.mem L.S hMask _).trans ?_; rw [hv]; simp only [decide_true]
  · show ((word t.mem L.S (slot L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [mask_word0 hL wo, kt.gpr (by decide)]
    exact hi

/-- What validation says of the key's values. -/
theorem spre_valid {s : State} (h : spContract.pre s) :
    VG.Proof.Dsa.shapeValid (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2)) ∧
      VG.Proof.Dsa.publicChecks (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2))
        (gOf s.mem (slayOf s) (s.gpr .a2)) (yOf s.mem (slayOf s) (s.gpr .a2)) ∧
      (0 < xOf s.mem (slayOf s) (s.gpr .a2) ∧ xOf s.mem (slayOf s) (s.gpr .a2) < qOf s.mem (slayOf s) (s.gpr .a2)) ∧
      gOf s.mem (slayOf s) (s.gpr .a2) ^ xOf s.mem (slayOf s) (s.gpr .a2) % pOf s.mem (slayOf s) (s.gpr .a2) =
        yOf s.mem (slayOf s) (s.gpr .a2) := by
  obtain ⟨h, hval⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -, hkl, -, -, -⟩ := h
  have h3 : (s.gpr .a3).toNat = 3 * (slayOf s).pl + 2 * (slayOf s).ql := hkl
  -- The specification's values.
  have hkey : Spec.Dsa.privateKeyBytes (s.gpr .a4).toNat (s.gpr .a6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) =
      ⟨⟨pOf s.mem (slayOf s) (s.gpr .a2), qOf s.mem (slayOf s) (s.gpr .a2), gOf s.mem (slayOf s) (s.gpr .a2)⟩,
        yOf s.mem (slayOf s) (s.gpr .a2), some (xOf s.mem (slayOf s) (s.gpr .a2))⟩ := by
    rw [VG.Proof.Dsa.privateKeyBytes_at s.mem (s.gpr .a2) (by simp only [slayOf] at h3; omega),
      VG.Proof.Dsa.publicKeyBytes_at s.mem (s.gpr .a2) (by simp only [slayOf] at h3; omega)]
    rfl
  rw [validatePrivate_eq hv (by rw [VG.Proof.Bignum.bytesAt_length]; exact h3) hkey] at hval
  exact of_decide_eq_true hval

theorem signPre_correct (s : State) (h : spContract.pre s) :
    ∃ tr t, Exec isa PrevalidatedSign.sign s tr t ∧ abiPreserved s t ∧ spContract.post s t := by
  show WP isa PrevalidatedSign.sign s fun t => abiPreserved s t ∧ sContract.post s t
  obtain ⟨h, hval⟩ := h
  suffices main : WP isa PrevalidatedSign.sign s fun t =>
      ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ sContract.post s t from
    WP.mono (WP.rdwr main) fun t ⟨⟨⟨hp, hra⟩, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  have hL := slayOf_ok h
  have hZ := hL.z256
  have hnwS := hL.nowrap
  have hpre := h
  obtain ⟨hrd, hwr, -, -, -, dOS, -, dKS, dNS, dDS, -, nwO, nwK, nwN, nwD, -, hv, hol, hkl, -, -, -⟩ := h
  have mkSrc : ∀ {A : Addr} {n k : Nat}, (⟨A, n⟩ : Region) ∈ s.rd ++ s.wr →
      (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ → A.toNat + n ≤ 2 ^ 64 → n < 2 ^ 64 →
      k ≤ n → ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (slayOf s) A k :=
    fun hm hd hnw hn hk t hr hw => ⟨fun i hi => ⟨_, by rw [hr, hw]; exact hm,
      Offset.contains_base _ (by omega) (by omega)⟩, fun i hi => Pub.ne_of_disjoint hd (by omega) i (by omega)⟩
  have h1 : (s.gpr .a1).toNat = 2 * (slayOf s).ql := hol
  have h3 : (s.gpr .a3).toNat = 3 * (slayOf s).pl + 2 * (slayOf s).ql := hkl
  have srcK := mkSrc (A := s.gpr .a2) (k := 3 * (slayOf s).pl + 2 * (slayOf s).ql)
    (List.mem_append_left _ (by rw [hrd]; simp)) dKS nwK (s.gpr .a3).isLt (by omega)
  have srcK3 : ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      Src t (slayOf s) (s.gpr .a2) (3 * (slayOf s).pl + (slayOf s).ql) :=
    fun t hr hw => (srcK t hr hw).take (by omega)
  have srcN := mkSrc (A := s.gpr .a5) (k := (slayOf s).ql) (List.mem_append_left _ (by rw [hrd]; simp)) dNS nwN
    (s.gpr .a6).isLt (Nat.le_refl _)
  have srcD := mkSrc (A := s.gpr .a7) (k := (stackArg s 0).toNat) (List.mem_append_left _ (by rw [hrd]; simp))
    dDS nwD (stackArg s 0).isLt (Nat.le_refl _)
  have srcO := mkSrc (A := s.gpr .a0) (k := 2 * (slayOf s).ql) (List.mem_append_right _ (by rw [hwr]; simp)) dOS nwO
    (s.gpr .a1).isLt (by omega)
  have hno : (s.gpr .a0).toNat + 2 * (slayOf s).ql ≤ 2 ^ 64 := by rw [← h1]; exact nwO
  have hout : ∀ t : State, t.wr = s.wr → ∀ i < 2 * (slayOf s).ql, InRegions t.wr (off (s.gpr .a0) i) 1 :=
    fun t ht i hi => ⟨_, by rw [ht, hwr]; exact List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  -- A change in `out` keeps `scratch`'s header.
  have outSep : ∀ {m m' : Mem}, Outside (s.gpr .a0) 0 (2 * (slayOf s).ql) m m' →
      ∀ {d : Nat}, d + 8 ≤ 256 → word m' (slayOf s).S d = word m (slayOf s).S d := fun ho d hd =>
    in_word (out_in (o := 0) (N := 2 * (slayOf s).ql)
      (by simpa only [off, BitVec.add_zero] using ho) (by omega) (by omega) (srcO s rfl rfl).sep)
      (by omega) (by omega)
  -- The specification's values.
  have hkey : Spec.Dsa.privateKeyBytes (s.gpr .a4).toNat (s.gpr .a6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) =
      ⟨⟨pOf s.mem (slayOf s) (s.gpr .a2), qOf s.mem (slayOf s) (s.gpr .a2), gOf s.mem (slayOf s) (s.gpr .a2)⟩,
        yOf s.mem (slayOf s) (s.gpr .a2), some (xOf s.mem (slayOf s) (s.gpr .a2))⟩ := by
    rw [VG.Proof.Dsa.privateKeyBytes_at s.mem (s.gpr .a2) (by simp only [slayOf] at h3; omega),
      VG.Proof.Dsa.publicKeyBytes_at s.mem (s.gpr .a2) (by simp only [slayOf] at h3; omega)]
    rfl
  have hspec : ∀ {n : Nat}, VG.Proof.Dsa.shapeValid (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2)) →
      Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) = 8 * n →
      sRes s = if VG.Proof.Dsa.publicChecks (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2))
            (gOf s.mem (slayOf s) (s.gpr .a2)) (yOf s.mem (slayOf s) (s.gpr .a2)) ∧
          SignOk (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2))
            (gOf s.mem (slayOf s) (s.gpr .a2)) (yOf s.mem (slayOf s) (s.gpr .a2))
            (xOf s.mem (slayOf s) (s.gpr .a2)) (kOf s.mem (slayOf s) (s.gpr .a5))
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (min (stackArg s 0).toNat n)))
        then some (Spec.Dsa.encodeBE (slayOf s).ql (sigR (pOf s.mem (slayOf s) (s.gpr .a2))
              (qOf s.mem (slayOf s) (s.gpr .a2)) (gOf s.mem (slayOf s) (s.gpr .a2)) (kOf s.mem (slayOf s) (s.gpr .a5))) ++
            Spec.Dsa.encodeBE (slayOf s).ql (sigS (qOf s.mem (slayOf s) (s.gpr .a2)) (xOf s.mem (slayOf s) (s.gpr .a2))
              (kOf s.mem (slayOf s) (s.gpr .a5))
              (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (min (stackArg s 0).toNat n)))
              (sigR (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2))
                (gOf s.mem (slayOf s) (s.gpr .a2)) (kOf s.mem (slayOf s) (s.gpr .a5)))))
        else none := fun {n} hs hq8 => by
    have hc := VG.Proof.Dsa.signBytes_compute (n := n) (k := kOf s.mem (slayOf s) (s.gpr .a5))
      (nonce := Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)
      (digest := Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat) hv hs
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact h3) (VG.Proof.Bignum.bytesAt_length _ _ _) hkey rfl hq8
    dsimp only at hc
    unfold sRes
    rw [hc, bytesAt_take]
    rfl
  unfold PrevalidatedSign.sign
  refine WP.seq (WP.mono (sfront_ok hpre) fun s₁ ⟨F, k₁⟩ => ?_)
  have hwr' : ∀ u : State, ScrL u (slayOf s) → ∀ i < 13, InRegions u.wr (off (savW (stackArg s 1)) (8 * i)) 8 :=
    fun u hu i hi => by
      rw [← saveOff_eq]; exact hu.st (d := saveOff i) (by simp only [saveOff, slayOf] at hZ ⊢; omega_arith)
  have hal' : ∀ i < 13, (off (savW (stackArg s 1)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [← saveOff_eq]; exact F.scr.al8 (d := saveOff i) (by simp only [saveOff, slayOf] at hZ ⊢; omega_arith)
      (by simp only [saveOff]; omega)
  have hsav' : ∀ u : State, Kept (slayOf s) s₁.mem u.mem → ∀ i < 13,
      word u.mem (stackArg s 1) (saveOff i) = s.gpr (saved i) := fun u hu i hi =>
    (hu.word (Or.inr ⟨by simp only [saveOff, hLens]; omega, by simp only [saveOff]; omega⟩)).trans (F.sav i hi)
  have hwo : ∀ u : State, Kept (slayOf s) s₁.mem u.mem → word u.mem (slayOf s).S Sign.hOut = s.gpr .a0 :=
    fun u hu => (hu.word (Or.inr ⟨by simp only [Sign.hOut, hLens]; omega, by simp only [Sign.hOut]; omega⟩)).trans F.outw
  have hwd : ∀ u : State, Kept (slayOf s) s₁.mem u.mem → word u.mem (slayOf s).S hDigest = s.gpr .a7 :=
    fun u hu => (hu.word (Or.inl (by simp only [hDigest, hLens]; omega))).trans F.dig
  have Out₁ : Outside (slayOf s).S 0 (slayOf s).Z s.mem s₁.mem :=
    F.out.mono (Nat.le_refl _) (by simp only [slayOf] at hZ ⊢; omega)
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := keyVals_kept (srcK3 s rfl rfl) Out₁
  -- Validation: the domain's and the public key's checks, `0 < x < q` and `g^x mod p = y`.
  have hvv := validatePrivate_eq hv (by rw [VG.Proof.Bignum.bytesAt_length]; exact h3) hkey
  rw [hvv] at hval
  obtain ⟨hsh, hpub, -, hgx⟩ := of_decide_eq_true hval
  have hKO₁ : KeyOk s₁.mem (slayOf s) (s.gpr .a2) := by
    simp only [KeyOk, ep₁, eq₁, eg₁, ey₁]; exact ⟨hsh, hpub⟩
  have hP₁ : ParamsOk s₁.mem (slayOf s) (s.gpr .a2) := (keyOk_iff.mp hKO₁).1
  refine WP.seq (setup_ok hL F.scr F.regs F.lens (by omega) (srcK3 s₁ k₁.2.1 k₁.2.2) hKO₁
    (fun t _ hc Kd kc => ?_))
  have kt := k₁.trans kc
  have Ot : Outside (slayOf s).S 0 (slayOf s).Z s.mem t.mem := Out₁.trans Kd.out
  have hq8 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) =
      8 * (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8) := by
    have := hsh.1; unfold Spec.Dsa.supportedSizes at this; omega
  have ex : xOf t.mem (slayOf s) (s.gpr .a2) = xOf s.mem (slayOf s) (s.gpr .a2) := by
    simp only [xOf]
    rw [((srcK s rfl rfl).sub (o := 3 * (slayOf s).pl + (slayOf s).ql) (k := (slayOf s).ql) (by omega)).bytes Ot
      (by omega)]
  have ek : kOf t.mem (slayOf s) (s.gpr .a5) = kOf s.mem (slayOf s) (s.gpr .a5) := by
    simp only [kOf]; rw [(srcN s rfl rfl).bytes Ot (by omega)]
  obtain ⟨ept, -, egt, eyt⟩ := keyVals_kept (srcK3 s rfl rfl) Ot
  have hvt : gOf t.mem (slayOf s) (s.gpr .a2) ^ xOf t.mem (slayOf s) (s.gpr .a2) % arrP t.mem (slayOf s) 0 =
      yOf t.mem (slayOf s) (s.gpr .a2) := by
    rw [hc.p0, ep₁, egt, ex, eyt]; exact hgx
  unfold PrevalidatedSign.body
  refine WP.mono (sbodyWith_ok hL hP₁ hc (setMask_KPOk hL hc.scr hc.regs hc.inp hc.inv hvt) Kd
    (srcK t kt.2.1 kt.2.2) (srcN t kt.2.1 kt.2.2) (by omega)
    ((srcD t kt.2.1 kt.2.2).take (Nat.min_le_left _ _)) (hwd t Kd) (hwo t Kd) (hout t kt.2.2) hno
    (srcO t kt.2.1 kt.2.2)) fun u ⟨⟨ob, r0u, ⟨m, Km, Om⟩, h6u, scru⟩, ku⟩ => ?_
  refine WP.mono (sfinish_ok h6u (hwr' u scru) hal'
    (fun i hi => (outSep Om (by simp only [saveOff]; omega)).trans
      ((Km.word (by simp only [saveOff]; omega) (by simp only [saveOff]; omega)).trans (hsav' t Kd i hi))))
    fun w ⟨hab, w0, wm⟩ => ⟨hab, ?_⟩
  rw [ep₁, eq₁, eg₁, ey₁, ex, ek] at ob r0u
  have ed : Spec.Rsa.bytesAt t.mem (s.gpr .a7)
      (min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8)) =
      Spec.Rsa.bytesAt s.mem (s.gpr .a7)
        (min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8)) := by
    have := hsh.1; unfold Spec.Dsa.supportedSizes at this
    rw [show min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8) =
      min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8) by omega]
    exact ((srcD s rfl rfl).take (Nat.min_le_left _ _)).bytes Ot (by omega)
  rw [ed] at ob r0u
  have hres := hspec hsh hq8
  simp only [hpub, true_and] at hres
  refine ⟨?_, ?_⟩
  · rw [w0, r0u, ret_ofNat, hres, signStatus_ite]
  · rw [wm, h1, ob, hres]
    split <;> rfl

end VG.Proof.Dsa.RISCV64
