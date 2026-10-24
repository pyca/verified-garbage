module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.DomainBody
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_check_domain` on PPC64LE: the function

`vg_ffdh_check_domain(domain = r3, domain_len = r4, p_len = r5, scratch = r6,
scratch_len = r7)` (`cdContract`): `checkDomain` saves the nonvolatile
registers in the working space's header, sets up the registers, loads and
checks p (`loadP_ok`), checks q and g (`domainBody_ok`) and restores the
registers (`cd_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot slot_sep bytesAt_length)

/-- The working space, `scratch_len` words at `r6`. -/
abbrev scrR6 (s : State) : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat * 8⟩

/-- `vg_ffdh_check_domain`, on the registers. -/
def cdContract : Contract isa where
  pre s :=
    s.rd = [domR s] ∧ s.wr = [scrR6 s] ∧ (domR s).Disjoint (scrR6 s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + (s.gpr .r7).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .r5).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .r5).toNat (s.gpr .r4).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r5).toNat ≤ (s.gpr .r7).toNat
  post s t :=
    ((t.gpr .r3).setWidth 32).toNat =
      if Spec.Ffdh.domainValid (s.gpr .r5).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) then 1
      else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat).map (·.toNat)

/-- The registers `setup` writes. -/
def setup0Regs : List Reg := [.r10, .r11, .r21, .r27, .r28, .r29, .r31]

/-- `setup`, the working space at `r23`. -/
theorem setup0_ok {s : State} {S D : Addr} {k L : Nat} (h3 : s.gpr .r3 = D)
    (h4 : s.gpr .r4 = BitVec.ofNat 64 L) (h5 : s.gpr .r5 = BitVec.ofNat 64 k)
    (h23 : s.gpr .r23 = S) (hk : k ≤ 1024) :
    WP isa (.block setup) s fun t =>
      (t.gpr .r21 = D ∧ t.gpr .r27 = BitVec.ofNat 64 L ∧ t.gpr .r28 = BitVec.ofNat 64 k ∧
        t.gpr .r11 = BitVec.ofNat 64 (2 * ((k + 7) / 8)) ∧ t.gpr .r29 = BitVec.ofNat 64 (8 * ((k + 7) / 8 + 2)) ∧
        t.gpr .r10 = off S (slot ((k + 7) / 8) 0) ∧ t.gpr .r31 = S ∧ t.mem = s.mem) ∧
      Keep setup0Regs s t := by
  refine WP.keep _ ?_ (by decide)
  unfold setup
  prun [h3, h4, h5, h23, BitVec.add_zero, Pub.ofNat_add7_shr3 k (by omega), Pub.ofNat_shl3, Pub.ofNat_shl1,
    hdrBytes]
  refine ⟨?_, by simp [off, slot, hdrBytes]⟩
  rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
  congr 1

theorem cd_pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i) →
    r ∉ ([.r23] : List Reg) ++ setup0Regs ++ ([.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] : List Reg) ++
      (domainBodyRegs ++ ([.r3] : List Reg)) := by
  decide

theorem mod_one_iff {p q : Nat} (hq : 2 ≤ q) (hp : 1 ≤ p) : p % q = 1 ↔ (p - 1) % q = 0 := by
  have e := Nat.div_add_mod p q
  constructor
  · intro h
    rw [h] at e
    rw [show p - 1 = q * (p / q) by omega, Nat.mul_mod_right]
  · intro h
    have e' := Nat.div_add_mod (p - 1) q
    rw [h, Nat.add_zero] at e'
    rw [show p = q * ((p - 1) / q) + 1 by omega, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hq

/-- `domainValid`, as `checkDomain` computes it. -/
theorem domainValid_body (m : Mem) (D : Addr) {k L : Nat} (hk : 1 ≤ k) (hL : L = 2 * k ∨ L = 3 * k) :
    Spec.Ffdh.domainValid k (Spec.Rsa.bytesAt m D L) = true ↔
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k)) k = true ∧
        bodyCond L k (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D (2 * k)) k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off D k) k)) := by
  rw [Proof.Ffdh.domainValid_iff, Proof.Ffdh.domainOf_p _ _ (by omega), Proof.Ffdh.domainOf_g _ _ (by omega)]
  rcases hL with rfl | rfl
  · rw [Proof.Ffdh.domainOf_q2 _ _ (by omega)]
    simp only [bodyCond, show ¬ 2 * k = 3 * k by omega, ↓reduceIte, reduceCtorEq, false_imp_iff, imp_true_iff,
      and_true]
  · rw [Proof.Ffdh.domainOf_q3]
    simp only [bodyCond, ↓reduceIte, Option.some.injEq, forall_eq', qConds]
    constructor
    · rintro ⟨hv, hg, ⟨hq1, hq2, hq3⟩, hd, hgq⟩
      have := modulus_facts hv
      exact ⟨hv, ⟨⟨hq2, hq3⟩, hq1⟩, ⟨hg, (mod_one_iff hq2 (by omega)).mpr hd⟩, hgq⟩
    · rintro ⟨hv, ⟨⟨hq2, hq3⟩, hq1⟩, ⟨hg, hd⟩, hgq⟩
      have := modulus_facts hv
      exact ⟨hv, hg, ⟨hq1, hq2, hq3⟩, (mod_one_iff hq2 (by omega)).mp hd, hgq⟩

theorem cd_correct (s : State) (h : cdContract.pre s) :
    ∃ tr t, Exec isa checkDomain s tr t ∧ abiPreserved s t ∧ cdContract.post s t := by
  show WP isa checkDomain s fun t => abiPreserved s t ∧ cdContract.post s t
  obtain ⟨hrd, hwr, dDS, nwD, nwS, ⟨hk, hk'⟩, hL, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [domR, scrR6] at hrd hwr dDS
  generalize hDd : s.gpr .r3 = D at hrd dDS nwD
  generalize hLd : (s.gpr .r4).toNat = L at hrd dDS nwD hL
  generalize hkd : (s.gpr .r5).toNat = k at hk hk' hL hsl
  generalize hSd : s.gpr .r6 = S at hwr dDS nwS
  generalize hZd : (s.gpr .r7).toNat * 8 = Z at hwr dDS nwS
  have hL' : L = 2 * k ∨ L = 3 * k := by simp only [Spec.Ffdh.domainLenValid] at hL; omega
  have hZ256 : 256 ≤ Z := by omega
  generalize hwd : (k + 7) / 8 = w
  have hw4 : 4 ≤ w := by omega
  have hw' : w ≤ 128 := by omega
  have hZw : slot w 28 ≤ Z := by rw [slot_eq]; omega_using [hsl, hZd, hwd, hk', hk]
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  have hin : ∀ i < 18, InRegions s.wr (off (savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega) (by omega)⟩
  have sepD := sep_of_disjoint (L := L) dDS (by omega)
  have rdD := rd_of_mem (s := s) (D := D) (L := L) (by rw [hrd]; simp) (by omega)
  unfold checkDomain
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (ws := .r6) (by decide) s (by rw [hSd]; exact hin)) fun s₁ hS => ?_
  have k1 := hS.keep
  have h23₁ : s₁.gpr .r23 = S := hS.r23.trans hSd
  have hfr₁ : Frame [savR S] s.mem s₁.mem := hSd ▸ hS.frame
  refine WP.mono (setup0_ok (D := D) (L := L) (k := k) ((k1.gpr .r3 (by decide)).trans hDd)
    (by rw [k1.gpr .r4 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [k1.gpr .r5 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64]) h23₁ hk')
    fun s₂ ⟨⟨a21, a27, a28, a11, a29, a10, a31, m2⟩, k2⟩ => ?_
  rw [hwd] at a11 a29 a10
  have k12 := k1.trans k2
  have e2 : Env s₂ S Z w := ⟨hs.congr k12.wr, a10, a29, a11, a31, hw4, hw', hZw⟩
  have hbD : ∀ (P : Addr) n, (∀ i < n, ∀ x, ofs S x < Z → off P i ≠ x) →
      Spec.Rsa.bytesAt s₂.mem P n = Spec.Rsa.bytesAt s.mem P n := fun P n hsep => by
    rw [m2]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hfr₁ _ fun r hr hc => ?_
    rw [List.mem_singleton] at hr
    subst hr
    have hc' := (Offset.sub_base (n := 144) (k := Z) S (d := 112) (by omega)) _ hc
    exact hsep i (List.mem_range.mp hi) _ (by simp only [Region.Contains] at hc'; exact hc') rfl
  have g23 : s₂.gpr .r23 = S := (k2.gpr .r23 (by decide)).trans h23₁
  have sep' : ∀ {a}, a + k ≤ L → ∀ i < k, ∀ x, ofs S x < Z → off (off D a) i ≠ x := fun ha i hi => by
    rw [off_off']; exact sepD _ (by omega)
  refine WP.seq (WP.mono (loadP_ok e2 a21 a28 hwd.symm hk hk' (fun i hi => by
      rw [k12.rd, k12.wr]; exact rdD i (by omega)) (fun i hi => sepD i (by omega)))
    fun s₃ ⟨⟨p3, c3, b3⟩, k3⟩ => ?_)
  rw [hbD D k fun i hi => sepD i (by omega)] at p3 c3
  have e3 : Env s₃ S Z w := e2.keep k3 (by decide)
  have k13 := k12.trans k3
  have hb3 : ∀ (P : Addr) n, (∀ i < n, ∀ x, ofs S x < Z → off P i ≠ x) →
      Spec.Rsa.bytesAt s₃.mem P n = Spec.Rsa.bytesAt s.mem P n := fun P n hsep => by
    rw [b3.bytesAt hZw hsep, hbD P n hsep]
  have hite : WP isa (.ite (.zero .d .r0) domainBody (.block [.li .r3 0])) s₃ fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k)) k = true ∧
          bodyCond L k (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) then 1 else 0)) ∧
        Body S w s₃.mem t.mem ∧ Keep (domainBodyRegs ++ ([.r3] : List Reg)) s₃ t := by
    refine WP.ite (s₃.gpr .r0 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
    · have hv := c3.mp (by simpa using hb)
      have hf := modulus_facts hv
      refine WP.mono (domainBody_ok (L := L) e3 ((k3.gpr .r23 (by decide)).trans g23)
        ((k3.gpr .r21 (by decide)).trans a21) ((k3.gpr .r27 (by decide)).trans a27)
        ((k3.gpr .r28 (by decide)).trans a28) (by omega) (by omega) hk' hL'
        (fun i hi => by rw [k13.rd, k13.wr]; exact rdD i hi) sepD
        (p3.trans (by rw [hb3 D k fun i hi => sepD i (by omega)])) (by rw [p3]; exact hf.1) (by rw [p3]; exact hf.2))
        fun t ⟨⟨t3, bt⟩, kt⟩ => ⟨?_, bt, kt.mono (by decide)⟩
      rw [t3, p3, hb3 (off D k) k (sep' (a := k) (by omega))]
      rcases hL' with rfl | rfl
      · simp only [hv, true_and, bodyCond, show ¬ 2 * k = 3 * k by omega, ↓reduceIte]
      · rw [hb3 (off D (2 * k)) k (sep' (a := 2 * k) (by omega))]
        simp only [hv, true_and]
    · refine WP.mono (li_ok s₃ 0 (by decide)) fun t ⟨⟨t3, tm⟩, kt⟩ =>
        ⟨?_, by rw [tm]; exact Outside.refl _ _ _ _, kt.mono (by decide)⟩
      rw [t3, ite_eq_right fun hc => absurd (c3.mpr hc.1) (by simpa using hb)]
  refine WP.seq (WP.mono hite fun t₄ ⟨t3, b4, k4⟩ => ?_)
  have k14 := k13.trans k4
  have hsav : ∀ i < 18, t₄.mem.readW (off (savW S) (8 * i)) 64 = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i) :=
      fun i hi => by
    have ea : off (savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    have e0 : slot w 0 = 256 := by rw [slot_eq]; omega
    rw [← hS.saved i hi, hSd, ea]
    show Mont.word t₄.mem S (112 + 8 * i) = Mont.word s₁.mem S (112 + 8 * i)
    rw [Outside.word b4 (by omega) (by omega), Outside.word b3 (by omega) (by omega), m2]
  refine WP.mono (restore_ok t₄ ((k4.gpr .r23 (by decide)).trans ((k3.gpr .r23 (by decide)).trans g23))
    (by rw [k14.wr]; exact hin) hsav) fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, k14.sp], by rw [ulr, k14.lr]⟩, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.Ffdh.PPC64LE.Domain.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      rw [uot r hn, k14.gpr r (cd_pres_not_written r hr hn)]
  · show ((u.gpr .r3).setWidth 32).toNat = _
    rw [uot .r3 (by decide), t3, ret_ofNat, hDd, hLd, hkd]
    exact ite_congr (propext (domainValid_body s.mem D (by omega) hL').symm) (fun _ => rfl) (fun _ => rfl)

end VG.Proof.Ffdh.PPC64LE.Domain
