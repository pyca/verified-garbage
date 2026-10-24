module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Fn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Front
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Body
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.ScalarEq
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.DomainBody
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_generate_key` on PPC64LE: correctness

`generateKey` saves the registers and sets up (`gk_front`), loads and checks
p (`loadP_ok`), cuts x from `rand`, computes `g^x mod p` or zeros and zeros x
but for the status 1 (`gkBody_ok`), and restores the registers
(`gk_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.GenerateKey
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot)

private theorem gk_pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i) →
    r ∉ gkFrontRegs ++ ([.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] : List Reg) ++
      (gkBodyRegs ++ ([.r3] : List Reg)) := by
  decide

theorem ret_st (n : Nat) (hn : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem gk_correct (s : State) (h : gkContract.pre s) :
    ∃ tr t, Exec isa generateKey s tr t ∧ abiPreserved s t ∧ gkContract.post s t := by
  show WP isa generateKey s fun t => abiPreserved s t ∧ gkContract.post s t
  have hpre := h
  obtain ⟨-, hrd, hwr, dXY, dXD, dXR, dXS, -, dYD, -, dYS, -, dDS, dRS, -, nwX, nwY, -, nwR, nwS, ⟨hk64, hk1024⟩, hL,
    hxl, hyl, hrl, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  rw [hxl] at hwr dXY dXD dXR dXS nwX
  rw [hyl] at hwr dXY dYD dYS nwY
  rw [hrl] at hrd dXR dRS nwR
  generalize hkd : (s.gpr .r9).toNat = k at hk64 hk1024 hL hxl hyl hrl hsl hwr dXY dXD dXR dXS dYD dYS dRS hrd nwR nwX nwY
  have hin : ∀ i < 18, InRegions s.wr (off (Domain.savW (stackArg s 1)) (8 * i)) 8 := fun i hi =>
    ⟨⟨stackArg s 1, (stackArg s 2).toNat * 8⟩, by rw [hwr]; simp, by
      rw [off, Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  -- The arguments apart.
  have sepXS := sep_of_disjoint dXS (by omega)
  have sepSX : ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → k ≤ ofs (s.gpr .r3) y :=
    Pub.sep_of_disjoint dXS.symm
  have sepRX := sep_of_disjoint dXR.symm (by omega)
  have sepDX := sep_of_disjoint dXD.symm (by omega)
  have sepXO := sep_of_disjoint dXY (by omega)
  have sepOX := sep_of_disjoint dXY.symm (by omega)
  have sepOS : ∀ x, ofs (s.gpr .r5) x < k → (stackArg s 2).toNat * 8 ≤ ofs (stackArg s 1) x :=
    Pub.sep_of_disjoint dYS
  have sepSO : ∀ x, ofs (stackArg s 1) x < (stackArg s 2).toNat * 8 → k ≤ ofs (s.gpr .r5) x :=
    Pub.sep_of_disjoint dYS.symm
  have sepRS := sep_of_disjoint dRS (by omega)
  have h4 : s.gpr .r4 = BitVec.ofNat 64 k := by rw [← hxl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold generateKey
  refine WP.seq (WP.mono (gk_front hpre) fun s₁ ⟨hb, w8, w9, w10, w11, hsav, hby, k1⟩ => ?_)
  have ek : (gcOf s).k = k := hkd
  have hk := hb.k64
  have hk' := hb.k1024
  have hLk := hb.hL
  have hZ := hb.env.hZ
  have hnw := hb.env.hs.nowrap
  rw [ek] at hk hk' hLk
  have e0 := Domain.slot_eq (gcOf s).w 0
  have e28 := Domain.slot_eq (gcOf s).w 28
  refine WP.seq (WP.mono (loadP_ok hb.env hb.r21 (by rw [hb.r28, ek]) rfl (by rw [ek]; omega) (by rw [ek]; omega)
    (fun i hi => hb.rdD i (by omega)) (fun i hi => hb.sepD i (by omega))) fun s₂ ⟨⟨p2, c2, b2⟩, k2⟩ => ?_)
  have hb2 := hb.keep k2 b2
  have k12 := k1.trans k2
  -- The bytes apart from the working space.
  have hsep : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off Q i ≠ y) →
      Spec.Rsa.bytesAt s₂.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hq => by
    rw [b2.bytesAt hZ hq]; exact hby Q n hq
  have sepD : ∀ i < (s.gpr .r8).toNat, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off (s.gpr .r7) i ≠ y :=
    hb.sepD
  rw [show (gcOf s).D = s.gpr .r7 from rfl, ek, hby _ _ fun i hi => sepD i (by
    rcases hLk with h | h <;> simp only [gcOf] at h <;> omega)] at p2 c2
  generalize hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) k) = p at p2 c2
  have hpk : p < 256 ^ k := by
    rw [← hp]; have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (s.gpr .r7) k)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  have hw2 : ∀ d, d + 8 ≤ 256 → word s₂.mem (stackArg s 1) d = word s₁.mem (stackArg s 1) d := fun d hd => by
    have b2' : Body (stackArg s 1) (gcOf s).w s₁.mem s₂.mem := b2
    rw [Outside.word b2' (by omega) (by omega)]
  have hL' : (s.gpr .r8).toNat = 2 * k ∨ (s.gpr .r8).toNat = 3 * k := hLk
  rw [show (gcOf s).S = stackArg s 1 from rfl, show (gcOf s).w = (k + 7) / 8 by simp only [gcOf, CD.w]; rw [hkd]] at p2
  generalize hD : s.gpr .r7 = D at hp sepD hsep hL' sepDX dYD dXD hrd ⊢
  generalize hL'' : (s.gpr .r8).toNat = L at hL' sepD sepDX dYD dXD hrd ⊢
  have sepP : ∀ i < k, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off (bptr D k L) i ≠ y :=
    fun i hi => by
      unfold bptr
      split
      · rw [off_off']; exact sepD _ (by omega)
      · exact sepD _ (by omega)
  have sepG : ∀ i < k, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off (off D k) i ≠ y :=
    fun i hi => by rw [off_off']; exact sepD _ (by omega)
  -- The arguments, as the code reads them.
  generalize hS : stackArg s 1 = S at hsep sepP sepG sepD sepXS sepSX sepRS sepOS sepSO hw2 hsav hin p2 ⊢
  generalize hZd : (stackArg s 2).toNat * 8 = Z at hsep sepP sepG sepD sepXS sepSX sepRS sepOS sepSO
  have g23 : s₂.gpr .r23 = S := hb2.r23.trans hS
  have e2 : Env s₂ S Z ((k + 7) / 8) := by
    have := hb2.env; rw [show (gcOf s).S = stackArg s 1 from rfl, hS] at this
    simp only [gcOf, CD.w] at this; rw [hkd, hZd] at this; exact this
  have hite : WP isa (.ite (.zero .d .r0) gkBody (.block [.li .r3 0])) s₂ fun t =>
      (Spec.Rsa.modulusValid p k = true →
        t.gpr .r3 = BitVec.ofNat 64 (gkSt (Spec.Rsa.os2ip (gkOct s₂.mem D (s.gpr .r10) k L))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (off D k) k)) p (Derive.bnd s₂.mem D k L p)) ∧
        Spec.Rsa.bytesAt t.mem (s.gpr .r5) k = (if gkSt (Spec.Rsa.os2ip (gkOct s₂.mem D (s.gpr .r10) k L))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (off D k) k)) p (Derive.bnd s₂.mem D k L p) = 1 then
          Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (off D k) k) ^
            Spec.Rsa.os2ip (gkOct s₂.mem D (s.gpr .r10) k L) % p) k else List.replicate k 0) ∧
        Spec.Rsa.bytesAt t.mem (s.gpr .r3) k = (if gkSt (Spec.Rsa.os2ip (gkOct s₂.mem D (s.gpr .r10) k L))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (off D k) k)) p (Derive.bnd s₂.mem D k L p) = 1 then
          gkOct s₂.mem D (s.gpr .r10) k L else List.replicate k 0)) ∧
      (∀ i < 18, word t.mem S (112 + 8 * i) = word s₂.mem S (112 + 8 * i)) ∧
      Keep (gkBodyRegs ++ ([.r3] : List Reg)) s₂ t := by
    refine WP.ite (s₂.gpr .r0 == 0) (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
    · have hv := c2.mp (by simpa using hz)
      have hf := modulus_facts hv
      have rdR : ∀ i < k, InRegions (s₂.rd ++ s₂.wr) (off (s.gpr .r10) i) 1 := by
        rw [k12.rd, k12.wr]
        exact rd_of_mem (s := s) (D := s.gpr .r10) (L := k) (by rw [hrd]; simp) (by omega)
      refine WP.mono (gkBody_ok (s := s₂) (Z := Z) (w := (k + 7) / 8) (k := k) (L := L) (p := p) (B := S) (D := D) (X := s.gpr .r3) (O := s.gpr .r5) (R := s.gpr .r10) e2 g23
        (by rw [hb2.r21]; exact hD) (by rw [hb2.r27, ← hL'']; rfl) (by rw [hb2.r28, ek]) rfl hk hk' hL'
        (by show word s₂.mem S 64 = _; rw [hw2 64 (by omega), ← hS, w8]; simp [off])
        (by show word s₂.mem S 72 = _; rw [hw2 72 (by omega), ← hS, w9, h4])
        (by show word s₂.mem S 80 = _; rw [hw2 80 (by omega), ← hS, w10]; simp [off])
        (by show word s₂.mem S 88 = _; rw [hw2 88 (by omega), ← hS, w11]; simp [off])
        (fun i hi => by
          have := hb2.rdD i (show i < (s.gpr .r8).toNat by omega)
          rwa [show (gcOf s).D = s.gpr .r7 from rfl, hD] at this)
        sepD
        rdR
        (Scr.of_mem (by rw [k12.wr, hwr]; simp) nwX) sepXS sepSX sepRX sepDX sepXO sepOX
        (Scr.of_mem (by rw [k12.wr, hwr]; simp) nwY) sepOS sepSO p2 hf.1 hf.2 hpk)
        fun t ⟨⟨t3, ty, tx, tw⟩, kt⟩ => ⟨fun _ => ⟨t3, ty, tx⟩, fun i hi => tw _ (by omega),
          kt.mono fun r hr => List.mem_append_left _ hr⟩
    · refine WP.mono (li_ok s₂ 0 (by decide)) fun t ⟨⟨_, tm⟩, kt⟩ =>
        ⟨fun hv => absurd (c2.mpr hv) (by simpa using hz), fun i hi => by rw [tm],
          kt.mono fun r hr => List.mem_append_right _ hr⟩
  refine WP.seq (WP.mono hite fun t₅ ⟨tpost, tw, k5⟩ => ?_)
  have kall := k12.trans k5
  have hsav' : ∀ i < 18, t₅.mem.readW (off (Domain.savW S) (8 * i)) 64 =
      s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i) := fun i hi => by
    have ea : off (Domain.savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [ea]
    show word t₅.mem S (112 + 8 * i) = _
    rw [tw i hi, hw2 _ (by omega)]
    exact hsav i hi
  refine WP.mono (Domain.restore_ok t₅ ((k5.gpr .r23 (by decide)).trans g23) (by rw [kall.wr]; exact hin) hsav')
    fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, kall.sp], by rw [ulr, kall.lr]⟩, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.Ffdh.PPC64LE.Domain.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      rw [uot r hn, kall.gpr r (gk_pres_not_written r hr hn)]
  · dsimp only [gkContract, gkScalar]
    intro hdv
    rw [hD, hL'', hkd] at hdv
    rw [hD, hL'', hkd, hrl]
    have hmod := Proof.Ffdh.domainValid_mod hdv
    rw [Proof.Ffdh.domainOf_p _ _ (by omega), hp] at hmod
    have hf := modulus_facts hmod
    -- The bytes the code read, as the arguments' bytes.
    have eO : gkOct s₂.mem D (s.gpr .r10) k L = gkOct s.mem D (s.gpr .r10) k L := by
      unfold gkOct; rw [hsep _ _ sepRS, hsep _ _ sepP]
    have eg : Spec.Rsa.bytesAt s₂.mem (off D k) k = Spec.Rsa.bytesAt s.mem (off D k) k := hsep _ _ sepG
    have eb : Derive.bnd s₂.mem D k L p = Derive.bnd s.mem D k L p := by
      unfold Derive.bnd
      by_cases hq : L = 3 * k
      · rw [ite_eq_left hq, ite_eq_left hq, hsep _ _ fun i hi => by rw [off_off']; exact sepD _ (by omega)]
      · rw [ite_eq_right hq, ite_eq_right hq]
    rw [eO, eg, eb] at tpost
    obtain ⟨t3, ty, tx⟩ := tpost hmod
    have hx := gkOct_eq s.mem D (s.gpr .r10) (by omega) hL' (fun _ => by rw [hp]; exact ⟨hf.2, by omega⟩)
    have hlen := gkOct_length s.mem D (s.gpr .r10) (L := L) (show 1 ≤ k by omega)
    rw [hx] at t3 ty tx
    generalize Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf k (Spec.Rsa.bytesAt s.mem D L))
      (Spec.Rsa.bytesAt s.mem (s.gpr .r10) k) = x at t3 ty tx hx ⊢
    rw [Derive.keyStatus_dom (by omega) hL' hdv, Proof.Ffdh.domainOf_g _ _ (by omega),
      Proof.Ffdh.domainOf_p _ _ (by omega), hp, VG.Proof.Bignum.powMod_eq]
    rw [um, uot .r3 (by decide), t3, ret_st _ (by unfold gkSt; split <;> [decide; split <;> decide])]
    rw [show s.gpr .r3 = s.gpr .r3 from rfl, ty, tx]
    refine ⟨rfl, ?_⟩
    by_cases h1 : gkSt x (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p (Derive.bnd s.mem D k L p) = 1
    · rw [ite_eq_left h1, ite_eq_left h1]
      simp only [gkSt] at h1 ⊢
      rw [ite_eq_left h1]
      refine ⟨?_, trivial⟩
      have e := VG.Proof.Rsa.i2osp_os2ip (gkOct s.mem D (s.gpr .r10) k L)
      rw [hlen] at e
      rw [← hx]
      exact e.symm
    · rw [ite_eq_right h1, ite_eq_right h1]
      simp only [gkSt] at h1 ⊢
      rw [ite_eq_right h1]
      exact ⟨trivial, trivial⟩

end VG.Proof.Ffdh.PPC64LE.GenerateKey
