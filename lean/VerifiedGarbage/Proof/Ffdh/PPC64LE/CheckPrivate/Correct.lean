module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Fn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Front
import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Body
import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Status
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.DomainBody
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Correct
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.CT
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_check_private` on PPC64LE: correctness

`checkPrivate` saves the registers and sets up (`kp_front`), loads and
checks p (`loadP_ok`), checks x's range and compares `g^x mod p` with 2,
`p − 2` and y (`cpBody_ok`), and restores the registers (`kp_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.CheckPrivate
open VG.Proof.Ffdh.PPC64LE.Domain VG.Proof.Ffdh.PPC64LE.Derive
open VG.Proof.Bignum (slot)

private theorem kp_pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i) →
    r ∉ kpFrontRegs ++ ([.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] : List Reg) ++
      (cpBodyRegs ++ ([.r3] : List Reg)) := by
  decide

theorem kp_correct (s : State) (h : kpContract.pre s) :
    ∃ tr t, Exec isa checkPrivate s tr t ∧ abiPreserved s t ∧ kpContract.post s t := by
  show WP isa checkPrivate s fun t => abiPreserved s t ∧ kpContract.post s t
  have hpre := h
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, nwS, -, hL, hyl, -, -, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hin : ∀ i < 18, InRegions s.wr (off (Domain.savW (s.gpr .r10)) (8 * i)) 8 := fun i hi =>
    ⟨⟨s.gpr .r10, (stackArg s 0).toNat * 8⟩, by rw [hwr]; simp, by
      rw [off, Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  unfold checkPrivate
  refine WP.seq (WP.mono (kp_front hpre) fun s₁ ⟨hb, he, hsav, hby, k1⟩ => ?_)
  have hk := hb.k64
  have hk' := hb.k1024
  have hLk := hb.hL
  have hZ := hb.env.hZ
  have hnw := hb.env.hs.nowrap
  have e0 := Domain.slot_eq (kdOf s).c.w 0
  have e28 := Domain.slot_eq (kdOf s).c.w 28
  refine WP.seq (WP.mono (loadP_ok hb.env hb.r21 hb.r28 rfl hk hk' (fun i hi => hb.rdD i (by omega))
    (fun i hi => hb.sepD i (by omega))) fun s₂ ⟨⟨p2, c2, b2⟩, k2⟩ => ?_)
  have hb2 := hb.keep k2 b2
  have he2 := he.keep k2 b2
  have hDk : Spec.Rsa.bytesAt s₁.mem (s.gpr .r3) (s.gpr .r5).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r5).toNat := by
    rw [← Proof.Ffdh.take_bytesAt _ _ (show (s.gpr .r5).toNat ≤ (s.gpr .r4).toNat by
      rcases hLk with h | h <;> simp only [kdOf] at h <;> omega), ← Proof.Ffdh.take_bytesAt s.mem _
      (show (s.gpr .r5).toNat ≤ (s.gpr .r4).toNat by rcases hLk with h | h <;> simp only [kdOf] at h <;> omega)]
    exact congrArg _ hb.bD
  rw [show (kdOf s).c.D = s.gpr .r3 from rfl, show (kdOf s).c.k = (s.gpr .r5).toNat from rfl, hDk] at p2 c2
  generalize hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r5).toNat) = p at p2 c2
  generalize hxv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (s.gpr .r8) (s.gpr .r9).toNat) = xv
  generalize hgv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (off (s.gpr .r3) (s.gpr .r5).toNat) (s.gpr .r5).toNat) = g
  generalize hyv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (s.gpr .r6) (s.gpr .r5).toNat) = yv
  generalize hbv : bnd s₂.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat p = b
  have k12 := k1.trans k2
  have hite : WP isa (.ite (.zero .d .r0) cpBody (.block [.li .r3 0])) s₂ fun t =>
      (Spec.Rsa.modulusValid p (s.gpr .r5).toNat = true →
        t.gpr .r3 = BitVec.ofNat 64 (if ¬ (0 < xv ∧ xv < b) then 2 else if good (g ^ xv % p) p yv then 1 else 0)) ∧
      (∀ i < 18, word t.mem (s.gpr .r10) (112 + 8 * i) = word s₂.mem (s.gpr .r10) (112 + 8 * i)) ∧
      Keep (cpBodyRegs ++ ([.r3] : List Reg)) s₂ t := by
    refine WP.ite (s₂.gpr .r0 == 0) (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
    · have hv := c2.mp (by simpa using hz)
      have hf := modulus_facts hv
      refine WP.mono (cpBody_ok (Yv := s.gpr .r6) hb2.env hb2.r23 hb2.r21 hb2.r27 hb2.r28 rfl hk hk' hLk
        he2.xl1 he2.xlk he2.wX he2.wXL he2.wY hb2.rdD hb2.sepD he2.rdX he2.sepX he2.rdY he2.sepY p2 hf.1
        hf.2 hxv hgv hyv hbv) fun t ⟨⟨t3, tw⟩, kt⟩ => ⟨fun _ => t3, tw, kt.mono (by decide)⟩
    · refine WP.mono (li_ok s₂ 0 (by decide)) fun t ⟨⟨_, tm⟩, kt⟩ =>
        ⟨fun hv => absurd (c2.mpr hv) (by simpa using hz), fun i hi => by rw [tm], kt.mono (by decide)⟩
  refine WP.seq (WP.mono hite fun t₅ ⟨tpost, tw, k5⟩ => ?_)
  have kall := k12.trans k5
  have hsav' : ∀ i < 18, t₅.mem.readW (off (Domain.savW (s.gpr .r10)) (8 * i)) 64 =
      s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i) := fun i hi => by
    have ea : off (Domain.savW (s.gpr .r10)) (8 * i) = off (s.gpr .r10) (112 + 8 * i) := by
      rw [off, off, Offset.add_add]
    rw [ea]
    show word t₅.mem (s.gpr .r10) (112 + 8 * i) = _
    have b2' : Body (s.gpr .r10) (kdOf s).c.w s₁.mem s₂.mem := b2
    rw [tw i hi, Outside.word b2' (by omega) (by omega)]
    exact hsav i hi
  refine WP.mono (Domain.restore_ok t₅ ((k5.gpr .r23 (by decide)).trans hb2.r23) (by rw [kall.wr]; exact hin) hsav')
    fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, kall.sp], by rw [ulr, kall.lr]⟩, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.Ffdh.PPC64LE.Domain.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      rw [uot r hn, kall.gpr r (kp_pres_not_written r hr hn)]
  · dsimp only [kpContract]
    intro hdv
    have hL' : (s.gpr .r4).toNat = 2 * (s.gpr .r5).toNat ∨ (s.gpr .r4).toNat = 3 * (s.gpr .r5).toNat := hLk
    have hmod := Proof.Ffdh.domainValid_mod hdv
    rw [Proof.Ffdh.domainOf_p _ _ (by omega), hp] at hmod
    have hsep : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (s.gpr .r10) y < (stackArg s 0).toNat * 8 → off Q i ≠ y) →
        Spec.Rsa.bytesAt s₂.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hq => by
      rw [b2.bytesAt hZ hq]; exact hby Q n hq
    have ex : Spec.Rsa.bytesAt s₂.mem (s.gpr .r8) (s.gpr .r9).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat := hsep _ _ he.sepX
    have eg : Spec.Rsa.bytesAt s₂.mem (off (s.gpr .r3) (s.gpr .r5).toNat) (s.gpr .r5).toNat =
        Spec.Rsa.bytesAt s.mem (off (s.gpr .r3) (s.gpr .r5).toNat) (s.gpr .r5).toNat := hsep _ _ hb.sepY
    have ey : Spec.Rsa.bytesAt s₂.mem (s.gpr .r6) (s.gpr .r5).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r5).toNat := hsep _ _ he.sepY
    have eb : bnd s₂.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat p =
        bnd s.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat p :=
      bnd_congr fun hq => hsep _ _ fun i hi => by
        rw [off_off']; exact hb.sepD (2 * (s.gpr .r5).toNat + i) (by simp only [kdOf]; omega)
    rw [ex] at hxv
    rw [eg] at hgv
    rw [ey] at hyv
    rw [eb] at hbv
    have hk0 : 0 < (s.gpr .r5).toNat := by have := hb.k64; simp only [kdOf] at this; omega
    rw [privateStatus_dom hk0 hL' hdv, hp, hyl, hyv, hxv, hgv, hbv, uot .r3 (by decide), tpost hmod,
      ret_status _ (by split <;> [decide; split <;> decide])]

end VG.Proof.Ffdh.PPC64LE.CheckPrivate
