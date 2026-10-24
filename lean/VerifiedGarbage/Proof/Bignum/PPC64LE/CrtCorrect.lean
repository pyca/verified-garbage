module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtFn
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtMid2
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtFront
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPre
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtMid1
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSave
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtVals
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.CrtNatural
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The RSA private-key operation on PPC64LE: correctness

`crt` saves the nonvolatile registers, stores its arguments and sets up `X`
(`front_ok`), computes the result (`mid1_ok`, `mid2_ok`) and restores the
registers (`fn_correct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

theorem pres_cases : ∀ r ∈ preserved, (∀ i < 18, r ≠ Crt.saved i) →
    r ∉ frontRegs ∧ r ∉ mid1Regs ++ mid2Regs := by
  decide

theorem toNat_flag (b : Bool) : BitVec.ofNat 64 (if b then 1 else 0) = BitVec.ofNat 64 b.toNat := by
  cases b <;> rfl

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa crt s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  show WP isa crt s fun t => abiPreserved s t ∧ fnContract.post s t
  have hP := pre_facts h
  have hn := hP.nw
  have hpre := h
  obtain ⟨hsp, hrd, hwr, dON, dOI, dOP, dOQ, dODP, dODQ, dOQI, dOS, dOA, dNS, dIS, dPS, dQS, dDPS, dDQS, dQIS,
    dSA, nwO, nwN, nwI, nwP, nwQ, nwDP, nwDQ, nwQI, nwS, ⟨hk, hk'⟩, hOL, hIL, hp1, hpk, hq1, hqk, hdpl, hqil, hdql,
    hsl⟩ := hpre
  simp only [Spec.Rsa.scratchWords] at hsl
  unfold crt
  refine WP.seq (WP.mono (front_ok s h) fun s₁ hF => ?_)
  refine mid1_ok hP hF fun t t26 v0 w0 v5 v7 p0 p4 q4 t10 t29 O1 k1 => ?_
  refine mid2_ok hP hF t26 v0 w0 v5 v7 p0 p4 q4 t10 t29 O1 k1 fun u ub u3 uF ku => ?_
  have kfu := hF.keep.trans ku
  have hS : (⟨cS s, cZ s⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hin : ∀ i < 18, InRegions u.wr (off (savW (cS s)) (8 * i)) 8 := fun i hi => by
    rw [kfu.wr]
    show InRegions _ (cS s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, hS, Offset.contains_base _ (by show _ ≤ (stackArg s 9).toNat * 8; omega) (by omega)⟩
  have hsav : ∀ i < 18, u.mem.readW (off (savW (cS s)) (8 * i)) 64 = s.gpr (Crt.saved i) := fun i hi => by
    rw [uF.readW (r := ⟨off (savW (cS s)) (8 * i), 8⟩) (by simp [Region.Contains]) ?_ (by decide)]
    · exact hF.sav i hi
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · show Region.Disjoint ⟨cS s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i), 8⟩
          ⟨cS s + BitVec.ofNat 64 256, _⟩
        rw [Offset.add_add]
        exact Offset.disjoint _ (Or.inl (by omega)) (by omega) (by show _ ≤ 2 ^ 64; omega)
      · have sub : Region.Sub ⟨off (savW (cS s)) (8 * i), 8⟩ ⟨cS s, cZ s⟩ := by
          show Region.Sub ⟨cS s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i), 8⟩ _
          rw [Offset.add_add]; exact Offset.sub_base _ (by show _ ≤ (stackArg s 9).toNat * 8; omega)
        have dOS' : (⟨s.gpr .r3, ck s⟩ : Region).Disjoint ⟨cS s, cZ s⟩ := by
          show (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region).Disjoint _
          rw [← hOL]; exact dOS
        exact dOS'.symm.sub_left sub
  refine WP.mono (restore_ok u (S := cS s) (v := fun i => s.gpr (Crt.saved i))
    (by rw [ku.gpr .r23 (by decide)]; exact hF.r23) hin hsav)
    fun w ⟨wrs, wot, wm, _, _, wsp, wlr⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Crt.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact wrs i hi
    · have hn : ∀ i < 18, r ≠ Crt.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      obtain ⟨h1, h2⟩ := pres_cases r hr hn
      rw [wot r hn, ku.gpr r h2, hF.keep.gpr r h1]
  · rw [wsp, kfu.sp]
  · rw [wlr, kfu.lr]
  · show Spec.Rsa.written w.mem (s.gpr .r3) (ck s) ((w.gpr .r3).setWidth 32) _
    rw [wm, wot .r3 (by decide), u3]
    refine VG.Proof.Bignum.crtWritten_of (VG.Proof.Bignum.bytesAt_length _ _ _) ub (toNat_flag _)
      (fun hv => ?_) (fun hv => ?_)
    · have hcb : cb s = (decide (vC s < vN s) && decide (vQI s < vP s) && decide (vP s * vQ s = vN s)) := by
        simp only [cb, crtMask, hv, Bool.true_and]
      refine ⟨?_, ?_⟩
      · rw [hcb]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, c, b⟩, fun ⟨a, c, b⟩ => ⟨⟨a, b⟩, c⟩⟩
      · unfold vr
        cases hb : cb s
        · rfl
        · obtain ⟨_, _, _, _, hp1', _, _, _⟩ := mask_true hP.k64
            (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk)
            hb
          simp only [↓reduceIte, VG.Proof.Bignum.crtResult]
          rw [VG.Proof.Bignum.crt_coefficient_natural (Nat.lt_trans Nat.zero_lt_one hp1')]
          unfold vh vm1 vm2 mQ mP mQI
          simp only [hb, ↓reduceIte]
          exact Nat.add_comm _ _
    · have hcb : cb s = false := by simp only [cb, crtMask, hv, Bool.false_and]
      exact ⟨hcb, by unfold vr; rw [hcb]; rfl⟩

end VG.Proof.Bignum.PPC64LE.Crt
