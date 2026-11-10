module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtFn
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtMid2
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtFront
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPre
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtMid1
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSave
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtVals
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
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

/-- `crtG pc`: with `pc`, given the cached values (`R2F`). -/
theorem crt_wp (pc : Bool) (s : State) {X : List Region} (h : preCore (baseRd s ++ X) s)
    (hR : pc = true → R2F s) :
    WP isa (crtG pc) s fun t => abiPreserved s t ∧ postCore s t := by
  have hP := pre_factsG h
  have hn := hP.nw
  have hpre := h
  obtain ⟨hsp, hrd, hwr, dON, dOI, dOP, dOQ, dODP, dODQ, dOQI, dOS, dOA, dNS, dIS, dPS, dQS, dDPS, dDQS, dQIS,
    dSA, nwO, nwN, nwI, nwP, nwQ, nwDP, nwDQ, nwQI, nwS, ⟨hk, hk'⟩, hOL, hIL, hp1, hpk, hq1, hqk, hdpl, hqil, hdql,
    hsl⟩ := hpre
  simp only [Spec.Rsa.scratchWords] at hsl
  unfold crtG
  refine WP.seq (WP.mono (front_okG pc s h) fun s₁ ⟨hF, hhd⟩ => ?_)
  have hR2 : pc = true → R2F s ∧ word s₁.mem (cS s) oR2 = s.gpr .r31 := fun hp => ⟨hR hp, hhd hp⟩
  refine mid1_ok hP hF hR2 fun t t26 v0 w0 v5 v7 p0 p4 q4 t10 t29 O1 k1 => ?_
  refine mid2_ok hP hF hR2 t26 v0 w0 v5 v7 p0 p4 q4 t10 t29 O1 k1 fun u ub u3 uF ku => ?_
  have kfu := hF.keep.trans ku
  have hS : (⟨cS s, cZ s⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hin : ∀ i < 18, InRegions u.wr (off (savW (cS s)) (8 * i)) 8 := fun i hi => by
    rw [kfu.wr]
    show InRegions _ (cS s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, hS, Offset.contains_base _ (by show _ ≤ (stackArg s 9).toNat * 8; omega_arith) (by omega_arith)⟩
  have hsav : ∀ i < 18, u.mem.readW (off (savW (cS s)) (8 * i)) 64 = s.gpr (Crt.saved i) := fun i hi => by
    rw [uF.readW (r := ⟨off (savW (cS s)) (8 * i), 8⟩) (by simp [Region.Contains]) ?_ (by decide)]
    · exact hF.sav i hi
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · show Region.Disjoint ⟨cS s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i), 8⟩
          ⟨cS s + BitVec.ofNat 64 256, _⟩
        rw [Offset.add_add]
        exact Offset.disjoint _ (Or.inl (by omega_arith)) (by omega_arith) (by show _ ≤ 2 ^ 64; omega_arith)
      · have sub : Region.Sub ⟨off (savW (cS s)) (8 * i), 8⟩ ⟨cS s, cZ s⟩ := by
          show Region.Sub ⟨cS s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i), 8⟩ _
          rw [Offset.add_add]; exact Offset.sub_base _ (by show _ ≤ (stackArg s 9).toNat * 8; omega_arith)
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

/-- A cache of two numbers of `a` and `b` words, as their words. -/
theorem cache_words {m : Mem} {P : Addr} {a b X Y : Nat}
    (h : Spec.Rsa.wordsAt m P (a + b) = Spec.Rsa.toWords X a ++ Spec.Rsa.toWords Y b)
    (hX : X < 2 ^ (64 * a)) (hY : Y < 2 ^ (64 * b)) : wv m P 0 a = X ∧ wv m P (8 * a) b = Y := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.toWords, Spec.Rsa.toWords, List.range_add, List.map_append, List.map_map] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  rw [List.map_inj_left] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [← Nat.mod_eq_of_lt hX]
    refine wv_of_words fun i hi => ?_
    show (m.readW (P + BitVec.ofNat 64 (0 + 8 * i)) 64).toNat = _
    rw [Nat.zero_add, h1 i (List.mem_range.mpr hi), BitVec.toNat_ofNat]
  · rw [← Nat.mod_eq_of_lt hY]
    refine wv_of_words fun i hi => ?_
    have := h2 i (List.mem_range.mpr hi)
    simp only [Function.comp_apply] at this
    show (m.readW (P + BitVec.ofNat 64 (8 * a + 8 * i)) 64).toNat = _
    rw [show 8 * a + 8 * i = 8 * (a + i) by omega_arith, this, BitVec.toNat_ofNat]

/-- `R2F` from `fnContractP`'s precondition. -/
theorem r2F_of {s : State} (h : fnContractP.pre s) : R2F s where
  hS := h.2.2.2.1
  rd i hi := by
    have hi' : i < wsWords (s.gpr .r10).toNat + wsWords (stackArg s 1).toNat := hi
    have := h.2.2.2.1; simp only [r2R] at this
    exact ⟨r2R s, List.mem_append_left _ (by rw [h.1.2.1]; exact List.mem_append_right _ (List.mem_singleton_self _)),
      Offset.contains_base _ (show 8 * i + 8 ≤ 8 * (wsWords (s.gpr .r10).toNat + wsWords (stackArg s 1).toNat) by
        omega_arith) (by omega_arith)⟩
  sep x hx := Pub.sep_of_disjoint h.2.2.1 x hx
  val hb := by
    have hw := h.2.2.2.2
    have ew : ∀ n, Spec.Rsa.primeWords n = wsWords n := fun _ => rfl
    simp only [Spec.Rsa.primeR2, VG.Proof.Bignum.bytesAt_length, ew] at hw
    obtain ⟨mP1, _, mQ1, _, mPb, mQb, _, _, _⟩ := masked_facts (pre_factsG h.1)
    have eP : mP s = vP s := by simp only [mP, hb, ↓reduceIte]
    have eQ : mQ s = vQ s := by simp only [mQ, hb, ↓reduceIte]
    rw [eP] at mP1 mPb; rw [eQ] at mQ1 mQb
    exact cache_words hw (Nat.lt_trans (Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one mP1)) mPb)
      (Nat.lt_trans (Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one mQ1)) mQb)

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa crt s tr t ∧ abiPreserved s t ∧ fnContract.post s t :=
  crt_wp false s (preCore_nil h) nofun

theorem fn_correctP (s : State) (h : fnContractP.pre s) :
    ∃ tr t, Exec isa crtP s tr t ∧ abiPreserved s t ∧ fnContractP.post s t :=
  crt_wp true s h.1 fun _ => r2F_of h

end VG.Proof.Bignum.PPC64LE.Crt
