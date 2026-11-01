module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvFail
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArith
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCheck
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Rsa.CrtValuesMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvMid
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Rsa.KeyWorkspace
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvStores
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
public import VerifiedGarbage.Spec.Rsa

/-!
# `vg_rsa_crt_values` on PPC64LE: correctness

`valid_ok`: for a valid modulus, the results are `crtKey`'s
(`Proof/Rsa/CrtValuesMath.lean`'s `crtKey_masked`); `fail_post`: for one
that is not, `crtKey` is `none` and the results are zeros. `cv_correct`:
with the entry, the check and the restore of `r29`–`r31`, `code` meets
`cvP`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.CrtValues (valid code restore sMask aDR2 aDR3 nArr)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)
open VG.Proof.Rsa.CrtValues (maskOf)

/-- Bytes that are all zero. -/
theorem bytes_zero {m : Mem} {O : Addr} {L : Nat} (h : ∀ c < L, m (off O c) = 0) :
    Spec.Rsa.bytesAt m O L = List.replicate L 0 := by
  rw [Spec.Rsa.bytesAt, List.eq_replicate_iff]
  refine ⟨by simp, fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact h i (List.mem_range.mp hi)

/-- The registers the function changes before the restore. -/
abbrev allRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r29, .r30, .r31]

/-- What holds before the restore. -/
def Done (s0 t : State) : Prop := (∃ m, Fr s0 m t) ∧ cvP.post s0 t

/-- A results' bytes from an array's low bytes. -/
theorem bytes_of {m m' : Mem} {B O : Addr} {w j L : Nat} (hL : L ≤ 4 * w)
    (hb : ∀ c < L, m' (off O c) = if true then m (off B (arr w j + (L - 1 - c))) else 0) :
    Spec.Rsa.bytesAt m' O L = Spec.Rsa.i2osp (num m B w j % 2 ^ (8 * L)) L := by
  rw [bytes_of_store hL fun c hc => by rw [hb c hc]; rfl, Nat.pow_mul]

theorem valid_ok [InvLaw] {s0 s : State} (h : Base s0 s) (ha : Args s0 s)
    (hv : Spec.Rsa.modulusValid (nIn s0) (cvK s0) = true) :
    WP isa valid s fun t => Done s0 t ∧ Keep allRegs s t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, p1, p2, q1, q2, -, -, -, -, -, -⟩ := h.pre
  obtain ⟨-, -, hkw⟩ := pre_ws h.pre |>.2
  have hk2 : (s0.gpr .r10).toNat ≤ 4 * cvW s0 := hkw
  rw [valid, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setup_ok h ha.r18) fun t1 ⟨b1, w1, z1, k1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok b1 (ha.of_keep k1) w1 z1) fun t2 ⟨b2, w2, i2, k2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have a2 := ha.of_keep (k1.trans k2)
  have hP := os2ip_bytes_lt s0.mem (PPC64LE.stackArg s0 0) (PPC64LE.stackArg s0 1).toNat
  have hQ := os2ip_bytes_lt s0.mem (PPC64LE.stackArg s0 2) (PPC64LE.stackArg s0 3).toNat
  have hw16 := (pre_ws h.pre).2.1
  refine WP.mono (arith_ok w2 i2 (pL := (PPC64LE.stackArg s0 1).toNat) (qL := (PPC64LE.stackArg s0 3).toNat)
    (by omega) (by rw [a2.r20]; exact ofNat_toNat64 _) (by rw [a2.r22]; exact ofNat_toNat64 _) p1 (by omega) (by omega) hP hQ)
    fun t3 ⟨w3, k3, ⟨X₁, X₂, V, hm, h₁, h₂⟩, h₃, h₄, r3⟩ => ?_
  have b3 : Base s0 t3 := b2.of_keep k3 (by decide) (by decide) r3.sp r3.lr r3.rd r3.wr (r3.gpr _ (by decide))
  rw [show seqs [VG.Impl.Rsa.PPC64LE.CrtValues.stores] = VG.Impl.Rsa.PPC64LE.CrtValues.stores from rfl]
  refine WP.mono (stores_ok b3 (ha.of_keep ((k1.trans k2).trans r3)) w3 (b := decide (maskOf (pIn s0) (qIn s0) X₁ X₂ V))
    (by rw [hm]; simp only [decide_eq_true_eq])) fun t ⟨ft, t3', vp, vq, vi, kt⟩ =>
      ⟨⟨⟨_, ft⟩, ?_⟩, ((((k1.trans k2).trans r3).trans kt)).mono⟩
  have hlen : ∀ (m : Mem) (p : Addr) (L : Nat), (Spec.Rsa.bytesAt m p L).length = L := fun _ _ _ => by
    simp [Spec.Rsa.bytesAt]
  show Spec.Rsa.writtenAll t.mem _ _ _
  rw [VG.Proof.Rsa.CrtValues.crtKey_masked (X₁ := X₁) (X₂ := X₂) (V := V) (R₂ := num t3.mem (cvB s0) (cvW s0) aDR2)
    (R₃ := num t3.mem (cvB s0) (cvW s0) aDR3) (X := num t3.mem (cvB s0) (cvW s0) 3)
    (by rw [hlen]; exact hv) (by rw [hlen, hlen]; exact p2) (by rw [hlen, hlen]; exact q2) h₁
    h₂ h₃ h₄]
  simp only [hlen]
  cases hb : decide (maskOf (pIn s0) (qIn s0) X₁ X₂ V)
  · rw [decide_eq_false_iff_not] at hb
    simp only [hb]
    rw [show decide (maskOf (pIn s0) (qIn s0) X₁ X₂ V) = false from decide_eq_false hb] at vp vq vi t3'
    refine ⟨by rw [t3']; rfl, fun o ho => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact bytes_zero fun c hc => by rw [vp c hc]; rfl
    · exact bytes_zero fun c hc => by rw [vq c hc]; rfl
    · exact bytes_zero fun c hc => by rw [vi c hc]; rfl
  · rw [decide_eq_true_iff] at hb
    simp only [hb, ↓reduceIte]
    rw [show decide (maskOf (pIn s0) (qIn s0) X₁ X₂ V) = true from decide_eq_true hb] at vp vq vi t3'
    refine ⟨by rw [t3']; rfl, ?_⟩
    simp only [List.map_cons, List.map_nil]
    rw [bytes_of (by omega_arith) vp, bytes_of (by omega_arith) vq, bytes_of (by omega_arith) vi]

/-- For a modulus that is not valid, `crtKey` is `none` and the results zeros. -/
theorem fail_post {s0 t : State} (hv : ¬ Spec.Rsa.modulusValid (nIn s0) (cvK s0) = true)
    (h3 : t.gpr .r3 = 0)
    (vp : ∀ c < (PPC64LE.stackArg s0 1).toNat, t.mem (off (s0.gpr .r3) c) = 0)
    (vq : ∀ c < (PPC64LE.stackArg s0 3).toNat, t.mem (off (s0.gpr .r5) c) = 0)
    (vi : ∀ c < (PPC64LE.stackArg s0 1).toNat, t.mem (off (s0.gpr .r7) c) = 0) : cvP.post s0 t := by
  have hlen : (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (cvK s0)).length = cvK s0 := by simp [Spec.Rsa.bytesAt]
  show Spec.Rsa.writtenAll t.mem _ _ _
  have hc : Spec.Rsa.crtKey (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (s0.gpr .r10).toNat)
      (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 0) (PPC64LE.stackArg s0 1).toNat)
      (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 2) (PPC64LE.stackArg s0 3).toNat)
      (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 4) (PPC64LE.stackArg s0 5).toNat) = none := by
    unfold Spec.Rsa.crtKey
    rw [hlen]
    simp only [nIn] at hv
    simp [hv]
  rw [hc]
  refine ⟨by rw [h3]; rfl, fun o ho => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact bytes_zero vp
  · exact bytes_zero vq
  · exact bytes_zero vi

/-- `restore`: the saved registers from the header. -/
theorem restore_ok {s0 t : State} {m : Mem} (h : Fr s0 m t) :
    WP isa (.block restore) t fun u => (u.gpr .r14 = s0.gpr .r14 ∧ u.gpr .r15 = s0.gpr .r15 ∧
      u.gpr .r16 = s0.gpr .r16 ∧ u.gpr .r17 = s0.gpr .r17 ∧ u.gpr .r18 = s0.gpr .r18 ∧
      u.gpr .r19 = s0.gpr .r19 ∧ u.gpr .r20 = s0.gpr .r20 ∧ u.gpr .r21 = s0.gpr .r21 ∧
      u.gpr .r22 = s0.gpr .r22 ∧ u.gpr .r23 = s0.gpr .r23 ∧ u.gpr .r24 = s0.gpr .r24 ∧
      u.gpr .r29 = s0.gpr .r29 ∧ u.gpr .r30 = s0.gpr .r30 ∧ u.gpr .r31 = s0.gpr .r31 ∧ u.mem = t.mem) ∧
      Keep [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r29, .r30, .r31] t u := by
  obtain ⟨hm, nw, hzs, -, -⟩ := pre_scr h.pre
  have hs : Scr t (cvB s0) (cvZ s0) := Scr.of_mem (by rw [h.wr]; exact hm) nw
  have e : ∀ i < 14, t.mem.readW (off (cvB s0) (8 * i)) 64 = s0.gpr (savedReg i) := fun i hi => by
    rw [h.readW (by omega_arith)]; exact h.hdr i hi
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide); have e4 := e 4 (by decide); have e5 := e 5 (by decide)
  have e6 := e 6 (by decide); have e7 := e 7 (by decide); have e8 := e 8 (by decide)
  have e9 := e 9 (by decide); have e10 := e 10 (by decide); have e11 := e 11 (by decide)
  have e12 := e 12 (by decide); have e13 := e 13 (by decide)
  simp only [savedReg, Nat.reduceMul] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
  refine WP.keep _ ?_ (by decide)
  prun [restore, h.r31, hs.ld (d := 0) (n := 8) (by omega_arith), hs.ld (d := 8) (n := 8) (by omega_arith),
    hs.ld (d := 16) (n := 8) (by omega_arith), hs.ld (d := 24) (n := 8) (by omega_arith),
    hs.ld (d := 32) (n := 8) (by omega_arith), hs.ld (d := 40) (n := 8) (by omega_arith),
    hs.ld (d := 48) (n := 8) (by omega_arith), hs.ld (d := 56) (n := 8) (by omega_arith),
    hs.ld (d := 64) (n := 8) (by omega_arith), hs.ld (d := 72) (n := 8) (by omega_arith),
    hs.ld (d := 80) (n := 8) (by omega_arith), hs.ld (d := 88) (n := 8) (by omega_arith),
    hs.ld (d := 96) (n := 8) (by omega_arith), hs.ld (d := 104) (n := 8) (by omega_arith),
    e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13]
  exact e0

theorem cv_correct [InvLaw] (s : State) (h : cvP.pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ cvP.post s t := by
  show WP isa code s fun t => abiPreserved s t ∧ cvP.post s t
  obtain ⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, dn, -, -, -, -, -, -, -, wn,
    -⟩ := id h
  obtain ⟨-, -, -, hk, hk'⟩ := pre_scr h
  unfold code
  refine WP.seq (WP.mono (entry_ok h) fun s1 ⟨b1, a1, k1⟩ => ?_)
  have hc : ∀ i < cvK s, (⟨s.gpr .r9, cvK s⟩ : Region).Contains (off (s.gpr .r9) i) 1 := fun i hi =>
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine WP.seq (WP.mono (check_ok (N := s.gpr .r9) (k := cvK s)
    (nb := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (cvK s))
    (by rw [k1.gpr _ (by decide)]; simp [off]) (by rw [k1.gpr _ (by decide)]; exact ofNat_toNat64 _) hk hk'
    (by simp [Spec.Rsa.bytesAt])
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [b1.rd, hrd]; simp), hc i hi⟩)
    (fun i hi => by rw [b1.frame _ (past_of_disjoint dn (hc i hi))]; simp [Spec.Rsa.bytesAt, off]))
    fun s2 ⟨hv, m2, k2⟩ => ?_)
  have b2 : Base s s2 := b1.of_regs k2 m2
  have a2 : Args s s2 := a1.of_keep k2
  refine WP.seq (WP.mono (Q := fun t => Done s t ∧ Keep allRegs s2 t)
    (WP.ite (s2.gpr .r0 == 0) (eval_zero s2 .r0) (fun hz => ?_) (fun hz => ?_)) fun t ⟨⟨⟨m, ft⟩, post⟩, kt⟩ => ?_)
  · have h0 : s2.gpr .r0 = 0 := by simpa using hz
    exact valid_ok b2 a2 (hv.mp h0)
  · refine WP.mono (fail_ok b2 a2) fun t ⟨ft, t3, vp, vq, vi, kt⟩ =>
      ⟨⟨⟨_, ft⟩, fail_post (fun hv' => ?_) t3 vp vq vi⟩, kt.mono⟩
    simp [hv.mpr hv'] at hz
  · refine WP.mono (restore_ok ft) fun u ⟨⟨u14, u15, u16, u17, u18, u19, u20, u21, u22, u23, u24, u29, u30, u31,
      um⟩, ku⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
    · have K := ((k1.trans k2).trans kt).trans ku
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;>
        first | exact K.gpr _ (by decide) | with_reducible assumption
    · rw [ku.sp, kt.sp, k2.sp, k1.sp]
    · rw [ku.lr, kt.lr, k2.lr, k1.lr]
    · have e3 : u.gpr .r3 = t.gpr .r3 := ku.gpr _ (by decide)
      show Spec.Rsa.writtenAll u.mem _ _ _
      rw [um, e3]
      exact post

end VG.Proof.Rsa.PPC64LE.CrtValues
