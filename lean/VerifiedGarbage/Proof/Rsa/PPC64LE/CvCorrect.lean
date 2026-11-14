module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvFail
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArith
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArithB
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
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.Rsa.CrtValuesMask
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcMath

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

/-- `crtKey_masked`, the remainders needed only when `p q = n`, which the
mask implies. -/
theorem crtKey_masked_pq {nb pb qb db : List Byte}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) nb.length = true)
    (hp : pb.length < nb.length) (hq : qb.length < nb.length) {X₁ X₂ V R₂ R₃ X : Nat}
    (h₁ : 0 < Spec.Rsa.os2ip pb → X₁ = Spec.Rsa.os2ip nb / Spec.Rsa.os2ip pb ∧
      X₂ = Spec.Rsa.os2ip nb % Spec.Rsa.os2ip pb)
    (h₂ : 1 < 2 * (Spec.Rsa.os2ip pb / 2) + 1 → V = Nat.gcd (Spec.Rsa.os2ip qb) (2 * (Spec.Rsa.os2ip pb / 2) + 1) ∧
      ((2 * (Spec.Rsa.os2ip pb / 2) + 1 : Nat) : Int) ∣ (X : Int) * Spec.Rsa.os2ip qb - V ∧
        X < 2 * (Spec.Rsa.os2ip pb / 2) + 1)
    (h₃ : 0 < 2 * (Spec.Rsa.os2ip pb / 2) → Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb →
      R₂ = Spec.Rsa.os2ip db % (2 * (Spec.Rsa.os2ip pb / 2)))
    (h₄ : 0 < 2 * (Spec.Rsa.os2ip qb / 2) → Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb →
      R₃ = Spec.Rsa.os2ip db % (2 * (Spec.Rsa.os2ip qb / 2))) :
    Spec.Rsa.crtKey nb pb qb db = if maskOf (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) X₁ X₂ V then
      some (Spec.Rsa.i2osp (R₂ % 2 ^ (8 * pb.length)) pb.length,
        Spec.Rsa.i2osp (R₃ % 2 ^ (8 * qb.length)) qb.length,
        Spec.Rsa.i2osp (X % 2 ^ (8 * pb.length)) pb.length) else none := by
  by_cases hm : maskOf (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) X₁ X₂ V = true
  · have hm' := hm
    simp only [maskOf, decide_eq_true_eq] at hm'
    obtain ⟨podd, e1, e2, -⟩ := hm'
    obtain ⟨f1, f2⟩ := h₁ (by omega_using [podd])
    have pq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb := by
      have := Nat.div_add_mod (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      rw [← f1, ← f2, e1, e2, Nat.add_zero] at this; exact this
    exact VG.Proof.Rsa.CrtValues.crtKey_masked hv hp hq h₁ h₂ (fun h => h₃ h pq) (fun h => h₄ h pq)
  · rw [VG.Proof.Rsa.CrtValues.crtKey_masked (R₂ := Spec.Rsa.os2ip db % (2 * (Spec.Rsa.os2ip pb / 2)))
      (R₃ := Spec.Rsa.os2ip db % (2 * (Spec.Rsa.os2ip qb / 2))) hv hp hq h₁ h₂ (fun _ => rfl) (fun _ => rfl),
      ite_eq_right hm, ite_eq_right hm]

/-- The valid branch up to the inverse and its checks (`partA`, `partB`): the
arguments, the base and the working space kept. -/
theorem preAB_ok [InvLaw] {s0 s : State} (h : Base s0 s) (ha : Args s0 s) :
    WP isa (seqs ([VG.Impl.Rsa.PPC64LE.CrtValues.setup, VG.Impl.Rsa.PPC64LE.CrtValues.loads] ++ (partA ++ partB))) s
      fun t => Base s0 t ∧ Args s0 t ∧ Ws t (cvB s0) (cvZ s0) (cvW s0) nArr := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, p1, p2, q1, q2, -, -, -, -, -, -⟩ := h.pre
  obtain ⟨-, -, hkw⟩ := pre_ws h.pre |>.2
  have hk2 : (s0.gpr .r10).toNat ≤ 4 * cvW s0 := hkw
  rw [List.cons_append, wp_seqs_cons (by simp)]
  refine WP.mono (setup_ok h ha.r18) fun t1 ⟨b1, w1, z1, k1⟩ => ?_
  rw [List.cons_append, List.nil_append, wp_seqs_cons (by simp [partA])]
  refine WP.mono (loads_ok b1 (ha.of_keep k1) w1 z1) fun t2 ⟨b2, w2, i2, k2⟩ => ?_
  have a2 := ha.of_keep (k1.trans k2)
  have hP := os2ip_bytes_lt s0.mem (PPC64LE.stackArg s0 0) (PPC64LE.stackArg s0 1).toNat
  have hQ := os2ip_bytes_lt s0.mem (PPC64LE.stackArg s0 2) (PPC64LE.stackArg s0 3).toNat
  have hw16 := (pre_ws h.pre).2.1
  refine WP.mono (arithAB_ok w2 i2 (hwe := by simp only [cvW]; omega_using []) (pL := (PPC64LE.stackArg s0 1).toNat)
    (qL := (PPC64LE.stackArg s0 3).toNat) (by omega_using [hw16]) (by rw [a2.r20]; exact ofNat_toNat64 _)
    (by rw [a2.r22]; exact ofNat_toNat64 _) p1 (by omega_using [p2, hk2]) (by omega_using [q2, hk2]) hP hQ) fun t3 ⟨w3, k3, r3⟩ => ?_
  have b3 : Base s0 t3 := b2.of_keep k3 (by decide) (by decide) r3.sp r3.lr r3.rd r3.wr (r3.gpr _ (by decide))
  exact ⟨b3, ha.of_keep ((k1.trans k2).trans r3), w3⟩

/-- `valid` up to the stores: the base and the arguments kept, and the stores
then end it. -/
theorem valid_pre_ok [InvLaw] {s0 s : State} (h : Base s0 s) (ha : Args s0 s)
    (hv : Spec.Rsa.modulusValid (nIn s0) (cvK s0) = true) :
    WP isa (seqs [VG.Impl.Rsa.PPC64LE.CrtValues.setup, VG.Impl.Rsa.PPC64LE.CrtValues.loads,
      VG.Impl.Rsa.PPC64LE.CrtValues.arith]) s fun t3 => (Base s0 t3 ∧ Args s0 t3 ∧ Ws t3 (cvB s0) (cvZ s0) (cvW s0) nArr) ∧
      WP isa VG.Impl.Rsa.PPC64LE.CrtValues.stores t3 fun t => Done s0 t ∧ Keep allRegs s t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, p1, p2, q1, q2, -, -, -, -, -, -⟩ := h.pre
  obtain ⟨-, -, hkw⟩ := pre_ws h.pre |>.2
  have hk2 : (s0.gpr .r10).toNat ≤ 4 * cvW s0 := hkw
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setup_ok h ha.r18) fun t1 ⟨b1, w1, z1, k1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok b1 (ha.of_keep k1) w1 z1) fun t2 ⟨b2, w2, i2, k2⟩ => ?_
  rw [show ∀ x : Prog isa, seqs [x] = x from fun _ => rfl]
  have a2 := ha.of_keep (k1.trans k2)
  have hP := os2ip_bytes_lt s0.mem (PPC64LE.stackArg s0 0) (PPC64LE.stackArg s0 1).toNat
  have hQ := os2ip_bytes_lt s0.mem (PPC64LE.stackArg s0 2) (PPC64LE.stackArg s0 3).toNat
  have hw16 := (pre_ws h.pre).2.1
  have hQN : qIn s0 < nIn s0 := by
    have hn : 256 ^ (cvK s0 - 1) ≤ nIn s0 := by
      simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
      exact hv.2
    refine Nat.lt_of_lt_of_le hQ (Nat.le_trans ?_ hn)
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by have : cvK s0 = (s0.gpr .r10).toNat := rfl; omega_using [q2, this])
  refine WP.mono (arith_ok w2 i2 (hwe := by simp only [cvW]; omega_using []) (pL := (PPC64LE.stackArg s0 1).toNat) (qL := (PPC64LE.stackArg s0 3).toNat)
    (by omega_using [hw16]) (by rw [a2.r20]; exact ofNat_toNat64 _) (by rw [a2.r22]; exact ofNat_toNat64 _) p1 q1 (by omega_using [p2, hk2]) (by omega_using [q2, hk2]) hP hQ hQN)
    fun t3 ⟨w3, k3, ⟨X₁, X₂, V, hm, h₁, h₂⟩, h₃, h₄, r3⟩ => ?_
  have b3 : Base s0 t3 := b2.of_keep k3 (by decide) (by decide) r3.sp r3.lr r3.rd r3.wr (r3.gpr _ (by decide))
  refine ⟨⟨b3, ha.of_keep ((k1.trans k2).trans r3), w3⟩, ?_⟩
  refine WP.mono (stores_ok b3 (ha.of_keep ((k1.trans k2).trans r3)) w3 (b := decide (maskOf (pIn s0) (qIn s0) X₁ X₂ V))
    (by rw [hm]; simp only [decide_eq_true_eq])) fun t ⟨ft, t3', vp, vq, vi, kt⟩ =>
      ⟨⟨⟨_, ft⟩, ?_⟩, ((((k1.trans k2).trans r3).trans kt)).mono⟩
  have hlen : ∀ (m : Mem) (p : Addr) (L : Nat), (Spec.Rsa.bytesAt m p L).length = L := fun _ _ _ => by
    simp [Spec.Rsa.bytesAt]
  show Spec.Rsa.writtenAll t.mem _ _ _
  have hn : 256 ^ (cvK s0 - 1) ≤ nIn s0 := by
    simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
    exact hv.2
  have h₃' : 0 < 2 * (pIn s0 / 2) → pIn s0 * qIn s0 = nIn s0 →
      num t3.mem (cvB s0) (cvW s0) aDR2 = dIn s0 % (2 * (pIn s0 / 2)) := fun h0 pq => h₃ h0 fun hs => KeyCheck.shape_bound hs (by simp only [cvW]; omega_using []) pq hn hQ
  have h₄' : 0 < 2 * (qIn s0 / 2) → pIn s0 * qIn s0 = nIn s0 →
      num t3.mem (cvB s0) (cvW s0) aDR3 = dIn s0 % (2 * (qIn s0 / 2)) := fun h0 pq => h₄ h0 fun hs => KeyCheck.shape_bound (p := qIn s0) (q := pIn s0)
      ⟨by have := hs.1; have := hs.2.2.1; omega_arith, by have := hs.2.1; have := hs.2.2.1; omega_arith, hs.2.2.1.symm,
        by have := hs.2.2.2; have := hs.2.2.1; omega_arith⟩ (by simp only [cvW]; omega_using []) (by rw [Nat.mul_comm]; exact pq) hn hP
  by_cases hk : maskOf (pIn s0) (qIn s0) X₁ X₂ V = true
  · -- Under the mask `p q = n`, so for a balanced key `p`'s top word is not zero.
    have h₂' : 1 < modOf (pIn s0) → V = Nat.gcd (qIn s0) (modOf (pIn s0)) ∧
        ((modOf (pIn s0) : Nat) : Int) ∣ (num t3.mem (cvB s0) (cvW s0) 3 : Int) * qIn s0 - V ∧
        num t3.mem (cvB s0) (cvW s0) 3 < modOf (pIn s0) := fun h1 => by
      obtain ⟨g, X, d, l, e⟩ := h₂ h1
      have hk' := hk
      simp only [maskOf, decide_eq_true_eq] at hk'
      obtain ⟨podd, e1, e2, -⟩ := hk'
      obtain ⟨f1, f2⟩ := h₁ (by omega_using [podd])
      have pq : pIn s0 * qIn s0 = nIn s0 := by
        have := Nat.div_add_mod (nIn s0) (pIn s0)
        rw [← f1, ← f2, e1, e2, Nat.add_zero] at this; exact this
      rw [e fun hs => by have := KeyCheck.shape_bound hs (by simp only [cvW]; omega_using []) pq hn hQ; unfold modOf; omega_using [this]]
      exact ⟨g, d, l⟩
    rw [crtKey_masked_pq (X₁ := X₁) (X₂ := X₂) (V := V) (R₂ := num t3.mem (cvB s0) (cvW s0) aDR2)
      (R₃ := num t3.mem (cvB s0) (cvW s0) aDR3) (X := num t3.mem (cvB s0) (cvW s0) 3)
      (by rw [hlen]; exact hv) (by rw [hlen, hlen]; exact p2) (by rw [hlen, hlen]; exact q2) h₁ h₂' h₃' h₄']
    simp only [hlen, hk, ↓reduceIte]
    rw [show decide (maskOf (pIn s0) (qIn s0) X₁ X₂ V) = true from decide_eq_true hk] at vp vq vi t3'
    refine ⟨by rw [t3']; rfl, ?_⟩
    simp only [List.map_cons, List.map_nil]
    rw [bytes_of (by omega_arith) vp, bytes_of (by omega_arith) vq, bytes_of (by omega_arith) vi]
  · -- Else the outputs are zeros, whatever the inverse.
    obtain ⟨X', h₂'⟩ : ∃ X' : Nat, 1 < modOf (pIn s0) → V = Nat.gcd (qIn s0) (modOf (pIn s0)) ∧
        ((modOf (pIn s0) : Nat) : Int) ∣ (X' : Int) * qIn s0 - V ∧ X' < modOf (pIn s0) := by
      by_cases h1 : 1 < modOf (pIn s0)
      · obtain ⟨g, X, d, l, -⟩ := h₂ h1; exact ⟨X, fun _ => ⟨g, d, l⟩⟩
      · exact ⟨0, fun h => absurd h h1⟩
    rw [crtKey_masked_pq (X₁ := X₁) (X₂ := X₂) (V := V) (R₂ := num t3.mem (cvB s0) (cvW s0) aDR2)
      (R₃ := num t3.mem (cvB s0) (cvW s0) aDR3) (X := X')
      (by rw [hlen]; exact hv) (by rw [hlen, hlen]; exact p2) (by rw [hlen, hlen]; exact q2) h₁ h₂' h₃' h₄']
    simp only [hlen]
    have hb : ¬ maskOf (pIn s0) (qIn s0) X₁ X₂ V = true := hk
    simp only [hb]
    rw [show decide (maskOf (pIn s0) (qIn s0) X₁ X₂ V) = false from decide_eq_false hb] at vp vq vi t3'
    refine ⟨by rw [t3']; rfl, fun o ho => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact bytes_zero fun c hc => by rw [vp c hc]; rfl
    · exact bytes_zero fun c hc => by rw [vq c hc]; rfl
    · exact bytes_zero fun c hc => by rw [vi c hc]; rfl

/-- For a modulus that is not valid, `crtKey` is `none` and the results zeros. -/
theorem valid_ok [InvLaw] {s0 s : State} (h : Base s0 s) (ha : Args s0 s)
    (hv : Spec.Rsa.modulusValid (nIn s0) (cvK s0) = true) :
    WP isa valid s fun t => Done s0 t ∧ Keep allRegs s t := by
  rw [valid, show [VG.Impl.Rsa.PPC64LE.CrtValues.setup, VG.Impl.Rsa.PPC64LE.CrtValues.loads,
      VG.Impl.Rsa.PPC64LE.CrtValues.arith, VG.Impl.Rsa.PPC64LE.CrtValues.stores] =
    [VG.Impl.Rsa.PPC64LE.CrtValues.setup, VG.Impl.Rsa.PPC64LE.CrtValues.loads,
      VG.Impl.Rsa.PPC64LE.CrtValues.arith] ++ [VG.Impl.Rsa.PPC64LE.CrtValues.stores] from rfl,
    wp_seqs_append (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)]
  exact WP.mono (valid_pre_ok h ha hv) fun _ h => h.2

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
