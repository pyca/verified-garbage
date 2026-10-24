module

import VerifiedGarbage.Proof.Rsa.PPC64LE.CvMid
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvArithA
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs

/-!
# `vg_rsa_crt_values` on PPC64LE: the inputs read

`ldIn_ok`: `load j` from a readable source apart from the working space.
`loads_ok`: `n`, `p`, `q` and `d` read into their arrays, from the arrays
`setup` zeroed: the arrays `arith` starts from (`ArInit`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.CrtValues (load loads aQ aP aDQ aD nArr)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- A number whose digits are zero. -/
theorem val32_of_zero {m : Mem} {B : Addr} : ∀ {d n : Nat}, (∀ i < n, w32 m B (d + 4 * i) = 0) →
    val32 m B d n = 0
  | _, 0, _ => rfl
  | d, n + 1, h => by
    have h0 := h 0 (by omega)
    rw [Nat.mul_zero, Nat.add_zero] at h0
    rw [val32, h0, val32_of_zero fun i hi => by
      rw [show d + 4 + 4 * i = d + 4 * (i + 1) by omega]; exact h (i + 1) (by omega)]

/-- `load j` from `L` bytes at `P`, readable and apart from the working space. -/
theorem ldIn_ok {s0 s : State} (h : Base s0 s) (hw : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr) {j : Nat}
    (hj : j < nArr) {P : Addr} {L : Nat} (h6 : s.gpr .r6 = P) (h8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (hL : 1 ≤ L) (hLw : L ≤ 4 * cvW s0) (hrd : (⟨P, L⟩ : Region) ∈ s0.rd)
    (hd : (⟨P, L⟩ : Region).Disjoint ⟨cvB s0, cvZ s0⟩) (hPw : P.toNat + L ≤ 2 ^ 64)
    (hz : num s.mem (cvB s0) (cvW s0) j = 0) :
    WP isa (load j) s fun t => Base s0 t ∧ Ws t (cvB s0) (cvZ s0) (cvW s0) nArr ∧
      num t.mem (cvB s0) (cvW s0) j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem P L) ∧
      Outside (cvB s0) (arr (cvW s0) j) (4 * cvW s0) s.mem t.mem ∧ Keep [.r0, .r5, .r6, .r8] s t := by
  have hc : ∀ i < L, (⟨P, L⟩ : Region).Contains (off P i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  have hv : val32 s.mem (cvB s0) (arr (cvW s0) j) (cvW s0) = 0 := hz
  refine WP.mono (load_ok hw hj (by decide) h6 h8 hL hLw
    (fun i hi => ⟨_, List.mem_append_left _ (h.rd ▸ hrd), hc i hi⟩)
    (fun i hi x hx e => by have := past_of_disjoint hd (hc i hi); rw [e] at this; omega)
    (fun p hp => by rw [← off_add]; exact byte_zero_of_val32 hv hp))
    fun t ⟨ht, k, v, kt, o⟩ => ⟨Base.of_keep h k (by simpa using hj) (by simp) kt.sp kt.lr kt.rd kt.wr
      (kt.gpr _ (by decide)), ht, ?_, o, kt⟩
  rw [v]
  congr 1
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h.frame _ (past_of_disjoint hd (hc i (List.mem_range.mp hi)))

/-- Two moves. -/
theorem mv2_ok {s : State} {d₁ d₂ a b : Reg} (ha : a ≠ .r0) (hb : b ≠ .r0) (hb1 : b ≠ d₁) (hd : d₂ ≠ d₁) :
    WP isa (.block [.addi d₁ a 0, .addi d₂ b 0]) s fun u =>
      (u.gpr d₁ = s.gpr a ∧ u.gpr d₂ = s.gpr b ∧ u.mem = s.mem) ∧ Keep [d₁, d₂] s u := by
  refine WP.of_runBlock ⟨(s.write d₁ (s.gpr a + BitVec.ofNat 64 0)).write d₂
    ((s.write d₁ (s.gpr a + BitVec.ofNat 64 0)).gpr b + BitVec.ofNat 64 0), ?_, ?_⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi ha (show 0 < 2 ^ 15 by decide),
      exec_addi hb (show 0 < 2 ^ 15 by decide)]
  · refine ⟨⟨?_, ?_, rfl⟩, ((Keep.write _ _ _).trans (Keep.write _ _ _)).mono fun r h => by simpa using h⟩
    · simp [State.write, Ne.symm hd]
    · simp [State.write, hb1]

/-- `n`'s, `p`'s, `q`'s and `d`'s bytes, from the initial state. -/
abbrev nIn (s0 : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (cvK s0))
abbrev pIn (s0 : State) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 0) (PPC64LE.stackArg s0 1).toNat)
abbrev qIn (s0 : State) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 2) (PPC64LE.stackArg s0 3).toNat)
abbrev dIn (s0 : State) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 4) (PPC64LE.stackArg s0 5).toNat)

theorem ofNat_toNat64 (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A number a load into another array keeps. -/
theorem num_out {m m' : Mem} {B : Addr} {w a b : Nat} (o : Outside B (arr w a) (4 * w) m m') (hab : a ≠ b)
    (fb : arr w b + S w ≤ 2 ^ 64) : num m' B w b = num m B w b := by
  have hS : S w = 4 * (w + 2) := rfl
  have := VG.Proof.Rsa.KeyWorkspace.arr_disj (w := w) hab
  exact o.val32 (by omega) (by omega)

/-- An array's extra digit, which a load keeps. -/
theorem top_out {m m' : Mem} {B : Addr} {w a b : Nat} (o : Outside B (arr w a) (4 * w) m m')
    (fb : arr w b + S w ≤ 2 ^ 64) : w32 m' B (arr w b + 4 * w) = w32 m B (arr w b + 4 * w) := by
  have hS : S w = 4 * (w + 2) := rfl
  by_cases hab : a = b
  · subst hab; exact o.w32 (by omega) (by omega)
  · have := VG.Proof.Rsa.KeyWorkspace.arr_disj (w := w) hab
    exact o.w32 (by omega) (by omega)

/-- `loads`: `n`, `p`, `q` and `d` into their arrays. -/
theorem loads_ok {s0 s : State} (h : Base s0 s) (ha : Args s0 s) (hw : Ws s (cvB s0) (cvZ s0) (cvW s0) nArr)
    (hz : ∀ j < nArr, ∀ i < cvW s0 + 2, w32 s.mem (cvB s0) (arr (cvW s0) j + 4 * i) = 0) :
    WP isa loads s fun t => Base s0 t ∧ Ws t (cvB s0) (cvZ s0) (cvW s0) nArr ∧
      ArInit t.mem (cvB s0) (cvW s0) (nIn s0) (pIn s0) (qIn s0) (dIn s0) ∧ Keep [.r0, .r5, .r6, .r8] s t := by
  obtain ⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, dn, dp, dq, dd, -, -, -,
    -, wn, wp, wq, wd, -, -, p1, p2, q1, q2, -, -, -, d1, d2, -⟩ := h.pre
  obtain ⟨fits, hw16, hw256, hkw⟩ := pre_ws h.pre
  obtain ⟨-, nw, hzs, hk, -⟩ := pre_scr h.pre
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  have hs : Scr s (cvB s0) (cvZ s0) := hw.scr
  have fit : ∀ j < nArr, arr (cvW s0) j + S (cvW s0) ≤ 2 ^ 64 := fun j hj => hw.fit64 hj
  have zn : ∀ j < nArr, num s.mem (cvB s0) (cvW s0) j = 0 := fun j hj =>
    val32_of_zero fun i hi => hz j hj i (by omega)
  have hk1 : 64 ≤ (s0.gpr .r10).toNat := hk
  have hk2 : (s0.gpr .r10).toNat ≤ 4 * cvW s0 := hkw
  rw [loads, wp_seqs_cons (List.cons_ne_nil _ _)]
  -- `n`.
  refine WP.mono (mv2_ok (s := s) (d₁ := .r6) (d₂ := .r8) (a := .r17) (b := .r18) (by decide) (by decide)
    (by decide) (by decide)) fun u0 ⟨⟨a6, a8, am⟩, ak⟩ => ?_
  rw [ha.r17] at a6
  rw [ha.r18] at a8
  have hb0 := h.of_regs ak am
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ldIn_ok hb0 (hw.of_keep ak) (j := aDQ) (L := (s0.gpr .r10).toNat) (by decide) a6 (by rw [a8]; exact ofNat_toNat64 _)
    (by omega) (by omega) (by rw [hrd]; simp) dn wn (by rw [am]; exact zn _ (by decide)))
    fun t1 ⟨b1, w1, v1, o1, k1⟩ => ?_
  -- `p`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mv2_ok (s := t1) (d₁ := .r6) (d₂ := .r8) (a := .r19) (b := .r20) (by decide) (by decide)
    (by decide) (by decide)) fun u2 ⟨⟨c6, c8, m2⟩, k2⟩ => ?_
  have a1 := ha.of_keep (ak.trans k1)
  rw [a1.r19] at c6
  rw [a1.r20] at c8
  have b2 := b1.of_regs k2 m2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ldIn_ok b2 (w1.of_keep k2) (j := aP) (L := (PPC64LE.stackArg s0 1).toNat) (by decide) c6 (by rw [c8]; exact ofNat_toNat64 _)
    p1 (by omega) (by rw [hrd]; simp) dp wp ?_) fun t3 ⟨b3, w3, v3, o3, k3⟩ => ?_
  · rw [m2, num_out o1 (by decide) (fit _ (by decide)), am]; exact zn _ (by decide)
  -- `q`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mv2_ok (s := t3) (d₁ := .r6) (d₂ := .r8) (a := .r21) (b := .r22) (by decide) (by decide)
    (by decide) (by decide)) fun u4 ⟨⟨c6', c8', m4⟩, k4⟩ => ?_
  have a3 := a1.of_keep ((k2.trans k3))
  rw [a3.r21] at c6'
  rw [a3.r22] at c8'
  have b4 := b3.of_regs k4 m4
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ldIn_ok b4 (w3.of_keep k4) (j := aQ) (L := (PPC64LE.stackArg s0 3).toNat) (by decide) c6' (by rw [c8']; exact ofNat_toNat64 _)
    q1 (by omega) (by rw [hrd]; simp) dq wq ?_) fun t5 ⟨b5, w5, v5, o5, k5⟩ => ?_
  · rw [m4, num_out o3 (by decide) (fit _ (by decide)), m2, num_out o1 (by decide) (fit _ (by decide)), am]
    exact zn _ (by decide)
  -- `d`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mv2_ok (s := t5) (d₁ := .r6) (d₂ := .r8) (a := .r23) (b := .r24) (by decide) (by decide)
    (by decide) (by decide)) fun u6 ⟨⟨c6'', c8'', m6⟩, k6⟩ => ?_
  have a5 := a3.of_keep ((k4.trans k5))
  rw [a5.r23] at c6''
  rw [a5.r24] at c8''
  have b6 := b5.of_regs k6 m6
  rw [show seqs [load aD] = load aD from rfl]
  refine WP.mono (ldIn_ok b6 (w5.of_keep k6) (j := aD) (L := (PPC64LE.stackArg s0 5).toNat) (by decide) c6'' (by rw [c8'']; exact ofNat_toNat64 _)
    d1 (by omega) (by rw [hrd]; simp) dd wd ?_) fun t ⟨b7, w7, v7, o7, k7⟩ => ?_
  · rw [m6, num_out o5 (by decide) (fit _ (by decide)), m4, num_out o3 (by decide) (fit _ (by decide)), m2,
      num_out o1 (by decide) (fit _ (by decide)), am]
    exact zn _ (by decide)
  have kk : Keep [.r0, .r5, .r6, .r8] s t :=
    ((((((ak.trans k1).trans k2).trans k3).trans k4).trans k5).trans (k6.trans k7)).mono
  have F : ∀ j < nArr, arr (cvW s0) j + S (cvW s0) ≤ 2 ^ 64 := fit
  refine ⟨b7, w7, ⟨?_, ?_, ?_, v7, fun j hj a b c d => ?_, fun j hj => ?_⟩, kk⟩
  · rw [num_out o7 (by decide) (F _ (by decide)), m6, num_out o5 (by decide) (F _ (by decide)), m4,
      num_out o3 (by decide) (F _ (by decide)), m2, v1]
  · rw [num_out o7 (by decide) (F _ (by decide)), m6, num_out o5 (by decide) (F _ (by decide)), m4, v3]
  · rw [num_out o7 (by decide) (F _ (by decide)), m6, v5]
  · rw [num_out o7 (Ne.symm d) (F _ hj), m6, num_out o5 (Ne.symm c) (F _ hj), m4,
      num_out o3 (Ne.symm b) (F _ hj), m2, num_out o1 (Ne.symm a) (F _ hj), am]
    exact zn j hj
  · rw [top_out o7 (F _ hj), m6, top_out o5 (F _ hj), m4, top_out o3 (F _ hj), m2, top_out o1 (F _ hj), am]
    exact hz j hj _ (by omega)

end VG.Proof.Rsa.PPC64LE.CrtValues
