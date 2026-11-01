module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbBatch
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import VerifiedGarbage.Proof.Rsa.PPC64LE.IbEnd
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The batched inverse on PPC64LE: the start

`init_ok`: from `x` in array 0 and the odd `m` in array 8, both below
`2^(32 n)`, the start of the inversion modulo `p = vmod m` (`m`, or 3 for
`m = 1`): `f = p`, `g = oddInput p x`, `a = 0`, `b = 1`, `d = 1`, with
`-p⁻¹ mod 2^32` in the window and `3 (n + 1)` batches to run.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop seqs subBody selBody copyBody eqBody)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num arr_disj)
open VG.Proof.Rsa.PPC64LE.Loops (copyLoop_ok zeroLoop_ok eqLoop_ok)
open VG.Proof.Rsa.Divstep (oddInput)

/-- The modulus of the batches: `m`, or 3 for `m = 1`. -/
def vmod (m : Nat) : Nat := if m = 1 then 3 else m

/-- `k` digits of a number below `2^(32 k)` stored in `w ≥ k` digits. -/
theorem val_low {m : Mem} {B : Addr} {d w k v : Nat} (hk : k ≤ w) (hv : val32 m B d w = v)
    (hvk : v < 2 ^ (32 * k)) : val32 m B d k = v := by
  have e := val32_append m B d k (w - k)
  rw [show k + (w - k) = w by omega, hv] at e
  have := val32_lt m B d k
  rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * k) (w - k)) with z | z
  · rw [z, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have : 2 ^ (32 * k) ≤ 2 ^ (32 * k) * val32 m B (d + 4 * k) (w - k) := Nat.le_mul_of_pos_right _ z
    omega

/-- `init`, its first part: `[2] = m` with a zero digit `n`, `r10 = n`. -/
theorem init1_ok {s : State} {B : Addr} {Z w N n m : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256)
    (hw : 10 ≤ w) (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w)
    (hm : val32 s.mem B (arr w aMin) n = m) :
    WP isa (.seq (.block (ptr .r5 aMz ++ ptr .r6 aMin ++ [.addi .r10 .r11 0] ++ cntN)) (countLoop .r8 copyBody)) s
      fun t => Ctx t B Z w N n 0 ∧ KeyWorkspace.Keep B w [aMz] [] s.mem t.mem ∧
        val32 t.mem B (arr w aMz) n = m ∧ t.gpr .r11 = s.gpr .r11 ∧
        Outside B (arr w aMz) (4 * n) s.mem t.mem ∧ Keep (.r10 :: kRegs) s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have fM := h.arr_fit (j := aMz) (by unfold aMz; omega)
  have fI := h.arr_fit (j := aMin) (by unfold aMin; omega)
  rw [WP.seq_iff, List.append_assoc, List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) (by decide) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r5 _)) (by decide) (by decide) (by decide) (by decide) ?_
  refine WP.mono (WP.keep [.r8, .r10] (Q := fun u => u.gpr .r10 = BitVec.ofNat 64 n ∧ u.gpr .r8 = BitVec.ofNat 64 n ∧
    u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨u10, u8, um⟩, ku⟩ => ?_
  · have e := cnt_eq (n := n) (c := 0) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at e
    prun [cntN, h11, BitVec.add_zero, e]
  have k1 : Keep (.r10 :: kRegs) s u := (((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).trans ku).mono (by decide)
  have h1 : Ctx u B Z w N n 0 := ⟨h.of_keep k1, by rw [u10]; simp, hn1, hnw, hN15, by decide, hw⟩
  refine WP.mono (copyLoop_ok (dO := arr w aMz) (dA := arr w aMin) h1.ws.scr
    (by rw [ku.gpr _ (by decide)]; simp [gpr_write]) (by rw [ku.gpr _ (by decide)]; simp [gpr_write]) u8 hn1
    (by omega) (by omega) (by omega) (ahead_k (by decide) (by omega))) fun t ⟨v, out, kt⟩ => ?_
  rw [um] at v out
  have k : Keep (.r10 :: kRegs) s t := k1.trans' (kt.mono (by decide))
  refine ⟨h1.of_keep (kt.mono (by decide)), KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega) (by simp), by rw [v, hm],
    (((((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).trans ku).trans kt).gpr _ (by decide)), out, k⟩

/-- `setTop aMz 0`: digit `n` of `[2]` := 0. -/
theorem setTop_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) (hN : N ≤ 256) :
    WP isa (.block (setTop aMz 0)) s fun t => (t.mem = s.mem.writeW (off B (arr w aMz + 4 * n)) (0 : BitVec 32) ∧
      t.gpr .r0 = 0) ∧ Keep [.r0, .r6, .r8] s t := by
  have fj := h.ws.arr_fit (j := aMz) (by have := h.room; unfold aMz; omega)
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  refine WP.keep _ ?_ (by decide)
  prun [setTop, ptr, cntN, exec_li (imm := aMz) (by decide),
    exec_addi (n := .r6) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, h.ptr aMz, h.cnt, shl2,
    h.ws.scr.st (show arr w aMz + 4 * n + 4 ≤ Z by omega)]
  exact ⟨rfl, rfl⟩

/-- The virtualization's mask: 2 where `r9` is zero. -/
theorem virt_mask (r : BitVec 64) (hr : r.toNat < 2 ^ 32) :
    (((0#64 - r) >>> 63 ^^^ 1#64) <<< 1) = if r = 0#64 then 2#64 else 0#64 := by
  split
  · next e => subst e; decide
  · next e =>
    have : r.toNat ≠ 0 := fun h => e (BitVec.eq_of_toNat_eq h)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_xor, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have h1 : (2 ^ 64 - r.toNat + (0#64).toNat) % 2 ^ 64 / 2 ^ 63 = 1 := by
      rw [show (0#64).toNat = 0 from rfl]; omega
    rw [h1]
    rfl

/-- The new low digit of the modulus: `d₀ | 2` where it is `1` (the modulus 1). -/
theorem virt_digit (d : BitVec 32) (b : Bool) :
    ((d.setWidth 64 ||| (if b then 2#64 else 0#64)).setWidth 32).toNat =
      if b ∧ d.toNat = 1 then 3 else if b then (d.toNat ||| 2) else d.toNat := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, false_and, BitVec.or_zero]
    rw [BitVec.toNat_setWidth, toNat_ext32]; exact Nat.mod_eq_of_lt d.isLt
  · simp only [↓reduceIte, true_and]
    rw [BitVec.toNat_setWidth, BitVec.toNat_or, toNat_ext32, show (2#64).toNat = 2 from rfl]
    have : d.toNat ||| 2 < 2 ^ 32 := Nat.or_lt_two_pow d.isLt (by decide)
    split
    · next e => rw [e]; rfl
    · exact Nat.mod_eq_of_lt this

/-- `m` of `k + 1` digits, its top digit replaced by zero. -/
theorem val_top0 {mm : Mem} {B : Addr} {d k : Nat} (h : d + 4 * k + 4 ≤ 2 ^ 64) :
    val32 (mm.writeW (off B (d + 4 * k)) (0 : BitVec 32)) B d (k + 1) = val32 mm B d k := by
  rw [val32_write_top _ _ _ _ _ h]; simp

/-- Bit 0 of a digit, inverted. -/
theorem even_bit (x : BitVec 32) :
    (((x.setWidth 64 <<< 63) >>> 63) ^^^ BitVec.ofNat 64 1).toNat = (if x.toNat % 2 = 0 then 1 else 0) := by
  rw [low_bit, BitVec.toNat_xor, BitVec.toNat_and, toNat_ext32, show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.and_one_is_mod, BitVec.toNat_ofNat]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with e | e <;> rw [e] <;> rfl

/-- `init`: the start of the inversion modulo `vmod m`. -/
theorem init_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256)
    (hw : 10 ≤ w) (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) {x m : Nat}
    (hx : val32 s.mem B (arr w aX) n = x) (hxn : x < 2 ^ (32 * n))
    (hm : val32 s.mem B (arr w aMin) n = m) (hmn : m < 2 ^ (32 * n)) (hodd : m % 2 = 1) :
    WP isa init s fun t => Ctx t B Z w N n (3 * (n + 1)) ∧
      (∃ iv, (vmod m * iv + 1) % 2 ^ 32 = 0 ∧
        StateAt t B w n (vmod m) iv (Divstep.W32.invRun 30 (vmod m) iv (oddInput (vmod m) x) 0)) ∧
      KeyWorkspace.Keep B w [aMz, aB, aW, aF, aG, aA] [] s.mem t.mem ∧ Keep (.r10 :: kRegs) s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have hnw' := h.nowrap
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.arr_fit hj
  have nM : aMz < N := by unfold aMz; omega
  have nB : aB < N := by unfold aB; omega
  have nW : aW < N := by unfold aW; omega
  have nF : aF < N := by unfold aF; omega
  have nG : aG < N := by unfold aG; omega
  have nA : aA < N := by unfold aA; omega
  have nX : aX < N := by unfold aX; omega
  have nI : aMin < N := by unfold aMin; omega
  have fM := fitZ _ nM
  have fB := fitZ _ nB
  have fW := fitZ _ nW
  have hk1 : n + 1 ≤ w + 2 := by omega
  simp only [init, seqs]
  -- 1: `[2] = m`.
  rw [WP.seq_iff]
  refine WP.mono (init1_ok h hN15 hN hw h11 hn1 hnw hm) fun t1 ⟨h1, K1, v1, r11a, out1, k1⟩ => ?_
  -- 2: its digit `n` zero, `[b] = 0`.
  rw [WP.seq_iff, WP.seq_iff, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setTop_ok h1 hN) fun t2 ⟨⟨m2, r0⟩, k2⟩ => ?_
  have h2 := h1.of_keep (k2.mono (by decide))
  refine ptr_ok h2.ws (by decide) (by decide) (by decide) (by decide) ?_
  refine WP.mono (cntN1_ok (h2.of_keep ((Keep.write _ .r5 _).mono (by decide)))) fun t3 ⟨⟨p8, m3⟩, k3⟩ => ?_
  have h3 := (h2.of_keep ((Keep.write _ .r5 _).mono (by decide))).of_keep (k3.mono (by decide))
  refine WP.mono (zeroLoop_ok h3.ws.scr (dO := arr w aB) (by rw [k3.gpr _ (by decide)]; simp [gpr_write]) p8
    (by rw [k3.gpr _ (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact r0) (by omega) (by omega)
    (by omega)) fun t4 ⟨z4, out4, k4⟩ => ?_
  have h4 := h3.of_keep (k4.mono (by decide))
  rw [mem_write] at m3
  rw [m3] at out4
  have vM4 : val32 t4.mem B (arr w aMz) (n + 1) = m := by
    rw [out4.val32 (by have := arr_disj (w := w) (show aMz ≠ aB by decide); omega) (by omega), m2,
      val_top0 (by omega), v1]
  have zB : ∀ i < n + 1, w32 t4.mem B (arr w aB + 4 * i) = 0 := z4
  -- 3: `[b] = 1`, and whether `m = 1`.
  rw [WP.seq_iff, WP.seq_iff]
  refine WP.mono (WP.keep [.r0, .r5, .r6, .r7, .r8, .r9] (Q := fun u =>
      u.mem = t4.mem.writeW (off B (arr w aB)) ((BitVec.ofNat 64 1).setWidth 32) ∧
      u.gpr .r6 = off B (arr w aMz) ∧ u.gpr .r7 = off B (arr w aB) ∧ u.gpr .r8 = BitVec.ofNat 64 (n + 1) ∧
      u.gpr .r9 = 0) ?_ (by decide)) fun t5 ⟨⟨m5, p6, p7, q8, p9⟩, k5⟩ => ?_
  · prun [ptr, cntN1, cntN, exec_li (imm := aB) (by decide), exec_li (imm := aMz) (by decide),
      exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide) (by decide),
      exec_addi (n := .r6) (imm := KeyWorkspace.hdr) (by decide) (by decide),
      exec_addi (n := .r7) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, h4.ptr aB, h4.ptr aMz,
      h4.cnt, ofNat_succ, h4.ws.scr.st (show arr w aB + 4 ≤ Z by omega)]
    rfl
  have h5 := h4.of_keep (k5.mono (by decide))
  have o5 := writeW32_outside t4.mem B (d := arr w aB) ((BitVec.ofNat 64 1).setWidth 32) (by omega)
  have vB5 : val32 t5.mem B (arr w aB) (n + 1) = 1 := by
    rw [m5]
    have e : val32 (t4.mem.writeW (off B (arr w aB)) ((BitVec.ofNat 64 1).setWidth 32)) B (arr w aB) (n + 1) =
        w32 (t4.mem.writeW (off B (arr w aB)) ((BitVec.ofNat 64 1).setWidth 32)) B (arr w aB) +
        2 ^ 32 * val32 (t4.mem.writeW (off B (arr w aB)) ((BitVec.ofNat 64 1).setWidth 32)) B (arr w aB + 4) n := rfl
    rw [e, w32_write_self, o5.val32 (by omega) (by omega),
      val32_zero (fun i hi => by rw [show arr w aB + 4 + 4 * i = arr w aB + 4 * (i + 1) by omega]; exact zB _ (by omega))]
    rfl
  have vM5 : val32 t5.mem B (arr w aMz) (n + 1) = m := by
    rw [m5, o5.val32 (by have := arr_disj (w := w) (show aMz ≠ aB by decide); omega) (by omega), vM4]
  refine WP.mono (eqLoop_ok h5.ws.scr p6 p7 q8 p9 (by omega) (by omega) (by omega) (by omega))
    fun t6 ⟨e6, l6, m6, k6⟩ => ?_
  have h6 := h5.of_keep (k6.mono (by decide))
  rw [vM5, vB5] at e6
  -- 4: `p = vmod m` in `[2]`.
  rw [WP.seq_iff]
  have d0 := (t6.mem.readW (off B (arr w aMz)) 32).isLt
  refine WP.mono (WP.keep [.r0, .r3, .r5] (Q := fun u =>
      u.mem = t6.mem.writeW (off B (arr w aMz)) (((t6.mem.readW (off B (arr w aMz)) 32).setWidth 64 |||
        (if t6.gpr .r9 = 0#64 then 2#64 else 0#64)).setWidth 32)) ?_ (by decide)) fun t7 ⟨m7, k7⟩ => ?_
  · prun [ptr, exec_li (imm := aMz) (by decide),
      exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, h6.ptr aMz,
      h6.ws.scr.ld (show arr w aMz + 4 ≤ Z by omega), h6.ws.scr.st (show arr w aMz + 4 ≤ Z by omega)]
    rw [← virt_mask _ l6]
  have h7 := h6.of_keep (k7.mono (by decide))
  have pv : val32 t7.mem B (arr w aMz) (n + 1) = vmod m := by
    rw [m6] at m7
    have e : val32 t7.mem B (arr w aMz) (n + 1) = w32 t7.mem B (arr w aMz) + 2 ^ 32 * val32 t7.mem B (arr w aMz + 4) n := rfl
    have em : val32 t5.mem B (arr w aMz) (n + 1) = w32 t5.mem B (arr w aMz) + 2 ^ 32 * val32 t5.mem B (arr w aMz + 4) n :=
      rfl
    rw [vM5] at em
    have o7 := writeW32_outside t5.mem B (d := arr w aMz) (((t5.mem.readW (off B (arr w aMz)) 32).setWidth 64 |||
        (if t6.gpr .r9 = 0#64 then 2#64 else 0#64)).setWidth 32) (by omega)
    rw [e, m7, w32_write_self, o7.val32 (by omega) (by omega)]
    have vd := virt_digit (t5.mem.readW (off B (arr w aMz)) 32) (decide (t6.gpr .r9 = 0#64))
    simp only [decide_eq_true_eq] at vd
    rw [vd]
    unfold vmod
    by_cases e1 : m = 1
    · have z : t6.gpr .r9 = 0#64 := e6.mpr (by rw [e1])
      have : w32 t5.mem B (arr w aMz) = 1 ∧ val32 t5.mem B (arr w aMz + 4) n = 0 := by
        simp only [w32] at em ⊢; omega
      simp only [z, true_and, ↓reduceIte, e1]
      rw [show (t5.mem.readW (off B (arr w aMz)) 32).toNat = 1 from this.1, this.2]
      rfl
    · have z : ¬ t6.gpr .r9 = 0#64 := fun x => e1 (by have := e6.mp x; omega)
      simp only [z, false_and, ↓reduceIte, e1]
      simp only [w32] at em
      omega
  have vodd : vmod m % 2 = 1 := by unfold vmod; split <;> omega
  have vlt : vmod m < 2 ^ (32 * n) := by
    unfold vmod; split
    · have : 2 ^ 32 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact hmn
  have d0p : w32 t7.mem B (arr w aMz) % 2 ^ 32 = vmod m % 2 ^ 32 := by
    have e : val32 t7.mem B (arr w aMz) (n + 1) = w32 t7.mem B (arr w aMz) + 2 ^ 32 * val32 t7.mem B (arr w aMz + 4) n :=
      rfl
    rw [pv] at e; omega
  -- 5: `-p⁻¹ mod 2^32` into `r12`.
  rw [WP.seq_iff]
  rw [← List.append_nil (ptr .r10 aMz ++ _), List.append_assoc]
  refine ptr_ok h7.ws (by decide) (by decide) (by decide) (by decide) ?_
  rw [List.append_nil]
  have wodd : (word (t7.write .r10 (off B (arr w aMz))).mem B (arr w aMz)).toNat % 2 = 1 := by
    rw [mem_write, word_eq_w32]; omega
  refine WP.mono (Pub.minv_ok (h7.ws.scr.congr rfl) (by simp [gpr_write]) (by omega) wodd)
    fun t8 ⟨⟨i8, inv8, m8⟩, k8⟩ => ?_
  rw [mem_write] at m8 inv8
  have hiv : (vmod m * (t8.gpr .r12).toNat + 1) % 2 ^ 32 = 0 := by
    rw [Nat.add_mod, Nat.mul_mod, ← d0p, ← Nat.mul_mod, ← Nat.add_mod]; exact inv8
  have r11b : t8.gpr .r11 = BitVec.ofNat 64 n := by
    rw [k8.gpr _ (by decide)]
    simp only [gpr_write, reduceCtorEq, ↓reduceIte]
    rw [k7.gpr _ (by decide), k6.gpr _ (by decide), k5.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide)]
    simp only [gpr_write, reduceCtorEq, ↓reduceIte]
    rw [k2.gpr _ (by decide), r11a, h11]
  have kk8 : Keep (.r10 :: kRegs) t7 t8 := ((Keep.write _ .r10 _).trans k8).mono (by decide)
  have w8 : Ws t8 B Z w N := h7.ws.of_keep kk8
  have pw : ∀ j, BitVec.ofNat 64 j * t8.gpr .r30 + t8.gpr .r31 + BitVec.ofNat 64 KeyWorkspace.hdr = off B (arr w j) :=
    fun j => by rw [w8.r30, w8.r31]; exact ptr_val _ _ _
  -- 6: the inverse to the window, `r10 = n`.
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r5, .r10] (Q := fun u => u.mem = t8.mem.writeW (off B (arr w aW + 40)) (t8.gpr .r12) ∧
      u.gpr .r10 = BitVec.ofNat 64 n) ?_ (by decide)) fun t9 ⟨⟨m9, r10⟩, k9⟩ => ?_
  · prun [ptr, wIv, exec_li (imm := aW) (by decide),
      exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, pw aW, r11b,
      w8.scr.st (show arr w aW + 40 + 8 ≤ Z by omega), BitVec.add_zero]
  have kk9 : Keep (.r10 :: kRegs) t8 t9 := k9.mono (by decide)
  have h9 : Ctx t9 B Z w N n 0 := ⟨w8.of_keep k9, by rw [r10]; simp, hn1, hnw, hN15, by decide, hw⟩
  have o9 := writeW64_outside t8.mem B (d := arr w aW + 40) (t8.gpr .r12) (by omega)
  have pv9 : val32 t9.mem B (arr w aMz) (n + 1) = vmod m := by
    rw [m9, o9.val32 (by have := arr_disj (w := w) (show aMz ≠ aW by decide); omega) (by omega), m8, pv]
  -- 7: `f = p`.
  rw [WP.seq_iff, WP.seq_iff, List.append_assoc]
  refine ptr_ok h9.ws (by decide) (by decide) (by decide) (by decide) ?_
  refine ptr_ok (h9.ws.of_keep (Keep.write _ .r5 _)) (by decide) (by decide) (by decide) (by decide) ?_
  refine WP.mono (cntN1_ok (h9.of_keep (((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).mono (by decide))))
    fun x10 ⟨⟨q8, xm⟩, kx⟩ => ?_
  have k10a : Keep kRegs t9 x10 := (((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).trans kx).mono (by decide)
  have h10a := h9.of_keep k10a
  refine WP.mono (copyLoop_ok (dO := arr w aF) (dA := arr w aMz) h10a.ws.scr
    (by rw [kx.gpr _ (by decide)]; simp [gpr_write]) (by rw [kx.gpr _ (by decide)]; simp [gpr_write]) q8
    (by omega) (by omega) (by have := fitZ _ nF; omega) (by omega) (ahead_k (by decide) (by omega)))
    fun t10 ⟨vF, out10, k10⟩ => ?_
  rw [xm, mem_write, mem_write] at vF out10
  rw [pv9] at vF
  have h10 := h10a.of_keep (k10.mono (by decide))
  -- 8: `k = 1` for an even `x`.
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r0, .r5, .r11] (Q := fun u => (u.gpr .r11).toNat =
      (if (t10.mem.readW (off B (arr w aX)) 32).toNat % 2 = 0 then 1 else 0) ∧ u.mem = t10.mem) ?_ (by decide))
    fun t11 ⟨⟨r11k, m11⟩, k11⟩ => ?_
  · prun [ptr, exec_li (imm := aX) (by decide), exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide) (by decide),
      hdr_eq, h10.ptr aX, h10.ws.scr.ld (show arr w aX + 4 ≤ Z by have := fitZ _ nX; omega)]
    exact even_bit _
  have h11' := h10.of_keep (k11.mono (by decide))
  -- The frame so far.
  have a2 : KeyWorkspace.Keep B w [aMz] [] t1.mem t2.mem := by
    rw [m2]; exact KeyWorkspace.Keep.of_arr (d := 4 * n) (writeW32_outside _ B _ (by omega)) (by omega) (by simp)
  have a4 : KeyWorkspace.Keep B w [aB] [] t2.mem t4.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out4) (by omega) (by simp)
  have a5 : KeyWorkspace.Keep B w [aB] [] t4.mem t5.mem := by
    rw [m5]; exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using o5) (by omega) (by simp)
  have a7 : KeyWorkspace.Keep B w [aMz] [] t6.mem t7.mem := by
    have o := writeW32_outside t6.mem B (d := arr w aMz) (((t6.mem.readW (off B (arr w aMz)) 32).setWidth 64 |||
      (if t6.gpr .r9 = 0#64 then 2#64 else 0#64)).setWidth 32) (by omega)
    rw [m7]; exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using o) (by omega) (by simp)
  have a9 : KeyWorkspace.Keep B w [aW] [] t8.mem t9.mem := by
    rw [m9]; exact KeyWorkspace.Keep.of_arr (d := 40) o9 (by omega) (by simp)
  have a10 : KeyWorkspace.Keep B w [aF] [] t9.mem t10.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out10) (by have := fitZ _ nF; omega)
      (by simp)
  have K10 : KeyWorkspace.Keep B w [aMz, aB, aW, aF] [] s.mem t10.mem :=
    (K1.mono (by simp)).trans ((a2.mono (by simp)).trans ((a4.mono (by simp)).trans ((a5.mono (by simp)).trans
      ((show KeyWorkspace.Keep B w [aMz, aB, aW, aF] [] t5.mem t6.mem by rw [m6]; exact KeyWorkspace.Keep.refl _ _ _ _ _).trans
        ((a7.mono (by simp)).trans ((show KeyWorkspace.Keep B w [aMz, aB, aW, aF] [] t7.mem t8.mem by
          rw [m8]; exact KeyWorkspace.Keep.refl _ _ _ _ _).trans ((a9.mono (by simp)).trans
            (a10.mono (by simp)))))))))
  have xX : val32 t11.mem B (arr w aX) n = x := by
    rw [m11, keep_val K10 (by omega) (by decide) (by simp) (fit _ nX), hx]
  have x0 : (t10.mem.readW (off B (arr w aX)) 32).toNat % 2 = x % 2 := by
    rw [← m11, ← xX]
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [hk]; simp only [val32, w32]; omega
  have a10' : KeyWorkspace.Keep B w [aF] [] t9.mem t10.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out10) (by have := fitZ _ nF; omega)
      (by simp)
  have pM10 : val32 t10.mem B (arr w aMz) (n + 1) = vmod m := by
    rw [keep_val a10' (k := n + 1) (by omega) (by decide) (by simp) (fit _ nM), pv9]
  have pM : val32 t11.mem B (arr w aMz) n = vmod m := by
    rw [m11]; exact val_low (by omega) pM10 vlt
  -- 9: `g = x + k p`, its carry the digit `n`.
  rw [WP.seq_iff]
  refine WP.mono (mac_ok h11' (fun u hu => cntN_ok hu) (K := n) hn1 (by omega) nG nX nM hN
    (by rw [r11k]; split <;> decide)) fun t12 ⟨h12, K12, v12, c12, p12, _, out12, k12⟩ => ?_
  rw [xX, pM, r11k, x0] at v12
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = t12.mem.writeW (off B (arr w aG + 4 * n))
      ((t12.gpr .r9).setWidth 32)) ?_ (by decide)) fun t13 ⟨m13, k13⟩ => ?_
  · prun [p12, h12.ws.scr.st (show arr w aG + 4 * n + 4 ≤ Z by have := fitZ _ nG; omega)]
  have h13 := h12.of_keep (k13.mono (by decide))
  have vG : val32 t13.mem B (arr w aG) (n + 1) = oddInput (vmod m) x := by
    rw [m13, val32_write_top _ _ _ _ _ (by have := fit _ nG; omega), BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt c12]
    unfold oddInput
    by_cases e : x % 2 = 0 <;> simp only [e, ↓reduceIte] at v12 ⊢ <;> omega
  -- 10: `a = 0`.
  rw [WP.seq_iff, WP.seq_iff, List.append_assoc]
  refine ptr_ok h13.ws (by decide) (by decide) (by decide) (by decide) ?_
  rw [WP.block_append_iff]
  refine WP.mono (cntN1_ok (h13.of_keep ((Keep.write _ .r5 _).mono (by decide)))) fun x14 ⟨⟨q8', xm'⟩, kx'⟩ => ?_
  refine WP.mono (WP.keep [.r0] (Q := fun u => u.gpr .r0 = 0 ∧ u.mem = x14.mem) (by prun; rfl) (by decide))
    fun y14 ⟨⟨y0, ym⟩, ky⟩ => ?_
  have k14a : Keep kRegs t13 y14 := (((Keep.write _ .r5 _).trans kx').trans ky).mono (by decide)
  refine WP.mono (zeroLoop_ok (dO := arr w aA) (n := n + 1) (h13.of_keep k14a).ws.scr
    (by rw [ky.gpr _ (by decide), kx'.gpr _ (by decide)]; simp [gpr_write])
    (by rw [ky.gpr _ (by decide)]; exact q8') y0 (by omega) (by omega) (by have := fitZ _ nA; omega))
    fun t14 ⟨z14, out14, k14⟩ => ?_
  rw [ym, xm', mem_write] at out14
  have h14 := (h13.of_keep k14a).of_keep (k14.mono (by decide))
  -- 11: `d = 1` and `3 (n + 1)` batches.
  refine WP.mono (WP.keep [.r0, .r3, .r5, .r10] (Q := fun u => u.mem = t14.mem.writeW (off B (arr w aW))
      (BitVec.ofNat 64 1) ∧ u.gpr .r10 = BitVec.ofNat 64 (n + 2 ^ 15 * (3 * (n + 1)))) ?_ (by decide))
    fun t15 ⟨⟨m15, r15⟩, k15⟩ => ?_
  · have e := h14.r10
    simp only [Nat.mul_zero, Nat.add_zero] at e
    prun [ptr, wD, exec_li (imm := aW) (by decide), exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide)
      (by decide), hdr_eq, h14.ptr aW, h14.ws.scr.st (show arr w aW + 8 ≤ Z by omega), e]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  -- The result.
  have a13 : KeyWorkspace.Keep B w [aG] [] t12.mem t13.mem := by
    have := fit _ nG
    rw [m13]; exact KeyWorkspace.Keep.of_arr (d := 4 * n) (writeW32_outside _ B _ (by omega)) (by omega) (by simp)
  have a14 : KeyWorkspace.Keep B w [aA] [] t13.mem t14.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out14) (by have := fitZ _ nA; omega)
      (by simp)
  have o15 := writeW64_outside t14.mem B (d := arr w aW) (BitVec.ofNat 64 1) (by omega)
  have a15 : KeyWorkspace.Keep B w [aW] [] t14.mem t15.mem := by
    rw [m15]; exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using o15) (by omega) (by simp)
  have K15 : KeyWorkspace.Keep B w [aG, aA, aW] [] t10.mem t15.mem :=
    (show KeyWorkspace.Keep B w [aG, aA, aW] [] t10.mem t11.mem by rw [m11]; exact KeyWorkspace.Keep.refl _ _ _ _ _).trans
      ((K12.mono (by simp)).trans ((a13.mono (by simp)).trans ((a14.mono (by simp)).trans (a15.mono (by simp)))))
  have K5 : KeyWorkspace.Keep B w [aMz, aW, aF, aG, aA] [] t5.mem t15.mem :=
    (show KeyWorkspace.Keep B w [aMz, aW, aF, aG, aA] [] t5.mem t6.mem by rw [m6]; exact KeyWorkspace.Keep.refl _ _ _ _ _).trans
      ((a7.mono (by simp)).trans ((show KeyWorkspace.Keep B w [aMz, aW, aF, aG, aA] [] t7.mem t8.mem by
        rw [m8]; exact KeyWorkspace.Keep.refl _ _ _ _ _).trans ((a9.mono (by simp)).trans ((a10'.mono (by simp)).trans
          (K15.mono (by simp))))))
  have hk2 : n + 1 ≤ w + 2 := by omega
  have m10 : ∀ {a b : State} {rs : List Reg}, Keep rs a b → (∀ r ∈ rs, r ∈ (.r10 :: kRegs)) →
      Keep (.r10 :: kRegs) a b := fun h hr => h.mono hr
  have k : Keep (.r10 :: kRegs) s t15 :=
    (((((((((((((k1.trans' (m10 k2 (by decide))).trans' (m10 ((Keep.write _ .r5 _).trans k3) (by decide))).trans'
      (m10 k4 (by decide))).trans' (m10 k5 (by decide))).trans' (m10 k6 (by decide))).trans' (m10 k7 (by decide))).trans'
      kk8).trans' kk9).trans' (m10 (k10a.trans k10) (by decide))).trans' (m10 k11 (by decide))).trans'
      (m10 (k12.trans k13) (by decide))).trans' (m10 (k14a.trans k14) (by decide))).trans' (m10 k15 (by decide)))
  refine ⟨⟨h14.ws.of_keep k15, r15, hn1, hnw, hN15, by omega, hw⟩, ⟨(t8.gpr .r12).toNat, hiv, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩,
    (K10.mono (by simp)).trans (K15.mono (by simp)), k⟩
  · show sv t15.mem B (arr w aF) n = (vmod m : Int)
    refine sv_of_val ?_ (by exact_mod_cast vlt)
    rw [keep_val K15 hk2 (by decide) (by simp) (fit _ nF), vF]
  · show sv t15.mem B (arr w aG) n = (oddInput (vmod m) x : Int)
    refine sv_of_eq (q := 0) ?_ ?_ ?_
    · rw [keep_val a15 hk2 (by decide) (by simp) (fit _ nG), keep_val a14 hk2 (by decide) (by simp) (fit _ nG), vG]
      simp
    · have : (0 : Int) ≤ 2 ^ (32 * n + 31) := by exact_mod_cast Nat.zero_le _
      have : (0 : Int) ≤ (oddInput (vmod m) x : Int) := Int.natCast_nonneg _
      omega
    · have h1 : oddInput (vmod m) x < 2 ^ (32 * n + 31) := by
        have : oddInput (vmod m) x ≤ vmod m + x := by unfold oddInput; split <;> omega
        have : 2 * 2 ^ (32 * n) ≤ 2 ^ (32 * n + 31) := by
          rw [show 32 * n + 31 = 32 * n + 1 + 30 by omega, Nat.pow_add, Nat.pow_succ]
          have := Nat.one_le_two_pow (n := 30)
          calc 2 * 2 ^ (32 * n) = 2 ^ (32 * n) * 2 * 1 := by omega
            _ ≤ 2 ^ (32 * n) * 2 * 2 ^ 30 := Nat.mul_le_mul_left _ this
        omega
      exact_mod_cast h1
  · show (val32 t15.mem B (arr w aA) (n + 1) : Int) = 0
    rw [keep_val a15 hk2 (by decide) (by simp) (fit _ nA), val32_zero z14]; rfl
  · show (val32 t15.mem B (arr w aB) (n + 1) : Int) = 1
    rw [keep_val K5 hk2 (by decide) (by simp) (fit _ nB), vB5]; rfl
  · show t15.mem.readW (off B (arr w aW + wD)) 64 = BitVec.ofInt 64 1
    rw [show arr w aW + wD = arr w aW from rfl, m15, Mem.readW_writeW_self64]; rfl
  · show (t15.mem.readW (off B (arr w aW + wIv)) 64).toNat = (t8.gpr .r12).toNat
    have w40 : 40 + 64 / 8 ≤ S w := by omega
    rw [show arr w aW + wIv = arr w aW + 40 from rfl, m15, Outside.readW64 o15 (by omega) (by omega),
      keep_word a14 w40 (by decide) (by simp) (fit _ nW), keep_word a13 w40 (by decide) (by simp) (fit _ nW),
      keep_word K12 w40 (by decide) (by simp) (fit _ nW), m11, keep_word a10' w40 (by decide) (by simp) (fit _ nW),
      m9, Mem.readW_writeW_self64]
  · rw [keep_val K15 hk2 (by decide) (by simp) (fit _ nM), pM10]

end VG.Proof.Rsa.PPC64LE.InvBatch
