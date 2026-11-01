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
  sorry

end VG.Proof.Rsa.PPC64LE.InvBatch
