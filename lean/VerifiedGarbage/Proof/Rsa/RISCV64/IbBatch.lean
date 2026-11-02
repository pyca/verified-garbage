module
-- separate module: its proofs (the reduction and a batch) build in parallel with `InvResult`'s and the doublings' imports, which `IbInverse` also imports

public import VerifiedGarbage.Proof.Rsa.RISCV64.IbOps
public import VerifiedGarbage.Proof.Divstep.Alg32Def
public import Mathlib.Algebra.Order.Ring.Abs
import VerifiedGarbage.Proof.Divstep.Mred32
import VerifiedGarbage.Proof.Divstep.Tc32Red
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Divstep.WordDef
import VerifiedGarbage.Proof.Divstep.Word
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The batched inverse on RISC-V: the reduction

`mred_ok`: `mred t o` leaves in array `o` the number
`Proof/Divstep/Alg32Def.lean`'s `mred p iv T` of the signed `T` in array
`t`, for the odd `p < 2^(32 n)` in array 2 and `iv = -p⁻¹ mod 2^32` in the
window: `k = T iv mod 2^32` from `T`'s low digit, `T + k p` (`mac`), its top
digit fixed by the carry, which leaves `2^32 R`, `R = mredRaw p iv T`, then
`R + p` (in `(0, 3p)`) and two conditional subtractions.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr seqs mov)
open VG.Impl.Rsa.RISCV64.InvBatch
open VG.RISCV64.RegUpd

/-- `ptr r j` at the head of a block, run: `r` holds the address of array `j`. -/
theorem runBlock_ptr (B : Addr) (w : Nat) {s : State} {r : Reg} {j : Nat} (rest : List Instr)
    (h10 : s.gpr .s10 = BitVec.ofNat 64 (S w)) (h11 : s.gpr .s11 = B) (hr10 : r ≠ .s10) (hr11 : r ≠ .s11)
    (hj : j < 2048) :
    runBlock isa (ptr r j ++ rest) s = runBlock isa rest (s.write r (off B (arr w j))) := by
  simp only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, exec_li_nat hj, exec_mul,
    exec_add, exec_addi_nat (show hdr < 2048 by decide), gpr_write, ite_true, Ne.symm hr10, Ne.symm hr11,
    ite_false, write_write, h10, h11, ptr_val]

/-- The arithmetic of the reduction: from the words the code leaves (see
the module doc), `R + p`, and the low digit zero. -/
theorem mred_arith {T V0 V2 V' X3 P A : Int} {p iv k C C2 d0 j0 j2 : Int} {D3 : Int}
    (hA : A = 2 ^ 32 * P) (hpP : p < P) (hp0 : 0 < p) (hm : (p * iv + 1) % 2 ^ 32 = 0)
    (hk : k = (T * iv) % 2 ^ 32) (hT : T = V0 + A * d0) (hmac : V2 + A * C = V0 + k * p)
    (hD3 : D3 - d0 - C = 2 ^ 32 * j0) (hlow : V2 + A * D3 = j2 + 2 ^ 32 * V')
    (hj2 : 0 ≤ j2) (hj2' : j2 < 2 ^ 32) (hR : X3 + A * C2 = V' + p) (hX0 : 0 ≤ X3) (hX1 : X3 < A)
    (hTr : |T| ≤ 2 ^ 31 * p) :
    X3 = Divstep.W32.mredRaw p iv T + p := by
  have spec := Divstep.W32.mredRaw_spec (t := T) hm
  have rng := Divstep.W32.mredRaw_range (t := T) hp0 hm hTr
  rw [← hk] at spec
  generalize Divstep.W32.mredRaw p iv T = R at spec rng ⊢
  have e1 : V2 + A * D3 = 2 ^ 32 * (R + A * j0) := by
    have : D3 = d0 + C + 2 ^ 32 * j0 := by omega
    rw [this]
    grind
  have hP0 : 0 < P := by omega
  have hA0 : 0 < A := by rw [hA]; omega
  have e2 : j2 = 2 ^ 32 * (R + A * j0 - V') := by grind
  have z := mul_small (H := 2 ^ 32) (d := R + A * j0 - V') (by decide) (by omega) (by omega)
  have e3 : V' = R + A * j0 := by omega
  have e4 : A * (j0 - C2) = X3 - (R + p) := by grind
  have bnd : 3 * p < A := by
    rw [hA]
    have : (3 : Int) * P ≤ 2 ^ 32 * P := Int.mul_le_mul_of_nonneg_right (by decide) (by omega)
    omega
  have := mul_small (H := A) (d := j0 - C2) hA0 (by omega) (by omega)
  rw [this, Int.mul_zero] at e4
  omega

/-- `norm p (R)` from `R + p` and two conditional subtractions. -/
theorem norm_twice {p R : Int} (X0 : Nat) (hX0 : (X0 : Int) = R + p) (P : Nat)
    (hP : (P : Int) = p) :
    ((if P ≤ (if P ≤ X0 then X0 - P else X0) then (if P ≤ X0 then X0 - P else X0) - P
      else (if P ≤ X0 then X0 - P else X0) : Nat) : Int) = Divstep.W32.norm p R := by
  unfold Divstep.W32.norm
  split_ifs <;> omega

/-- `mred t o`: `[o] = mred p iv T` for `T` the signed number of `n + 2`
digits in `[t]`. -/
theorem mred_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {t o : Nat}
    (ht : t < N) (ho : o < N) (hN : N ≤ 256) (h3 : aT3 < N) (hm : aMz < N) (htm : t ≠ aMz)
    (ht3 : t ≠ aT3) (h3m : aT3 ≠ aMz) (ho3 : o ≠ aT3) (hot : o ≠ t) {p iv : Nat} {T : Int}
    (hp : val32 s.mem B (arr w aMz) (n + 1) = p) (hpA : p < 2 ^ (32 * n)) (hp0 : 0 < p)
    (hiv : (s.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv) (hinv : (p * iv + 1) % 2 ^ 32 = 0)
    (hT : sv s.mem B (arr w t) (n + 1) = T) (hTr : |T| ≤ 2 ^ 31 * p) :
    WP isa (mred t o) s fun u => Ctx u B Z w N n ∧ Keys.Frame B w [o, t, aT3] [] s.mem u.mem ∧
      (val32 u.mem B (arr w o) (n + 1) : Int) = Divstep.W32.mred p iv T ∧ Keep kRegs s u := by
  have ft := h.ws.arr_fit ht
  have f3 := h.ws.arr_fit h3
  have fm := h.ws.arr_fit hm
  have fW := h.ws.arr_fit (j := aW) (by have := h.room; unfold aW; omega)
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have := h.npos
  have := h.ws.wle
  have := h.wbig
  have hnw := h.ws.nowrap
  have hs := h.ws.scr
  have := arr_al4 w t
  have := arr_al4 w aT3
  have := arr_al4 w aMz
  have := arr_al w aW
  rw [mred]; simp only [seqs]; rw [WP.seq_iff]
  -- 1: `k = T₀ iv mod 2^32` into `a5`.
  have hb1 : WP isa (.block (ptr .t0 t ++ ldW .t6 wIv ++
      ([.load .w .t5 .t0 0, .mul .a5 .t5 .t6, .shift .sll .d .a5 .a5 32, .shift .srl .d .a5 .a5 32] :
        List Instr))) s fun u =>
      Ctx u B Z w N n ∧ u.mem = s.mem ∧ (u.gpr .a5).toNat = (w32 s.mem B (arr w t) * iv) % 2 ^ 32 ∧
      Keep kRegs s u := by
    refine WP.mono (WP.keep kRegs (Q := fun u => (u.gpr .a5).toNat = (w32 s.mem B (arr w t) * iv) % 2 ^ 32 ∧
      u.mem = s.mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨u5, um⟩, ku⟩ => ⟨h.of_keep ku, um, u5, ku⟩
    brun [exec_li, ldW, List.append_assoc, runBlock_ptr B w, (show t < 2048 by omega), (show aW < 2048 by decide), h.ws.s10, h.ws.s11, exec_load_w,
      hs.ld (show arr w t + 4 ≤ Z by omega), Scr.al4 hs (show arr w t + 4 ≤ Z by omega) (by omega),
      wIv, hs.ld (show arr w aW + 40 + 8 ≤ Z by omega), hs.al8 (show arr w aW + 40 + 8 ≤ Z by omega) (by omega)]
    have hiv' : (s.mem.readW (off B (arr w aW + 40)) 64).toNat = iv := hiv
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_mul, toNat_ext32, hiv',
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    generalize (s.mem.readW (off B (arr w t)) 32).toNat * iv = P
    omega
  refine WP.mono hb1 fun t1 ⟨h1, m1, ka5, k1⟩ => ?_
  rw [WP.seq_iff]
  -- 2: `[t] += k m`.
  refine WP.mono (mac_ok h1 (fun u hu => cntN1_ok hu) (K := n + 1) (by omega) (by omega) ht ht hm hN
    (by rw [ka5]; exact Nat.mod_lt _ (by decide))) fun t2 ⟨h2, kp2, mac2, c2, p0, _, out2, k2⟩ => ?_
  rw [WP.seq_iff]
  -- 3: the top digit plus the carry.
  refine WP.mono (WP.keep [.t5] (Q := fun u => u.mem = t2.mem.writeW (off B (arr w t + 4 * (n + 1)))
      (((t2.mem.readW (off B (arr w t + 4 * (n + 1))) 32).setWidth 64 + t2.gpr .t4).setWidth 32)) ?_
      (by rfl) (by rfl)) fun t3 ⟨m3, k3⟩ => ?_
  · have hs2 := h2.ws.scr
    brun [exec_li, p0, exec_load_w, exec_store_w, hs2.ld (show arr w t + 4 * (n + 1) + 4 ≤ Z by omega),
      hs2.st (show arr w t + 4 * (n + 1) + 4 ≤ Z by omega),
      Scr.al4 hs2 (show arr w t + 4 * (n + 1) + 4 ≤ Z by omega) (by omega)]
  have h3' := h2.of_keep (k3.mono (by decide))
  rw [WP.seq_iff]
  -- 4: `[aT3] = R + p`.
  have hb4 : WP isa (.block (ptr .t0 aT3 ++ ptr .t1 t ++ ptr .t2 aMz ++
      ([.addi .t1 .t1 4, .li .a5 1] : List Instr) ++ cntN1 ++ ([.li .t4 0] : List Instr))) t3 fun u =>
      Ctx u B Z w N n ∧ u.mem = t3.mem ∧ u.gpr .t0 = off B (arr w aT3) ∧ u.gpr .t1 = off B (arr w t + 4) ∧
      u.gpr .t2 = off B (arr w aMz) ∧ u.gpr .t3 = BitVec.ofNat 64 (n + 1) ∧ u.gpr .t4 = 0 ∧
      u.gpr .a5 = 1#64 ∧ Keep kRegs t3 u := by
    rw [show ptr .t0 aT3 ++ ptr .t1 t ++ ptr .t2 aMz ++ ([.addi .t1 .t1 4, .li .a5 1] : List Instr) ++ cntN1 ++
      ([.li .t4 0] : List Instr) = VG.Impl.Rsa.RISCV64.Keys.ptrs aT3 t aMz ++
        (([.addi .t1 .t1 4, .li .a5 1] : List Instr) ++ cntN1 ++ ([.li .t4 0] : List Instr)) by
          simp only [VG.Impl.Rsa.RISCV64.Keys.ptrs, List.append_assoc]]
    refine ptrs_ok h3'.ws (by omega) (by omega) (by omega) fun u q0 q1 q2 ku mu => ?_
    have hu := h3'.of_keep (ku.mono (by decide))
    refine WP.mono (WP.keep [.t1, .t3, .t4, .a5] (Q := fun y => y.gpr .t1 = off B (arr w t + 4) ∧
      y.gpr .t3 = BitVec.ofNat 64 (n + 1) ∧ y.gpr .t4 = 0 ∧ y.gpr .a5 = 1#64 ∧ y.mem = u.mem) ?_
      (by rfl) (by rfl)) fun y ⟨⟨y1, y3, y4, y5, ym⟩, ky⟩ => ?_
    · brun [exec_li, cntN1, hu.s8, ofNat_succ, q1, fin64_exec_li_zero]
      try rfl
    have k0 : Keep kRegs t3 y := (ku.trans ky).mono (by decide)
    refine ⟨h3'.of_keep k0, ym.trans mu, ?_, y1, ?_, y3, y4, y5, k0⟩
    · rw [ky.gpr (by decide)]; exact q0
    · rw [ky.gpr (by decide)]; exact q2
  refine WP.mono hb4 fun t4 ⟨h4, m4, q0, q1, q2, q3, q4, q5, k4⟩ => ?_
  rw [WP.seq_iff]
  have dt3 := arr_disj (w := w) ht3
  have d3m := arr_disj (w := w) h3m
  refine WP.mono (macLoop_ok h4.ws.scr q0 q1 q2 q3 (by rw [q4]; decide) (by rw [q5]; decide) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by unfold Ahead; omega) (by unfold Ahead; omega)) fun t5 ⟨c5, mac5, _, out5, k5⟩ => ?_
  have h5 := h4.of_keep (k5.mono (by decide))
  -- The frame so far.
  have K3 : Keys.Frame B w [t] [] t2.mem t3.mem := by
    rw [m3]
    exact Keys.Frame.of_arr (d := 4 * (n + 1)) (writeW32_outside _ B _ (by omega)) (by omega) (by simp)
  have K5 : Keys.Frame B w [t, aT3] [] s.mem t5.mem := by
    rw [← m1]
    exact (kp2.mono (by simp)).trans ((K3.mono (by simp)).trans (by
      rw [← m4]
      exact Keys.Frame.of_arr (o := aT3) (d := 0) (by simpa only [Nat.add_zero] using out5) (by omega)
        (by simp)))
  have pm5 : val32 t5.mem B (arr w aMz) (n + 1) = p := by
    rw [keep_val K5 (by omega) (by simp; omega) (by simp) (by omega), hp]
  rw [WP.seq_iff]
  refine WP.mono (csub_ok h5 h3 h3 ht hm hN ht3 htm ht3.symm pm5 rfl) fun t6 ⟨h6, K6, v6, k6⟩ => ?_
  have pm6 : val32 t6.mem B (arr w aMz) (n + 1) = p := by
    rw [keep_val K6 (by omega) (by simp; omega) (by simp) (by omega), pm5]
  refine WP.mono (csub_ok h6 ho h3 ht hm hN ht3 htm hot pm6 v6) fun t7 ⟨h7, K7, v7, k7⟩ => ?_
  have k : Keep kRegs s t7 := Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans'
    (Keep.trans' k1 k2) (k3.mono (by decide))) k4) (k5.mono (by decide))) k6) k7
  refine ⟨h.of_keep k, (K5.mono (by simp)).trans ((K6.mono (by simp)).trans (K7.mono (by simp))), ?_, k⟩
  rw [v7]
  -- The arithmetic.
  have pm3 : val32 t3.mem B (arr w aMz) (n + 1) = p := by
    have K := (show Keys.Frame B w [t] [] s.mem t2.mem by rw [← m1]; exact kp2).trans K3
    rw [keep_val K (by omega) (by simp; omega) (by simp) (by omega), hp]
  have dd : t2.mem.readW (off B (arr w t + 4 * (n + 1))) 32 = s.mem.readW (off B (arr w t + 4 * (n + 1))) 32 := by
    rw [Outside.readW32 out2 (by omega) (by omega), m1]
  have v3 : val32 t3.mem B (arr w t) (n + 1 + 1) = val32 t2.mem B (arr w t) (n + 1) +
      2 ^ (32 * (n + 1)) * (((t2.mem.readW (off B (arr w t + 4 * (n + 1))) 32).setWidth 64 +
        t2.gpr .t4).setWidth 32).toNat := by
    rw [m3, val32_write_top _ _ _ _ _ (by omega)]
  have eD3 : (((t2.mem.readW (off B (arr w t + 4 * (n + 1))) 32).setWidth 64 + t2.gpr .t4).setWidth 32).toNat =
      ((s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).toNat + (t2.gpr .t4).toNat) % 2 ^ 32 := by
    rw [dd, BitVec.toNat_setWidth, BitVec.toNat_add, toNat_ext32]
    have := (s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).isLt
    omega
  have v3' : val32 t3.mem B (arr w t) (n + 1 + 1) =
      w32 t3.mem B (arr w t) + 2 ^ 32 * val32 t3.mem B (arr w t + 4) (n + 1) := rfl
  rw [m1, ka5, hp] at mac2
  rw [m4, pm3, q5, q4, show (1#64 : BitVec 64).toNat = 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl,
    Nat.one_mul, Nat.add_zero] at mac5
  have hTs := hT
  unfold sv at hTs
  -- `k ≡ T iv`.
  have hk : (((w32 s.mem B (arr w t) * iv) % 2 ^ 32 : Nat) : Int) = (T * iv) % 2 ^ 32 := by
    have e0 : val32 s.mem B (arr w t) (n + 1) = w32 s.mem B (arr w t) + 2 ^ 32 * val32 s.mem B (arr w t + 4) n := rfl
    have hW := (s.mem.readW (off B (arr w t)) 32).isLt
    have eT : T = (w32 s.mem B (arr w t) : Int) + 2 ^ 32 * ((val32 s.mem B (arr w t + 4) n : Int) +
        2 ^ (32 * n) * (s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).toInt) := by
      rw [← hTs, e0, show 32 * (n + 1) = 32 + 32 * n by omega, Int.pow_add]
      push_cast
      grind
    have hTmod : T % 2 ^ 32 = (w32 s.mem B (arr w t) : Int) := by
      rw [eT, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by omega) (by simp only [w32]; omega)
    rw [Int.natCast_emod, Int.natCast_mul, Int.mul_emod, Int.mul_emod T, hTmod]
    push_cast
    rw [Int.emod_eq_of_lt (a := (w32 s.mem B (arr w t) : Int)) (by omega) (by simp only [w32]; omega)]
  have hd0 := toInt_cond (s.mem.readW (off B (arr w t + 4 * (n + 1))) 32)
  have hdl := (s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).isLt
  have X := mred_arith (T := T) (V0 := val32 s.mem B (arr w t) (n + 1)) (V2 := val32 t2.mem B (arr w t) (n + 1))
    (V' := val32 t3.mem B (arr w t + 4) (n + 1)) (X3 := val32 t5.mem B (arr w aT3) (n + 1))
    (P := 2 ^ (32 * n)) (A := 2 ^ (32 * (n + 1))) (p := p) (iv := iv)
    (k := (((w32 s.mem B (arr w t) * iv) % 2 ^ 32 : Nat) : Int)) (C := (t2.gpr .t4).toNat)
    (C2 := (t5.gpr .t4).toNat) (d0 := (s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).toInt)
    (j0 := (if 2 ^ 31 ≤ (s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).toNat then 1 else 0) -
      ((((s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).toNat + (t2.gpr .t4).toNat) / 2 ^ 32 : Nat) : Int))
    (j2 := w32 t3.mem B (arr w t))
    (D3 := ((((s.mem.readW (off B (arr w t + 4 * (n + 1))) 32).toNat + (t2.gpr .t4).toNat) % 2 ^ 32 : Nat) : Int))
    (by rw [show 32 * (n + 1) = 32 + 32 * n by omega, Int.pow_add]) (by exact_mod_cast hpA)
    (by exact_mod_cast hp0) (by exact_mod_cast hinv) hk hTs.symm (by exact_mod_cast mac2)
    (by rw [hd0]; split <;> omega)
    (by rw [← eD3]; exact_mod_cast (v3.symm.trans v3'))
    (by omega) (by exact_mod_cast (t3.mem.readW (off B (arr w t)) 32).isLt) (by exact_mod_cast mac5) (by omega)
    (by exact_mod_cast val32_lt _ _ _ _) hTr
  exact norm_twice _ X _ rfl

end VG.Proof.Rsa.RISCV64.InvBatch

/-!
# The batched inverse on RISC-V: a batch

`batch_ok`: from the arrays and the window holding a state of
`Proof/Divstep/Alg32Def.lean`'s inversion (`StateAt`), a batch leaves the next
one: 30 divsteps on the low digits (`head_ok`), then the new `f`, `g`
(`updateG_ok`), `a` and `b` (`updateAB_ok`). `batchG_ok`: the same for `f`
and `g` alone (`StateG`), which do not depend on `a` and `b`.
-/

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr seqs mov)
open VG.Impl.Rsa.RISCV64.InvBatch
open VG.Proof.Divstep (MSt msteps WSt)
open VG.RISCV64.RegUpd

/-- A 64-bit word outside the bytes that changed. -/
theorem Outside.readW64 {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 ≤ 2 ^ 64) :
    m'.readW (off base d) 64 = m.readW (off base d) 64 :=
  Mem.readW_congr fun _ _ => h _ (by rw [ofs_off base (by omega)]; omega)

/-- A 64-bit store changes only its 8 bytes. -/
theorem writeW64_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 ≤ 2 ^ 64) :
    Outside base d 8 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

/-- `d`, `f` and `g` of the inversion in the arrays and the window. -/
structure StateG (s : State) (B : Addr) (w n : Nat) (st : Divstep.W32.IState) : Prop where
  f : sv s.mem B (arr w aF) n = st.f
  g : sv s.mem B (arr w aG) n = st.g
  d : s.mem.readW (off B (arr w aW + wD)) 64 = BitVec.ofInt 64 st.d

/-- The state of the inversion in the arrays and the window. -/
structure StateAt (s : State) (B : Addr) (w n p iv : Nat) (st : Divstep.W32.IState) : Prop where
  f : sv s.mem B (arr w aF) n = st.f
  g : sv s.mem B (arr w aG) n = st.g
  a : (val32 s.mem B (arr w aA) (n + 1) : Int) = st.a
  b : (val32 s.mem B (arr w aB) (n + 1) : Int) = st.b
  d : s.mem.readW (off B (arr w aW + wD)) 64 = BitVec.ofInt 64 st.d
  iv : (s.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv
  p : val32 s.mem B (arr w aMz) (n + 1) = p

theorem StateAt.stG {s : State} {B : Addr} {w n p iv : Nat} {st : Divstep.W32.IState}
    (h : StateAt s B w n p iv st) : StateG s B w n st := ⟨h.f, h.g, h.d⟩

/-! ## The divsteps -/

/-- The words the batch's divsteps leave. -/
abbrev mat (st : Divstep.W32.IState) : MSt := msteps 30 (MSt.init st.d st.f st.g)

/-- A signed number is its low digit modulo `2^32`. -/
theorem sv_mod (m : Mem) (B : Addr) (d n : Nat) (hn : 1 ≤ n) :
    sv m B d n % 2 ^ 32 = (w32 m B d : Int) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have e : val32 m B d (k + 1) = w32 m B d + 2 ^ 32 * val32 m B (d + 4) k := rfl
  unfold sv
  rw [e, show 32 * (k + 1) = 32 + 32 * k by omega, Int.pow_add]
  have hw := (m.readW (off B d) 32).isLt
  push_cast
  rw [Int.mul_assoc 4294967296]
  generalize (2 : Int) ^ (32 * k) * (m.readW (off B (d + 4 * (k + 1))) 32).toInt = Q
  simp only [w32] at hw ⊢
  omega

/-- `save`: `d` and the matrix stored to the window. -/
theorem save_ok {t : State} {B : Addr} {Z w N n : Nat} (h : Ctx t B Z w N n) :
    WP isa (.block save) t fun u => (u.mem = ((((t.mem.writeW (off B (arr w aW)) (t.gpr .t6)).writeW
      (off B (arr w aW + 8)) (t.gpr .t1)).writeW (off B (arr w aW + 16)) (t.gpr .t2)).writeW
      (off B (arr w aW + 24)) (t.gpr .t3)).writeW (off B (arr w aW + 32)) (t.gpr .t4)) ∧ Keep [.a4] t u := by
  have hW : aW < N := by have := h.room; unfold aW; omega
  have fW := h.ws.arr_fit hW
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  have hnw := h.ws.nowrap
  have := arr_al w aW
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have hs := h.ws.scr
  brun [exec_li, save, List.append_assoc, (show aW < 2048 by decide), wD, wU, wV, wQ, wR, runBlock_ptr B w, h.ws.s10, h.ws.s11, exec_store_d,
    hs.st (show arr w aW + 8 ≤ Z by omega), hs.st (show arr w aW + 8 + 8 ≤ Z by omega),
    hs.st (show arr w aW + 16 + 8 ≤ Z by omega), hs.st (show arr w aW + 24 + 8 ≤ Z by omega),
    hs.st (show arr w aW + 32 + 8 ≤ Z by omega),
    hs.al8 (show arr w aW + 8 ≤ Z by omega) (by omega), hs.al8 (show arr w aW + 8 + 8 ≤ Z by omega) (by omega),
    hs.al8 (show arr w aW + 16 + 8 ≤ Z by omega) (by omega),
    hs.al8 (show arr w aW + 24 + 8 ≤ Z by omega) (by omega),
    hs.al8 (show arr w aW + 32 + 8 ≤ Z by omega) (by omega)]

/-- The words of `save`'s stores, read back. -/
theorem save_read (m : Mem) (B : Addr) (d : Nat) (hd : d + 40 ≤ 2 ^ 64) (a b c e f : BitVec 64) :
    let m' := ((((m.writeW (off B d) a).writeW (off B (d + 8)) b).writeW (off B (d + 16)) c).writeW
      (off B (d + 24)) e).writeW (off B (d + 32)) f
    m'.readW (off B d) 64 = a ∧ m'.readW (off B (d + 8)) 64 = b ∧ m'.readW (off B (d + 16)) 64 = c ∧
      m'.readW (off B (d + 24)) 64 = e ∧ m'.readW (off B (d + 32)) 64 = f ∧ Outside B d 40 m m' := by
  intro m'
  have o1 := writeW64_outside m B (d := d) a (by omega)
  have o2 := writeW64_outside (m.writeW (off B d) a) B (d := d + 8) b (by omega)
  have o3 := writeW64_outside ((m.writeW (off B d) a).writeW (off B (d + 8)) b) B (d := d + 16) c (by omega)
  have o4 := writeW64_outside (((m.writeW (off B d) a).writeW (off B (d + 8)) b).writeW (off B (d + 16)) c) B
    (d := d + 24) e (by omega)
  have o5 := writeW64_outside ((((m.writeW (off B d) a).writeW (off B (d + 8)) b).writeW (off B (d + 16)) c).writeW
    (off B (d + 24)) e) B (d := d + 32) f (by omega)
  refine ⟨?_, ?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _, ?_⟩
  · rw [Outside.readW64 o5 (by omega) (by omega), Outside.readW64 o4 (by omega) (by omega),
      Outside.readW64 o3 (by omega) (by omega), Outside.readW64 o2 (by omega) (by omega),
      Mem.readW_writeW_self64]
  · rw [Outside.readW64 o5 (by omega) (by omega), Outside.readW64 o4 (by omega) (by omega),
      Outside.readW64 o3 (by omega) (by omega), Mem.readW_writeW_self64]
  · rw [Outside.readW64 o5 (by omega) (by omega), Outside.readW64 o4 (by omega) (by omega),
      Mem.readW_writeW_self64]
  · rw [Outside.readW64 o5 (by omega) (by omega), Mem.readW_writeW_self64]
  · exact ((((o1.mono (by omega) (by omega)).trans (o2.mono (by omega) (by omega))).trans
      (o3.mono (by omega) (by omega))).trans (o4.mono (by omega) (by omega))).trans (o5.mono (by omega) (by omega))

/-- `start`, 30 divsteps and `save`: `d` and the matrix of 30 divsteps from
`(d, f, g)` in the window. -/
theorem head_ok {s : State} {B : Addr} {Z w N n : Nat} {st : Divstep.W32.IState}
    (h : Ctx s B Z w N n) (hst : StateG s B w n st) (hN : N ≤ 256)
    (hd : |st.d| + 60 < 2 ^ 62) (hf : st.f % 2 = 1) :
    WP isa (.block (start ++ wsteps 30 ++ save)) s fun t => Ctx t B Z w N n ∧
      Keys.Frame B w [aW] [] s.mem t.mem ∧ Outside B (arr w aW) 40 s.mem t.mem ∧
      t.mem.readW (off B (arr w aW + wD)) 64 = BitVec.ofInt 64 (mat st).d ∧
      t.mem.readW (off B (arr w aW + wU)) 64 = BitVec.ofInt 64 (mat st).u ∧
      t.mem.readW (off B (arr w aW + wV)) 64 = BitVec.ofInt 64 (mat st).v ∧
      t.mem.readW (off B (arr w aW + wQ)) 64 = BitVec.ofInt 64 (mat st).q ∧
      t.mem.readW (off B (arr w aW + wR)) 64 = BitVec.ofInt 64 (mat st).r ∧ Keep kRegs s t := by
  have hW : aW < N := by have := h.room; unfold aW; omega
  have hFN : aF < N := by have := h.room; unfold aF; omega
  have hGN : aG < N := by have := h.room; unfold aG; omega
  have fW := h.ws.arr_fit hW
  have fF := h.ws.arr_fit hFN
  have fG := h.ws.arr_fit hGN
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  have hnw := h.ws.nowrap
  have hs := h.ws.scr
  have := arr_al w aW
  have := arr_al4 w aF
  have := arr_al4 w aG
  rw [WP.block_append_iff, WP.block_append_iff]
  -- The start: the low digits, `d` and the identity.
  have hs1 : WP isa (.block start) s fun t => (regsW t = ⟨BitVec.ofInt 64 st.d,
      (s.mem.readW (off B (arr w aF)) 32).setWidth 64, (s.mem.readW (off B (arr w aG)) 32).setWidth 64,
      BitVec.ofNat 64 1, BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 1⟩ ∧ t.mem = s.mem) ∧
      Keep kRegs s t := by
    have hd0 : s.mem.readW (off B (arr w aW)) 64 = BitVec.ofInt 64 st.d := by
      simpa only [wD, Nat.add_zero] using hst.d
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li, start, ldW, List.append_assoc, (show aW < 2048 by decide), (show aF < 2048 by decide),
      (show aG < 2048 by decide), regsW, wD, runBlock_ptr B w, h.ws.s10, h.ws.s11, exec_load_w, fin64_exec_li_zero,
      hs.ld (show arr w aF + 4 ≤ Z by omega), hs.ld (show arr w aG + 4 ≤ Z by omega),
      hs.ld (show arr w aW + 8 ≤ Z by omega), Scr.al4 hs (show arr w aF + 4 ≤ Z by omega) (by omega),
      Scr.al4 hs (show arr w aG + 4 ≤ Z by omega) (by omega), hs.al8 (show arr w aW + 8 ≤ Z by omega) (by omega),
      hd0]
    try rfl
  refine WP.mono hs1 fun t1 ⟨⟨r1, m1⟩, k1⟩ => ?_
  refine WP.mono (wsteps_ok 30 t1) fun t2 ⟨⟨r2, m2⟩, k2⟩ => ?_
  have h2 := h.of_keep (Keep.trans' k1 k2)
  -- The words of the divsteps.
  have rel : (regsW t1).rel (MSt.init st.d st.f st.g) 30 := by
    rw [r1]
    have e := sv_mod s.mem B (arr w aF) n h.npos
    have e' := sv_mod s.mem B (arr w aG) n h.npos
    rw [hst.f] at e
    rw [hst.g] at e'
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · show ((((s.mem.readW (off B (arr w aF)) 32).setWidth 64).toNat : Nat) : Int) % 2 ^ 30 = st.f % 2 ^ 30
      rw [toNat_ext32, show (2 : Int) ^ 30 = 2 ^ 30 from rfl,
        ← Int.emod_emod_of_dvd st.f (show (2 : Int) ^ 30 ∣ 2 ^ 32 by decide), e]
    · show ((((s.mem.readW (off B (arr w aG)) 32).setWidth 64).toNat : Nat) : Int) % 2 ^ 30 = st.g % 2 ^ 30
      rw [toNat_ext32, ← Int.emod_emod_of_dvd st.g (show (2 : Int) ^ 30 ∣ 2 ^ 32 by decide), e']
  have R := Divstep.wsteps_rel (by decide) rel (by simpa [MSt.init] using hd) hf 30 (Nat.le_refl _)
  rw [← r2] at R
  obtain ⟨Rd, Ru, Rv, Rq, Rr, -, -⟩ := R
  refine WP.mono (save_ok h2) fun t3 ⟨m3, k3⟩ => ?_
  obtain ⟨e0, e1, e2, e3, e4, out⟩ := save_read t2.mem B (arr w aW) (by omega) (t2.gpr .t6) (t2.gpr .t1)
    (t2.gpr .t2) (t2.gpr .t3) (t2.gpr .t4)
  rw [← m3] at e0 e1 e2 e3 e4 out
  rw [m2, m1] at out
  have k : Keep kRegs s t3 := Keep.trans' (Keep.trans' k1 k2) (k3.mono (by decide))
  refine ⟨h.of_keep k, Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out) (by omega)
    (by simp), out, ?_, ?_, ?_, ?_, ?_, k⟩
  · simpa only [wD, Nat.add_zero] using e0.trans Rd
  · exact e1.trans Ru
  · exact e2.trans Rv
  · exact e3.trans Rq
  · exact e4.trans Rr

/-! ## The update -/

theorem natAbs_bnd {u v : Int} (h : |u| + |v| ≤ 2 ^ 30) : u.natAbs + v.natAbs ≤ 2 ^ 30 := by
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h; omega

/-- A number below `2^(32 n)` in `n + 1` digits, as a signed number. -/
theorem sv_of_val {m : Mem} {B : Addr} {d n : Nat} {a : Int} (h : (val32 m B d (n + 1) : Int) = a)
    (h1 : a < 2 ^ (32 * n)) : sv m B d n = a :=
  sv_of_eq (q := 0) (by rw [h, Int.mul_zero, Int.add_zero]) (by
    have : (0 : Int) ≤ 2 ^ (32 * n + 31) := by exact_mod_cast Nat.zero_le _
    omega) (by
    have : (2 : Int) ^ (32 * n) ≤ 2 ^ (32 * n + 31) := by exact_mod_cast Nat.pow_le_pow_right (by decide) (by omega)
    omega)

/-- `updateG`: the new `f` and `g` from the matrix in the window. -/
theorem updateG_ok {s : State} {B : Addr} {Z w N n cap : Nat} {st : Divstep.W32.IState}
    (h : Ctx s B Z w N n) (hN : N ≤ 256)
    (hf : sv s.mem B (arr w aF) n = st.f) (hg : sv s.mem B (arr w aG) n = st.g)
    (hU : s.mem.readW (off B (arr w aW + wU)) 64 = BitVec.ofInt 64 (mat st).u)
    (hV : s.mem.readW (off B (arr w aW + wV)) 64 = BitVec.ofInt 64 (mat st).v)
    (hQ : s.mem.readW (off B (arr w aW + wQ)) 64 = BitVec.ofInt 64 (mat st).q)
    (hR : s.mem.readW (off B (arr w aW + wR)) 64 = BitVec.ofInt 64 (mat st).r)
    (hodd : st.f % 2 = 1) (hfc : |st.f| ≤ cap) (hgc : |st.g| ≤ cap) (hcap : cap < 2 ^ (32 * n + 1)) :
    WP isa updateG s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aT1, aT2, aF, aG] [] s.mem t.mem ∧
      sv t.mem B (arr w aF) n = (mat st).f ∧ sv t.mem B (arr w aG) n = (mat st).g ∧
      2 ^ 30 * (mat st).f = (mat st).u * st.f + (mat st).v * st.g ∧
      2 ^ 30 * (mat st).g = (mat st).q * st.f + (mat st).r * st.g ∧
      |(mat st).f| ≤ cap ∧ |(mat st).g| ≤ cap ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  obtain ⟨bu, bq⟩ := Divstep.msteps_bnd st.d st.f st.g 30
  obtain ⟨ef, eg⟩ := Divstep.msteps_mat (d := st.d) (g := st.g) hodd 30
  change 2 ^ 30 * (mat st).f = (mat st).u * st.f + (mat st).v * st.g at ef
  change 2 ^ 30 * (mat st).g = (mat st).q * st.f + (mat st).r * st.g at eg
  change |(mat st).u| + |(mat st).v| ≤ 2 ^ 30 at bu
  change |(mat st).q| + |(mat st).r| ≤ 2 ^ 30 at bq
  have nfc : |(mat st).f| ≤ cap := by
    have := Divstep.W32.comb_le bu hfc hgc
    rw [← ef, abs_mul, abs_of_pos (by decide : (0 : Int) < 2 ^ 30)] at this
    exact le_of_mul_le_mul_left this (by decide)
  have ngc : |(mat st).g| ≤ cap := by
    have := Divstep.W32.comb_le bq hfc hgc
    rw [← eg, abs_mul, abs_of_pos (by decide : (0 : Int) < 2 ^ 30)] at this
    exact le_of_mul_le_mul_left this (by decide)
  have rng : ∀ z : Int, |z| ≤ cap → -2 ^ (32 * n + 31) ≤ z ∧ z < 2 ^ (32 * n + 31) := by
    intro z hz
    rw [abs_le] at hz
    have : (2 : Int) ^ (32 * n + 1) ≤ 2 ^ (32 * n + 31) := by exact_mod_cast Nat.pow_le_pow_right (by decide) (by omega)
    have : (cap : Int) < 2 ^ (32 * n + 1) := by exact_mod_cast hcap
    omega
  have nF : aF < N := by unfold aF; omega
  have nG : aG < N := by unfold aG; omega
  have n1 : aT1 < N := by unfold aT1; omega
  have n2 : aT2 < N := by unfold aT2; omega
  have nW : aW < N := by unfold aW; omega
  have w8 : ∀ o, o + 8 ≤ 48 → o + 64 / 8 ≤ S w := fun o ho => by have := h.wbig; omega
  have hk2 : 4 * (n + 1 + 1) ≤ S w := by omega
  simp only [updateG, seqs]
  -- 1, 2: `u f + v g` and `q f + r g`.
  rw [WP.seq_iff]
  refine WP.mono (lin_ok h n1 nF nG hN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hU hV (natAbs_bnd bu)) fun t1 ⟨h1, K1, e1, k1⟩ => ?_
  rw [hf, hg, ← ef] at e1
  rw [WP.seq_iff]
  refine WP.mono (lin_ok h1 n2 nF nG hN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [keep_word K1 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact hQ)
    (by rw [keep_word K1 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact hR) (natAbs_bnd bq))
    fun t2 ⟨h2, K2, e2, k2⟩ => ?_
  rw [keep_sv K1 (by omega) (by decide) (by simp) (fit _ nF), keep_sv K1 (by omega) (by decide) (by simp)
    (fit _ nG), hf, hg, ← eg] at e2
  -- 3, 4: the new `f` and `g`.
  rw [WP.seq_iff]
  refine WP.mono (shr_ok h2 nF n1 hN (by decide) (z := (mat st).f)
    (by rw [keep_sv K2 hk2 (by decide) (by simp) (fit _ n1)]; exact e1) (rng _ nfc).1 (rng _ nfc).2)
    fun t3 ⟨h3, K3, e3, k3⟩ => ?_
  refine WP.mono (shr_ok h3 nG n2 hN (by decide) (z := (mat st).g)
    (by rw [keep_sv K3 hk2 (by decide) (by simp) (fit _ n2)]; exact e2) (rng _ ngc).1 (rng _ ngc).2)
    fun t4 ⟨h4, K4, e4, k4⟩ => ?_
  have k : Keep kRegs s t4 := Keep.trans' (Keep.trans' (Keep.trans' k1 k2) k3) k4
  refine ⟨h.of_keep k,
    (K1.mono (by simp)).trans ((K2.mono (by simp)).trans ((K3.mono (by simp)).trans (K4.mono (by simp)))),
    ?_, e4, ef, eg, nfc, ngc, k⟩
  rw [keep_sv K4 (by omega) (by decide) (by simp) (fit _ nF), e3]

/-- `updateAB`: the new `a` and `b` from the matrix in the window. -/
theorem updateAB_ok {s : State} {B : Addr} {Z w N n p iv : Nat} {st : Divstep.W32.IState}
    (h : Ctx s B Z w N n) (hN : N ≤ 256)
    (ha : (val32 s.mem B (arr w aA) (n + 1) : Int) = st.a) (hb : (val32 s.mem B (arr w aB) (n + 1) : Int) = st.b)
    (hp : val32 s.mem B (arr w aMz) (n + 1) = p) (hiv : (s.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv)
    (hU : s.mem.readW (off B (arr w aW + wU)) 64 = BitVec.ofInt 64 (mat st).u)
    (hV : s.mem.readW (off B (arr w aW + wV)) 64 = BitVec.ofInt 64 (mat st).v)
    (hQ : s.mem.readW (off B (arr w aW + wQ)) 64 = BitVec.ofInt 64 (mat st).q)
    (hR : s.mem.readW (off B (arr w aW + wR)) 64 = BitVec.ofInt 64 (mat st).r)
    (ha0 : 0 ≤ st.a) (ha1 : st.a < p) (hb0 : 0 ≤ st.b) (hb1 : st.b < p) (hpA : p < 2 ^ (32 * n)) (hp0 : 0 < p)
    (hinv : (p * iv + 1) % 2 ^ 32 = 0) :
    WP isa updateAB s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aT1, aT2, aA, aB, aT3] [] s.mem t.mem ∧
      (val32 t.mem B (arr w aA) (n + 1) : Int) = (Divstep.W32.batch 30 p iv st).a ∧
      (val32 t.mem B (arr w aB) (n + 1) : Int) = (Divstep.W32.batch 30 p iv st).b ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  obtain ⟨bu, bq⟩ := Divstep.msteps_bnd st.d st.f st.g 30
  change |(mat st).u| + |(mat st).v| ≤ 2 ^ 30 at bu
  change |(mat st).q| + |(mat st).r| ≤ 2 ^ 30 at bq
  have hpI : (p : Int) < 2 ^ (32 * n) := by exact_mod_cast hpA
  have sa := sv_of_val ha (by omega)
  have sb := sv_of_val hb (by omega)
  have nA : aA < N := by unfold aA; omega
  have nB : aB < N := by unfold aB; omega
  have n1 : aT1 < N := by unfold aT1; omega
  have n2 : aT2 < N := by unfold aT2; omega
  have n3 : aT3 < N := by unfold aT3; omega
  have nM : aMz < N := by unfold aMz; omega
  have nW : aW < N := by unfold aW; omega
  have w8 : ∀ o, o + 8 ≤ 48 → o + 64 / 8 ≤ S w := fun o ho => by have := h.wbig; omega
  have hk : 4 * (n + 1) ≤ S w := by omega
  have hk2 : 4 * (n + 1 + 1) ≤ S w := by omega
  simp only [updateAB, seqs]
  -- 5, 6: `u a + v b` and `q a + r b`.
  rw [WP.seq_iff]
  refine WP.mono (lin_ok h n1 nA nB hN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hU hV (natAbs_bnd bu)) fun t5 ⟨h5, K5, e5, k5⟩ => ?_
  rw [sa, sb] at e5
  rw [WP.seq_iff]
  refine WP.mono (lin_ok h5 n2 nA nB hN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [keep_word K5 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact hQ)
    (by rw [keep_word K5 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact hR)
    (natAbs_bnd bq)) fun t6 ⟨h6, K6, e6, k6⟩ => ?_
  rw [keep_sv K5 (by omega) (by decide) (by simp) (fit _ nA), keep_sv K5 (by omega) (by decide) (by simp)
    (fit _ nB), sa, sb] at e6
  have K16 : Keys.Frame B w [aT1, aT2] [] s.mem t6.mem := (K5.mono (by simp)).trans (K6.mono (by simp))
  have small : ∀ x y : Int, |x| + |y| ≤ 2 ^ 30 → |x * st.a + y * st.b| ≤ 2 ^ 31 * (p : Int) := by
    intro x y hxy
    have := Divstep.W32.comb_le hxy (p := p) (by rw [abs_of_nonneg ha0]; omega) (by rw [abs_of_nonneg hb0]; omega)
    have : (0 : Int) ≤ p := by omega
    calc |x * st.a + y * st.b| ≤ 2 ^ 30 * (p : Int) := by assumption
      _ ≤ 2 ^ 31 * (p : Int) := Int.mul_le_mul_of_nonneg_right (by decide) this
  -- 7, 8: the new `a` and `b`.
  rw [WP.seq_iff]
  refine WP.mono (mred_ok h6 n1 nA hN n3 nM (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [keep_val K16 hk (by decide) (by simp) (fit _ nM)]; exact hp) hpA hp0
    (by rw [keep_word K16 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW)]; exact hiv) hinv
    (by rw [keep_sv K6 hk2 (by decide) (by simp) (fit _ n1)]; exact e5) (small _ _ bu))
    fun t7 ⟨h7, K7, e7, k7⟩ => ?_
  refine WP.mono (mred_ok h7 n2 nB hN n3 nM (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [keep_val K7 hk (by decide) (by simp) (fit _ nM), keep_val K16 hk (by decide) (by simp) (fit _ nM), hp])
    hpA hp0
    (by rw [keep_word K7 (w8 _ (by decide)) (by decide) (by simp) (fit _ nW), keep_word K16 (w8 _ (by decide))
      (by decide) (by simp) (fit _ nW), hiv]) hinv
    (by rw [keep_sv K7 hk2 (by decide) (by simp) (fit _ n2)]; exact e6) (small _ _ bq))
    fun t8 ⟨h8, K8, e8, k8⟩ => ?_
  have k : Keep kRegs s t8 := Keep.trans' (Keep.trans' (Keep.trans' k5 k6) k7) k8
  refine ⟨h.of_keep k, (K16.mono (by simp)).trans ((K7.mono (by simp)).trans (K8.mono (by simp))), ?_, ?_, k⟩
  · rw [keep_val K8 hk (by decide) (by simp) (fit _ nA), e7, Divstep.W32.batch_a]
  · rw [e8, Divstep.W32.batch_b]

/-- `(batch 30 p iv st).f`, `.g`: those of the batch's matrix. -/
theorem batch_fg {p iv : Int} {st : Divstep.W32.IState} (hodd : st.f % 2 = 1) :
    (Divstep.W32.batch 30 p iv st).f = (mat st).f ∧ (Divstep.W32.batch 30 p iv st).g = (mat st).g := by
  obtain ⟨ef, eg⟩ := Divstep.msteps_mat (d := st.d) (g := st.g) hodd 30
  change 2 ^ 30 * (mat st).f = (mat st).u * st.f + (mat st).v * st.g at ef
  change 2 ^ 30 * (mat st).g = (mat st).q * st.f + (mat st).r * st.g at eg
  refine ⟨?_, ?_⟩
  · show ((mat st).u * st.f + (mat st).v * st.g) / 2 ^ 30 = (mat st).f
    rw [← ef, Int.mul_ediv_cancel_left _ (by decide)]
  · show ((mat st).q * st.f + (mat st).r * st.g) / 2 ^ 30 = (mat st).g
    rw [← eg, Int.mul_ediv_cancel_left _ (by decide)]

/-! ## A batch -/

/-- The count of the batches left, decremented. -/
theorem dec_ok {t : State} {c : Nat} (h7 : t.gpr .s7 = BitVec.ofNat 64 (c + 1)) :
    WP isa (.block [.addi .s7 .s7 (-1)]) t fun u =>
      (u.gpr .s7 = BitVec.ofNat 64 c ∧ u.mem = t.mem) ∧ Keep [.s7] t u := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [exec_li, h7]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A batch: the next state, and the count of the batches left, `c`, in `s7`. -/
theorem batch_ok {s : State} {B : Addr} {Z w N n c p iv cap : Nat} {st : Divstep.W32.IState}
    (h : Ctx s B Z w N n) (h7 : s.gpr .s7 = BitVec.ofNat 64 (c + 1)) (hst : StateAt s B w n p iv st)
    (hN : N ≤ 256) (hd : |st.d| + 60 < 2 ^ 62) (hodd : st.f % 2 = 1) (hfc : |st.f| ≤ cap) (hgc : |st.g| ≤ cap)
    (hcap : cap < 2 ^ (32 * n + 1)) (ha0 : 0 ≤ st.a) (ha1 : st.a < p) (hb0 : 0 ≤ st.b) (hb1 : st.b < p)
    (hpA : p < 2 ^ (32 * n)) (hp0 : 0 < p) (hinv : (p * iv + 1) % 2 ^ 32 = 0) :
    WP isa batch s fun t => Ctx t B Z w N n ∧ StateAt t B w n p iv (Divstep.W32.batch 30 p iv st) ∧
      t.gpr .s7 = BitVec.ofNat 64 c ∧
      Keys.Frame B w [aF, aG, aA, aB, aT1, aT2, aT3, aW] [] s.mem t.mem ∧ Keep (.s7 :: kRegs) s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  have hnw := h.ws.nowrap
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have nW : aW < N := by unfold aW; omega
  have nM : aMz < N := by unfold aMz; omega
  have nF : aF < N := by unfold aF; omega
  have nG : aG < N := by unfold aG; omega
  have nA : aA < N := by unfold aA; omega
  have nB : aB < N := by unfold aB; omega
  have hk : 4 * (n + 1) ≤ S w := by have := h.nw; omega
  simp only [batch, seqs, update]
  rw [WP.seq_iff]
  refine WP.mono (head_ok h hst.stG hN hd hodd) fun t1 ⟨h1, K1, out1, d1, u1, v1, q1, r1, k1⟩ => ?_
  have fW := fit _ nW
  have iv1 : (t1.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv := by
    rw [Outside.readW64 out1 (by unfold wIv; omega) (by unfold wIv; omega)]; exact hst.iv
  rw [WP.seq_iff, WP.seq_iff]
  refine WP.mono (updateG_ok h1 hN (cap := cap)
    (by rw [keep_sv K1 (by omega) (by decide) (by simp) (fit _ nF)]; exact hst.f)
    (by rw [keep_sv K1 (by omega) (by decide) (by simp) (fit _ nG)]; exact hst.g) u1 v1 q1 r1
    hodd hfc hgc hcap) fun t2 ⟨h2, K2, ef, eg, _, _, _, _, k2⟩ => ?_
  have wd2 : ∀ o, o + 8 ≤ 48 → t2.mem.readW (off B (arr w aW + o)) 64 = t1.mem.readW (off B (arr w aW + o)) 64 :=
    fun o ho => keep_word K2 (by omega) (by decide) (by simp) (fit _ nW)
  refine WP.mono (updateAB_ok h2 hN
    (by rw [keep_val K2 hk (by decide) (by simp) (fit _ nA), keep_val K1 hk (by decide) (by simp) (fit _ nA)];
        exact hst.a)
    (by rw [keep_val K2 hk (by decide) (by simp) (fit _ nB), keep_val K1 hk (by decide) (by simp) (fit _ nB)];
        exact hst.b)
    (by rw [keep_val K2 hk (by decide) (by simp) (fit _ nM), keep_val K1 hk (by decide) (by simp) (fit _ nM)];
        exact hst.p)
    (by rw [wd2 _ (by decide)]; exact iv1) (by rw [wd2 _ (by decide)]; exact u1) (by rw [wd2 _ (by decide)]; exact v1)
    (by rw [wd2 _ (by decide)]; exact q1) (by rw [wd2 _ (by decide)]; exact r1)
    ha0 ha1 hb0 hb1 hpA hp0 hinv) fun t3 ⟨h3, K3, ea, eb, k3⟩ => ?_
  have wd : ∀ o, o + 8 ≤ 48 → t3.mem.readW (off B (arr w aW + o)) 64 = t1.mem.readW (off B (arr w aW + o)) 64 :=
    fun o ho => (keep_word K3 (by omega) (by decide) (by simp) (fit _ nW)).trans (wd2 o ho)
  have s73 : t3.gpr .s7 = BitVec.ofNat 64 (c + 1) :=
    ((Keep.trans' (Keep.trans' k1 k2) k3).gpr (by decide)).trans h7
  refine WP.mono (dec_ok s73) fun t4 ⟨⟨r7, m4⟩, k4⟩ => ?_
  obtain ⟨nf, ng⟩ := batch_fg (p := p) (iv := iv) hodd
  have k : Keep (.s7 :: kRegs) s t4 :=
    Keep.trans' ((Keep.trans' (Keep.trans' k1 k2) k3).mono (by decide)) (k4.mono (by decide))
  refine ⟨⟨h3.ws.of_keep k4, (k4.gpr (by decide)).trans h3.s8, h.npos, h.nw, h.room, h.wbig⟩,
    ⟨?_, ?_, by rw [m4]; exact ea, by rw [m4]; exact eb, ?_, ?_, ?_⟩, r7,
    by rw [m4]; exact (K1.mono (by simp)).trans ((K2.mono (by simp)).trans (K3.mono (by simp))), k⟩
  · rw [m4, keep_sv K3 (by omega) (by decide) (by simp) (fit _ nF), ef, nf]
  · rw [m4, keep_sv K3 (by omega) (by decide) (by simp) (fit _ nG), eg, ng]
  · rw [m4, wd _ (by decide), d1, Divstep.W32.batch_d]
  · rw [m4, wd _ (by decide)]; exact iv1
  · rw [m4, keep_val K3 hk (by decide) (by simp) (fit _ nM), keep_val K2 hk (by decide) (by simp) (fit _ nM),
      keep_val K1 hk (by decide) (by simp) (fit _ nM)]
    exact hst.p

/-- A batch of `f` and `g` alone: the next `d`, `f` and `g`. -/
theorem batchG_ok {s : State} {B : Addr} {Z w N n c p iv cap : Nat} {st : Divstep.W32.IState}
    (h : Ctx s B Z w N n) (h7 : s.gpr .s7 = BitVec.ofNat 64 (c + 1)) (hst : StateG s B w n st)
    (hN : N ≤ 256) (hd : |st.d| + 60 < 2 ^ 62) (hodd : st.f % 2 = 1) (hfc : |st.f| ≤ cap) (hgc : |st.g| ≤ cap)
    (hcap : cap < 2 ^ (32 * n + 1)) :
    WP isa batchG s fun t => Ctx t B Z w N n ∧ StateG t B w n (Divstep.W32.batch 30 p iv st) ∧
      t.gpr .s7 = BitVec.ofNat 64 c ∧
      Keys.Frame B w [aF, aG, aT1, aT2, aW] [] s.mem t.mem ∧ Keep (.s7 :: kRegs) s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.wbig
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have nW : aW < N := by unfold aW; omega
  have nF : aF < N := by unfold aF; omega
  have nG : aG < N := by unfold aG; omega
  have := h.nw
  simp only [batchG, seqs]
  rw [WP.seq_iff]
  refine WP.mono (head_ok h hst hN hd hodd) fun t1 ⟨h1, K1, _, d1, u1, v1, q1, r1, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (updateG_ok h1 hN (cap := cap)
    (by rw [keep_sv K1 (by omega) (by decide) (by simp) (fit _ nF)]; exact hst.f)
    (by rw [keep_sv K1 (by omega) (by decide) (by simp) (fit _ nG)]; exact hst.g) u1 v1 q1 r1
    hodd hfc hgc hcap) fun t2 ⟨h2, K2, ef, eg, _, _, _, _, k2⟩ => ?_
  have s72 : t2.gpr .s7 = BitVec.ofNat 64 (c + 1) := ((Keep.trans' k1 k2).gpr (by decide)).trans h7
  refine WP.mono (dec_ok s72) fun t3 ⟨⟨r7, m3⟩, k3⟩ => ?_
  obtain ⟨nf, ng⟩ := batch_fg (p := p) (iv := iv) hodd
  have k : Keep (.s7 :: kRegs) s t3 := Keep.trans' ((Keep.trans' k1 k2).mono (by decide)) (k3.mono (by decide))
  refine ⟨⟨h2.ws.of_keep k3, (k3.gpr (by decide)).trans h2.s8, h.npos, h.nw, h.room, h.wbig⟩,
    ⟨by rw [m3, ef, nf], by rw [m3, eg, ng], ?_⟩, r7,
    by rw [m3]; exact (K1.mono (by simp)).trans (K2.mono (by simp)), k⟩
  rw [m3, keep_word K2 (by unfold wD; omega) (by decide) (by simp) (fit _ nW), d1, Divstep.W32.batch_d]

end VG.Proof.Rsa.RISCV64.InvBatch
