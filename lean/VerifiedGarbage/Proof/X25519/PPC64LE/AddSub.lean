module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
public import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
public import VerifiedGarbage.Proof.X25519.PPC64LE.Product
public import VerifiedGarbage.Proof.X25519.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X25519 on PPC64LE: sums and differences

`add o x y` and `sub o x y` store at `o` a number congruent to `[x] + [y]`
and `[x] - [y]` (`add_ok`, `sub_ok`); `o` may be `x` or `y`, since every
load comes before the stores. Both run a chain of four carrying operations
over the doublewords of `[x]` and `[y]` (`chain_ok`): `addc`/`adde` for the
sum, whose carry is folded in as `38 t` twice (`foldTop_ok`), and
`subc`/`sube` for the difference, from which 38 is subtracted if it borrowed
(`2²⁵⁶ ≡ 38`), twice (`borrowFold_ok`; the second does not borrow).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE
open VG.Spec.X25519 (P)

section
variable {b : Addr}

/-- A word the pass has not written yet (the pass writes `[o, o + 4k)`). -/
theorem wd_pass {s0 s : State} (hc : Ctx b s0) {o k d : Nat}
    (hf : Frame [⟨s0.gpr .r6 + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem)
    (hd : d + 4 ≤ o ∨ o + 4 * k ≤ d) (hd' : d + 4 ≤ 4096) (ho : o + 4 * k ≤ 4096) :
    wd s.mem b d = wd s0.mem b d := by
  rw [hc.r6] at hf
  exact wd_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd (by omega_using [hd']) (by omega_using [ho])

/-! ## The borrow chain -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_subc {d n m : Reg}
    (k : ∀ s', UpdC s s' d ((s.gpr n).toNat + (2 ^ 64 - 1 - (s.gpr m).toNat) + 1) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subc d n m :: is)) s Q := by
  have := (s.gpr n).isLt
  exact WP.cons exec_subc (k _ (UpdC.writeCarry _ _ (by omega)))

theorem wp_sube {d n m : Reg}
    (k : ∀ s', UpdC s s' d ((s.gpr n).toNat + (2 ^ 64 - 1 - (s.gpr m).toNat) + s.ca.toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.sube d n m :: is)) s Q := by
  have := (s.gpr n).isLt; have : s.ca.toNat ≤ 1 := Bool.toNat_le _
  exact WP.cons exec_sube (k _ (UpdC.writeCarry _ _ (by omega)))

end

/-! ## A chain over the doublewords of two elements -/

/-- Step `k` of the chain: `addc`/`adde`, or with `sub` `subc`/`sube`. -/
def copW (sub : Bool) (k : Nat) (d : Reg) : Instr :=
  if sub then (if k = 0 then .subc d d .r4 else .sube d d .r4)
  else (if k = 0 then .addc d d .r4 else .adde d d .r4)

/-- What step `k` adds of the second operand's word `y`. -/
def cvW (sub : Bool) (y : Nat) : Nat := if sub then 2 ^ 64 - 1 - y else y

/-- The carry into step `k` (`c` the carry out of step `k - 1`). -/
def cinW (sub : Bool) (k c : Nat) : Nat := if k = 0 then (if sub then 1 else 0) else c

/-- The code of step `k` over `[x]` and `[y]`. -/
def cstep (sub : Bool) (x y k : Nat) : List Instr :=
  [.load .d (wreg k) .r6 (x + 8 * k), .load .d .r4 .r6 (y + 8 * k), copW sub k (wreg k)]

theorem addW_eq (x y : Nat) : addW x y = cstep false x y := by
  funext k; unfold addW cstep copW; simp

theorem subW_eq (x y : Nat) : subW x y = cstep true x y := by
  funext k; unfold subW cstep copW; simp

/-- Two doublewords of the working space loaded into `d` and `r4`. -/
theorem ld2_ok {s : State} (hc : Ctx b s) {d : Reg} (hd4 : d ≠ .r4) (hd6 : d ≠ .r6) {x y : Nat}
    (hx : x + 8 ≤ 4096) (hx4 : x % 4 = 0) (hy : y + 8 ≤ 4096) (hy4 : y % 4 = 0)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', (s'.gpr d).toNat = dw s.mem b x → (s'.gpr .r4).toNat = dw s.mem b y → s'.ca = s.ca →
      Rest [.r4, d] s s' → s'.mem = s.mem → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d d .r6 x :: .load .d .r4 .r6 y :: is)) s Q := by
  refine ldw_ok hc hx hx4 ?_
  have hr1 : Rest [.r4, d] s (s.write d (s.mem.readW (b + BitVec.ofNat 64 x) 64)) :=
    (Upd.write _ _ _).rest (by simp)
  refine ldw_ok (hc.of_rest hr1 (by simp [Ne.symm hd6])) hy hy4 ?_
  refine k _ ?_ ?_ ?_ ?_ ?_
  · rw [RegUpd.gpr_write_of_ne _ _ hd4, RegUpd.gpr_write_self]; rfl
  · rw [RegUpd.gpr_write_self, RegUpd.mem_write]; rfl
  · rw [RegUpd.ca_write, RegUpd.ca_write]
  · exact hr1.trans ((Upd.write _ _ _).rest (by simp))
  · rw [RegUpd.mem_write, RegUpd.mem_write]

theorem cstep_ok (sub : Bool) {k : Nat} (hk : k < 4) {x y : Nat} (hx : x + 32 ≤ 4096)
    (hx4 : x % 4 = 0) (hy : y + 32 ≤ 4096) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (cstep sub x y k)) s fun s' =>
      (s'.gpr (wreg k)).toNat + 2 ^ 64 * s'.ca.toNat =
        dw s.mem b (x + 8 * k) + cvW sub (dw s.mem b (y + 8 * k)) + cinW sub k s.ca.toNat ∧
      Rest [.r4, wreg k] s s' ∧ s'.mem = s.mem := by
  have hw : wreg k ≠ .r4 ∧ wreg k ≠ .r6 := by revert hk; revert k; decide
  unfold cstep
  refine ld2_ok hc hw.1 hw.2 (by omega) (by omega) (by omega) (by omega)
    fun s2 e1 e2 c2 r2 m2 => ?_
  have post : ∀ s3 : State, ∀ v, UpdC s2 s3 (wreg k) v →
      v = dw s.mem b (x + 8 * k) + cvW sub (dw s.mem b (y + 8 * k)) + cinW sub k s.ca.toNat →
      WP isa (.block []) s3 fun s' =>
        (s'.gpr (wreg k)).toNat + 2 ^ 64 * s'.ca.toNat =
          dw s.mem b (x + 8 * k) + cvW sub (dw s.mem b (y + 8 * k)) + cinW sub k s.ca.toNat ∧
        Rest [.r4, wreg k] s s' ∧ s'.mem = s.mem := fun s3 v u3 hv =>
    WP.block_nil ⟨by rw [u3.val, hv], r2.trans (u3.rest (by simp)), by rw [u3.mem, m2]⟩
  cases sub <;> by_cases h0 : k = 0
  · subst h0
    exact wp_addc fun s3 u3 => post s3 _ u3 (by rw [e1, e2]; simp [cvW, cinW])
  · simp only [copW, h0, Bool.false_eq_true, ↓reduceIte]
    exact wp_adde fun s3 u3 => post s3 _ u3 (by rw [e1, e2, c2]; simp [cvW, cinW, h0])
  · subst h0
    exact wp_subc fun s3 u3 => post s3 _ u3 (by rw [e1, e2]; simp [cvW, cinW])
  · simp only [copW, h0, ↓reduceIte]
    exact wp_sube fun s3 u3 => post s3 _ u3 (by rw [e1, e2, c2]; simp [cvW, cinW, h0])

/-- The chain: `rv4 + 2²⁵⁶ CA = X + Y'` (`Y'` the words `cvW`), plus 1 for a
difference. -/
theorem chain_ok (sub : Bool) {x y : Nat} (hx : x + 32 ≤ 4096) (hx4 : x % 4 = 0)
    (hy : y + 32 ≤ 4096) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block ((List.range 4).flatMap (cstep sub x y))) s fun s' =>
      rv4 s' + 2 ^ 256 * s'.ca.toNat =
        val4 (fun k => dw s.mem b (x + 8 * k)) + val4 (fun k => cvW sub (dw s.mem b (y + 8 * k))) +
          (if sub then 1 else 0) ∧
      Rest [.r4, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_singleton, List.append_assoc]
  refine WP.append (cstep_ok sub (k := 0) (by decide) hx hx4 hy hy4 hc) fun s1 ⟨v1, r1, m1⟩ => ?_
  have hc1 := hc.of_rest r1 (by decide)
  refine WP.append (cstep_ok sub (k := 1) (by decide) hx hx4 hy hy4 hc1) fun s2 ⟨v2, r2, m2⟩ => ?_
  have hc2 := hc1.of_rest r2 (by decide)
  refine WP.append (cstep_ok sub (k := 2) (by decide) hx hx4 hy hy4 hc2) fun s3 ⟨v3', r3, m3⟩ => ?_
  have hc3 := hc2.of_rest r3 (by decide)
  refine WP.mono (cstep_ok sub (k := 3) (by decide) hx hx4 hy hy4 hc3)
    fun s4 ⟨v4, r4, m4⟩ => ⟨?_, ?_, by rw [m4, m3, m2, m1]⟩
  · simp only [m1, m2, m3, cinW, Nat.reduceEqDiff, ↓reduceIte] at v1 v2 v3' v4
    have e8 : s4.gpr (wreg 0) = s1.gpr (wreg 0) := by
      rw [r4.gpr _ (by decide), r3.gpr _ (by decide), r2.gpr _ (by decide)]
    have e9 : s4.gpr (wreg 1) = s2.gpr (wreg 1) := by
      rw [r4.gpr _ (by decide), r3.gpr _ (by decide)]
    have e10 : s4.gpr (wreg 2) = s3.gpr (wreg 2) := by rw [r4.gpr _ (by decide)]
    simp only [rv4, val4, e8, e9, e10]
    generalize (if sub = true then 1 else 0) = c0 at *
    omega_arith
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      (r4.mono (by decide))))

theorem val4_cv_true (Y : Nat → Nat) (hY : ∀ k, Y k < 2 ^ 64) :
    val4 (fun k => cvW true (Y k)) + val4 Y = 2 ^ 256 - 1 := by
  have := hY 0; have := hY 1; have := hY 2; have := hY 3
  simp only [val4, cvW, ↓reduceIte]
  omega_arith

/-! ## Subtracting 38 on a borrow -/

/-- `borrowFold`: `rv4` less `38` if CA is clear (the last subtraction
borrowed), modulo `2²⁵⁶`, with the new borrow in CA. -/
theorem borrowFold_ok {s : State} (h5 : s.gpr .r5 = 38) :
    WP isa (.block borrowFold) s fun s' =>
      rv4 s' + 2 ^ 256 * s'.ca.toNat + 38 * (1 - s.ca.toNat) = rv4 s + 2 ^ 256 ∧
      Rest [.r4, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  unfold borrowFold
  refine wp_sube fun s1 u1 => WP.cons exec_logic (WP.cons (exec_li (by decide)) ?_)
  simp only
  generalize hs2 : s1.write .r4 (s1.gpr .r7 &&& s1.gpr .r5) = s2
  generalize hs3 : s2.write .r7 (BitVec.ofNat 64 0) = s3
  refine wp_subc fun s4 u4 => wp_sube fun s5 u5 => wp_sube fun s6 u6 => wp_sube fun s7 u7 =>
    WP.block_nil ?_
  have c0 : s.ca.toNat ≤ 1 := Bool.toNat_le _
  have v1 := u1.val
  have l1 := (s1.gpr .r7).isLt
  have c1 := u1.ca
  -- `r7` is the mask `CA - 1`, and the carry is unchanged.
  have hca1 : s1.ca.toNat = s.ca.toNat := by omega
  have e4 : (s2.gpr .r4).toNat = 38 * (1 - s.ca.toNat) := by
    have h51 : s1.gpr .r5 = 38 := by rw [u1.other _ (by decide), h5]
    rw [← hs2, RegUpd.gpr_write_self, h51]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp c0 with h | h
    · have : s1.gpr .r7 = BitVec.allOnes 64 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_allOnes]; omega)
      rw [this, BitVec.allOnes_and, h]; rfl
    · have : s1.gpr .r7 = 0#64 := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega)
      rw [this, BitVec.zero_and, h]; rfl
  have hca3 : s3.ca = s1.ca := by rw [← hs3, ← hs2, RegUpd.ca_write, RegUpd.ca_write]
  have g3 : ∀ r, r ≠ .r4 → r ≠ .r7 → s3.gpr r = s1.gpr r := fun r h4 h7 => by
    rw [← hs3, ← hs2, RegUpd.gpr_write_of_ne _ _ h7, RegUpd.gpr_write_of_ne _ _ h4]
  have e34 : s3.gpr .r4 = s2.gpr .r4 := by rw [← hs3, RegUpd.gpr_write_of_ne _ _ (by decide)]
  have e37 : (s3.gpr .r7).toNat = 0 := by rw [← hs3, RegUpd.gpr_write_self]; rfl
  have v4 := u4.val; have v5 := u5.val; have v6 := u6.val; have v7 := u7.val
  rw [e34, e4, g3 _ (by decide) (by decide), u1.other _ (by decide)] at v4
  rw [u4.other _ (by decide), u4.other _ (by decide), e37, g3 _ (by decide) (by decide),
    u1.other _ (by decide)] at v5
  rw [u5.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u4.other _ (by decide),
    e37, g3 _ (by decide) (by decide), u1.other _ (by decide)] at v6
  rw [u6.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u5.other _ (by decide),
    u4.other _ (by decide), u4.other _ (by decide), e37, g3 _ (by decide) (by decide),
    u1.other _ (by decide)] at v7
  have e8 : s7.gpr .r8 = s4.gpr .r8 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide)]
  have e9 : s7.gpr .r9 = s5.gpr .r9 := by rw [u7.other _ (by decide), u6.other _ (by decide)]
  have e10 : s7.gpr .r10 = s6.gpr .r10 := by rw [u7.other _ (by decide)]
  refine ⟨?_, ?_, ?_⟩
  · simp only [rv4, val4, wreg, Nat.reduceEqDiff, ↓reduceIte, e8, e9, e10]
    have := (s.gpr .r8).isLt; have := (s.gpr .r9).isLt; have := (s.gpr .r10).isLt
    have := (s.gpr .r11).isLt
    omega_arith
  · have r3 : Rest [.r4, .r7] s1 s3 := by
      rw [← hs3, ← hs2]
      exact ((Upd.write _ _ _).rest (by simp)).trans ((Upd.write _ _ _).rest (by simp))
    exact (u1.rest (by decide)).trans ((r3.mono (by decide)).trans ((u4.rest (by decide)).trans
      ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans (u7.rest (by decide))))))
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, ← hs3, ← hs2, RegUpd.mem_write, RegUpd.mem_write, u1.mem]

/-! ## Sums and differences -/

theorem frame_stores {o : Nat} {m1 m2 m3 : Mem} (h12 : m2 = m1)
    (h23 : Frame [⟨b + BitVec.ofNat 64 o, 32⟩] m2 m3) : Frame [⟨b + BitVec.ofNat 64 o, 32⟩] m1 m3 := by
  rw [h12] at h23; exact h23

theorem add_ok {o x y : Nat} (ho : o + 32 ≤ 4096) (hx : x + 32 ≤ 4096) (hy : y + 32 ≤ 4096)
    (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (add o x y)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x + V s.mem b y) % P := by
  unfold add stores4
  rw [addW_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (chain_ok false hx hx4 hy hy4 hc) fun s1 ⟨v1, r1, m1⟩ => ?_
  refine WP.cons (exec_li (by decide)) (wp_addze fun s2 u2 => WP.cons (exec_li (by decide)) ?_)
  generalize hs3 : s2.write .r5 (BitVec.ofNat 64 38) = s3
  have c1 : s1.ca.toNat ≤ 1 := Bool.toNat_le _
  have v2 := u2.val
  rw [RegUpd.gpr_write_self, RegUpd.ca_write] at v2
  have z : (BitVec.ofNat 64 0).toNat = 0 := rfl
  rw [z] at v2
  have l2 := (s2.gpr .r7).isLt
  have c2 := u2.ca
  have e7 : (s3.gpr .r7).toNat = s1.ca.toNat := by
    rw [← hs3, RegUpd.gpr_write_of_ne _ _ (by decide)]; omega
  have rv3 : rv4 s3 = rv4 s1 := by
    simp only [rv4, val4, wreg, Nat.reduceEqDiff, ↓reduceIte]
    rw [← hs3]
    simp only [RegUpd.gpr_write_of_ne _ _ (show ¬Reg.r8 = .r5 by decide),
      RegUpd.gpr_write_of_ne _ _ (show ¬Reg.r9 = .r5 by decide),
      RegUpd.gpr_write_of_ne _ _ (show ¬Reg.r10 = .r5 by decide),
      RegUpd.gpr_write_of_ne _ _ (show ¬Reg.r11 = .r5 by decide)]
    rw [u2.other _ (by decide), u2.other _ (by decide), u2.other _ (by decide), u2.other _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide)]
  have r3 : Rest [.r4, .r5, .r7, .r8, .r9, .r10, .r11] s1 s3 := by
    rw [← hs3]
    exact ((Upd.write _ _ _).rest (by decide)).trans ((u2.rest (by decide)).trans
      ((Upd.write _ _ _).rest (by decide)))
  have m3 : s3.mem = s1.mem := by rw [← hs3, RegUpd.mem_write, u2.mem, RegUpd.mem_write]
  have h53 : s3.gpr .r5 = 38 := by rw [← hs3, RegUpd.gpr_write_self]; rfl
  have hc3 := (hc.of_rest r1 (by decide)).of_rest r3 (by decide)
  refine WP.append (foldTop_ok h53 (by omega)) fun s4 ⟨v4, t4, r4, m4⟩ => ?_
  refine WP.append (foldTop_ok (by rw [r4.gpr _ (by decide), h53]) (by omega))
    fun s5 ⟨v5, t5, r5, m5⟩ => ?_
  have hc5 := hc3.of_rest (r4.trans r5) (by decide)
  refine WP.mono (stores4_ok ho ho4 hc5) fun s6 ⟨v6, f6, r6⟩ => ⟨?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans
      ((r5.mono (by decide)).trans (r6.mono (by decide)))))
  · rw [m5, m4, m3, m1] at f6; exact f6
  · rw [v6, V_eq4, V_eq4]
    simp only [cvW, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at v1
    have b1 := rv4_lt s1; have b4 := rv4_lt s4; have b5 := rv4_lt s5
    have hP : P = 2 ^ 255 - 19 := rfl
    rw [e7, rv3] at v4
    generalize val4 (ew s.mem b x) = X at *
    generalize val4 (ew s.mem b y) = Y at *
    have z5 : (s5.gpr .r7).toNat = 0 := by omega
    rw [z5] at v5
    rw [hP]
    omega

theorem sub_ok {o x y : Nat} (ho : o + 32 ≤ 4096) (hx : x + 32 ≤ 4096) (hy : y + 32 ≤ 4096)
    (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (sub o x y)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      (V s'.mem b o + V s.mem b y) % P = V s.mem b x % P := by
  unfold sub stores4
  rw [subW_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (chain_ok true hx hx4 hy hy4 hc) fun s1 ⟨v1, r1, m1⟩ => ?_
  refine WP.cons (exec_li (by decide)) ?_
  generalize hs2 : s1.write .r5 (BitVec.ofNat 64 38) = s2
  have h52 : s2.gpr .r5 = 38 := by rw [← hs2, RegUpd.gpr_write_self]; rfl
  have r2 : Rest [.r5] s1 s2 := by rw [← hs2]; exact (Upd.write _ _ _).rest (by decide)
  have rv2 : rv4 s2 = rv4 s1 := by
    simp only [rv4, val4, wreg, Nat.reduceEqDiff, ↓reduceIte]
    rw [r2.gpr _ (by decide), r2.gpr _ (by decide), r2.gpr _ (by decide), r2.gpr _ (by decide)]
  have ca2 : s2.ca = s1.ca := by rw [← hs2, RegUpd.ca_write]
  have m2 : s2.mem = s1.mem := by rw [← hs2, RegUpd.mem_write]
  refine WP.append (borrowFold_ok h52) fun s3 ⟨v3, r3, m3⟩ => ?_
  refine WP.append (borrowFold_ok (by rw [r3.gpr _ (by decide), h52])) fun s4 ⟨v4, r4, m4⟩ => ?_
  have hc4 := (((hc.of_rest r1 (by decide)).of_rest r2 (by decide)).of_rest r3 (by decide)).of_rest r4
    (by decide)
  refine WP.mono (stores4_ok ho ho4 hc4) fun s5 ⟨v5, f5, r5⟩ => ⟨?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((r4.mono (by decide)).trans (r5.mono (by decide)))))
  · rw [m4, m3, m2, m1] at f5; exact f5
  · rw [v5, V_eq4, V_eq4]
    have hY := val4_cv_true (fun k => dw s.mem b (y + 8 * k)) fun k => dw_lt _ _ _
    simp only [↓reduceIte] at v1
    rw [rv2, ca2] at v3
    have b1 := rv4_lt s1; have b3 := rv4_lt s3; have b4 := rv4_lt s4
    have c1 : s1.ca.toNat ≤ 1 := Bool.toNat_le _
    have c3 : s3.ca.toNat ≤ 1 := Bool.toNat_le _
    have c4 : s4.ca.toNat ≤ 1 := Bool.toNat_le _
    have hP : P = 2 ^ 255 - 19 := rfl
    generalize val4 (ew s.mem b x) = X at *
    generalize val4 (ew s.mem b y) = Y at *
    generalize val4 (fun k => cvW true (dw s.mem b (y + 8 * k))) = Y' at *
    have hc4 : s4.ca.toNat = 1 := by omega
    have key : rv4 s4 + Y = X + (2 ^ 255 - 19) * (2 * ((1 - s1.ca.toNat) + (1 - s3.ca.toNat))) := by
      omega
    rw [hP, key, Nat.add_mul_mod_self_left]


/-! ## The multiple by `a24` -/

/-- A write that keeps CA. -/
theorem wp_wr {i : Instr} {d : Reg} {v : BitVec 64} {is : List Instr} {s : State}
    {Q : State → Prop} (he : exec i s = some (s.write d v))
    (k : ∀ s', Upd s s' d v → s'.ca = s.ca → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q :=
  WP.cons he (k _ (Upd.write _ _ _) rfl)

/-- Word `off` of the working space times `121665` (in `r5`): its low word
into `d` and its high word into `h`. -/
theorem wstep_ok {d h : Reg} (hdh : d ≠ h) (hd5 : d ≠ .r5) (hh5 : h ≠ .r5) {off : Nat} (ho : off + 8 ≤ 4096) (ho4 : off % 4 = 0) {s : State}
    (hc : Ctx b s) (h5 : s.gpr .r5 = 121665) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', (s'.gpr d).toNat = dw s.mem b off * 121665 % 2 ^ 64 →
      (s'.gpr h).toNat = dw s.mem b off * 121665 / 2 ^ 64 → s'.ca = s.ca → Rest [d, h] s s' →
      s'.mem = s.mem → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d d .r6 off :: .mulhu h d .r5 :: .mul d d .r5 :: is)) s Q := by
  refine ldw_ok hc ho ho4 ?_
  generalize hs1 : s.write d _ = s1
  have u1 : Upd s s1 d (s.mem.readW (b + BitVec.ofNat 64 off) 64) := hs1 ▸ Upd.write _ _ _
  have c1 : s1.ca = s.ca := by rw [← hs1]; rfl
  refine wp_wr exec_mulhu fun s2 u2 c2 => wp_wr exec_mul fun s3 u3 c3 => k s3 ?_ ?_ ?_ ?_ ?_
  · have g1 : (s1.gpr d).toNat = dw s.mem b off := by rw [u1.gpr]; rfl
    have g5 : s1.gpr .r5 = 121665 := by rw [u1.other _ (Ne.symm hd5), h5]
    rw [u3.gpr, u2.other _ hdh, u2.other _ (Ne.symm hh5), g5, BitVec.toNat_mul, g1]; rfl
  · have g1 : (s1.gpr d).toNat = dw s.mem b off := by rw [u1.gpr]; rfl
    have g5 : s1.gpr .r5 = 121665 := by rw [u1.other _ (Ne.symm hd5), h5]
    have hw := dw_lt s.mem b off
    rw [u3.other _ (Ne.symm hdh), u2.gpr, g1, g5, show (121665 : BitVec 64).toNat = 121665 from rfl,
      toNat_imm (by omega)]
  · rw [c3, c2, c1]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))
  · rw [u3.mem, u2.mem, u1.mem]

theorem lis_ori_a24 : ((((1 : BitVec 16) ++ (0 : BitVec 16)).signExtend 64) |||
    (0xdb41 : BitVec 16).setWidth 64) = 121665 := by decide

/-- `mulA24 o x`: a number congruent to `121665 [x]` at `o`. -/
theorem mulA24_ok {o x : Nat} (ho : o + 32 ≤ 4096) (hx : x + 32 ≤ 4096) (ho4 : o % 4 = 0)
    (hx4 : x % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (mulA24 o x)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (121665 * V s.mem b x) % P := by
  unfold mulA24 a24Const stores4
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_wr exec_lis fun s1 u1 _ => wp_wr exec_ori fun s2 u2 _ => ?_
  have r2 : Rest [.r5] s s2 := (u1.rest (by simp)).trans (u2.rest (by simp))
  have hc2 := hc.of_rest r2 (by decide)
  have h52 : s2.gpr .r5 = 121665 := by rw [u2.gpr, u1.gpr]; exact lis_ori_a24
  have m2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  -- Word 0.
  refine wstep_ok (d := .r8) (h := .r7) (by decide) (by decide) (by decide)
    (by omega) (by omega) hc2 h52 fun s3 a3 b3 c3 r3 m3 => ?_
  have hc3 := hc2.of_rest r3 (by decide)
  -- Word 1.
  refine wstep_ok (d := .r9) (h := .r4) (by decide) (by decide) (by decide)
    (by omega) (by omega) hc3 (by rw [r3.gpr _ (by decide), h52]) fun s4 a4 b4 c4 r4 m4 => ?_
  refine wp_addc fun s5 u5 => ?_
  have hc5 := (hc3.of_rest r4 (by decide)).of_rest (u5.rest (ws := [.r9]) (by decide)) (by decide)
  -- Word 2.
  refine wstep_ok (d := .r10) (h := .r7) (by decide) (by decide) (by decide)
    (by omega) (by omega) hc5
    (by rw [u5.other _ (by decide), r4.gpr _ (by decide), r3.gpr _ (by decide), h52])
    fun s6 a6 b6 c6 r6 m6 => ?_
  refine wp_adde fun s7 u7 => ?_
  have hc7 := (hc5.of_rest r6 (by decide)).of_rest (u7.rest (ws := [.r10]) (by decide)) (by decide)
  -- Word 3.
  refine wstep_ok (d := .r11) (h := .r4) (by decide) (by decide) (by decide)
    (by omega) (by omega) hc7
    (by rw [u7.other _ (by decide), r6.gpr _ (by decide), u5.other _ (by decide), r4.gpr _ (by decide),
      r3.gpr _ (by decide), h52])
    fun s8 a8 b8 c8 r8 m8 => ?_
  refine wp_adde fun s9 u9 => wp_addze fun s10 u10 => WP.cons (exec_li (by decide)) ?_
  generalize hs11 : s10.write .r5 (BitVec.ofNat 64 38) = s11
  have r11 : Rest [.r5] s10 s11 := by rw [← hs11]; exact (Upd.write _ _ _).rest (by simp)
  have h511 : s11.gpr .r5 = 38 := by rw [← hs11, RegUpd.gpr_write_self]; rfl
  have m11 : s11.mem = s.mem := by
    rw [← hs11, RegUpd.mem_write, u10.mem, u9.mem, m8, u7.mem, m6, u5.mem, m4, m3, m2]
  -- The words of the product.
  have K := fun i => Nat.mod_add_div (dw s.mem b (x + 8 * i) * 121665) (2 ^ 64)
  have W := fun i => dw_lt s.mem b (x + 8 * i)
  have M3 : s3.mem = s.mem := by rw [m3, m2]
  have M5 : s5.mem = s.mem := by rw [u5.mem, m4, M3]
  have M7 : s7.mem = s.mem := by rw [u7.mem, m6, M5]
  rw [m2] at a3 b3; rw [M3] at a4 b4; rw [M5] at a6 b6; rw [M7] at a8 b8
  have v5 := u5.val; have v7 := u7.val; have v9 := u9.val; have v10 := u10.val
  rw [a4, r4.gpr .r7 (by decide), b3] at v5
  rw [a6, r6.gpr .r4 (by decide), u5.other .r4 (by decide), b4, c6] at v7
  rw [a8, r8.gpr .r7 (by decide), u7.other .r7 (by decide), b6, c8] at v9
  rw [u9.other .r4 (by decide), b8] at v10
  have h3 : dw s.mem b (x + 24) * 121665 / 2 ^ 64 < 121665 :=
    Nat.div_lt_of_lt_mul (by have := dw_lt s.mem b (x + 24); omega)
  have c9 : s9.ca.toNat ≤ 1 := u9.ca
  have l10 := (s10.gpr .r7).isLt
  have e7 : (s11.gpr .r7).toNat = dw s.mem b (x + 24) * 121665 / 2 ^ 64 + s9.ca.toNat := by
    rw [r11.gpr _ (by decide)]; have := u10.ca; omega
  have e8 : (s11.gpr .r8).toNat = dw s.mem b x * 121665 % 2 ^ 64 := by
    rw [r11.gpr _ (by decide), u10.other _ (by decide), u9.other _ (by decide), r8.gpr _ (by decide),
      u7.other _ (by decide), r6.gpr _ (by decide), u5.other _ (by decide), r4.gpr _ (by decide), a3]
  have e9 : s11.gpr .r9 = s5.gpr .r9 := by
    rw [r11.gpr _ (by decide), u10.other _ (by decide), u9.other _ (by decide), r8.gpr _ (by decide),
      u7.other _ (by decide), r6.gpr _ (by decide)]
  have e10 : s11.gpr .r10 = s7.gpr .r10 := by
    rw [r11.gpr _ (by decide), u10.other _ (by decide), u9.other _ (by decide), r8.gpr _ (by decide)]
  have e11 : s11.gpr .r11 = s9.gpr .r11 := by rw [r11.gpr _ (by decide), u10.other _ (by decide)]
  have hv11 : rv4 s11 + 2 ^ 256 * (s11.gpr .r7).toNat = 121665 * V s.mem b x := by
    rw [V_eq4, e7]
    simp only [rv4, val4, ew, wreg, Nat.reduceEqDiff, ↓reduceIte, e9, e10, e11]
    rw [e8]
    simp only [Nat.mul_zero, Nat.add_zero] at K W v5 v7 v9 ⊢
    have := K 0; have := K 1; have := K 2; have := K 3
    simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at *
    omega_arith
  have r11' : Rest clob s s11 :=
    (r2.mono (by decide)).trans ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans
      ((u5.rest (by decide)).trans ((r6.mono (by decide)).trans ((u7.rest (by decide)).trans
      ((r8.mono (by decide)).trans ((u9.rest (by decide)).trans ((u10.rest (by decide)).trans
      (r11.mono (by decide))))))))))
  have hc11 := hc.of_rest r11' (by decide)
  have b11 : (s11.gpr .r7).toNat < 2 ^ 58 := by rw [e7]; omega
  refine WP.append (foldTop_ok h511 b11) fun s12 ⟨v12, t12, r12, m12⟩ => ?_
  refine WP.append (foldTop_ok (by rw [r12.gpr _ (by decide), h511]) (by omega))
    fun s13 ⟨v13, t13, r13, m13⟩ => ?_
  refine WP.mono (stores4_ok ho ho4 (hc11.of_rest (r12.trans r13) (by decide)))
    fun s14 ⟨v14, f14, r14⟩ => ⟨?_, ?_, ?_⟩
  · exact r11'.trans ((r12.mono (by decide)).trans ((r13.mono (by decide)).trans (r14.mono (by decide))))
  · rw [m13, m12, m11] at f14; exact f14
  · rw [v14]
    have b12 := rv4_lt s12; have b13 := rv4_lt s13; have b11' := rv4_lt s11
    have hP : P = 2 ^ 255 - 19 := rfl
    generalize V s.mem b x = X at *
    have z13 : (s13.gpr .r7).toNat = 0 := by omega
    rw [z13] at v13
    rw [hP]
    omega

end

end VG.Proof.X25519.PPC64LE
