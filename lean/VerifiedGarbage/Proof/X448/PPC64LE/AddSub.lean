module

public import VerifiedGarbage.Proof.X448.PPC64LE.Field
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.PPC64LE.Pass
public import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
public import VerifiedGarbage.Proof.X448.PPC64LE.Product
public import VerifiedGarbage.Proof.X25519.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X448 on PPC64LE: sums and differences

`add o x y` and `sub o x y` store at `o` a number congruent to `[x] + [y]` and
`[x] - [y]` (as `[x] + 4p - [y]`); `o` may be `x` or `y`.
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P)

section
variable {b : Addr}

/-! ## Chains of doublewords through memory -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_subc64 {d n m : Reg}
    (k : ∀ s', UpdC s s' d ((s.gpr n).toNat + (2 ^ 64 - 1 - (s.gpr m).toNat) + 1) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subc d n m :: is)) s Q := by
  have := (s.gpr n).isLt
  exact WP.cons exec_subc (k _ (UpdC.writeCarry _ _ (by omega_using [])))

theorem wp_sube64 {d n m : Reg}
    (k : ∀ s', UpdC s s' d ((s.gpr n).toNat + (2 ^ 64 - 1 - (s.gpr m).toNat) + s.ca.toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.sube d n m :: is)) s Q := by
  have := (s.gpr n).isLt; have : s.ca.toNat ≤ 1 := Bool.toNat_le _
  exact WP.cons exec_sube (k _ (UpdC.writeCarry _ _ (by omega_using [this])))

/-- `std t, d(r6)` in the working space, which keeps CA. -/
theorem sdC_ok (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 8 ≤ 4096) (hd4 : d % 4 = 0)
    (k : ∀ s', Mupd s s' (s.mem.writeW (b + BitVec.ofNat 64 d) (s.gpr t)) → s'.ca = s.ca →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t .r6 d :: is)) s Q := by
  have e := exec_store_d (s := s) (t := t) (n := .r6) (off := d) (by decide) ⟨by omega_using [hd], hd4⟩
    (by rw [hc.r6]; exact hc.inW hd)
  rw [hc.r6] at e
  exact WP.cons e (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

end

/-- What step `k` of a chain adds of the second operand's word `w`: `w`, or
for a difference its complement. -/
def cvD (sub : Bool) (w : Nat) : Nat := if sub then 2 ^ 64 - 1 - w else w

/-- The carry into step `k` (`c` the carry out of step `k - 1`). -/
def cinD (sub : Bool) (k c : Nat) : Nat := if k = 0 then (if sub then 1 else 0) else c

/-- After `k` steps of a chain from `s0` into `[o]`: the doublewords
`o[0, k)` and CA hold `X_{<k} + W'_{<k}` (plus 1 for a difference), `W'` the
words `cvD` of `W`. -/
structure CInv (ws : List Reg) (sub : Bool) (o : Nat) (X W : Nat → Nat) (s0 : State) (k : Nat)
    (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest ws s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 8 * k⟩] s0.mem s.mem
  val : 0 < k → colsV (ew s.mem b o) k + (2 ^ 64) ^ k * s.ca.toNat =
    colsV X k + colsV (fun j => cvD sub (W j)) k + (if sub then 1 else 0)

theorem CInv.start {ws : List Reg} {sub : Bool} {o : Nat} {X W : Nat → Nat} {s0 : State}
    (hc : Ctx b s0) : CInv (b := b) ws sub o X W s0 0 s0 :=
  ⟨hc, Rest.refl _ _, Frame.refl _ _, fun h => absurd h (Nat.lt_irrefl 0)⟩

/-- The store that ends step `k`, of `r7` holding the step's sum. -/
theorem cstore_ok {ws : List Reg} {sub : Bool} {o : Nat} {X W : Nat → Nat} {s0 : State} {k : Nat}
    (hk : k < 7) (ho : o + 56 ≤ 4096) (ho4 : o % 4 = 0) {s t : State}
    (h : CInv (b := b) ws sub o X W s0 k s) (hct : Ctx b t) (hr : Rest ws s t) (hm : t.mem = s.mem)
    (hv : (t.gpr .r7).toNat + 2 ^ 64 * t.ca.toNat = X k + cvD sub (W k) + cinD sub k s.ca.toNat) :
    WP isa (.block [.store .d .r7 .r6 (o + 8 * k)]) t (CInv (b := b) ws sub o X W s0 (k + 1)) := by
  refine sdC_ok hct (by omega_using [hk, ho]) (by omega_using [ho4]) fun t1 u1 c1 => WP.block_nil ⟨hct.of_rest (u1.rest []) (by decide),
    h.rest.trans (hr.trans (u1.rest _)), ?_, fun _ => ?_⟩
  · rw [u1.mem, hm]
    exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [hk, ho]))
  · have ew1 : ∀ j < k, ew t1.mem b o j = ew s.mem b o j := fun j hj => by
      show dw _ _ _ = dw _ _ _
      rw [u1.mem, hm, dw_write_other _ _ _ (by omega_using [hj]) (by omega_using [hk, ho, hj]) (by omega_using [hk, ho])]
    have es : ew t1.mem b o k = (t.gpr .r7).toNat := by
      show dw _ _ _ = _
      rw [u1.mem, dw_write_self]
    simp only [colsV]
    rw [colsV_congr ew1, es, c1]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [colsV, cinD, ↓reduceIte, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.pow_one] at hv ⊢
      omega_using [hv]
    · have hp := h.val hk0
      simp only [cinD, Nat.ne_of_gt hk0, ↓reduceIte] at hv
      rw [show ((2 : Nat) ^ 64) ^ (k + 1) = (2 ^ 64) ^ k * 2 ^ 64 from Nat.pow_succ _ _]
      generalize (2 ^ 64) ^ k = K at *
      generalize colsV (ew s.mem b o) k = S at *
      generalize colsV X k = CX at *
      generalize colsV (fun j => cvD sub (W j)) k = CW at *
      generalize (t.gpr .r7).toNat = L at *
      generalize t.ca.toNat = C' at *
      generalize s.ca.toNat = C at *
      generalize X k = Xk at *
      generalize cvD sub (W k) = Wk at *
      have e1 : K * L + K * 2 ^ 64 * C' = K * Xk + K * Wk + K * C := by
        rw [Nat.mul_assoc, ← Nat.mul_add, hv, Nat.mul_add, Nat.mul_add]
      generalize K * L = KL at *
      generalize K * 2 ^ 64 * C' = KC' at *
      generalize K * Xk = KX at *
      generalize K * Wk = KW at *
      generalize K * C = KC at *
      omega_using [hp, e1]


theorem updC_congr {s t : State} {d : Reg} {v v' : Nat} (h : UpdC s t d v) (e : v = v') : UpdC s t d v' :=
  e ▸ h

/-- A step's carrying operation of `r7` and `src`. -/
theorem chainOp_ok (sub : Bool) (k : Nat) (src : Reg) {is : List Instr} {s : State}
    {Q : State → Prop}
    (hk : ∀ t, UpdC s t .r7 ((s.gpr .r7).toNat + cvD sub (s.gpr src).toNat + cinD sub k s.ca.toNat) →
      WP isa (.block is) t Q) :
    WP isa (.block (chainOp sub k src :: is)) s Q := by
  cases sub <;> by_cases h0 : k = 0 <;> simp only [chainOp, h0, Bool.false_eq_true, ↓reduceIte]
  · exact wp_addc fun t u => hk t (updC_congr u (by simp [cvD, cinD, h0]))
  · exact wp_adde fun t u => hk t (updC_congr u (by simp [cvD, cinD, h0]))
  · exact wp_subc64 fun t u => hk t (updC_congr u (by simp [cvD, cinD, h0]))
  · exact wp_sube64 fun t u => hk t (updC_congr u (by simp [cvD, cinD, h0]))

/-- Step `k` of the chain of `[x]` and `[y]` into `[o]`. -/
theorem chainStep_ok {sub : Bool} {o x y : Nat} (ho : o + 56 ≤ 4096) (hx : x + 56 ≤ 4096)
    (hy : y + 56 ≤ 4096) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0)
    (hox : x = o ∨ x + 56 ≤ o ∨ o + 56 ≤ x) (hoy : y = o ∨ y + 56 ≤ o ∨ o + 56 ≤ y)
    {s0 : State} {k : Nat} (hk : k < 7) {s : State}
    (h : CInv (b := b) [.r7, .r8] sub o (ew s0.mem b x) (ew s0.mem b y) s0 k s) :
    WP isa (.block (chainStep sub o x y k)) s
      (CInv (b := b) [.r7, .r8] sub o (ew s0.mem b x) (ew s0.mem b y) s0 (k + 1)) := by
  have hc := h.ctx
  have eX : dw s.mem b (x + 8 * k) = dw s0.mem b (x + 8 * k) := dw_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_using [hox, hk]) (by omega_using [hx, hk]) (by omega_using [ho, hk])
  have eY : dw s.mem b (y + 8 * k) = dw s0.mem b (y + 8 * k) := dw_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_using [hoy, hk]) (by omega_using [hy, hk]) (by omega_using [ho, hk])
  unfold chainStep
  refine ldw_ok hc (by omega_using [hx, hk]) (by omega_using [hx4]) ?_
  generalize hs1 : s.write .r7 (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * k)) 64) = s1
  have r1 : Rest [.r7, .r8] s s1 := by rw [← hs1]; exact (Upd.write _ _ _).rest (by simp)
  have hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  have m1 : s1.mem = s.mem := by rw [← hs1, RegUpd.mem_write]
  refine ldw_ok hc1 (by omega_using [hy, hk]) (by omega_using [hy4]) ?_
  generalize hs2 : s1.write .r8 (s1.mem.readW (b + BitVec.ofNat 64 (y + 8 * k)) 64) = s2
  have r2 : Rest [.r7, .r8] s1 s2 := by rw [← hs2]; exact (Upd.write _ _ _).rest (by simp)
  have m2 : s2.mem = s.mem := by rw [← hs2, RegUpd.mem_write, m1]
  have c2 : s2.ca = s.ca := by rw [← hs2, ← hs1, RegUpd.ca_write, RegUpd.ca_write]
  have g7 : (s2.gpr .r7).toNat = dw s0.mem b (x + 8 * k) := by
    rw [← hs2, RegUpd.gpr_write_of_ne _ _ (by decide), ← hs1, RegUpd.gpr_write_self, ← eX]; rfl
  have g8 : (s2.gpr .r8).toNat = dw s0.mem b (y + 8 * k) := by
    rw [← hs2, RegUpd.gpr_write_self, m1, ← eY]; rfl
  refine chainOp_ok sub k .r8 fun t u => ?_
  refine cstore_ok hk ho ho4 h (hc1.of_rest (r2.trans (u.rest (by simp))) (by decide))
    (r1.trans (r2.trans (u.rest (by simp)))) (by rw [u.mem, m2]) ?_
  rw [u.val, g7, g8, c2]

theorem foldSrc64_ne (k : Nat) : foldSrc64 k ≠ .r7 := by
  unfold foldSrc64; split
  · decide
  · split <;> decide

/-- Step `k` of the fold of the registers `foldSrc64` into `[o]`. -/
theorem foldStep_ok {sub : Bool} {o : Nat} (ho : o + 56 ≤ 4096) (ho4 : o % 4 = 0) {s0 : State}
    {k : Nat} (hk : k < 7) {s : State}
    (h : CInv (b := b) [.r7] sub o (ew s0.mem b o) (fun j => (s0.gpr (foldSrc64 j)).toNat) s0 k s) :
    WP isa (.block (foldStep sub o k)) s
      (CInv (b := b) [.r7] sub o (ew s0.mem b o) (fun j => (s0.gpr (foldSrc64 j)).toNat) s0 (k + 1)) := by
  have hc := h.ctx
  have eX : dw s.mem b (o + 8 * k) = dw s0.mem b (o + 8 * k) := dw_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_using []) (by omega_using [ho, hk]) (by omega_using [ho, hk])
  have hn := foldSrc64_ne k
  unfold foldStep
  refine ldw_ok hc (by omega_using [ho, hk]) (by omega_using [ho4]) ?_
  generalize hs1 : s.write .r7 (s.mem.readW (b + BitVec.ofNat 64 (o + 8 * k)) 64) = s1
  have r1 : Rest [.r7] s s1 := by rw [← hs1]; exact (Upd.write _ _ _).rest (by simp)
  have hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  have m1 : s1.mem = s.mem := by rw [← hs1, RegUpd.mem_write]
  have c1 : s1.ca = s.ca := by rw [← hs1, RegUpd.ca_write]
  have g7 : (s1.gpr .r7).toNat = dw s0.mem b (o + 8 * k) := by
    rw [← hs1, RegUpd.gpr_write_self, ← eX]; rfl
  have gs : s1.gpr (foldSrc64 k) = s0.gpr (foldSrc64 k) := by
    rw [r1.gpr _ (by simp [hn]), h.rest.gpr _ (by simp [hn])]
  refine chainOp_ok sub k (foldSrc64 k) fun t u => ?_
  refine cstore_ok hk ho ho4 h (hc1.of_rest (u.rest (ws := [.r7]) (by simp)) (by decide))
    (r1.trans (u.rest (by simp))) (by rw [u.mem, m1]) ?_
  rw [u.val, g7, gs, c1]


/-- The chain of `[x]` and `[y]` into `[o]`. -/
theorem chainRun_ok {sub : Bool} {o x y : Nat} (ho : o + 56 ≤ 4096) (hx : x + 56 ≤ 4096)
    (hy : y + 56 ≤ 4096) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0)
    (hox : x = o ∨ x + 56 ≤ o ∨ o + 56 ≤ x) (hoy : y = o ∨ y + 56 ≤ o ∨ o + 56 ≤ y)
    {s0 : State} (hc : Ctx b s0) :
    WP isa (.block ((List.range 7).flatMap (chainStep sub o x y))) s0
      (CInv (b := b) [.r7, .r8] sub o (ew s0.mem b x) (ew s0.mem b y) s0 7) :=
  wp_range_flatMap (M := isa) (N := 7) _
    (fun _ _ hk ht => chainStep_ok ho hx hy ho4 hx4 hy4 hox hoy hk ht) 7 (Nat.le_refl _) s0
    (CInv.start hc)

/-- The fold of the registers `foldSrc64` into `[o]`. -/
theorem foldRun_ok {sub : Bool} {o : Nat} (ho : o + 56 ≤ 4096) (ho4 : o % 4 = 0) {s0 : State}
    (hc : Ctx b s0) :
    WP isa (.block ((List.range 7).flatMap (foldStep sub o))) s0
      (CInv (b := b) [.r7] sub o (ew s0.mem b o) (fun j => (s0.gpr (foldSrc64 j)).toNat) s0 7) :=
  wp_range_flatMap (M := isa) (N := 7) _ (fun _ _ hk ht => foldStep_ok ho ho4 hk ht) 7
    (Nat.le_refl _) s0 (CInv.start hc)

/-- The registers a fold adds, as a number: `c + 2²²⁴ c`. -/
theorem foldW_val (s : State) {c : Nat} (h4 : (s.gpr .r4).toNat = c) (h5 : (s.gpr .r5).toNat = 2 ^ 32 * c)
    (h8 : (s.gpr .r8).toNat = 0) :
    colsV (fun j => (s.gpr (foldSrc64 j)).toNat) 7 = c + 2 ^ 224 * c := by
  simp only [colsV, foldSrc64, Nat.reduceEqDiff, ↓reduceIte, h4, h5, h8]
  omega_using []

theorem colsV_cvD_false (W : Nat → Nat) : colsV (fun j => cvD false (W j)) 7 = colsV W 7 := rfl

theorem colsV_cvD_true (W : Nat → Nat) (hW : ∀ j, W j < 2 ^ 64) :
    colsV (fun j => cvD true (W j)) 7 + colsV W 7 = 2 ^ 224 * 2 ^ 224 - 1 := by
  have := hW 0; have := hW 1; have := hW 2; have := hW 3; have := hW 4; have := hW 5; have := hW 6
  simp only [colsV, cvD, ↓reduceIte]
  omega_arith

/-- `carryPrep`: the carry `c` in `r4`, `2³² c` in `r5`, zero in `r8`. -/
theorem carryPrep_ok {s : State} (hc : Ctx b s) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Ctx b t → Rest [.r4, .r5, .r8] s t → t.mem = s.mem → (t.gpr .r4).toNat = s.ca.toNat →
      (t.gpr .r5).toNat = 2 ^ 32 * s.ca.toNat → (t.gpr .r8).toNat = 0 → WP isa (.block is) t Q) :
    WP isa (.block (carryPrep ++ is)) s Q := by
  simp only [carryPrep, List.cons_append, List.nil_append]
  refine WP.cons (exec_li (by decide)) (wp_addze fun s2 u2 => wp_lsl (by decide) fun s3 u3 =>
    wp_li (by decide) fun s4 u4 => ?_)
  have v2 := u2.val
  rw [RegUpd.gpr_write_self, RegUpd.ca_write] at v2
  have z : (BitVec.ofNat 64 0).toNat = 0 := rfl
  rw [z] at v2
  have c0 : s.ca.toNat ≤ 1 := Bool.toNat_le _
  have l2 := (s2.gpr .r4).isLt
  have e2 : (s2.gpr .r4).toNat = s.ca.toNat := by omega_using [v2, c0]
  have r4' : Rest [.r4, .r5, .r8] s s4 :=
    ((Upd.write _ _ _).rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      (u4.rest (by simp))))
  refine k s4 (hc.of_rest r4' (by decide)) r4' (by rw [u4.mem, u3.mem, u2.mem, RegUpd.mem_write]) ?_ ?_ ?_
  · rw [u4.other _ (by decide), u3.other _ (by decide), e2]
  · rw [u4.other _ (by decide), u3.gpr, toNat_shl, e2, Nat.mod_eq_of_lt (by omega_using [c0]), Nat.mul_comm]
  · rw [u4.gpr]; rfl

/-- `borrowPrep`: the borrow `β = 1 - CA` in `r4`, `2³² β` in `r5`, zero in `r8`. -/
theorem borrowPrep_ok {s : State} (hc : Ctx b s) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Ctx b t → Rest [.r4, .r5, .r8] s t → t.mem = s.mem → (t.gpr .r4).toNat = 1 - s.ca.toNat →
      (t.gpr .r5).toNat = 2 ^ 32 * (1 - s.ca.toNat) → (t.gpr .r8).toNat = 0 → WP isa (.block is) t Q) :
    WP isa (.block (borrowPrep ++ is)) s Q := by
  simp only [borrowPrep, List.cons_append, List.nil_append]
  refine WP.cons (exec_li (by decide)) (wp_sube64 fun s2 u2 => wp_sub fun s3 u3 => wp_lsl (by decide)
    fun s4 u4 => ?_)
  have v2 := u2.val
  rw [RegUpd.gpr_write_self, RegUpd.ca_write] at v2
  have z : (BitVec.ofNat 64 0).toNat = 0 := rfl
  rw [z] at v2
  have c0 : s.ca.toNat ≤ 1 := Bool.toNat_le _
  have l2 := (s2.gpr .r4).isLt
  have c2 := u2.ca
  have g8 : s2.gpr .r8 = 0#64 := by rw [u2.other _ (by decide), RegUpd.gpr_write_self]
  have e3 : (s3.gpr .r4).toNat = 1 - s.ca.toNat := by
    rw [u3.gpr, g8]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp c0 with h | h
    · have : s2.gpr .r4 = BitVec.allOnes 64 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_allOnes]; omega_using [v2, h])
      rw [this, h]; rfl
    · have : s2.gpr .r4 = 0#64 := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega_using [v2, h])
      rw [this, h]; rfl
  have r4' : Rest [.r4, .r5, .r8] s s4 :=
    ((Upd.write _ _ _).rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      (u4.rest (by simp))))
  refine k s4 (hc.of_rest r4' (by decide)) r4' (by rw [u4.mem, u3.mem, u2.mem, RegUpd.mem_write]) ?_ ?_ ?_
  · rw [u4.other _ (by decide), e3]
  · rw [u4.gpr, toNat_shl, e3, Nat.mod_eq_of_lt (by omega_using []), Nat.mul_comm]
  · rw [u4.other _ (by decide), u3.other _ (by decide), g8]; rfl

theorem V_cols_lt (m : Mem) (o : Nat) : colsV (ew m b o) 7 < 2 ^ 224 * 2 ^ 224 := by
  have := V_lt m b o; rw [V_eq_cols] at this; exact this

theorem add_ok {o x y : Nat} (ho : o + 56 ≤ 4096) (hx : x + 56 ≤ 4096) (hy : y + 56 ≤ 4096)
    (hox : o = x ∨ o + 56 ≤ x ∨ x + 56 ≤ o) (hoy : o = y ∨ o + 56 ≤ y ∨ y + 56 ≤ o)
    (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (add o x y)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x + V s.mem b y) % P := by
  unfold add
  simp only [List.append_assoc]
  refine WP.append (chainRun_ok (sub := false) ho hx hy ho4 hx4 hy4 (by omega_using [hox]) (by omega_using [hoy]) hc)
    fun s1 h1 => ?_
  refine carryPrep_ok h1.ctx fun s2 hc2 r2 m2 e4 e5 e8 => ?_
  refine WP.append (foldRun_ok (sub := false) ho ho4 hc2) fun s3 h3 => ?_
  refine carryPrep_ok h3.ctx fun s4 hc4 r4 m4 f4 f5 f8 => ?_
  refine WP.mono (foldRun_ok (sub := false) ho ho4 hc4) fun s5 h5 => ⟨?_, ?_, ?_⟩
  · exact (h1.rest.mono (by decide)).trans ((r2.mono (by decide)).trans ((h3.rest.mono (by decide)).trans
      ((r4.mono (by decide)).trans (h5.rest.mono (by decide)))))
  · exact h1.frame.trans (by rw [← m2]; exact h3.frame.trans (by rw [← m4]; exact h5.frame))
  · have v1 := h1.val (by decide)
    have v3 := h3.val (by decide)
    have v5 := h5.val (by decide)
    rw [colsV_cvD_false] at v1 v3 v5
    rw [foldW_val s2 e4 e5 e8, m2] at v3
    rw [foldW_val s4 f4 f5 f8, m4] at v5
    rw [V_eq_cols, V_eq_cols, V_eq_cols]
    have b1 := V_cols_lt (b := b) s1.mem o; have b3 := V_cols_lt (b := b) s3.mem o
    have b5 := V_cols_lt (b := b) s5.mem o
    have c1 : s1.ca.toNat ≤ 1 := Bool.toNat_le _
    have c3 : s3.ca.toNat ≤ 1 := Bool.toNat_le _
    have c5 : s5.ca.toNat ≤ 1 := Bool.toNat_le _
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at v1 v3 v5
    generalize colsV (ew s.mem b x) 7 = X at *
    generalize colsV (ew s.mem b y) 7 = Y at *
    have z5 : s5.ca.toNat = 0 := by omega_using [e4, e5, f4, f5, b1, b3, b5, c1, c3, c5, v3, v5, v1]
    have key : colsV (ew s5.mem b o) 7 + (2 ^ 224 * 2 ^ 224 - 2 ^ 224 - 1) * (s1.ca.toNat + s3.ca.toNat) =
        X + Y := by
      omega_using [e4, e5, f4, f5, b1, b3, b5, c1, c3, c5, v3, v5, v1, z5]
    rw [P_eq, ← key, Nat.add_mul_mod_self_left]

theorem sub_ok {o x y : Nat} (ho : o + 56 ≤ 4096) (hx : x + 56 ≤ 4096) (hy : y + 56 ≤ 4096)
    (hox : o = x ∨ o + 56 ≤ x ∨ x + 56 ≤ o) (hoy : o = y ∨ o + 56 ≤ y ∨ y + 56 ≤ o)
    (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (sub o x y)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      (V s'.mem b o + V s.mem b y) % P = V s.mem b x % P := by
  unfold sub
  simp only [List.append_assoc]
  refine WP.append (chainRun_ok (sub := true) ho hx hy ho4 hx4 hy4 (by omega_using [hox]) (by omega_using [hoy]) hc)
    fun s1 h1 => ?_
  refine borrowPrep_ok h1.ctx fun s2 hc2 r2 m2 e4 e5 e8 => ?_
  refine WP.append (foldRun_ok (sub := true) ho ho4 hc2) fun s3 h3 => ?_
  refine borrowPrep_ok h3.ctx fun s4 hc4 r4 m4 f4 f5 f8 => ?_
  refine WP.mono (foldRun_ok (sub := true) ho ho4 hc4) fun s5 h5 => ⟨?_, ?_, ?_⟩
  · exact (h1.rest.mono (by decide)).trans ((r2.mono (by decide)).trans ((h3.rest.mono (by decide)).trans
      ((r4.mono (by decide)).trans (h5.rest.mono (by decide)))))
  · exact h1.frame.trans (by rw [← m2]; exact h3.frame.trans (by rw [← m4]; exact h5.frame))
  · have v1 := h1.val (by decide)
    have v3 := h3.val (by decide)
    have v5 := h5.val (by decide)
    have w1 := colsV_cvD_true (ew s.mem b y) fun j => dw_lt _ _ _
    have w3 := colsV_cvD_true (fun j => (s2.gpr (foldSrc64 j)).toNat) fun j => (s2.gpr _).isLt
    have w5 := colsV_cvD_true (fun j => (s4.gpr (foldSrc64 j)).toNat) fun j => (s4.gpr _).isLt
    rw [foldW_val s2 e4 e5 e8] at w3
    rw [foldW_val s4 f4 f5 f8] at w5
    rw [m2] at v3
    rw [m4] at v5
    rw [V_eq_cols, V_eq_cols, V_eq_cols]
    have b1 := V_cols_lt (b := b) s1.mem o; have b3 := V_cols_lt (b := b) s3.mem o
    have b5 := V_cols_lt (b := b) s5.mem o
    have c1 : s1.ca.toNat ≤ 1 := Bool.toNat_le _
    have c3 : s3.ca.toNat ≤ 1 := Bool.toNat_le _
    have c5 : s5.ca.toNat ≤ 1 := Bool.toNat_le _
    simp only [↓reduceIte] at v1 v3 v5
    generalize colsV (ew s.mem b x) 7 = X at *
    generalize colsV (ew s.mem b y) 7 = Y at *
    generalize colsV (fun j => cvD true (ew s.mem b y j)) 7 = Y' at *
    generalize colsV (fun j => cvD true ((s2.gpr (foldSrc64 j)).toNat)) 7 = F3 at *
    generalize colsV (fun j => cvD true ((s4.gpr (foldSrc64 j)).toNat)) 7 = F5 at *
    have z5 : s5.ca.toNat = 1 := by omega_using [e4, e5, f4, f5, b1, b3, b5, c1, c3, c5, v1, w1, w3, v3, w5, v5]
    have key : colsV (ew s5.mem b o) 7 + Y =
        X + (2 ^ 224 * 2 ^ 224 - 2 ^ 224 - 1) * ((1 - s1.ca.toNat) + (1 - s3.ca.toNat)) := by
      omega_using [e4, e5, f4, f5, b1, b3, b5, c1, c3, c5, v1, w1, w3, v3, w5, v5, z5]
    rw [P_eq, key, Nat.add_mul_mod_self_left]


/-! ## The multiplication by `a24` -/

/-- A register write that keeps CA. -/
theorem wp_wr64 {i : Instr} {d : Reg} {v : BitVec 64} {is : List Instr} {s : State}
    {Q : State → Prop} (he : exec i s = some (s.write d v))
    (k : ∀ s', Upd s s' d v → s'.ca = s.ca → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q :=
  WP.cons he (k _ (Upd.write _ _ _) rfl)

/-- After `k` steps of `mulA24 o a` from `s0`: `o[0, k)`, the high word in
`r7` and CA hold `a24 · a_{<k}`. -/
structure AInv (o a : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest [.r7, .r8, .r9] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 8 * k⟩] s0.mem s.mem
  val : colsV (ew s.mem b o) k + (2 ^ 64) ^ k * ((s.gpr .r7).toNat + (if k = 0 then 0 else s.ca.toNat)) =
    39081 * colsV (ew s0.mem b a) k

/-- A step's carrying addition of `r7` into `r9`. -/
theorem a24Op_ok (k : Nat) {is : List Instr} {s : State} {Q : State → Prop}
    (hk : ∀ t, UpdC s t .r9 ((s.gpr .r9).toNat + (s.gpr .r7).toNat + (if k = 0 then 0 else s.ca.toNat)) →
      WP isa (.block is) t Q) :
    WP isa (.block ((if k = 0 then Instr.addc .r9 .r9 .r7 else .adde .r9 .r9 .r7) :: is)) s Q := by
  by_cases h0 : k = 0
  · simp only [h0, ↓reduceIte]
    exact wp_addc fun t u => hk t (updC_congr u (by simp [h0]))
  · simp only [h0, ↓reduceIte]
    exact wp_adde fun t u => hk t (updC_congr u (by simp [h0]))

/-- Step `k` of `mulA24 o a`. -/
theorem a24Step_ok {o a : Nat} (ho : o + 56 ≤ 4096) (ha : a + 56 ≤ 4096) (ho4 : o % 4 = 0)
    (ha4 : a % 4 = 0) (hoa : a = o ∨ a + 56 ≤ o ∨ o + 56 ≤ a) {s0 : State}
    (h5 : s0.gpr .r5 = BitVec.ofNat 64 39081) {k : Nat} (hk : k < 7) {s : State}
    (h : AInv (b := b) o a s0 k s) :
    WP isa (.block (a24Step o a k)) s (AInv (b := b) o a s0 (k + 1)) := by
  have hc := h.ctx
  have eA : dw s.mem b (a + 8 * k) = dw s0.mem b (a + 8 * k) := dw_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_using [hoa, hk]) (by omega_using [ha, hk]) (by omega_using [ho, hk])
  have g5 : s.gpr .r5 = BitVec.ofNat 64 39081 := by rw [h.rest.gpr _ (by decide), h5]
  unfold a24Step
  refine ldw_ok hc (by omega_using [ha, hk]) (by omega_using [ha4]) ?_
  generalize hs1 : s.write .r8 (s.mem.readW (b + BitVec.ofNat 64 (a + 8 * k)) 64) = s1
  have u1 : Upd s s1 .r8 (s.mem.readW (b + BitVec.ofNat 64 (a + 8 * k)) 64) := hs1 ▸ Upd.write _ _ _
  have c1 : s1.ca = s.ca := by rw [← hs1, RegUpd.ca_write]
  have w1 : (s1.gpr .r8).toNat = dw s0.mem b (a + 8 * k) := by rw [u1.gpr, ← eA]; rfl
  have g51 : s1.gpr .r5 = BitVec.ofNat 64 39081 := by rw [u1.other _ (by decide), g5]
  refine wp_wr64 exec_mul fun s2 u2 c2 => a24Op_ok k fun s3 u3 => wp_wr64 exec_mulhu fun s4 u4 c4 => ?_
  have hw := dw_lt s0.mem b (a + 8 * k)
  have lo : (s2.gpr .r9).toNat = dw s0.mem b (a + 8 * k) * 39081 % 2 ^ 64 := by
    rw [u2.gpr, BitVec.toNat_mul, w1, g51]; rfl
  have r72 : s2.gpr .r7 = s.gpr .r7 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  have c2' : s2.ca = s.ca := by rw [c2, c1]
  have v3 := u3.val
  rw [lo, r72, c2'] at v3
  have g83 : s3.gpr .r8 = s1.gpr .r8 := by rw [u3.other _ (by decide), u2.other _ (by decide)]
  have g53 : s3.gpr .r5 = s1.gpr .r5 := by rw [u3.other _ (by decide), u2.other _ (by decide)]
  have hi : (s4.gpr .r7).toNat = dw s0.mem b (a + 8 * k) * 39081 / 2 ^ 64 := by
    rw [u4.gpr, g83, g53, w1, g51, show (BitVec.ofNat 64 39081).toNat = 39081 from rfl,
      toNat_imm (Nat.div_lt_of_lt_mul (by omega_using [w1]))]
  have g94 : s4.gpr .r9 = s3.gpr .r9 := u4.other _ (by decide)
  have r4' : Rest [.r7, .r8, .r9] s s4 :=
    (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))
  have hc4 : Ctx b s4 := hc.of_rest r4' (by decide)
  have m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  refine sdC_ok hc4 (by omega_using [ho, hk]) (by omega_using [ho4]) fun t ut ct => WP.block_nil
    ⟨hc4.of_rest (ut.rest []) (by decide), h.rest.trans (r4'.trans (ut.rest _)), ?_, ?_⟩
  · rw [ut.mem, m4]
    exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [ho, hk]))
  · have ew1 : ∀ j < k, ew t.mem b o j = ew s.mem b o j := fun j hj => by
      show dw _ _ _ = dw _ _ _
      rw [ut.mem, m4, dw_write_other _ _ _ (by omega_using [hj]) (by omega_using [ho, hk, hj]) (by omega_using [ho, hk])]
    have es : ew t.mem b o k = (s3.gpr .r9).toNat := by
      show dw _ _ _ = _
      rw [ut.mem, dw_write_self, g94]
    have g7 : (t.gpr .r7).toNat = dw s0.mem b (a + 8 * k) * 39081 / 2 ^ 64 := by rw [ut.gpr, hi]
    have ct' : t.ca = s3.ca := by rw [ct, c4]
    have hv := h.val
    simp only [colsV]
    rw [colsV_congr ew1, es, g7, ct']
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    have ewk : ew s0.mem b a k = dw s0.mem b (a + 8 * k) := rfl
    rw [ewk]
    have dm := Nat.mod_add_div (dw s0.mem b (a + 8 * k) * 39081) (2 ^ 64)
    rw [show ((2 : Nat) ^ 64) ^ (k + 1) = (2 ^ 64) ^ k * 2 ^ 64 from Nat.pow_succ _ _]
    generalize (2 ^ 64) ^ k = K at *
    generalize colsV (ew s.mem b o) k = S at *
    generalize colsV (ew s0.mem b a) k = A at *
    generalize dw s0.mem b (a + 8 * k) = w at *
    generalize w * 39081 % 2 ^ 64 = l at *
    generalize w * 39081 / 2 ^ 64 = hh at *
    generalize (s3.gpr .r9).toNat = R at *
    generalize s3.ca.toNat = C' at *
    generalize (s.gpr .r7).toNat = H at *
    generalize (if k = 0 then 0 else s.ca.toNat) = Ci at *
    have e1 : K * R + K * 2 ^ 64 * C' = K * l + K * H + K * Ci := by
      rw [Nat.mul_assoc, ← Nat.mul_add, v3, Nat.mul_add, Nat.mul_add]
    have e2 : K * l + K * (2 ^ 64 * hh) = 39081 * (K * w) := by
      rw [← Nat.mul_add, dm, Nat.mul_comm w, Nat.mul_left_comm]
    have e3 : K * (2 ^ 64) * (hh + C') = K * (2 ^ 64 * hh) + K * 2 ^ 64 * C' := by
      rw [Nat.mul_add, Nat.mul_assoc K (2 ^ 64) hh]
    have e4 : K * (H + Ci) = K * H + K * Ci := Nat.mul_add _ _ _
    rw [e3, Nat.mul_add 39081, Nat.mul_comm K w]
    rw [e4] at hv
    rw [Nat.mul_comm K w] at e2
    generalize K * R = KR at *
    generalize K * 2 ^ 64 * C' = KC at *
    generalize K * l = KL at *
    generalize K * H = KH at *
    generalize K * Ci = KCi at *
    generalize K * (2 ^ 64 * hh) = KHH at *
    generalize w * K = WK at *
    omega_using [hv, e1, e2]

/-- The value of `mulA24`'s folds: `S + 2⁴⁴⁸ t`, its top word `t` folded twice. -/
theorem fold2_arith {S t S9 c9 S11 c11 : Nat} (ht : t < 2 ^ 32) (hS : S < 2 ^ 224 * 2 ^ 224)
    (hS9 : S9 < 2 ^ 224 * 2 ^ 224) (h11 : c11 ≤ 1)
    (v9 : S9 + (2 ^ 64) ^ 7 * c9 = S + (t + 2 ^ 224 * t) + 0)
    (v11 : S11 + (2 ^ 64) ^ 7 * c11 = S9 + (c9 + 2 ^ 224 * c9) + 0) :
    S11 % P = (S + (2 ^ 64) ^ 7 * t) % P := by
  have z : c11 = 0 := by omega
  have key : S11 + (2 ^ 224 * 2 ^ 224 - 2 ^ 224 - 1) * (t + c9) = S + (2 ^ 64) ^ 7 * t := by
    omega_using [ht, hS, hS9, v9, v11]
  rw [P_eq, ← key, Nat.add_mul_mod_self_left]

theorem ori_a24 : (BitVec.ofNat 64 0 ||| (0x98a9 : BitVec 16).setWidth 64) = BitVec.ofNat 64 39081 := by
  decide

/-- `mulA24 o x`: a number congruent to `39081 [x]` at `o`. -/
theorem mulA24_ok {o x : Nat} (ho : o + 56 ≤ 4096) (hx : x + 56 ≤ 4096)
    (hox : x = o ∨ x + 56 ≤ o ∨ o + 56 ≤ x) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) {s : State}
    (hc : Ctx b s) :
    WP isa (.block (mulA24 o x)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (39081 * V s.mem b x) % P := by
  unfold mulA24
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_wr64 (exec_li (by decide)) fun s1 u1 _ => wp_wr64 exec_ori fun s2 u2 _ =>
    wp_wr64 (exec_li (by decide)) fun s3 u3 _ => ?_
  have r3 : Rest [.r5, .r7] s s3 := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))
  have hc3 : Ctx b s3 := hc.of_rest r3 (by decide)
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have h5 : s3.gpr .r5 = BitVec.ofNat 64 39081 := by
    rw [u3.other _ (by decide), u2.gpr, u1.gpr]; exact ori_a24
  refine WP.append (wp_range_flatMap (M := isa) (N := 7) (AInv (b := b) o x s3)
    (fun _ _ hk ht => a24Step_ok ho hx ho4 hx4 hox h5 hk ht) 7 (Nat.le_refl _) s3
    ⟨hc3, Rest.refl _ _, Frame.refl _ _, by rw [u3.gpr]; rfl⟩) fun s4 h4 => ?_
  refine wp_addze fun s5 u5 => wp_lsl (by decide) fun s6 u6 => wp_li (by decide) fun s7 u7 => ?_
  have hc4 := h4.ctx
  have v4 : colsV (ew s4.mem b o) 7 + (2 ^ 64) ^ 7 * ((s4.gpr .r7).toNat + s4.ca.toNat) =
      39081 * colsV (ew s3.mem b x) 7 := h4.val
  rw [m3] at v4
  have bX := V_cols_lt (b := b) s.mem x
  have v5 := u5.val
  have l5 := (s5.gpr .r4).isLt
  have c5 : s5.ca.toNat ≤ 1 := Bool.toNat_le _
  have e5 : (s5.gpr .r4).toNat = (s4.gpr .r7).toNat + s4.ca.toNat := by omega_using [v4, bX, v5]
  have ht : (s5.gpr .r4).toNat < 2 ^ 32 := by omega_using [v4, bX, v5]
  have r7' : Rest [.r4, .r5, .r8] s4 s7 :=
    (u5.rest (by simp)).trans ((u6.rest (by simp)).trans (u7.rest (by simp)))
  have hc7 : Ctx b s7 := hc4.of_rest r7' (by decide)
  have m7 : s7.mem = s4.mem := by rw [u7.mem, u6.mem, u5.mem]
  have f4 : (s7.gpr .r4).toNat = (s5.gpr .r4).toNat := by rw [u7.other _ (by decide), u6.other _ (by decide)]
  have f5 : (s7.gpr .r5).toNat = 2 ^ 32 * (s5.gpr .r4).toNat := by
    rw [u7.other _ (by decide), u6.gpr, toNat_shl, Nat.mod_eq_of_lt (by omega_using [ht])]; omega_using []
  have f8 : (s7.gpr .r8).toNat = 0 := by rw [u7.gpr]; rfl
  refine WP.append (foldRun_ok (sub := false) ho ho4 hc7) fun s9 h9 => ?_
  refine carryPrep_ok h9.ctx fun s10 hc10 r10 m10 e4' e5' e8' => ?_
  refine WP.mono (foldRun_ok (sub := false) ho ho4 hc10) fun s11 h11 => ⟨?_, ?_, ?_⟩
  · exact (r3.mono (by decide)).trans ((h4.rest.mono (by decide)).trans ((r7'.mono (by decide)).trans
      ((h9.rest.mono (by decide)).trans ((r10.mono (by decide)).trans (h11.rest.mono (by decide))))))
  · have f11 := h11.frame
    have f9 := h9.frame
    rw [m10] at f11
    rw [m7] at f9
    rw [← m3]
    exact h4.frame.trans (f9.trans f11)
  · have v9 : colsV (ew s9.mem b o) 7 + (2 ^ 64) ^ 7 * s9.ca.toNat =
        colsV (ew s7.mem b o) 7 + colsV (fun j => cvD false ((s7.gpr (foldSrc64 j)).toNat)) 7 + 0 :=
      h9.val (by decide)
    have v11 : colsV (ew s11.mem b o) 7 + (2 ^ 64) ^ 7 * s11.ca.toNat =
        colsV (ew s10.mem b o) 7 + colsV (fun j => cvD false ((s10.gpr (foldSrc64 j)).toNat)) 7 + 0 :=
      h11.val (by decide)
    rw [colsV_cvD_false, foldW_val s7 f4 f5 f8, m7] at v9
    rw [colsV_cvD_false, foldW_val s10 e4' e5' e8', m10] at v11
    have key := fold2_arith ht (V_cols_lt s4.mem o) (V_cols_lt s9.mem o) (Bool.toNat_le _) v9 v11
    rw [V_eq_cols, V_eq_cols, key, e5, v4]


end

end VG.Proof.X448.PPC64LE
