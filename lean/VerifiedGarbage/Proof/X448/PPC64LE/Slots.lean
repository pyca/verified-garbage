module

public import VerifiedGarbage.Proof.X448.PPC64LE.Field
public import VerifiedGarbage.Proof.X448.PPC64LE.Product
import VerifiedGarbage.Proof.X25519.PPC64LE.Cswap
import VerifiedGarbage.Proof.X448.PPC64LE.Cswap
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
public import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
public import VerifiedGarbage.Proof.X25519.PPC64LE.Product
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
public import VerifiedGarbage.Proof.X25519.PPC64LE.Reduce

/-! ### `X448.PPC64LE.Mul`, which this module and modules that import it used -/

section

/-! ### `X448.PPC64LE.AddSub`, which this module and modules that import it used -/

section

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
  obtain e := exec_store_d (s := s) (t := t) (n := .r6) (off := d) (by decide) ⟨by omega_using [hd], hd4⟩
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
    obtain es : ew t1.mem b o k = (t.gpr .r7).toNat := by
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
      obtain e1 : K * L + K * 2 ^ 64 * C' = K * Xk + K * Wk + K * C := by
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
  obtain eX : dw s.mem b (x + 8 * k) = dw s0.mem b (x + 8 * k) := dw_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_using [hox, hk]) (by omega_using [hx, hk]) (by omega_using [ho, hk])
  obtain eY : dw s.mem b (y + 8 * k) = dw s0.mem b (y + 8 * k) := dw_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_using [hoy, hk]) (by omega_using [hy, hk]) (by omega_using [ho, hk])
  unfold chainStep
  refine ldw_ok hc (by omega_using [hx, hk]) (by omega_using [hx4]) ?_
  generalize hs1 : s.write .r7 (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * k)) 64) = s1
  obtain r1 : Rest [.r7, .r8] s s1 := by rw [← hs1]; exact (Upd.write _ _ _).rest (by simp)
  obtain hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  obtain m1 : s1.mem = s.mem := by rw [← hs1, RegUpd.mem_write]
  refine ldw_ok hc1 (by omega_using [hy, hk]) (by omega_using [hy4]) ?_
  generalize hs2 : s1.write .r8 (s1.mem.readW (b + BitVec.ofNat 64 (y + 8 * k)) 64) = s2
  obtain r2 : Rest [.r7, .r8] s1 s2 := by rw [← hs2]; exact (Upd.write _ _ _).rest (by simp)
  obtain m2 : s2.mem = s.mem := by rw [← hs2, RegUpd.mem_write, m1]
  obtain c2 : s2.ca = s.ca := by rw [← hs2, ← hs1, RegUpd.ca_write, RegUpd.ca_write]
  obtain g7 : (s2.gpr .r7).toNat = dw s0.mem b (x + 8 * k) := by
    rw [← hs2, RegUpd.gpr_write_of_ne _ _ (by decide), ← hs1, RegUpd.gpr_write_self, ← eX]; rfl
  obtain g8 : (s2.gpr .r8).toNat = dw s0.mem b (y + 8 * k) := by
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
  obtain eX : dw s.mem b (o + 8 * k) = dw s0.mem b (o + 8 * k) := dw_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_using []) (by omega_using [ho, hk]) (by omega_using [ho, hk])
  obtain hn := foldSrc64_ne k
  unfold foldStep
  refine ldw_ok hc (by omega_using [ho, hk]) (by omega_using [ho4]) ?_
  generalize hs1 : s.write .r7 (s.mem.readW (b + BitVec.ofNat 64 (o + 8 * k)) 64) = s1
  obtain r1 : Rest [.r7] s s1 := by rw [← hs1]; exact (Upd.write _ _ _).rest (by simp)
  obtain hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  obtain m1 : s1.mem = s.mem := by rw [← hs1, RegUpd.mem_write]
  obtain c1 : s1.ca = s.ca := by rw [← hs1, RegUpd.ca_write]
  obtain g7 : (s1.gpr .r7).toNat = dw s0.mem b (o + 8 * k) := by
    rw [← hs1, RegUpd.gpr_write_self, ← eX]; rfl
  obtain gs : s1.gpr (foldSrc64 k) = s0.gpr (foldSrc64 k) := by
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
  obtain c0 : s.ca.toNat ≤ 1 := Bool.toNat_le _
  obtain l2 := (s2.gpr .r4).isLt
  obtain e2 : (s2.gpr .r4).toNat = s.ca.toNat := by omega_using [v2, c0]
  obtain r4' : Rest [.r4, .r5, .r8] s s4 :=
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
  obtain c0 : s.ca.toNat ≤ 1 := Bool.toNat_le _
  obtain l2 := (s2.gpr .r4).isLt
  have c2 := u2.ca
  obtain g8 : s2.gpr .r8 = 0#64 := by rw [u2.other _ (by decide), RegUpd.gpr_write_self]
  obtain e3 : (s3.gpr .r4).toNat = 1 - s.ca.toNat := by
    rw [u3.gpr, g8]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp c0 with h | h
    · have : s2.gpr .r4 = BitVec.allOnes 64 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_allOnes]; omega_using [v2, h])
      rw [this, h]; rfl
    · have : s2.gpr .r4 = 0#64 := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega_using [v2, h])
      rw [this, h]; rfl
  obtain r4' : Rest [.r4, .r5, .r8] s s4 :=
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
    obtain v3 := h3.val (by decide)
    obtain v5 := h5.val (by decide)
    rw [colsV_cvD_false] at v1 v3 v5
    rw [foldW_val s2 e4 e5 e8, m2] at v3
    rw [foldW_val s4 f4 f5 f8, m4] at v5
    rw [V_eq_cols, V_eq_cols, V_eq_cols]
    obtain b1 := V_cols_lt (b := b) s1.mem o; have b3 := V_cols_lt (b := b) s3.mem o
    obtain b5 := V_cols_lt (b := b) s5.mem o
    obtain c1 : s1.ca.toNat ≤ 1 := Bool.toNat_le _
    obtain c3 : s3.ca.toNat ≤ 1 := Bool.toNat_le _
    obtain c5 : s5.ca.toNat ≤ 1 := Bool.toNat_le _
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at v1 v3 v5
    generalize colsV (ew s.mem b x) 7 = X at *
    generalize colsV (ew s.mem b y) 7 = Y at *
    obtain z5 : s5.ca.toNat = 0 := by omega_using [e4, e5, f4, f5, b1, b3, b5, c1, c3, c5, v3, v5, v1]
    obtain key : colsV (ew s5.mem b o) 7 + (2 ^ 224 * 2 ^ 224 - 2 ^ 224 - 1) * (s1.ca.toNat + s3.ca.toNat) =
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
    obtain v3 := h3.val (by decide)
    obtain v5 := h5.val (by decide)
    obtain w1 := colsV_cvD_true (ew s.mem b y) fun j => dw_lt _ _ _
    obtain w3 := colsV_cvD_true (fun j => (s2.gpr (foldSrc64 j)).toNat) fun j => (s2.gpr _).isLt
    obtain w5 := colsV_cvD_true (fun j => (s4.gpr (foldSrc64 j)).toNat) fun j => (s4.gpr _).isLt
    rw [foldW_val s2 e4 e5 e8] at w3
    rw [foldW_val s4 f4 f5 f8] at w5
    rw [m2] at v3
    rw [m4] at v5
    rw [V_eq_cols, V_eq_cols, V_eq_cols]
    obtain b1 := V_cols_lt (b := b) s1.mem o; have b3 := V_cols_lt (b := b) s3.mem o
    obtain b5 := V_cols_lt (b := b) s5.mem o
    obtain c1 : s1.ca.toNat ≤ 1 := Bool.toNat_le _
    obtain c3 : s3.ca.toNat ≤ 1 := Bool.toNat_le _
    obtain c5 : s5.ca.toNat ≤ 1 := Bool.toNat_le _
    simp only [↓reduceIte] at v1 v3 v5
    generalize colsV (ew s.mem b x) 7 = X at *
    generalize colsV (ew s.mem b y) 7 = Y at *
    generalize colsV (fun j => cvD true (ew s.mem b y j)) 7 = Y' at *
    generalize colsV (fun j => cvD true ((s2.gpr (foldSrc64 j)).toNat)) 7 = F3 at *
    generalize colsV (fun j => cvD true ((s4.gpr (foldSrc64 j)).toNat)) 7 = F5 at *
    obtain z5 : s5.ca.toNat = 1 := by omega_using [e4, e5, f4, f5, b1, b3, b5, c1, c3, c5, v1, w1, w3, v3, w5, v5]
    obtain key : colsV (ew s5.mem b o) 7 + Y =
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
  obtain eA : dw s.mem b (a + 8 * k) = dw s0.mem b (a + 8 * k) := dw_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_using [hoa, hk]) (by omega_using [ha, hk]) (by omega_using [ho, hk])
  obtain g5 : s.gpr .r5 = BitVec.ofNat 64 39081 := by rw [h.rest.gpr _ (by decide), h5]
  unfold a24Step
  refine ldw_ok hc (by omega_using [ha, hk]) (by omega_using [ha4]) ?_
  generalize hs1 : s.write .r8 (s.mem.readW (b + BitVec.ofNat 64 (a + 8 * k)) 64) = s1
  obtain u1 : Upd s s1 .r8 (s.mem.readW (b + BitVec.ofNat 64 (a + 8 * k)) 64) := hs1 ▸ Upd.write _ _ _
  obtain c1 : s1.ca = s.ca := by rw [← hs1, RegUpd.ca_write]
  obtain w1 : (s1.gpr .r8).toNat = dw s0.mem b (a + 8 * k) := by rw [u1.gpr, ← eA]; rfl
  obtain g51 : s1.gpr .r5 = BitVec.ofNat 64 39081 := by rw [u1.other _ (by decide), g5]
  refine wp_wr64 exec_mul fun s2 u2 c2 => a24Op_ok k fun s3 u3 => wp_wr64 exec_mulhu fun s4 u4 c4 => ?_
  obtain hw := dw_lt s0.mem b (a + 8 * k)
  obtain lo : (s2.gpr .r9).toNat = dw s0.mem b (a + 8 * k) * 39081 % 2 ^ 64 := by
    rw [u2.gpr, BitVec.toNat_mul, w1, g51]; rfl
  obtain r72 : s2.gpr .r7 = s.gpr .r7 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  obtain c2' : s2.ca = s.ca := by rw [c2, c1]
  have v3 := u3.val
  rw [lo, r72, c2'] at v3
  obtain g83 : s3.gpr .r8 = s1.gpr .r8 := by rw [u3.other _ (by decide), u2.other _ (by decide)]
  obtain g53 : s3.gpr .r5 = s1.gpr .r5 := by rw [u3.other _ (by decide), u2.other _ (by decide)]
  obtain hi : (s4.gpr .r7).toNat = dw s0.mem b (a + 8 * k) * 39081 / 2 ^ 64 := by
    rw [u4.gpr, g83, g53, w1, g51, show (BitVec.ofNat 64 39081).toNat = 39081 from rfl,
      toNat_imm (Nat.div_lt_of_lt_mul (by omega_using [w1]))]
  obtain g94 : s4.gpr .r9 = s3.gpr .r9 := u4.other _ (by decide)
  obtain r4' : Rest [.r7, .r8, .r9] s s4 :=
    (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))
  obtain hc4 : Ctx b s4 := hc.of_rest r4' (by decide)
  obtain m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  refine sdC_ok hc4 (by omega_using [ho, hk]) (by omega_using [ho4]) fun t ut ct => WP.block_nil
    ⟨hc4.of_rest (ut.rest []) (by decide), h.rest.trans (r4'.trans (ut.rest _)), ?_, ?_⟩
  · rw [ut.mem, m4]
    exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [ho, hk]))
  · have ew1 : ∀ j < k, ew t.mem b o j = ew s.mem b o j := fun j hj => by
      show dw _ _ _ = dw _ _ _
      rw [ut.mem, m4, dw_write_other _ _ _ (by omega_using [hj]) (by omega_using [ho, hk, hj]) (by omega_using [ho, hk])]
    obtain es : ew t.mem b o k = (s3.gpr .r9).toNat := by
      show dw _ _ _ = _
      rw [ut.mem, dw_write_self, g94]
    obtain g7 : (t.gpr .r7).toNat = dw s0.mem b (a + 8 * k) * 39081 / 2 ^ 64 := by rw [ut.gpr, hi]
    obtain ct' : t.ca = s3.ca := by rw [ct, c4]
    have hv := h.val
    simp only [colsV]
    rw [colsV_congr ew1, es, g7, ct']
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    have ewk : ew s0.mem b a k = dw s0.mem b (a + 8 * k) := rfl
    rw [ewk]
    obtain dm := Nat.mod_add_div (dw s0.mem b (a + 8 * k) * 39081) (2 ^ 64)
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
    obtain e1 : K * R + K * 2 ^ 64 * C' = K * l + K * H + K * Ci := by
      rw [Nat.mul_assoc, ← Nat.mul_add, v3, Nat.mul_add, Nat.mul_add]
    obtain e2 : K * l + K * (2 ^ 64 * hh) = 39081 * (K * w) := by
      rw [← Nat.mul_add, dm, Nat.mul_comm w, Nat.mul_left_comm]
    obtain e3 : K * (2 ^ 64) * (hh + C') = K * (2 ^ 64 * hh) + K * 2 ^ 64 * C' := by
      rw [Nat.mul_add, Nat.mul_assoc K (2 ^ 64) hh]
    obtain e4 : K * (H + Ci) = K * H + K * Ci := Nat.mul_add _ _ _
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
  obtain r3 : Rest [.r5, .r7] s s3 := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))
  obtain hc3 : Ctx b s3 := hc.of_rest r3 (by decide)
  obtain m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  obtain h5 : s3.gpr .r5 = BitVec.ofNat 64 39081 := by
    rw [u3.other _ (by decide), u2.gpr, u1.gpr]; exact ori_a24
  refine WP.append (wp_range_flatMap (M := isa) (N := 7) (AInv (b := b) o x s3)
    (fun _ _ hk ht => a24Step_ok ho hx ho4 hx4 hox h5 hk ht) 7 (Nat.le_refl _) s3
    ⟨hc3, Rest.refl _ _, Frame.refl _ _, by rw [u3.gpr]; rfl⟩) fun s4 h4 => ?_
  refine wp_addze fun s5 u5 => wp_lsl (by decide) fun s6 u6 => wp_li (by decide) fun s7 u7 => ?_
  have hc4 := h4.ctx
  have v4 : colsV (ew s4.mem b o) 7 + (2 ^ 64) ^ 7 * ((s4.gpr .r7).toNat + s4.ca.toNat) =
      39081 * colsV (ew s3.mem b x) 7 := h4.val
  rw [m3] at v4
  obtain bX := V_cols_lt (b := b) s.mem x
  have v5 := u5.val
  obtain l5 := (s5.gpr .r4).isLt
  obtain c5 : s5.ca.toNat ≤ 1 := Bool.toNat_le _
  obtain e5 : (s5.gpr .r4).toNat = (s4.gpr .r7).toNat + s4.ca.toNat := by omega_using [v4, bX, v5]
  obtain ht : (s5.gpr .r4).toNat < 2 ^ 32 := by omega_using [v4, bX, v5]
  obtain r7' : Rest [.r4, .r5, .r8] s4 s7 :=
    (u5.rest (by simp)).trans ((u6.rest (by simp)).trans (u7.rest (by simp)))
  obtain hc7 : Ctx b s7 := hc4.of_rest r7' (by decide)
  obtain m7 : s7.mem = s4.mem := by rw [u7.mem, u6.mem, u5.mem]
  obtain f4 : (s7.gpr .r4).toNat = (s5.gpr .r4).toNat := by rw [u7.other _ (by decide), u6.other _ (by decide)]
  obtain f5 : (s7.gpr .r5).toNat = 2 ^ 32 * (s5.gpr .r4).toNat := by
    rw [u7.other _ (by decide), u6.gpr, toNat_shl, Nat.mod_eq_of_lt (by omega_using [ht])]; omega_using []
  obtain f8 : (s7.gpr .r8).toNat = 0 := by rw [u7.gpr]; rfl
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
    obtain v11 : colsV (ew s11.mem b o) 7 + (2 ^ 64) ^ 7 * s11.ca.toNat =
        colsV (ew s10.mem b o) 7 + colsV (fun j => cvD false ((s10.gpr (foldSrc64 j)).toNat)) 7 + 0 :=
      h11.val (by decide)
    rw [colsV_cvD_false, foldW_val s7 f4 f5 f8, m7] at v9
    rw [colsV_cvD_false, foldW_val s10 e4' e5' e8', m10] at v11
    obtain key := fold2_arith ht (V_cols_lt s4.mem o) (V_cols_lt s9.mem o) (Bool.toNat_le _) v9 v11
    rw [V_eq_cols, V_eq_cols, key, e5, v4]


end

end VG.Proof.X448.PPC64LE

end

end

/-!
# X448 on PPC64LE: multiplication

`mul o x y` (`mulX`) stores at `o` a number congruent to `[x] · [y]`, in
registers it does not restore (`clobR`; `mul_ok`): it loads the operands
(`ldsAt_ok`), computes the product's fourteen doublewords (`columns_ok`,
`Proof/X448/PPC64LE/Product.lean`), reduces them by three carry chains and
two folds (`chainN_ok`, `rotsN_ok`, `reduceR_ok`, whose arithmetic is
`reduce_arith`), and stores the result (`stdsAt_ok`). Also the rows of a
product of limbs (`row_ok`, the loop invariant `RowInv`: after `i` rows,
`ACC[0, i + 14)` holds the limbs of `x_{<i} · y`), which Ed448's scalar
arithmetic uses.
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P)

theorem ACC_eq : ACC = 952 := rfl

section
variable {b : Addr}

theorem zeroAcc_ok {s : State} (hc : Ctx b s) :
    WP isa (.block zeroAcc) s fun s' => (∀ j < 14, accw ACC s'.mem b j = 0) ∧
      Frame [⟨b + BitVec.ofNat 64 ACC, 56⟩] s.mem s'.mem ∧ Rest [.r7] s s' := by
  unfold zeroAcc
  refine wp_li (by decide) fun s1 u1 => ?_
  obtain hc1 := hc.of_rest (u1.rest (ws := [.r7]) (by decide)) (by decide)
  refine WP.mono (stores_ok (r := .r7) (o := ACC) (n := 14) (by decide) hc1) fun s' ⟨h1, h2, _, h4⟩ =>
    ⟨fun j hj => by rw [accw, h1 j hj, u1.gpr]; rfl, by rw [← u1.mem]; exact h2,
      (u1.rest (by decide)).trans (h4.mono (by decide))⟩

/-- The loop invariant of the rows of `mul o x y` from `s0`, after `i` rows. -/
structure RowInv (b : Addr) (x y : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest clob s0 s
  r9 : s.gpr .r9 = b + BitVec.ofNat 64 (4 * i)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (14 - i)
  frame : Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s0.mem s.mem
  val : val32 (accw ACC s.mem b) (i + 14) = val32 (limb s0.mem b x) i * V s0.mem b y

theorem mulPre_ok {x y : Nat} {s : State} (hc : Ctx b s) :
    WP isa (.block (zeroAcc ++ ([.addi .r9 .r6 0, .li .r11 14] : List Instr))) s
      (RowInv b x y s 0) := by
  refine WP.append (zeroAcc_ok hc) fun s2 ⟨hz, hf2, hr2⟩ => ?_
  obtain hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  refine wp_addi (by decide) (by decide) fun s3 u3 => wp_li (by decide) fun s4 u4 => WP.block_nil ?_
  obtain hr : Rest clob s s4 :=
    (hr2.mono (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
  obtain hm4 : s4.mem = s2.mem := by rw [u4.mem, u3.mem]
  refine ⟨hc.of_rest hr (by decide), hr, ?_, u4.gpr, ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.gpr, hc2.r6]
  · rw [hm4]; exact hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
  · rw [hm4, val32_congr (g := fun _ => 0) (fun k hk => hz k hk), val32_zero_fn]
    exact (Nat.zero_mul _).symm

theorem row_ok {x y : Nat} (hx : x + 56 ≤ ACC) (hy : y + 56 ≤ ACC)
    {s0 : State} {i : Nat} (hi : i < 14) {s : State} (h : RowInv b x y s0 i s) :
    WP isa (.block (row x y)) s fun s' =>
      RowInv b x y s0 (i + 1) s' ∧ (s'.gpr .r11 != 0) = decide (14 - (i + 1) ≠ 0) := by
  have hA := ACC_eq
  obtain hframe0 : ∀ z : Nat, z + 56 ≤ ACC → ∀ k < 14,
      limb s.mem b z k = limb s0.mem b z k := fun z hz k hk =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  simp only [row, List.cons_append, List.nil_append]
  refine wp_lw (a := b + BitVec.ofNat 64 (x + 4 * i)) (by decide) (by omega_arith)
    (by rw [h.r9, Offset.add_add, Nat.add_comm]) (h.ctx.inR (by omega_arith)) fun s1 u1 => ?_
  refine wp_li (by decide) fun s2 u2 => ?_
  obtain hr2 : Rest [.r4, .r8] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hc2 : Ctx b s2 := h.ctx.of_rest hr2 (by decide)
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  obtain e1 : (s2.gpr .r4).toNat = limb s0.mem b x i := by
    rw [u2.other _ (by decide), u1.gpr, toNat_ext32, ← hframe0 x hx i hi]; rfl
  obtain e9 : s2.gpr .r9 = b + BitVec.ofNat 64 (4 * i) := by rw [hr2.gpr _ (by decide), h.r9]
  obtain hlt : ∀ j < 14, rowC (accw ACC s.mem b) (limb s0.mem b x) (limb s0.mem b y) i j + 2 ^ 32 ≤ 2 ^ 64 :=
    fun j _ => rowC_le (limb_lt _ _ _ _) (limb_lt _ _ _ _) (wd_lt _ _ _)
  refine WP.append (pass_ok (rb := .r9) (o := ACC) (s0 := s2)
    (c := rowC (accw ACC s.mem b) (limb s0.mem b x) (limb s0.mem b y) i)
    (cin := 0) (by decide) (by decide) (by omega_arith)
    (fun k hk => by rw [e9, Offset.add_add]; exact hc2.inW (by omega_arith))
    (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    obtain hc' : Ctx b s' := hc2.of_rest hp'.rest (by decide)
    obtain hf' : Frame [⟨b + BitVec.ofNat 64 (4 * i + ACC), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [e9, Offset.add_add] at this
    simp only [rowSrc]
    refine lw0_ok hc' (d := y + 4 * k) (by omega_arith) fun t1 v1 => ?_
    refine wp_mul fun t2 v2 => ?_
    refine wp_lw (a := b + BitVec.ofNat 64 (4 * i + (ACC + 4 * k))) (by decide) (by omega_arith)
      (by rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), e9,
        Offset.add_add]) (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc'.inR (by omega_arith))
      fun t3 v3 => ?_
    refine wp_add fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have ey : (t1.gpr .r5).toNat = limb s0.mem b y k := by
        rw [v1.gpr, toNat_ext32, ← hframe0 y hy k hk, ← hm2]
        show wd s'.mem _ _ = wd s2.mem _ _
        exact wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      obtain ea : (t1.gpr .r4).toNat = limb s0.mem b x i := by
        rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
      obtain e2 : (t2.gpr .r5).toNat = limb s0.mem b x i * limb s0.mem b y k := by
        rw [v2.gpr, toNat_mul_lt (by rw [ea, ey]; exact mul32_lt (limb_lt _ _ _ _) (limb_lt _ _ _ _)), ea, ey]
      obtain e3 : (t3.gpr .r7).toNat = accw ACC s.mem b (i + k) := by
        rw [v3.gpr, toNat_ext32, v2.mem, v1.mem, accw, ← hm2]
        show wd s'.mem _ _ = _
        rw [wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)]
        congr 1; omega_arith
      have := hlt k hk
      rw [v4.gpr, v3.other .r5 (by decide)]
      rw [toNat_add_lt (by rw [e3, e2]; simp only [rowC] at this; omega_arith), e3, e2,
        rowC, Nat.add_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · -- The carry, and the next row.
    obtain hc3 : Ctx b s3 := hc2.of_rest hp.rest (by decide)
    obtain e9' : s3.gpr .r9 = b + BitVec.ofNat 64 (4 * i) := by rw [hp.rest.gpr _ (by decide), e9]
    refine wp_sw (a := b + BitVec.ofNat 64 (4 * i + (ACC + 56))) (by decide) (by omega_arith)
      (by rw [e9', Offset.add_add]) (hc3.inW (by omega_arith)) fun s4 u4 => ?_
    refine wp_addi (by decide) (by decide) fun s5 u5 => wp_subi (by decide) (by decide) fun s6 u6 => ?_
    refine WP.block_nil ?_
    obtain hr6 : Rest [.r4, .r5, .r7, .r8, .r9, .r11] s s6 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans (u6.rest (by decide)))))
    obtain hm6 : s6.mem = s3.mem.writeW (b + BitVec.ofNat 64 (4 * i + (ACC + 56))) ((s3.gpr .r8).setWidth 32) := by
      rw [u6.mem, u5.mem, u4.mem]
    obtain hpf : Frame [⟨b + BitVec.ofNat 64 (4 * i + ACC), 56⟩] s.mem s3.mem := by
      have := hp.frame; rw [e9, Offset.add_add] at this; rw [← hm2]; exact this
    obtain hr11 : s6.gpr .r11 = BitVec.ofNat 64 (14 - (i + 1)) := by
      rw [u6.gpr, u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide), hr2.gpr _ (by decide), h.r11,
        ofNat_sub_one (by omega_arith) (by omega_arith)]
      congr 1
    obtain hch := chain_lt (cin := 0) hlt (by decide) 14 (Nat.le_refl _)
    -- The limbs of `ACC` after the row.
    obtain hacc : ∀ k < i + 15, accw ACC s6.mem b k =
        rowAcc (accw ACC s.mem b) (limb s0.mem b x) (limb s0.mem b y) i k := by
      intro k hk
      rw [accw, hm6]
      rcases Nat.lt_or_ge k (i + 14) with hk' | hk'
      · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
        rcases Nat.lt_or_ge k i with hki | hki
        · rw [wd_frame hpf fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)]
          simp only [rowAcc, hki, ite_true]; rfl
        · have := hp.outs (k - i) (by omega_arith)
          rw [e9, wd_shift, show 4 * i + (ACC + 4 * (k - i)) = ACC + 4 * k by omega_arith] at this
          rw [this]
          simp only [rowAcc, show ¬ k < i by omega_arith, hk', ite_false, ite_true]
      · rw [show ACC + 4 * k = 4 * i + (ACC + 56) by omega_arith, wd_write_self, toNat_lo32, hp.r8,
          Nat.mod_eq_of_lt hch]
        simp only [rowAcc, show ¬ k < i by omega_arith, show ¬ k < i + 14 by omega_arith, ite_false]
    refine ⟨⟨hc3.of_rest ((u4.rest [.r9, .r11]).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))
        (by decide), h.rest.trans (hr6.mono (by decide)), ?_, hr11, ?_, ?_⟩, ?_⟩
    · rw [u6.other _ (by decide), u5.gpr, u4.gpr, e9', Offset.add_add, Nat.mul_succ]
    · rw [hm6]
      refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [val32_congr hacc]; exact row_val h.val
    · rw [hr11, ofNat_ne_zero (by omega_arith)]

/-! ## The reduction -/

/-- What `rotR k` leaves in `rotReg k`: doubleword `k` of `h` rotated by 224 bits. -/
def rotW (h : Nat → Nat) (k : Nat) : Nat := h ((k + 3) % 7) / 2 ^ 32 + h ((k + 4) % 7) % 2 ^ 32 * 2 ^ 32

/-- What `hiReg k` holds: doubleword `k` of `h` with its low 224 bits cleared. -/
def hiW (h : Nat → Nat) (k : Nat) : Nat :=
  if k < 3 then 0 else if k = 3 then h 3 / 2 ^ 32 * 2 ^ 32 else h k

/-- The low 224 bits of `colsV h 7`. -/
def loP (h : Nat → Nat) : Nat := h 0 + 2 ^ 64 * h 1 + 2 ^ 128 * h 2 + 2 ^ 192 * (h 3 % 2 ^ 32)

/-- `colsV h 7` above bit 224. -/
def hiP (h : Nat → Nat) : Nat := h 3 / 2 ^ 32 + 2 ^ 32 * h 4 + 2 ^ 96 * h 5 + 2 ^ 160 * h 6

theorem colsV_split (h : Nat → Nat) : colsV h 7 = loP h + 2 ^ 224 * hiP h := by
  have := Nat.mod_add_div (h 3) (2 ^ 32)
  simp only [colsV, loP, hiP]
  generalize h 3 % 2 ^ 32 = l at *
  generalize h 3 / 2 ^ 32 = a at *
  omega_arith

theorem colsV_rotW (h : Nat → Nat) : colsV (rotW h) 7 = hiP h + 2 ^ 224 * loP h := by
  obtain e0 := Nat.mod_add_div (h 0) (2 ^ 32); have e1 := Nat.mod_add_div (h 1) (2 ^ 32)
  obtain e2 := Nat.mod_add_div (h 2) (2 ^ 32); have e3 := Nat.mod_add_div (h 3) (2 ^ 32)
  obtain e4 := Nat.mod_add_div (h 4) (2 ^ 32); have e5 := Nat.mod_add_div (h 5) (2 ^ 32)
  obtain e6 := Nat.mod_add_div (h 6) (2 ^ 32)
  simp only [colsV, rotW, loP, hiP, Nat.reduceAdd, Nat.reduceMod]
  generalize h 0 % 2 ^ 32 = l0 at *; generalize h 0 / 2 ^ 32 = a0 at *
  generalize h 1 % 2 ^ 32 = l1 at *; generalize h 1 / 2 ^ 32 = a1 at *
  generalize h 2 % 2 ^ 32 = l2 at *; generalize h 2 / 2 ^ 32 = a2 at *
  generalize h 3 % 2 ^ 32 = l3 at *; generalize h 3 / 2 ^ 32 = a3 at *
  generalize h 4 % 2 ^ 32 = l4 at *; generalize h 4 / 2 ^ 32 = a4 at *
  generalize h 5 % 2 ^ 32 = l5 at *; generalize h 5 / 2 ^ 32 = a5 at *
  generalize h 6 % 2 ^ 32 = l6 at *; generalize h 6 / 2 ^ 32 = a6 at *
  omega_arith

theorem colsV_hiW (h : Nat → Nat) : colsV (hiW h) 7 = 2 ^ 224 * hiP h := by
  simp only [colsV, hiW, hiP, Nat.reduceLT, Nat.lt_irrefl, Nat.reduceEqDiff, ↓reduceIte]
  generalize h 3 / 2 ^ 32 = a
  omega_arith

theorem mul_mod_shift (c : Nat) : c * 2 ^ 32 % 2 ^ 64 = c % 2 ^ 32 * 2 ^ 32 :=
  Nat.mul_mod_mul_right (2 ^ 32) c (2 ^ 32)

/-- The value of the reduction: the sums `S + 2⁴⁴⁸ c` of its three chains, folded twice, are
congruent to the product. -/
theorem reduce_arith {L Lo Hi S c S9 c9 S11 c11 : Nat} (hc : c ≤ 3) (hS : S < 2 ^ 224 * 2 ^ 224)
    (hS9 : S9 < 2 ^ 224 * 2 ^ 224) (h11 : c11 ≤ 1)
    (v : S + (2 ^ 64) ^ 7 * c = L + Lo + 2 ^ 224 * Hi + (Hi + 2 ^ 224 * Lo) + 2 ^ 224 * Hi)
    (v9 : S9 + (2 ^ 64) ^ 7 * c9 = S + (c + 2 ^ 224 * c) + 0)
    (v11 : S11 + (2 ^ 64) ^ 7 * c11 = S9 + (c9 + 2 ^ 224 * c9) + 0) :
    S11 % P = (L + (2 ^ 64) ^ 7 * (Lo + 2 ^ 224 * Hi)) % P := by
  have z : c11 = 0 := by omega
  have key : S11 + (2 ^ 224 * 2 ^ 224 - 2 ^ 224 - 1) * (c + c9 + Lo + (2 ^ 224 + 1) * Hi) =
      L + (2 ^ 64) ^ 7 * (Lo + 2 ^ 224 * Hi) := by
    omega_using [hc, hS, hS9, v, v9, v11]
  rw [P_eq, ← key, Nat.add_mul_mod_self_left]

/-! ## Stores and loads at offsets of the working space -/

open VG.PPC64LE.Spill (saveMem Saved Fits saveMem_saved saveMem_frame_base)

/-- `stdsAt base l`: the memory is `saveMem` of the registers of `l`, from `b + base`. -/
theorem stdsAt_ok {base : Nat} {l : List (Reg × Nat)} (h4 : base % 4 = 0)
    (hl : ∀ p ∈ l, p.2 % 4 = 0 ∧ base + p.2 + 8 ≤ 4096) {s : State} (hc : Ctx b s)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (b + BitVec.ofNat 64 base) s.gpr l → WP isa (.block rest) s' Q) :
    WP isa (.block (stdsAt base l ++ rest)) s Q := by
  induction l generalizing s with
  | nil => exact k s rfl rfl rfl rfl rfl
  | cons p l ih =>
    obtain ⟨r, d⟩ := p
    obtain hd := hl (r, d) List.mem_cons_self
    simp only [stdsAt, List.map_cons, List.cons_append]
    refine sd0_ok hc (d := base + d) (by omega_using [hd]) (by omega_using [h4, hd]) fun s1 u1 => ?_
    obtain hc1 : Ctx b s1 := ⟨by rw [u1.gpr]; exact hc.r6, by rw [u1.wr]; exact hc.wr⟩
    refine ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hc1 fun s' g' rd' wr' sp' m' => ?_
    refine k s' (g'.trans u1.gpr) (rd'.trans u1.rd) (wr'.trans u1.wr) (sp'.trans u1.sp) ?_
    rw [m', u1.mem, u1.gpr, saveMem, Offset.add_add]

/-- `ld0_ok`, which also keeps the link register. -/
theorem ld0_okL {s : State} (hc : Ctx b s) {t : Reg} {d : Nat} {is : List Instr} {Q : State → Prop}
    (hd : d + 8 ≤ 4096) (hd4 : d % 4 = 0)
    (k : ∀ s', Upd s s' t (s.mem.readW (b + BitVec.ofNat 64 d) 64) → s'.lr = s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t .r6 d :: is)) s Q := by
  obtain e := exec_load_d (s := s) (t := t) (n := .r6) (off := d) (by decide) ⟨by omega_using [hd], hd4⟩
    (by rw [hc.r6]; exact hc.inR hd)
  rw [hc.r6] at e
  exact WP.cons e (k _ (Upd.write _ _ _) rfl)

/-- `ldsAt base l`: each register of `l` (distinct, none `r6`) holds its
doubleword from `b + base`. -/
theorem ldsAt_ok {base : Nat} {l : List (Reg × Nat)} (h4 : base % 4 = 0)
    (hl : ∀ p ∈ l, p.2 % 4 = 0 ∧ base + p.2 + 8 ≤ 4096) (hr : (l.map Prod.fst).Nodup)
    (h6 : ∀ p ∈ l, p.1 ≠ .r6) {s : State} (hc : Ctx b s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx b s' → Rest (l.map Prod.fst) s s' → s'.mem = s.mem → s'.lr = s.lr →
      (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (b + BitVec.ofNat 64 base + BitVec.ofNat 64 p.2) 64) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (ldsAt base l ++ rest)) s Q := by
  induction l generalizing s with
  | nil => exact k s hc (Rest.refl _ _) rfl rfl fun _ h => absurd h List.not_mem_nil
  | cons p l ih =>
    obtain ⟨r, d⟩ := p
    obtain hd := hl (r, d) List.mem_cons_self
    obtain hnd := List.nodup_cons.mp hr
    obtain hr6 : r ≠ .r6 := h6 (r, d) List.mem_cons_self
    simp only [ldsAt, List.map_cons, List.cons_append]
    refine ld0_okL hc (d := base + d) (by omega_using [hd]) (by omega_using [h4, hd]) fun s1 u1 l1 => ?_
    obtain hr1 : Rest ((r, d) :: l |>.map Prod.fst) s s1 := u1.rest List.mem_cons_self
    obtain hc1 : Ctx b s1 := hc.of_rest hr1 (by
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨Ne.symm hr6, fun hm => by
        obtain ⟨q, hq, e⟩ := List.mem_map.mp hm
        exact h6 q (List.mem_cons_of_mem _ hq) e⟩)
    refine ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hnd.2
      (fun q hq => h6 q (List.mem_cons_of_mem _ hq)) hc1 fun s' c' r' m' l' v' => ?_
    refine k s' c' (hr1.trans (r'.mono fun x hx => List.mem_cons_of_mem _ hx)) (m'.trans u1.mem)
      (l'.trans l1) fun q hq => ?_
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [r'.gpr _ hnd.1, u1.gpr, Offset.add_add]
    · rw [v' q hq, u1.mem]

/-! ## The carry chains of the reduction -/

/-- After `n` steps of `chain7 src` from `s0` (`src` apart from `pw 0`, …,
`pw 6`): `pw 0`, …, `pw (n - 1)` and CA hold `pw_{<n} + src_{<n}`. -/
theorem chainN_ok {src : Nat → Reg} (hs : ∀ k < 7, ∀ j < 7, src k ≠ pw j) {s0 : State} :
    ∀ n ≤ 7, WP isa (.block ((List.range n).map fun k => chainR k (src k))) s0 fun s =>
      colsV (fun j => (s.gpr (pw j)).toNat) n + (2 ^ 64) ^ n * (if n = 0 then 0 else s.ca.toNat) =
        colsV (fun j => (s0.gpr (pw j)).toNat) n + colsV (fun j => (s0.gpr (src j)).toNat) n ∧
      Rest clobR s0 s ∧ (∀ r, (∀ j < n, r ≠ pw j) → s.gpr r = s0.gpr r) ∧ s.mem = s0.mem
  | 0, _ => WP.block_nil ⟨by simp [colsV], Rest.refl _ _, fun _ _ => rfl, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.append (chainN_ok hs n (by omega_using [hn])) fun s1 ⟨v1, r1, k1, m1⟩ => ?_
    obtain hpn : ∀ j < n, pw n ≠ pw j := fun j hj e => by have := pw_inj _ (by omega_using [hn]) _ (by omega_using [hn, hj]) e; omega_using [hj, this]
    obtain e0 : s1.gpr (pw n) = s0.gpr (pw n) := k1 _ hpn
    obtain es : s1.gpr (src n) = s0.gpr (src n) := k1 _ fun j hj => hs n (by omega_using [hn]) j (by omega_using [hn, hj])
    obtain hpc : pw n ∈ clobR := (pw_facts n (by omega_using [hn])).2.2.2
    obtain fin : ∀ (s2 : State), UpdC s1 s2 (pw n) ((s1.gpr (pw n)).toNat + (s1.gpr (src n)).toNat +
        (if n = 0 then 0 else s1.ca.toNat)) → WP isa (.block []) s2 fun s =>
        colsV (fun j => (s.gpr (pw j)).toNat) (n + 1) + (2 ^ 64) ^ (n + 1) *
          (if n + 1 = 0 then 0 else s.ca.toNat) =
          colsV (fun j => (s0.gpr (pw j)).toNat) (n + 1) + colsV (fun j => (s0.gpr (src j)).toNat) (n + 1) ∧
        Rest clobR s0 s ∧ (∀ r, (∀ j < n + 1, r ≠ pw j) → s.gpr r = s0.gpr r) ∧ s.mem = s0.mem := by
      intro s2 u2
      refine WP.block_nil ⟨?_, r1.trans (u2.rest hpc), fun r hr => ?_, u2.mem.trans m1⟩
      · have hlow : colsV (fun j => (s2.gpr (pw j)).toNat) n = colsV (fun j => (s1.gpr (pw j)).toNat) n :=
          colsV_congr fun j hj => by rw [u2.other _ (Ne.symm (hpn j hj))]
        have v2 := u2.val
        rw [e0, es] at v2
        obtain h2 := congrArg ((2 ^ 64) ^ n * ·) v2
        simp only [Nat.mul_add] at h2
        rw [colsV, colsV, colsV, hlow, show (2 ^ 64) ^ (n + 1) = (2 ^ 64) ^ n * 2 ^ 64 from Nat.pow_succ _ _,
          Nat.mul_assoc]
        simp only [Nat.add_one_ne_zero, ↓reduceIte]
        generalize (2 ^ 64) ^ n = K at *
        omega_using [v1, h2]
      · rw [u2.other _ (hr n (by omega_using [])), k1 _ fun j hj => hr j (by omega_using [hj])]
    by_cases h0 : n = 0
    · subst h0
      simp only [chainR, ↓reduceIte]
      exact wp_addc fun s2 u2 => fin s2 (by simpa using u2)
    · simp only [chainR, h0, ↓reduceIte]
      exact wp_adde fun s2 u2 => fin s2 (by simpa [h0] using u2)

/-! ## The reduction in registers -/

theorem rot_facts : ∀ k < 7, rotReg k ≠ .r18 ∧ rotReg k ≠ .r4 ∧ rotReg k ∈ clobR ∧
    (∀ j < 14, rotReg k ≠ pw j) ∧ (∀ j < 7, j ≠ k → rotReg k ≠ rotReg j) := by decide

theorem pw_ne : ∀ j < 14, pw j ≠ .r18 ∧ pw j ≠ .r19 ∧ pw j ≠ .r20 := by decide

theorem hiReg_ne : ∀ k < 7, ∀ j < 7, hiReg k ≠ pw j := by decide

theorem foldReg_ne : ∀ k < 7, ∀ j < 7, foldReg k ≠ pw j := by decide

theorem hi_ne : ∀ k < 7, ∀ j < 7, pw (7 + k) ≠ pw j := by decide

/-- After `n` steps of the rotation from `s0`: `rotReg j` (`j < n`) holds
doubleword `j` of the high half `pw 7`, …, `pw 13` rotated by 224 bits. -/
theorem rotsN_ok {s0 : State} : ∀ n ≤ 7, WP isa (.block ((List.range n).flatMap rotR)) s0 fun s =>
    Rest clobR s0 s ∧ s.mem = s0.mem ∧ (∀ r, r ≠ .r18 → (∀ j < n, r ≠ rotReg j) → s.gpr r = s0.gpr r) ∧
    ∀ j < n, (s.gpr (rotReg j)).toNat = rotW (fun i => (s0.gpr (pw (7 + i))).toNat) j
  | 0, _ => WP.block_nil ⟨Rest.refl _ _, rfl, fun _ _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.append (rotsN_ok n (by omega_using [hn])) fun s1 ⟨r1, m1, k1, v1⟩ => ?_
    obtain ⟨t27, -, tc, tpw, ttr⟩ := rot_facts n (by omega_using [hn])
    obtain kpw : ∀ i < 14, s1.gpr (pw i) = s0.gpr (pw i) := fun i hi =>
      k1 _ (pw_ne i hi).1 fun j hj e => (rot_facts j (by omega_using [hn, hj])).2.2.2.1 i hi e.symm
    simp only [rotR]
    refine wp_lsr (by decide) fun s2 u2 => wp_lsl (by decide) fun s3 u3 => wp_add fun s4 u4 => WP.block_nil ?_
    obtain hx : s2.gpr (rotReg n) = s0.gpr (pw (7 + (n + 3) % 7)) >>> 32 := by
      rw [u2.gpr, kpw _ (by omega_using [])]
    obtain hy : s3.gpr .r18 = s0.gpr (pw (7 + (n + 4) % 7)) <<< 32 := by
      rw [u3.gpr, u2.other _ (tpw _ (by omega_using [])).symm, kpw _ (by omega_using [])]
    obtain hv : (s4.gpr (rotReg n)).toNat = rotW (fun i => (s0.gpr (pw (7 + i))).toNat) n := by
      rw [u4.gpr, u3.other _ t27, hx, hy]
      obtain l1 : (s0.gpr (pw (7 + (n + 3) % 7)) >>> 32).toNat < 2 ^ 32 := by
        rw [toNat_shr]; have := (s0.gpr (pw (7 + (n + 3) % 7))).isLt; omega_using []
      obtain l2 : (s0.gpr (pw (7 + (n + 4) % 7)) <<< 32).toNat =
          (s0.gpr (pw (7 + (n + 4) % 7))).toNat % 2 ^ 32 * 2 ^ 32 := by
        rw [toNat_shl, mul_mod_shift]
      obtain l3 : (s0.gpr (pw (7 + (n + 4) % 7))).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
      rw [toNat_add_lt (by rw [l2]; omega_arith), toNat_shr, l2]; rfl
    refine ⟨r1.trans ((u2.rest tc).trans ((u3.rest (by decide)).trans (u4.rest tc))),
      by rw [u4.mem, u3.mem, u2.mem, m1], fun r h27 hr => ?_, fun j hj => ?_⟩
    · have hn' : r ≠ rotReg n := hr n (by omega_using [])
      rw [u4.other _ hn', u3.other _ h27, u2.other _ hn', k1 _ h27 fun j hj => hr j (by omega_using [hj])]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hne : rotReg j ≠ rotReg n := fun e => ttr j (by omega_arith) (by omega_using [hj]) e.symm
        rw [u4.other _ hne, u3.other _ (rot_facts j (by omega_arith)).1, u2.other _ hne, v1 j hj]
      · exact hv

/-- `li r4, 0; addze r4, r4`: the carry into `r4`. -/
theorem capture_ok {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Rest [.r4] s t → t.mem = s.mem → (t.gpr .r4).toNat = s.ca.toNat → WP isa (.block is) t Q) :
    WP isa (.block (.li .r4 0 :: .addze .r4 .r4 :: is)) s Q := by
  refine WP.cons (exec_li (by decide)) (wp_addze fun s2 u2 => ?_)
  have v2 := u2.val
  rw [RegUpd.gpr_write_self, RegUpd.ca_write] at v2
  have z : (BitVec.ofNat 64 0).toNat = 0 := rfl
  rw [z] at v2
  obtain c0 : s.ca.toNat ≤ 1 := Bool.toNat_le _
  obtain l2 := (s2.gpr .r4).isLt
  exact k s2 (((Upd.write _ _ _).rest (by simp)).trans (u2.rest (by simp)))
    (by rw [u2.mem, RegUpd.mem_write]) (by omega_using [v2, c0])

/-- The doublewords of a product of fourteen, split at seven. -/
theorem colsV_14 (f : Nat → Nat) : colsV f 14 = colsV f 7 + (2 ^ 64) ^ 7 * colsV (fun k => f (7 + k)) 7 := by
  simp only [colsV, Nat.reducePow, Nat.reduceAdd]
  omega_using []

/-- `reduceR`: `pw 0`, …, `pw 6` congruent to the product in `pw`. -/
theorem reduceR_ok {s : State} (hc : Ctx b s) :
    WP isa (.block reduceR) s fun s' => Ctx b s' ∧ Rest clobR s s' ∧ s'.mem = s.mem ∧
      colsV (fun j => (s'.gpr (pw j)).toNat) 7 % P = pwSum s 14 % P := by
  obtain hpw7 : ∀ i < 7, pw (7 + i) ∈ clobR := fun i hi => (pw_facts (7 + i) (by omega_using [hi])).2.2.2
  generalize hH : (fun i => (s.gpr (pw (7 + i))).toNat) = H
  unfold reduceR
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- `L + H`.
  refine WP.append (chainN_ok (src := fun k => pw (7 + k)) (fun k hk j hj => hi_ne k hk j hj) 7
    (Nat.le_refl _)) fun s1 ⟨v1, r1, k1, m1⟩ => ?_
  simp only [↓reduceIte, show (7 : Nat) ≠ 0 from by decide] at v1
  obtain kH1 : ∀ i < 7, s1.gpr (pw (7 + i)) = s.gpr (pw (7 + i)) := fun i hi =>
    k1 _ fun j hj => hi_ne i hi j hj
  refine capture_ok fun s2 r2 m2 e2 => ?_
  obtain kH2 : ∀ i < 7, s2.gpr (pw (7 + i)) = s.gpr (pw (7 + i)) := fun i hi => by
    rw [r2.gpr _ (by simp; exact (pw_facts _ (by omega_using [hi])).1), kH1 i hi]
  -- `+= 2²²⁴ Hₗ + Hₕ`.
  refine WP.append (rotsN_ok 7 (Nat.le_refl _)) fun s3 ⟨r3, m3, k3, v3⟩ => ?_
  obtain kp3 : ∀ i < 14, s3.gpr (pw i) = s2.gpr (pw i) := fun i hi =>
    k3 _ (pw_ne i hi).1 fun j hj e => (rot_facts j hj).2.2.2.1 i hi e.symm
  obtain e43 : s3.gpr .r4 = s2.gpr .r4 := k3 _ (by decide) fun j hj e => (rot_facts j hj).2.1 e.symm
  refine WP.append (chainN_ok (src := rotReg) (fun k hk j hj => (rot_facts k hk).2.2.2.1 j (by omega_using [hj])) 7
    (Nat.le_refl _)) fun s4 ⟨v4, r4, k4, m4⟩ => ?_
  simp only [show (7 : Nat) ≠ 0 from by decide, ↓reduceIte] at v4
  obtain e44 : s4.gpr .r4 = s3.gpr .r4 := k4 _ fun j hj e => (pw_facts j (by omega_using [hj])).1 e.symm
  refine wp_addze fun s5 u5 => ?_
  -- `+= 2²²⁴ Hₕ`.
  refine wp_li (by decide) fun s6 u6 => wp_lsr (by decide) fun s7 u7 => wp_lsl (by decide) fun s8 u8 => ?_
  obtain c1 : s1.ca.toNat ≤ 1 := Bool.toNat_le _
  obtain c4 : s4.ca.toNat ≤ 1 := Bool.toNat_le _
  obtain e5 : (s5.gpr .r4).toNat = s1.ca.toNat + s4.ca.toNat := by
    have := u5.val; have := u5.ca; have := (s5.gpr .r4).isLt
    rw [e44, e43, ← e2] at *; omega_arith
  obtain k6 : ∀ i < 14, s6.gpr (pw i) = s4.gpr (pw i) := fun i hi => by
    rw [u6.other _ (pw_ne i hi).2.1, u5.other _ (pw_facts i (by omega_using [hi])).1]
  obtain k8 : ∀ i < 14, s8.gpr (pw i) = s4.gpr (pw i) := fun i hi => by
    rw [u8.other _ (pw_ne i hi).2.2, u7.other _ (pw_ne i hi).2.2, k6 i hi]
  obtain kH4 : ∀ i < 7, s4.gpr (pw (7 + i)) = s.gpr (pw (7 + i)) := fun i hi => by
    rw [k4 _ fun j hj => hi_ne i hi j hj, kp3 _ (by omega_using [hi]), kH2 i hi]
  obtain eZ : s8.gpr .r19 = 0 := by rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr]; rfl
  obtain eW : (s8.gpr .r20).toNat = H 3 / 2 ^ 32 * 2 ^ 32 := by
    rw [u8.gpr, u7.gpr, toNat_shl, toNat_shr, show pw 10 = pw (7 + 3) from rfl, k6 _ (by decide),
      kH4 3 (by decide), ← hH]
    have := (s.gpr (pw (7 + 3))).isLt
    rw [Nat.mod_eq_of_lt (by omega_arith)]
  obtain hH8 : ∀ i < 7, (s8.gpr (pw (7 + i))).toNat = H i := fun i hi => by
    rw [k8 _ (by omega_using [hi]), kH4 i hi, ← hH]
  obtain hsrc3 : colsV (fun j => (s8.gpr (hiReg j)).toNat) 7 = colsV (hiW H) 7 := colsV_congr fun j hj => by
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega_using [hj]
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [hiReg, hiW, Nat.reduceLT, ↓reduceIte, Nat.reduceEqDiff, eZ, eW] <;>
      first | rfl | exact hH8 _ (by decide)
  refine WP.append (chainN_ok (src := hiReg) hiReg_ne 7 (Nat.le_refl _)) fun s9 ⟨v9, r9, k9, m9⟩ => ?_
  simp only [show (7 : Nat) ≠ 0 from by decide, ↓reduceIte] at v9
  rw [hsrc3] at v9
  obtain e94 : (s9.gpr .r4).toNat = s1.ca.toNat + s4.ca.toNat := by
    rw [k9 _ fun j hj e => (pw_facts j (by omega_using [hj])).1 e.symm, u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), e5]
  obtain e9Z : s9.gpr .r19 = 0 := by rw [k9 _ fun j hj e => (pw_ne j (by omega_using [hj])).2.1 e.symm, eZ]
  refine wp_addze fun s10 u10 => wp_lsl (by decide) fun s11 u11 => ?_
  obtain c9 : s9.ca.toNat ≤ 1 := Bool.toNat_le _
  obtain e10 : (s10.gpr .r4).toNat = s1.ca.toNat + s4.ca.toNat + s9.ca.toNat := by
    obtain hv := u10.val; have := u10.ca; rw [e94] at hv; omega_using [c1, c4, c9, hv]
  -- The folds.
  obtain fold_val : ∀ (t : State) (c : Nat), (t.gpr .r4).toNat = c → (t.gpr .r5).toNat = 2 ^ 32 * c →
      t.gpr .r19 = 0 → colsV (fun j => (t.gpr (foldReg j)).toNat) 7 = c + 2 ^ 224 * c := by
    intro t c h4 h5 h18
    simp only [colsV, foldReg, Nat.reduceEqDiff, ↓reduceIte, h4, h5, h18]
    have z : (0 : BitVec 64).toNat = 0 := rfl
    rw [z]; omega_using []
  obtain e11r5 : (s11.gpr .r5).toNat = 2 ^ 32 * (s1.ca.toNat + s4.ca.toNat + s9.ca.toNat) := by
    rw [u11.gpr, toNat_shl, e10, Nat.mod_eq_of_lt (by omega_using [c1, c4, c9]), Nat.mul_comm]
  obtain hf1 := fold_val s11 _ (by rw [u11.other _ (by decide), e10]) e11r5
    (by rw [u11.other _ (by decide), u10.other _ (by decide), e9Z])
  refine WP.append (chainN_ok (src := foldReg) foldReg_ne 7 (Nat.le_refl _)) fun s12 ⟨v12, r12, k12, m12⟩ => ?_
  simp only [show (7 : Nat) ≠ 0 from by decide, ↓reduceIte] at v12
  rw [hf1] at v12
  refine capture_ok fun s13 r13 m13 e13 => wp_lsl (by decide) fun s14 u14 => ?_
  obtain c12 : s12.ca.toNat ≤ 1 := Bool.toNat_le _
  obtain e14Z : s14.gpr .r19 = 0 := by
    rw [u14.other _ (by decide), r13.gpr _ (by decide), k12 _ fun j hj e => (pw_ne j (by omega_using [hj])).2.1 e.symm,
      u11.other _ (by decide), u10.other _ (by decide), e9Z]
  obtain hf2 := fold_val s14 s12.ca.toNat (by rw [u14.other _ (by decide), e13])
    (by rw [u14.gpr, toNat_shl, e13, Nat.mod_eq_of_lt (by omega_using [c12]), Nat.mul_comm])
    e14Z
  refine WP.mono (chainN_ok (src := foldReg) foldReg_ne 7 (Nat.le_refl _)) fun s15 ⟨v15, r15, k15, m15⟩ => ?_
  simp only [show (7 : Nat) ≠ 0 from by decide, ↓reduceIte] at v15
  rw [hf2] at v15
  -- The registers and memory along the way.
  obtain hr : Rest clobR s s15 := r1.trans ((r2.mono (by decide)).trans (r3.trans (r4.trans
    ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans
    ((u8.rest (by decide)).trans (r9.trans ((u10.rest (by decide)).trans ((u11.rest (by decide)).trans
    (r12.trans ((r13.mono (by decide)).trans ((u14.rest (by decide)).trans r15)))))))))))))
  refine ⟨hc.of_rest hr (by decide), hr, by
    rw [m15, u14.mem, m13, m12, u11.mem, u10.mem, m9, u8.mem, u7.mem, u6.mem, u5.mem, m4, m3, m2, m1], ?_⟩
  -- The value.
  obtain p1 : colsV (fun j => (s.gpr (pw (7 + j))).toNat) 7 = colsV H 7 := by rw [← hH]
  rw [p1, colsV_split H] at v1
  obtain p3 : colsV (fun j => (s3.gpr (pw j)).toNat) 7 = colsV (fun j => (s1.gpr (pw j)).toNat) 7 :=
    colsV_congr fun j hj => by rw [kp3 j (by omega_using [hj]), r2.gpr _ (by simp; exact (pw_facts j (by omega_using [hj])).1)]
  obtain p3r : colsV (fun j => (s3.gpr (rotReg j)).toNat) 7 = colsV (rotW H) 7 :=
    colsV_congr fun j hj => by
      rw [v3 j hj, ← hH]
      simp only [rotW]
      rw [kH2 _ (Nat.mod_lt _ (by decide)), kH2 _ (Nat.mod_lt _ (by decide))]
  rw [p3, p3r, colsV_rotW] at v4
  obtain p8 : colsV (fun j => (s8.gpr (pw j)).toNat) 7 = colsV (fun j => (s4.gpr (pw j)).toNat) 7 :=
    colsV_congr fun j hj => by rw [k8 j (by omega_using [hj])]
  rw [p8, colsV_hiW] at v9
  obtain p11 : colsV (fun j => (s11.gpr (pw j)).toNat) 7 = colsV (fun j => (s9.gpr (pw j)).toNat) 7 :=
    colsV_congr fun j hj => by
      rw [u11.other _ (pw_facts j (by omega_using [hj])).2.1, u10.other _ (pw_facts j (by omega_using [hj])).1]
  rw [p11] at v12
  obtain p14 : colsV (fun j => (s14.gpr (pw j)).toNat) 7 = colsV (fun j => (s12.gpr (pw j)).toNat) 7 :=
    colsV_congr fun j hj => by
      rw [u14.other _ (pw_facts j (by omega_using [hj])).2.1, r13.gpr _ (by simp; exact (pw_facts j (by omega_using [hj])).1)]
  rw [p14] at v15
  rw [show pwSum s 14 = colsV (fun j => (s.gpr (pw j)).toNat) 14 from rfl, colsV_14]
  rw [p1, colsV_split H]
  obtain hS := colsV_lt (fun j => (s9.gpr (pw j)).isLt) 7
  obtain hS9 := colsV_lt (fun j => (s12.gpr (pw j)).isLt) 7
  obtain e448 : (2 ^ 64) ^ 7 = (2 : Nat) ^ 224 * 2 ^ 224 := by
    rw [← Nat.pow_mul, show 64 * 7 = 32 * 14 from rfl]; exact pow448
  obtain c15 : s15.ca.toNat ≤ 1 := Bool.toNat_le _
  obtain c9' : s9.ca.toNat ≤ 1 := Bool.toNat_le _
  exact reduce_arith (L := colsV (fun j => (s.gpr (pw j)).toNat) 7) (Lo := loP H) (Hi := hiP H)
    (S := colsV (fun j => (s9.gpr (pw j)).toNat) 7) (c := (s10.gpr .r4).toNat)
    (S9 := colsV (fun j => (s12.gpr (pw j)).toNat) 7) (c9 := s12.ca.toNat)
    (S11 := colsV (fun j => (s15.gpr (pw j)).toNat) 7) (c11 := s15.ca.toNat)
    (by omega_using [v1, e2, v4, c1, c4, e5, v9, e94, c9, e10, e11r5, v12, c9']) (e448 ▸ hS) (e448 ▸ hS9) c15 (by rw [e10]; omega_using [v1, e2, v4, c1, c4, e5, v9, e94, c9, e10, e11r5, v12, hS, c9']) (by rw [e10]; omega_using [v1, e2, v4, c1, c4, e5, v9, e94, c9, e10, e11r5, v12, e13, c12, v15, hS, hS9, c9']) (by omega_using [v15])

/-! ## The multiplication in registers -/

theorem slotsOf_mem {R : Nat → Reg} {n : Nat} {p : Reg × Nat} (hp : p ∈ slotsOf R n) :
    ∃ i < n, p = (R i, 8 * i) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem slotsOf_fit {R : Nat → Reg} {n base : Nat} (h4 : base % 4 = 0) (hb : base + 8 * n ≤ 4096) :
    ∀ p ∈ slotsOf R n, p.2 % 4 = 0 ∧ base + p.2 + 8 ≤ 4096 := fun p hp => by
  obtain ⟨i, hi, rfl⟩ := slotsOf_mem hp
  exact ⟨by omega, by omega⟩

theorem opsA_in : ∀ p ∈ slotsOf opA 7, p.1 ∈ clobR := by decide

theorem opsB_in : ∀ p ∈ slotsOf opB 7, p.1 ∈ clobR := by decide

/-- The doublewords at `B + 8 i` of `saveMem` of `slotsOf R n` hold the registers. -/
theorem saved_dw {R : Nat → Reg} {n : Nat} (hf : Fits (slotsOf R n)) (m : Mem) (B : Addr)
    (g : Reg → BitVec 64) {i : Nat} (hi : i < n) :
    (saveMem m B g (slotsOf R n)).readW (B + BitVec.ofNat 64 (8 * i)) 64 = g (R i) :=
  saveMem_saved hf m B g (R i, 8 * i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)


/-- `mul o x y`: `[o] = [x] · [y]` modulo `p`, in registers it does not restore. -/
theorem mul_ok {o x y : Nat} (ho : o + 56 ≤ ACC) (hx : x + 56 ≤ ACC)
    (hy : y + 56 ≤ ACC) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) (ho4 : o % 4 = 0) {s : State}
    (hc : Ctx b s) :
    WP isa (mul o x y) s fun s' => Ctx b s' ∧ Rest clobR s s' ∧
      Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x * V s.mem b y) % P := by
  have hA := ACC_eq
  unfold mul mulX
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- The operands.
  refine ldsAt_ok (l := slotsOf opA 7) hx4 (slotsOf_fit hx4 (by omega_using [hx, hA])) (by decide) (by decide) hc
    fun s2 hc2 r2 m2 _ v2 => ?_
  refine ldsAt_ok (l := slotsOf opB 7) hy4 (slotsOf_fit hy4 (by omega_using [hy, hA])) (by decide) (by decide) hc2
    fun s3 hc3 r3 m3 _ v3 => ?_
  obtain opsA : ∀ i < 7, (s3.gpr (opA i)).toNat = ew s.mem b x i := fun i hi => by
    rw [r3.gpr _ (by revert i; decide), v2 (opA i, 8 * i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩),
      Offset.add_add]; rfl
  obtain opsB : ∀ j < 7, (s3.gpr (opB j)).toNat = ew s.mem b y j := fun j hj => by
    rw [v3 (opB j, 8 * j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩), m2, Offset.add_add]; rfl
  -- The product.
  refine wp_li (by decide) fun s5 u5 => wp_li (by decide) fun s6 u6 => ?_
  obtain hr6 : Rest clobR s3 s6 := (u5.rest (by decide)).trans (u6.rest (by decide))
  refine WP.append (columns_ok (b := b) (hc3.of_rest hr6 (by decide))
    (by rw [u6.other _ (by decide), u5.gpr]; rfl) (by rw [u6.gpr]; rfl)) fun s7 ⟨hc7, r7, m7, v7⟩ => ?_
  obtain hA7 : colsV (fun i => (s6.gpr (opA i)).toNat) 7 = V s.mem b x := by
    rw [V_eq_cols]; exact colsV_congr fun i hi => by
      rw [u6.other _ (by revert i; decide), u5.other _ (by revert i; decide), opsA i hi]
  obtain hB7 : colsV (fun j => (s6.gpr (opB j)).toNat) 7 = V s.mem b y := by
    rw [V_eq_cols]; exact colsV_congr fun j hj => by
      rw [u6.other _ (by revert j; decide), u5.other _ (by revert j; decide), opsB j hj]
  rw [hA7, hB7] at v7
  refine WP.append (reduceR_ok hc7) fun s8 ⟨hc8, r8, m8, v8⟩ => ?_
  -- The result stored at `o`.
  refine stdsAt_ok (l := slotsOf pw 7) ho4 (slotsOf_fit ho4 (by omega_using [ho, hA])) hc8 fun s9 g9 rd9 wr9 sp9 mem9 => ?_
  refine WP.block_nil ⟨⟨by rw [g9]; exact hc8.r6, by rw [wr9]; exact hc8.wr⟩,
    ⟨fun r hr => ?_, by rw [rd9, r8.rd, r7.rd, u6.rd, u5.rd, r3.rd, r2.rd],
      by rw [wr9, r8.wr, r7.wr, u6.wr, u5.wr, r3.wr, r2.wr], by rw [sp9, r8.sp, r7.sp, u6.sp, u5.sp, r3.sp, r2.sp]⟩,
    ?_, ?_⟩
  · rw [congrFun g9, r8.gpr _ hr, r7.gpr _ hr, hr6.gpr _ hr,
      r3.gpr _ (fun h => hr (by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact opsB_in p hp)),
      r2.gpr _ (fun h => hr (by obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact opsA_in p hp))]
  · rw [mem9, m8, m7, u6.mem, u5.mem, m3, m2]
    exact saveMem_frame_base (fun p hp => by obtain ⟨i, hi, rfl⟩ := slotsOf_mem hp; omega) (by decide) _ _ _
  · rw [V_eq_cols, ← v7, ← v8]
    congr 1
    refine colsV_congr fun k hk => ?_
    rw [mem9]
    show (Mem.readW _ _ 64).toNat = _
    rw [← Offset.add_add, saved_dw (by decide) _ _ _ hk]

end

end VG.Proof.X448.PPC64LE

end

end

/-!
# X448 on PPC64LE: the field elements the working space holds

`SlotsOk m B qs v`: each slot `q` of `qs` holds the element `v q`. The field
operations as updates of `v` (`mulS`, `addS`, `subS`, `cswapS`), for slots
whose separation from the output is decided on their offsets (`Sep1`), and
writing only the field area `[0, ACC + 112)` of the working space (`FA`).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P Fe)
open VG.Proof.X448 (toFe toFe_mul toFe_add toFe_sub)

/-- Each slot `q` of `qs` holds `v q`. -/
def SlotsOk (m : Mem) (B : Addr) (qs : List Nat) (v : Nat → Fe) : Prop :=
  ∀ q ∈ qs, FS m B q = v q

theorem SlotsOk.mono {m : Mem} {B : Addr} {qs qs' : List Nat} {v : Nat → Fe} (h : SlotsOk m B qs v)
    (hs : ∀ q ∈ qs', q ∈ qs) : SlotsOk m B qs' v := fun q hq => h q (hs q hq)

theorem SlotsOk.congr {m : Mem} {B : Addr} {qs : List Nat} {v w : Nat → Fe} (h : SlotsOk m B qs v)
    (hs : ∀ q ∈ qs, v q = w q) : SlotsOk m B qs w := fun q hq => (h q hq).trans (hs q hq)

/-- `v` with the element `x` at `o`. -/
def upd (v : Nat → Fe) (o : Nat) (x : Fe) (q : Nat) : Fe := if q = o then x else v q

theorem upd_self (v : Nat → Fe) (o : Nat) (x : Fe) : upd v o x o = x := by simp [upd]

theorem upd_of_ne (v : Nat → Fe) {o q : Nat} (x : Fe) (h : q ≠ o) : upd v o x q = v q := by simp [upd, h]

/-- Every slot of `qs` is `o` or separate from it, and below `ACC`. -/
def Sep1 (o : Nat) (qs : List Nat) : Bool :=
  qs.all fun q => (q == o || q + 56 ≤ o || o + 56 ≤ q) && q + 56 ≤ ACC

theorem sep1_get {o : Nat} {qs : List Nat} (h : Sep1 o qs = true) {q : Nat} (hq : q ∈ qs) :
    (q = o ∨ q + 56 ≤ o ∨ o + 56 ≤ q) ∧ q + 56 ≤ ACC := by
  have := List.all_eq_true.mp h q hq
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.elim (fun h => h.elim .inl (fun h => .inr (.inl h))) (fun h => .inr (.inr h)), this.2⟩

/-- The field area `[0, ACC + 112)` of the working space: the elements and
the product at `ACC`. -/
abbrev FA (b : Addr) : Region := ⟨b, ACC + 112⟩

section
variable {b : Addr}

/-- The slots of `qs` other than `o` after a write of `o` (and `ACC`). -/
theorem slots_after {o : Nat} {qs : List Nat} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] m m')
    {v : Nat → Fe} (hS : SlotsOk m b qs v) {q : Nat} (hq' : q ∈ qs) (hqo : q ≠ o) :
    FS m' b q = v q := by
  obtain ⟨h1, h3⟩ := sep1_get hq hq'
  have hA := ACC_eq
  have e : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega_using [hqo, h1, hk]) (by omega_using [hA, h3, hk]) (by omega_using [hA, ho])
      · exact Offset.disjoint _ (.inl (by omega_using [h3, hk])) (by omega_using [hA, h3, hk]) (by omega_using [hA])
  rw [FS, V, val32_congr e]; exact hS q hq'

theorem frame_FA {o : Nat} (ho : o + 56 ≤ ACC) {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] m m') :
    Frame [FA b] m m' := by
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega_using [ho])

theorem mulS {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0)
    (ho4 : o % 4 = 0) {s : State} (hc : Ctx b s) (hS : SlotsOk s.mem b qs v) :
    WP isa (mul o x y) s fun s' => Rest clobR s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (v x * v y)) := by
  refine WP.mono (mul_ok ho (sep1_get hq hx).2 (sep1_get hq hy).2 hx4 hy4 ho4 hc)
    fun s' ⟨_, hr, hf1, hv⟩ => ?_
  have hf : Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem s'.mem :=
    hf1.mono fun r hr => by simp [List.mem_singleton.mp hr]
  refine ⟨hr, frame_FA ho hf, fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    rw [upd_self, ← hS x hx, ← hS y hy]
    exact toFe_mul hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq ho hf hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem frame_o {o : Nat} {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 o, 56⟩] m m') :
    Frame [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 ACC, 112⟩] m m' :=
  hf.mono fun r hr => by simp [List.mem_singleton.mp hr]

theorem mul24S {o x : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) {s : State}
    (hc : Ctx b s) (hS : SlotsOk s.mem b qs v) :
    WP isa (.block (mulA24 o x)) s fun s' => Rest clob s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (Spec.X448.a24 * v x)) := by
  have hx' := sep1_get hq hx
  have hA := ACC_eq
  refine WP.mono (mulA24_ok (by omega_using [hA, ho]) (by omega_using [hA, hx'.2]) hx'.1
    ho4 hx4 hc) fun s' ⟨hr, hf, hv⟩ => ⟨hr, frame_FA ho (frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    rw [upd_self, ← hS x hx, show Spec.X448.a24 = toFe 39081 from rfl]
    exact toFe_mul hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq ho (frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem addS {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0)
    (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b qs v) :
    WP isa (.block (add o x y)) s fun s' => Rest clob s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (v x + v y)) := by
  have hx' := sep1_get hq hx
  have hy' := sep1_get hq hy
  have hA := ACC_eq
  refine WP.mono (add_ok (by omega_using [hA, ho]) (by omega_using [hA, hx']) (by omega_using [hA, hy'])
    (hx'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm) (hy'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm)
    ho4 hx4 hy4 hc) fun s' ⟨hr, hf, hv⟩ => ⟨hr, frame_FA ho (frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    rw [upd_self, ← hS x hx, ← hS y hy]
    exact toFe_add hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq ho (frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem subS {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) (ho4 : o % 4 = 0) (hx4 : x % 4 = 0)
    (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b qs v) :
    WP isa (.block (sub o x y)) s fun s' => Rest clob s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (v x - v y)) := by
  have hx' := sep1_get hq hx
  have hy' := sep1_get hq hy
  have hA := ACC_eq
  refine WP.mono (sub_ok (by omega_using [hA, ho]) (by omega_using [hA, hx']) (by omega_using [hA, hy'])
    (hx'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm) (hy'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm)
    ho4 hx4 hy4 hc) fun s' ⟨hr, hf, hv⟩ => ⟨hr, frame_FA ho (frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    rw [upd_self, ← hS x hx, ← hS y hy]
    exact toFe_sub hv
  · rw [upd_of_ne _ _ hqo]
    exact slots_after hq ho (frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

/-- The elements after swapping `x` and `y` if `sw = 1`. -/
def swapV (x y sw : Nat) (v : Nat → Fe) (q : Nat) : Fe :=
  if q = x then sel sw (v x) (v y) else if q = y then sel sw (v y) (v x) else v q

theorem cswapS {x y : Nat} {qs : List Nat} {v : Nat → Fe}
    (hq : Sep1 x qs = true) (hq' : Sep1 y qs = true)
    (hx : x ∈ qs) (hy : y ∈ qs) (hxy : x + 56 ≤ y ∨ y + 56 ≤ x) {s : State} (hc : Ctx b s) {sw : Nat}
    (hsw : sw ≤ 1) (h11 : s.gpr .r11 = 0 - BitVec.ofNat 64 sw) (hS : SlotsOk s.mem b qs v) :
    WP isa (.block (cswap x y)) s fun s' => Rest [.r5, .r7, .r8] s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b qs (swapV x y sw v) := by
  have hx' := sep1_get hq hx
  have hy' := sep1_get hq hy
  have hA := ACC_eq
  refine WP.mono (cswap_ok (b := b) (by omega_using [hA, hx']) (by omega_using [hA, hy']) hxy hc hsw h11)
    fun s' h => ⟨h.rest, ?_, ?_⟩
  · refine h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by omega_using [hA, hx', hy'])
  · intro q hq''
    have hlx : ∀ k < 14, limb s'.mem b x k = sel sw (limb s.mem b x k) (limb s.mem b y k) := h.lx
    have hly : ∀ k < 14, limb s'.mem b y k = sel sw (limb s.mem b y k) (limb s.mem b x k) := h.ly
    by_cases hqx : q = x
    · subst hqx
      simp only [swapV, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · have e : ∀ k < 14, limb s'.mem b q k = limb s.mem b q k := fun k hk => by rw [hlx k hk]; rfl
        rw [FS, V, val32_congr e]; exact hS q hx
      · have e : ∀ k < 14, limb s'.mem b q k = limb s.mem b y k := fun k hk => by rw [hlx k hk]; rfl
        rw [FS, V, val32_congr e]; exact hS y hy
    by_cases hqy : q = y
    · subst hqy
      simp only [swapV, hqx, ite_false, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · have e : ∀ k < 14, limb s'.mem b q k = limb s.mem b q k := fun k hk => by rw [hly k hk]; rfl
        rw [FS, V, val32_congr e]; exact hS q hy
      · have e : ∀ k < 14, limb s'.mem b q k = limb s.mem b x k := fun k hk => by rw [hly k hk]; rfl
        rw [FS, V, val32_congr e]; exact hS x hx
    · simp only [swapV, hqx, hqy, ite_false]
      obtain ⟨h1, h3⟩ := sep1_get hq hq''
      obtain ⟨h1', -⟩ := sep1_get hq' hq''
      have e : ∀ k < 14, limb s'.mem b q k = limb s.mem b q k :=
        limb_frame h.frame fun r hr k hk => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (by omega_using [hqx, h1, hk]) (by omega_using [hA, h3, hk]) (by omega_using [hA, hx'])
          · exact Offset.disjoint _ (by omega_using [hqy, h1', hk]) (by omega_using [hA, h3, hk]) (by omega_using [hA, hy'])
      rw [FS, V, val32_congr e]; exact hS q hq''

end

end VG.Proof.X448.PPC64LE
