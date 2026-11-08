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

/-- A `pass` of sums, then the `tail`, with no carry in `r8`. -/
theorem passTail_ok {o : Nat} (ho : o + 56 ≤ 4096) {src : Nat → List Instr} {c : Nat → Nat}
    (hc : ∀ k < 14, c k + 2 ^ 32 ≤ 2 ^ 64) (hv : val32 c 14 < 5 * (2 ^ 224 * 2 ^ 224)) {s1 : State}
    (hc1 : Ctx b s1) (h8 : s1.gpr .r8 = 0)
    (hsrc : ∀ k < 14, ∀ s', PassInv .r6 o s1 c 0 k s' → WP isa (.block (src k)) s' fun s'' =>
        (s''.gpr .r7).toNat = c k ∧ Rest [.r5, .r7] s' s'' ∧ s''.mem = s'.mem) :
    WP isa (.block (pass .r6 o src ++ tail o)) s1 fun s' =>
      Rest [.r5, .r7, .r8, .r10] s1 s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s1.mem s'.mem ∧
      V s'.mem b o % P = val32 c 14 % P := by
  refine WP.append (pass_ok (s0 := s1) (c := c) (cin := 0) (by decide) (by decide) ho
    (fun k hk => by rw [hc1.r6]; exact hc1.inW (by omega_using [ho, hk]))
    (by rw [h8]; rfl) hc (by decide) hsrc) fun s2 hp => ?_
  have hc2 : Ctx b s2 := hc1.of_rest hp.rest (by decide)
  have hpo : ∀ j < 14, wd s2.mem b (o + 4 * j) = out c 0 j := fun j hj => by
    have := hp.outs j hj; rwa [hc1.r6] at this
  have hpf : Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s1.mem s2.mem := by
    have := hp.frame; rwa [hc1.r6] at this
  have hcl := carry_le hv
  refine WP.mono (tail_ok ho hc2 hp.r8 hcl) fun s3 ⟨hr3, hf3, hv3⟩ => ?_
  refine ⟨(hp.rest.mono (by decide)).trans hr3, hpf.trans hf3, ?_⟩
  have hcv := chain_val c 0 14
  rw [pow448, Nat.add_zero] at hcv
  rw [hv3, V, val32_congr (f := limb s2.mem b o) (g := out c 0) (fun k hk => hpo k hk), hcv]

/-! ## Chains of doublewords through memory -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_subc64 {d n m : Reg}
    (k : ∀ s', UpdC s s' d ((s.gpr n).toNat + (2 ^ 64 - 1 - (s.gpr m).toNat) + 1) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subc d n m :: is)) s Q := by
  have := (s.gpr n).isLt
  exact WP.cons exec_subc (k _ (UpdC.writeCarry _ _ (by omega)))

theorem wp_sube64 {d n m : Reg}
    (k : ∀ s', UpdC s s' d ((s.gpr n).toNat + (2 ^ 64 - 1 - (s.gpr m).toNat) + s.ca.toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.sube d n m :: is)) s Q := by
  have := (s.gpr n).isLt; have : s.ca.toNat ≤ 1 := Bool.toNat_le _
  exact WP.cons exec_sube (k _ (UpdC.writeCarry _ _ (by omega)))

/-- `std t, d(r6)` in the working space, which keeps CA. -/
theorem sdC_ok (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 8 ≤ 4096) (hd4 : d % 4 = 0)
    (k : ∀ s', Mupd s s' (s.mem.writeW (b + BitVec.ofNat 64 d) (s.gpr t)) → s'.ca = s.ca →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t .r6 d :: is)) s Q := by
  have e := exec_store_d (s := s) (t := t) (n := .r6) (off := d) (by decide) ⟨by omega, hd4⟩
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
  refine sdC_ok hct (by omega) (by omega) fun t1 u1 c1 => WP.block_nil ⟨hct.of_rest (u1.rest []) (by decide),
    h.rest.trans (hr.trans (u1.rest _)), ?_, fun _ => ?_⟩
  · rw [u1.mem, hm]
    exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  · have ew1 : ∀ j < k, ew t1.mem b o j = ew s.mem b o j := fun j hj => by
      show dw _ _ _ = dw _ _ _
      rw [u1.mem, hm, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have es : ew t1.mem b o k = (t.gpr .r7).toNat := by
      show dw _ _ _ = _
      rw [u1.mem, dw_write_self]
    simp only [colsV]
    rw [colsV_congr ew1, es, c1]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [colsV, cinD, ↓reduceIte, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.pow_one] at hv ⊢
      omega
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
      omega


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
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have eY : dw s.mem b (y + 8 * k) = dw s0.mem b (y + 8 * k) := dw_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  unfold chainStep
  refine ldw_ok hc (by omega) (by omega) ?_
  generalize hs1 : s.write .r7 (s.mem.readW (b + BitVec.ofNat 64 (x + 8 * k)) 64) = s1
  have r1 : Rest [.r7, .r8] s s1 := by rw [← hs1]; exact (Upd.write _ _ _).rest (by simp)
  have hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  have m1 : s1.mem = s.mem := by rw [← hs1, RegUpd.mem_write]
  refine ldw_ok hc1 (by omega) (by omega) ?_
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
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have hn := foldSrc64_ne k
  unfold foldStep
  refine ldw_ok hc (by omega) (by omega) ?_
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
  omega

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
  have e2 : (s2.gpr .r4).toNat = s.ca.toNat := by omega
  have r4' : Rest [.r4, .r5, .r8] s s4 :=
    ((Upd.write _ _ _).rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      (u4.rest (by simp))))
  refine k s4 (hc.of_rest r4' (by decide)) r4' (by rw [u4.mem, u3.mem, u2.mem, RegUpd.mem_write]) ?_ ?_ ?_
  · rw [u4.other _ (by decide), u3.other _ (by decide), e2]
  · rw [u4.other _ (by decide), u3.gpr, toNat_shl, e2, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
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
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_allOnes]; omega)
      rw [this, h]; rfl
    · have : s2.gpr .r4 = 0#64 := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega)
      rw [this, h]; rfl
  have r4' : Rest [.r4, .r5, .r8] s s4 :=
    ((Upd.write _ _ _).rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      (u4.rest (by simp))))
  refine k s4 (hc.of_rest r4' (by decide)) r4' (by rw [u4.mem, u3.mem, u2.mem, RegUpd.mem_write]) ?_ ?_ ?_
  · rw [u4.other _ (by decide), e3]
  · rw [u4.gpr, toNat_shl, e3, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
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
  refine WP.append (chainRun_ok (sub := false) ho hx hy ho4 hx4 hy4 (by omega) (by omega) hc)
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
    have z5 : s5.ca.toNat = 0 := by omega
    have key : colsV (ew s5.mem b o) 7 + (2 ^ 224 * 2 ^ 224 - 2 ^ 224 - 1) * (s1.ca.toNat + s3.ca.toNat) =
        X + Y := by
      omega
    rw [P_eq, ← key, Nat.add_mul_mod_self_left]

theorem sub_ok {o x y : Nat} (ho : o + 56 ≤ 4096) (hx : x + 56 ≤ 4096) (hy : y + 56 ≤ 4096)
    (hox : o = x ∨ o + 56 ≤ x ∨ x + 56 ≤ o) (hoy : o = y ∨ o + 56 ≤ y ∨ y + 56 ≤ o)
    (ho4 : o % 4 = 0) (hx4 : x % 4 = 0) (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (.block (sub o x y)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      (V s'.mem b o + V s.mem b y) % P = V s.mem b x % P := by
  unfold sub
  simp only [List.append_assoc]
  refine WP.append (chainRun_ok (sub := true) ho hx hy ho4 hx4 hy4 (by omega) (by omega) hc)
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
    have z5 : s5.ca.toNat = 1 := by omega
    have key : colsV (ew s5.mem b o) 7 + Y =
        X + (2 ^ 224 * 2 ^ 224 - 2 ^ 224 - 1) * ((1 - s1.ca.toNat) + (1 - s3.ca.toNat)) := by
      omega
    rw [P_eq, key, Nat.add_mul_mod_self_left]

end

end VG.Proof.X448.PPC64LE
