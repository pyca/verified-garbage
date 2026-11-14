module

import VerifiedGarbage.Proof.Sha3.X86_64.X4.Wp
public import VerifiedGarbage.Impl.Sha3.X86_64.X4Reg
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Sha3.X86_64.Permute
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha3.X86_64.X4.Round
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Sha3.X86_64.X4.Loop
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Sha3.X86_64.X4R.Round`, which only this module used -/

section

/-! ### `Sha3.X86_64.X4R.Wp`, which only this module used -/

section

/-!
# Keccak-f[1600] four times at once, in registers: one instruction at a time

Weakest-precondition rules for the EVEX-encoded instructions of `permute4R`
(`Impl/Sha3/X86_64/X4Reg.lean`) on the thirty-two `ymm` registers, and for
its copies of a register (`wp_ecopy`: `vmovdqa` between two of
`ymm0`–`ymm15`), in terms of the four 64-bit elements of each (`qy`), one per
state.
-/

@[expose] public section

namespace VG.Proof.Sha3.X86_64.X4R

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4R

/-- Element `k` (`k < 4`) of `ymm r`. -/
def qy (s : State) (r : VReg) (k : Nat) : BitVec 64 := qword256 (s.vy r) k

/-! ## Values -/

/-- Quadword `k` (`k < 4`) of a 256-bit value. -/
theorem qword256_eq (x : BitVec 256) (k : Nat) :
    qword256 x k = qword (x.extractLsb' (128 * (k / 2)) 128) (k % 2) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword256, qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 64 * (k % 2) + j < 128 by omega_using [hj])]
  congr 1; omega_using []

theorem lane_app0 (x y : BitVec 128) : (x ++ y).extractLsb' 0 128 = y := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, Nat.zero_add]
  rw [BitVec.getLsbD_append]; simp [hj]

theorem lane_app1 (x y : BitVec 128) : (x ++ y).extractLsb' 128 128 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append]; simp [hj]

/-- Element `k` of a value made of two lanes. -/
theorem qword256_lanes (x y : BitVec 128) {k : Nat} (hk : k < 4) :
    qword256 (x ++ y) k = qword (if k / 2 = 0 then y else x) (k % 2) := by
  rw [qword256_eq]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceDiv, Nat.reduceMul, Nat.reduceMod, lane_app0, lane_app1, ite_true, ite_false,
      Nat.one_ne_zero]

/-- Element `k` of a value made of the two lanes of a three-operand operation. -/
theorem qword256_lanes3 (f : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128) (a b c : BitVec 256)
    {k : Nat} (hk : k < 4) :
    qword256 (f (lane256 a 1) (lane256 b 1) (lane256 c 1) ++ f (lane256 a 0) (lane256 b 0) (lane256 c 0)) k =
      qword (f (lane256 a (k / 2)) (lane256 b (k / 2)) (lane256 c (k / 2))) (k % 2) := by
  rw [qword256_lanes _ _ hk]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl

/-- Element `k` of each lane-wise result: of the lanes `k / 2`. -/
theorem qword256_lanes256 (f : BitVec 128 → BitVec 128 → BitVec 128) (a b : BitVec 256) {k : Nat} (hk : k < 4) :
    qword256 (lanes256 f a b) k = qword (f (lane256 a (k / 2)) (lane256 b (k / 2))) (k % 2) := by
  rw [lanes256, qword256_lanes _ _ hk]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl

/-- Element `j` of a lane, as an element of the whole. -/
theorem qword_lane (v : BitVec 256) {k : Nat} (_hk : k < 4) : qword (lane256 v (k / 2)) (k % 2) = qword256 v k := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword256, qword, lane256, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  have : 64 * (k % 2) + j < 128 := by omega_using [hj]
  simp only [this, decide_true, Bool.true_and]
  congr 1; omega_using []

theorem qword_xor (x y : BitVec 128) (i : Nat) : qword (x ^^^ y) i = qword x i ^^^ qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [qword, hj]

theorem ternlog96 (a b c : BitVec 128) : ternlog a b c 0x96 = a ^^^ b ^^^ c := by
  simp only [ternlog, List.range, List.range.loop, List.foldl, show (0x96 : BitVec 8).getLsbD 0 = false from rfl, show (0x96 : BitVec 8).getLsbD 1 = true from rfl, show (0x96 : BitVec 8).getLsbD 2 = true from rfl, show (0x96 : BitVec 8).getLsbD 3 = false from rfl, show (0x96 : BitVec 8).getLsbD 4 = true from rfl, show (0x96 : BitVec 8).getLsbD 5 = false from rfl, show (0x96 : BitVec 8).getLsbD 6 = false from rfl, show (0x96 : BitVec 8).getLsbD 7 = true from rfl, Nat.testBit, Nat.reduceShiftRight, Nat.reduceAnd, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, show (0 : BitVec 128).getLsbD j = false from BitVec.getLsbD_zero, hj,
    decide_true, Bool.true_and]
  generalize a.getLsbD j = x; generalize b.getLsbD j = y; generalize c.getLsbD j = z
  revert x y z; decide

theorem ternlogD2 (a b c : BitVec 128) : ternlog a b c 0xD2 = (~~~b &&& c) ^^^ a := by
  simp only [ternlog, List.range, List.range.loop, List.foldl, show (0xD2 : BitVec 8).getLsbD 0 = false from rfl, show (0xD2 : BitVec 8).getLsbD 1 = true from rfl, show (0xD2 : BitVec 8).getLsbD 2 = false from rfl, show (0xD2 : BitVec 8).getLsbD 3 = false from rfl, show (0xD2 : BitVec 8).getLsbD 4 = true from rfl, show (0xD2 : BitVec 8).getLsbD 5 = false from rfl, show (0xD2 : BitVec 8).getLsbD 6 = true from rfl, show (0xD2 : BitVec 8).getLsbD 7 = true from rfl, Nat.testBit, Nat.reduceShiftRight, Nat.reduceAnd, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, show (0 : BitVec 128).getLsbD j = false from BitVec.getLsbD_zero, hj,
    decide_true, Bool.true_and]
  generalize a.getLsbD j = x; generalize b.getLsbD j = y; generalize c.getLsbD j = z
  revert x y z; decide

theorem qword_tern96 (a b c : BitVec 128) (i : Nat) :
    qword (ternlog a b c 0x96) i = qword a i ^^^ qword b i ^^^ qword c i := by
  rw [ternlog96, qword_xor, qword_xor]

theorem qword_ternD2 (a b c : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (ternlog a b c 0xD2) i = (qword b i ^^^ 0xffffffffffffffff) &&& qword c i ^^^ qword a i := by
  rw [ternlogD2]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have e : (0xffffffffffffffff : BitVec 64).getLsbD j = true := by
    rw [show (0xffffffffffffffff : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.getLsbD_allOnes]; simp [hj]
  simp only [qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_and, BitVec.getLsbD_not, e, show 64 * i + j < 128 by omega_using [hi, hj]]
  cases b.getLsbD (64 * i + j) <;> rfl

theorem qword_ror (x : BitVec 128) (n : BitVec 8) {i : Nat} (hi : i < 2) :
    qword (rorQwords x n) i = (qword x i).rotateRight (n.toNat % 64) := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1) with rfl | rfl <;> simp [rorQwords, VG.Proof.Sha3.X86_64.X4.qword_app0,
    VG.Proof.Sha3.X86_64.X4.qword_app1]

/-! ## The machine -/

theorem qy_setVy (s : State) (d r : VReg) (v : BitVec 256) (k : Nat) :
    qy (s.setVy d v) r k = if r = d then qword256 v k else qy s r k := by
  cases d with
  | lo d =>
    cases r with
    | lo r =>
      simp only [qy, State.vy, State.setVy, VReg.lo.injEq]
      by_cases h : r = d
      · subst h
        simp only [ite_true, State.ymm, State.setV]
        congr 1
        apply BitVec.eq_of_getLsbD_eq; intro j hj
        rw [BitVec.getLsbD_append]
        by_cases h' : j < 128
        · simp [h']
        · simp [h', show j - 128 < 128 by omega_using [hj], show 128 + (j - 128) = j by omega_using [h']]
      · simp only [h, ite_false, State.ymm, State.setV]
    | hi r => simp only [qy, State.vy, State.setVy, reduceCtorEq, ite_false]; rfl
  | hi d =>
    cases r with
    | lo r => simp only [qy, State.vy, State.setVy, reduceCtorEq, ite_false]; rfl
    | hi r =>
      simp only [qy, State.vy, State.setVy, VReg.hi.injEq]
      split <;> rfl

/-- `s'` is `s` with `ymm d` set to the four elements `v`. -/
structure YUpd (s s' : State) (d : VReg) (v : Nat → BitVec 64) : Prop where
  val : ∀ k < 4, qy s' d k = v k
  other : ∀ r, r ≠ d → ∀ k < 4, qy s' r k = qy s r k
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  zf : s'.zf = s.zf

theorem YUpd.setVy (s : State) (d : VReg) (w : BitVec 256) {v : Nat → BitVec 64}
    (hv : ∀ k < 4, qword256 w k = v k) : YUpd s (s.setVy d w) d v :=
  ⟨fun k hk => by rw [qy_setVy, ite_eq_left rfl]; exact hv k hk,
    fun r hr k _ => by rw [qy_setVy, ite_eq_right hr], by cases d <;> rfl, by cases d <;> rfl,
    by cases d <;> rfl, by cases d <;> rfl, by cases d <;> rfl⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_exor {d a b : VReg} (k : ∀ s', YUpd s s' d (fun i => qy s a i ^^^ qy s b i) → WP isa (.block is) s' Q) :
    WP isa (.block (eb .vpxorq d a b :: is)) s Q :=
  WP.cons rfl (k _ (YUpd.setVy _ _ _ fun i hi => by
    rw [qword256_lanes256 _ _ _ hi]
    simp only [EBinOp.sse, XBinOp.eval, qword_xor, qword_lane _ hi]; rfl))

/-- `copy` as `vporq` of a register with itself. -/
theorem wp_eor_self {d a : VReg} (k : ∀ s', YUpd s s' d (fun i => qy s a i) → WP isa (.block is) s' Q) :
    WP isa (.block (eb .vporq d a a :: is)) s Q :=
  WP.cons rfl (k _ (YUpd.setVy _ _ _ fun i hi => by
    rw [qword256_lanes256 _ _ _ hi]
    simp only [EBinOp.sse, XBinOp.eval, qword_lane _ hi, BitVec.or_self]; rfl))

theorem wp_ecopy {d a : VReg} (k : ∀ s', YUpd s s' d (fun i => qy s a i) → WP isa (.block is) s' Q) :
    WP isa (.block (copy d a :: is)) s Q := by
  cases d with
  | hi d => cases a <;> exact wp_eor_self k
  | lo d =>
    cases a with
    | hi a => exact wp_eor_self k
    | lo a =>
      -- `vmovdqa`: the two lanes of `ymm a`.
      have e : exec (copy (.lo d) (.lo a)) s = some (s.setVy (.lo d) (s.vy (.lo a))) := by
        simp only [copy, exec, VOp.exec, State.setVy, State.vy, State.ymm, State.lane, lane_app0, lane_app1]
        rfl
      exact WP.cons e (k _ (YUpd.setVy _ _ _ fun i _ => rfl))

theorem wp_tern96 {d a b : VReg}
    (k : ∀ s', YUpd s s' d (fun i => qy s d i ^^^ qy s a i ^^^ qy s b i) → WP isa (.block is) s' Q) :
    WP isa (.block (tern d a b 0x96 :: is)) s Q :=
  WP.cons rfl (k _ (YUpd.setVy _ _ _ fun i hi => by
    rw [qword256_lanes3 (fun x y z => ternlog x y z 0x96) _ _ _ hi, qword_tern96, qword_lane _ hi, qword_lane _ hi,
      qword_lane _ hi]; rfl))

theorem wp_ternD2 {d a b : VReg}
    (k : ∀ s', YUpd s s' d (fun i => (qy s a i ^^^ 0xffffffffffffffff) &&& qy s b i ^^^ qy s d i) →
      WP isa (.block is) s' Q) :
    WP isa (.block (tern d a b 0xD2 :: is)) s Q :=
  WP.cons rfl (k _ (YUpd.setVy _ _ _ fun i hi => by
    rw [qword256_lanes3 (fun x y z => ternlog x y z 0xD2) _ _ _ hi, qword_ternD2 _ _ _ (by omega_using []), qword_lane _ hi,
      qword_lane _ hi, qword_lane _ hi]; rfl))

theorem wp_eror {d a : VReg} {n : Nat} (hn : n < 64)
    (k : ∀ s', YUpd s s' d (fun i => (qy s a i).rotateRight n) → WP isa (.block is) s' Q) :
    WP isa (.block (ror d a n :: is)) s Q := by
  have en : (BitVec.ofNat 8 n).toNat % 64 = n := by rw [BitVec.toNat_ofNat]; omega_using [hn]
  exact WP.cons rfl (k _ (YUpd.setVy _ _ _ fun i hi => by
    rw [qword256_lanes256 _ _ _ hi, qword_ror _ _ (by omega_using []), en, qword_lane _ hi]; rfl))

theorem wp_evld {d : VReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 32)
    (k : ∀ s', YUpd s s' d (fun i => s.mem.readW (a + BitVec.ofNat 64 (8 * i)) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.evLoad d m :: is)) s Q :=
  WP.cons (s' := s.setVy d (s.mem.readW a 256))
    (by simp only [exec, ha, State.load256, hin, ite_true, Option.map_some])
    (k _ (YUpd.setVy _ _ _ fun i hi => by
      rw [qword256, show 64 * i = 8 * (8 * i) by omega_using []]
      exact readW_extract _ _ (k := 8 * i) (n := 8) (by omega_using [hi])))

theorem wp_evst {m : MemOp} {r : VReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 32)
    (k : WP isa (.block is) { s with mem := s.mem.writeW a (s.vy r) } Q) :
    WP isa (.block (.evStore m r :: is)) s Q :=
  WP.cons (by simp [exec, State.store256, ha, hout]) k

end

/-- Element `k` of a stored register, read back. -/
theorem readW_evst (m : Mem) (a : Addr) (s : State) (r : VReg) {k : Nat} (hk : k < 4) :
    (m.writeW a (s.vy r)).readW (a + BitVec.ofNat 64 (8 * k)) 64 = qy s r k := by
  have e := readW_writeW_inside m a (s.vy r) (k := 8 * k) (n := 8) (by omega_using [hk]) (by decide)
  rw [show 8 * (8 * k) = 64 * k by omega_using []] at e
  exact e

end VG.Proof.Sha3.X86_64.X4R

end

end


/-!
# Keccak-f[1600] four times at once, in registers: one round

One round (`round`) of the four states held in the registers `lreg i`
(`Regs4`), lane by lane (`Proof.Sha3.out`) in each of the four elements:
θ's columns (`columns_ok`) and `D` (`dcols_ok`), ρ and π along `piChain`
(`rhoPi_ok`), χ plane by plane (`chis_ok`) and ι (`iota_ok`).
-/

@[expose] public section

namespace VG.Proof.Sha3.X86_64.X4R

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4R
open VG.Proof.Sha3 (C D B out rotl outState)
open VG.Impl.Sha3 (piSrc rhoOff)
open VG.Proof.Sha3.X86_64.X4 (KState Lane la la_eq not_eq_xor)
open VG.Proof.Sha3.X86_64 (wp_nil)
open VG.Impl.Sha3.X86_64 (at_)

/-- The four states are held in the registers: lane `i` of state `k` is
element `k` of `lreg i`. -/
def Regs4 (s : State) (A : Nat → KState) : Prop := ∀ i < 25, ∀ k < 4, qy s (lreg i) k = (A k)[i]!

/-! ## Registers -/

theorem vreg_inj : ∀ i < 31, ∀ j < 31, vreg i = vreg j → i = j := by decide

theorem lnum_lt : ∀ i < 25, lnum i < 31 := by decide
theorem lnum_inj : ∀ i < 25, ∀ j < 25, lnum i = lnum j → i = j := by decide
/-- No lane is in the register of a `C[x]` or in `T`. -/
theorem lnum_ne : ∀ i < 25, ∀ x < 6, lnum i ≠ 10 + x := by decide

theorem lreg_ne {i j : Nat} (hi : i < 25) (hj : j < 25) (h : i ≠ j) : lreg i ≠ lreg j :=
  fun e => h (lnum_inj i hi j hj (vreg_inj _ (lnum_lt i hi) _ (lnum_lt j hj) e))

theorem creg_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x ≠ x') : creg x ≠ creg x' :=
  fun e => h (by have := vreg_inj (10 + x) (by omega_using [hx]) (10 + x') (by omega_using [hx']) e; omega_using [this])

theorem lreg_creg {i x : Nat} (hi : i < 25) (hx : x < 5) : lreg i ≠ creg x :=
  fun e => lnum_ne i hi x (by omega_using [hx]) (vreg_inj _ (lnum_lt i hi) (10 + x) (by omega_using [hx]) e)

theorem lreg_T {i : Nat} (hi : i < 25) : lreg i ≠ T :=
  fun e => lnum_ne i hi 5 (by omega_using []) (vreg_inj _ (lnum_lt i hi) (10 + 5) (by omega_using []) e)

theorem creg_T {x : Nat} (hx : x < 5) : creg x ≠ T :=
  fun e => by have := vreg_inj (10 + x) (by omega_using [hx]) 15 (by omega_using []) e; omega_using [hx, this]

/-! ## Vector code -/

theorem ite_t {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by simp [h]
theorem ite_f {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by simp [h]

/-- `s'` agrees with `s` but for the vector registers and the flags. -/
structure Same (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Same.refl (s : State) : Same s s := ⟨rfl, rfl, rfl, rfl⟩

theorem Same.trans {s₁ s₂ s₃ : State} (h₁ : Same s₁ s₂) (h₂ : Same s₂ s₃) : Same s₁ s₃ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem YUpd.same {s s' : State} {d : VReg} {v : Nat → BitVec 64} (h : YUpd s s' d v) : Same s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr⟩

/-- Running `f 0, …, f (n - 1)`, one instruction each. -/
theorem wp_range_map {f : Nat → Instr} {N : Nat} (Inv : Nat → State → Prop)
    (hstep : ∀ k s, k < N → Inv k s → WP isa (.block [f k]) s (Inv (k + 1))) (s : State) (hs : Inv 0 s) :
    WP isa (.block ((List.range N).map f)) s (Inv N) := by
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap (M := isa) Inv hstep N (Nat.le_refl _) s hs

/-! ## θ: the columns -/

theorem column_ok (x : Nat) (hx : x < 5) (s : State) (A : Nat → KState) (hA : Regs4 s A) :
    WP isa (.block (column x)) s fun s' =>
      Same s s' ∧ (∀ r, r ≠ creg x → ∀ k < 4, qy s' r k = qy s r k) ∧ ∀ k < 4, qy s' (creg x) k = C (A k) x := by
  rcases (by omega_using [hx] : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4) with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [column, colRows, List.getD_cons_zero, List.getD_cons_succ]
    refine wp_ecopy fun s₁ u₁ => wp_tern96 fun s₂ u₂ => wp_tern96 fun s₃ u₃ => wp_nil
      ⟨(u₁.same.trans u₂.same).trans u₃.same, fun r hr k hk => by rw [u₃.other r hr k hk, u₂.other r hr k hk,
        u₁.other r hr k hk], fun k hk => ?_⟩
    have h1 : ∀ i, i < 25 → qy s₁ (lreg i) k = (A k)[i]! := fun i hi => by
      rw [u₁.other _ (lreg_creg hi hx) k hk, hA i hi k hk]
    have h2 : ∀ i, i < 25 → qy s₂ (lreg i) k = (A k)[i]! := fun i hi => by
      rw [u₂.other _ (lreg_creg hi hx) k hk, h1 i hi]
    rw [u₃.val k hk, u₂.val k hk, u₁.val k hk, hA _ (by decide) k hk, h1 _ (by decide), h1 _ (by decide),
      h2 _ (by decide), h2 _ (by decide)]
    simp only [C, Nat.reduceMul, Nat.reduceAdd] <;> ac_rfl

/-- After the first `n` columns. -/
def ColInv (s₀ : State) (A : Nat → KState) (n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ Regs4 s A ∧ ∀ x < n, ∀ k < 4, qy s (creg x) k = C (A k) x

theorem columns_ok (s₀ : State) (A : Nat → KState) (hA : Regs4 s₀ A) :
    WP isa (.block ((List.range 5).flatMap column)) s₀ (ColInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (ColInv s₀ A) (fun x s hx ⟨hw, hr, hc⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Same.refl _, hA, fun _ h => absurd h (by omega_using [])⟩
  refine WP.mono (column_ok x hx s A hr) fun s' ⟨h, ho, hv⟩ => ⟨hw.trans h, fun i hi k hk => ?_, fun x' hx' k hk => ?_⟩
  · rw [ho _ (lreg_creg hi hx) k hk, hr i hi k hk]
  · by_cases e : x' = x
    · subst e; exact hv k hk
    · rw [ho _ (creg_ne (by omega_using [hx, hx']) hx e) k hk, hc x' (by omega_using [hx', e]) k hk]

/-! ## θ: `D` -/

/-- Lane `i` after θ. -/
def Th (A : KState) (i : Nat) : Lane := A[i]! ^^^ D A (i % 5)

theorem xor_D (a c r : Lane) : a ^^^ c ^^^ r = a ^^^ (r ^^^ c) := by
  rw [BitVec.xor_assoc, BitVec.xor_comm c r]

/-- The lanes of column `x` with the first `n` updated. -/
def DyInv (s₀ : State) (A : Nat → KState) (x n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ (∀ x' < 5, ∀ k < 4, qy s (creg x') k = qy s₀ (creg x') k) ∧
    (∀ k < 4, qy s T k = (C (A k) ((x + 1) % 5)).rotateRight 63) ∧
    ∀ i < 25, ∀ k < 4, qy s (lreg i) k = if i % 5 = x ∧ i / 5 < n then Th (A k) i else qy s₀ (lreg i) k

theorem dcol_ok (x : Nat) (hx : x < 5) (s : State) (A : Nat → KState)
    (hc : ∀ x' < 5, ∀ k < 4, qy s (creg x') k = C (A k) x')
    (hl : ∀ i < 25, ∀ k < 4, i % 5 = x → qy s (lreg i) k = (A k)[i]!) :
    WP isa (.block (dcol x)) s fun s' =>
      Same s s' ∧ (∀ x' < 5, ∀ k < 4, qy s' (creg x') k = qy s (creg x') k) ∧
      ∀ i < 25, ∀ k < 4, qy s' (lreg i) k = if i % 5 = x then Th (A k) i else qy s (lreg i) k := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega_using [])
  have h4 : (x + 4) % 5 < 5 := Nat.mod_lt _ (by omega_using [])
  unfold dcol
  refine wp_eror (by decide) fun s₁ u₁ => ?_
  refine WP.mono (wp_range_map (DyInv s₁ A x) (fun y t hy ⟨hw, hcs, hT, hls⟩ => ?_) s₁
    ⟨Same.refl _, fun _ _ _ _ => rfl, fun k hk => by rw [u₁.val k hk, hc _ h1 k hk],
      fun i _ k _ => by simp only [Nat.not_lt_zero, and_false, ite_false]⟩) fun s' ⟨hw, hcs, _, hls⟩ => ?_
  · have hi : x + 5 * y < 25 := by omega_using [hx, hy]
    refine wp_tern96 fun t' u => wp_nil ⟨hw.trans u.same, fun x' hx' k hk => by
        rw [u.other _ (lreg_creg hi hx').symm k hk, hcs x' hx' k hk],
      fun k hk => by rw [u.other _ (lreg_T hi).symm k hk, hT k hk], fun i hi' k hk => ?_⟩
    by_cases e : i = x + 5 * y
    · subst e
      have e1 : (x + 5 * y) % 5 = x := by omega_using [hx]
      have e2 : ¬((x + 5 * y) % 5 = x ∧ (x + 5 * y) / 5 < y) := by omega_using []
      have e3 : (x + 5 * y) % 5 = x ∧ (x + 5 * y) / 5 < y + 1 := by omega_using [e1]
      rw [u.val k hk, hls _ hi k hk, hT k hk, hcs _ h4 k hk, u₁.other _ (creg_T h4) k hk, hc _ h4 k hk,
        ite_f e2, ite_t e3, u₁.other _ (lreg_T hi) k hk, hl _ hi k hk e1, Th, e1, D, xor_D]
    · rw [u.other _ (lreg_ne hi' hi e) k hk, hls i hi' k hk]
      congr 1
      apply propext; constructor
      · intro ⟨a, b⟩; exact ⟨a, by omega_using [b]⟩
      · intro ⟨a, b⟩; exact ⟨a, by omega_using [e, a, b]⟩
  · refine ⟨u₁.same.trans hw, fun x' hx' k hk => by rw [hcs x' hx' k hk, u₁.other _ (creg_T hx') k hk],
      fun i hi k hk => ?_⟩
    rw [hls i hi k hk, u₁.other _ (lreg_T hi) k hk]
    congr 1
    apply propext; constructor
    · intro ⟨a, _⟩; exact a
    · intro a; exact ⟨a, by omega_using [hi]⟩

/-- After the first `n` columns' `D`. -/
def DInv (s₀ : State) (A : Nat → KState) (n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ (∀ x < 5, ∀ k < 4, qy s (creg x) k = C (A k) x) ∧
    ∀ i < 25, ∀ k < 4, qy s (lreg i) k = if i % 5 < n then Th (A k) i else (A k)[i]!

theorem dcols_ok (s₀ : State) (A : Nat → KState) (hA : Regs4 s₀ A)
    (hc : ∀ x < 5, ∀ k < 4, qy s₀ (creg x) k = C (A k) x) :
    WP isa (.block ((List.range 5).flatMap dcol)) s₀ (DInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (DInv s₀ A) (fun x s hx ⟨hw, hcs, hl⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Same.refl _, hc, fun i hi k hk => by simp only [Nat.not_lt_zero, ite_false]; exact hA i hi k hk⟩
  refine WP.mono (dcol_ok x hx s A hcs fun i hi k hk e => by
      rw [hl i hi k hk, ite_f (show ¬ i % 5 < x by omega_using [e])])
    fun s' ⟨h, hc', hl'⟩ => ⟨hw.trans h, fun x' hx' k hk => by rw [hc' x' hx' k hk, hcs x' hx' k hk],
      fun i hi k hk => ?_⟩
  rw [hl' i hi k hk]
  by_cases e : i % 5 = x
  · rw [ite_t e, ite_t (show i % 5 < x + 1 by omega_using [e])]
  · rw [ite_f e, hl i hi k hk]
    by_cases e' : i % 5 < x
    · rw [ite_t e', ite_t (show i % 5 < x + 1 by omega_using [e'])]
    · rw [ite_f e', ite_f (show ¬ i % 5 < x + 1 by omega_using [e, e'])]

/-! ## ρ and π -/

/-- The facts about `piChain` the proof uses, each for the 24 lanes. -/
theorem chain_lt : ∀ j < 24, piChain.getD j 0 < 25 ∧ piChain.getD j 0 ≠ 0 := by decide
theorem chain_inj : ∀ j < 24, ∀ j' < 24, piChain.getD j 0 = piChain.getD j' 0 → j = j' := by decide
theorem chain_src : ∀ j < 23,
    piSrc (piChain.getD j 0 % 5) (piChain.getD j 0 / 5) = piChain.getD (j + 1) 0 := by decide
theorem chain_last : piSrc (piChain.getD 23 0 % 5) (piChain.getD 23 0 / 5) = piChain.getD 0 0 := by decide
theorem chain_all : ∀ p < 25, p ≠ 0 → ∃ j < 24, piChain.getD j 0 = p := by decide
theorem chain_rho : ∀ j < 24, 0 < rhoOff (piChain.getD j 0) ∧ rhoOff (piChain.getD j 0) < 64 := by decide
theorem piSrc_zero : piSrc (0 % 5) (0 / 5) = 0 := rfl
theorem rhoOff_zero : rhoOff 0 = 0 := rfl
theorem piSrc_mod (x y : Nat) : piSrc x y % 5 = (x + 3 * y) % 5 := by
  simp only [piSrc]; omega_using []

/-- Lane `p` after ρ and π: `B` at it. -/
def Bp (A : KState) (p : Nat) : Lane := B A (p % 5) (p / 5)

theorem Bp_eq (A : KState) (p : Nat) :
    Bp A p = rotl (Th A (piSrc (p % 5) (p / 5))) (rhoOff (piSrc (p % 5) (p / 5))) := by
  rw [Bp, B, Th, piSrc_mod]

/-- After the first `n` steps of the chain. -/
def ChInv (s₀ : State) (A : Nat → KState) (n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ (∀ x < 5, ∀ k < 4, qy s (creg x) k = qy s₀ (creg x) k) ∧
    (∀ k < 4, qy s T k = Th (A k) (piChain.getD 0 0)) ∧
    ∀ i < 25, ∀ k < 4, qy s (lreg i) k = if ∃ j < n, piChain.getD j 0 = i then Bp (A k) i else Th (A k) i

theorem rotl_ror (v : Lane) {r : Nat} (h₁ : 0 < r) (h₂ : r < 64) : v.rotateRight (64 - r) = rotl v r := by
  rw [rotl, ite_f (show ¬ r = 0 by omega)]

theorem rhoPi_ok (s₀ : State) (A : Nat → KState) (hT : ∀ i < 25, ∀ k < 4, qy s₀ (lreg i) k = Th (A k) i) :
    WP isa (.block rhoPi) s₀ fun s =>
      Same s₀ s ∧ (∀ x < 5, ∀ k < 4, qy s (creg x) k = qy s₀ (creg x) k) ∧
      ∀ p < 25, ∀ k < 4, qy s (lreg p) k = Bp (A k) p := by
  unfold rhoPi
  refine wp_ecopy fun s₁ u₁ => ?_
  rw [List.append_eq, WP.block_append_iff]
  refine WP.mono (wp_range_map (ChInv s₀ A) (fun j t hj ⟨hw, hcs, hTt, hls⟩ => ?_) s₁
    ⟨u₁.same, fun x hx k hk => u₁.other _ (creg_T hx) k hk, fun k hk => by rw [u₁.val k hk]; exact hT 1 (by omega_using []) k hk,
      fun i hi k hk => by
        rw [u₁.other _ (lreg_T hi) k hk, hT i hi k hk,
          ite_f (show ¬ ∃ j < 0, piChain.getD j 0 = i from fun ⟨_, h, _⟩ => absurd h (by omega_using []))]⟩)
    fun s₂ ⟨hw, hcs, hTt, hls⟩ => ?_
  · have ⟨hc₀, _⟩ := chain_lt j (by omega_using [hj])
    have ⟨hc₁, _⟩ := chain_lt (j + 1) (by omega_using [hj])
    have ⟨r₀, r₁⟩ := chain_rho (j + 1) (by omega_using [hj])
    refine wp_eror (by unfold rhoR; omega_using [r₀]) fun t' u => wp_nil ⟨hw.trans u.same,
      fun x hx k hk => by rw [u.other _ (lreg_creg hc₀ hx).symm k hk, hcs x hx k hk],
      fun k hk => by rw [u.other _ (lreg_T hc₀).symm k hk, hTt k hk], fun i hi k hk => ?_⟩
    by_cases e : i = piChain.getD j 0
    · subst e
      have nf : ¬ ∃ j' < j, piChain.getD j' 0 = piChain.getD (j + 1) 0 := by
        rintro ⟨j', hj', e'⟩
        have := chain_inj j' (by omega_using [hj, hj']) (j + 1) (by omega_using [hj]) e'
        omega_using [hj', this]
      have tt : ∃ j' < j + 1, piChain.getD j' 0 = piChain.getD j 0 := ⟨j, by omega_using [], rfl⟩
      rw [u.val k hk, hls _ hc₁ k hk, ite_f nf, ite_t tt, Bp_eq, chain_src j hj, rhoR]
      exact rotl_ror _ r₀ r₁
    · rw [u.other _ (lreg_ne hi hc₀ e) k hk, hls i hi k hk]
      congr 1
      apply propext; constructor
      · rintro ⟨j', hj', e'⟩; exact ⟨j', by omega_using [hj'], e'⟩
      · rintro ⟨j', hj', e'⟩
        refine ⟨j', ?_, e'⟩
        by_contra h
        exact e (by rw [← e', show j' = j by omega_using [hj', h]])
  · have c23 : piChain.getD 23 0 = 10 := rfl
    have c0 : piChain.getD 0 0 = 1 := rfl
    refine wp_eror (show rhoR 1 < 64 by decide) fun s₃ u => wp_nil ⟨hw.trans u.same,
      fun x hx k hk => by rw [u.other _ (lreg_creg (by decide) hx).symm k hk, hcs x hx k hk],
      fun p hp k hk => ?_⟩
    by_cases e : p = 10
    · subst e
      rw [u.val k hk, hTt k hk, Bp_eq, ← c23, chain_last, c0, rhoR]
      exact rotl_ror _ (by decide) (by decide)
    · rw [u.other _ (lreg_ne hp (by decide) e) k hk, hls p hp k hk]
      by_cases e0 : p = 0
      · subst e0
        have nf : ¬ ∃ j' < 23, piChain.getD j' 0 = 0 := fun ⟨j', hj', e'⟩ => (chain_lt j' (by omega_using [hj'])).2 e'
        rw [ite_f nf, Bp_eq, piSrc_zero, rhoOff_zero, rotl, ite_t rfl]
      · obtain ⟨j', hj', e'⟩ := chain_all p hp e0
        have tt : ∃ j'' < 23, piChain.getD j'' 0 = p := ⟨j', by
          by_contra h
          exact e (by rw [← e', show j' = 23 by omega_using [hj', h]]; rfl), e'⟩
        rw [ite_t tt]
/-! ## χ -/

/-- Lane `p` of the output of χ, before ι. -/
def Xp (A : KState) (p : Nat) : Lane := out A 0 (p % 5) (p / 5)

theorem out_t (A : KState) (rc : Lane) (x y : Nat) (h : ¬(x = 0 ∧ y = 0)) : out A rc x y = out A 0 x y := by
  simp only [out, h, ite_false]

theorem chi_val (A : KState) (x y : Nat) :
    (B A ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B A ((x + 2) % 5) y ^^^ B A x y = out A 0 x y := by
  simp only [out]; split <;> simp

/-- After the first `n` planes of χ. -/
def ChiInv (s₀ : State) (A : Nat → KState) (n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ ∀ i < 25, ∀ k < 4, qy s (lreg i) k = if i / 5 < n then Xp (A k) i else Bp (A k) i

/-- χ on five lanes `b₀, …, b₄` in the distinct registers `a₀, …, a₄`, with
the copies in `t₀` and `t₁`. -/
theorem chi5_ok (s : State) (a₀ a₁ a₂ a₃ a₄ t₀ t₁ : VReg) (b : Nat → Nat → Lane)
    (n01 : a₀ ≠ a₁) (n02 : a₀ ≠ a₂) (n03 : a₀ ≠ a₃) (n04 : a₀ ≠ a₄) (n12 : a₁ ≠ a₂) (n13 : a₁ ≠ a₃)
    (n14 : a₁ ≠ a₄) (n23 : a₂ ≠ a₃) (n24 : a₂ ≠ a₄) (n34 : a₃ ≠ a₄) (m0 : t₀ ≠ t₁)
    (p0 : ∀ a ∈ [a₀, a₁, a₂, a₃, a₄], a ≠ t₀) (p1 : ∀ a ∈ [a₀, a₁, a₂, a₃, a₄], a ≠ t₁)
    (h0 : ∀ k < 4, qy s a₀ k = b 0 k) (h1 : ∀ k < 4, qy s a₁ k = b 1 k) (h2 : ∀ k < 4, qy s a₂ k = b 2 k)
    (h3 : ∀ k < 4, qy s a₃ k = b 3 k) (h4 : ∀ k < 4, qy s a₄ k = b 4 k) :
    WP isa (.block [copy t₀ a₀, copy t₁ a₁, tern a₀ a₁ a₂ 0xD2, tern a₁ a₂ a₃ 0xD2, tern a₂ a₃ a₄ 0xD2,
      tern a₃ a₄ t₀ 0xD2, tern a₄ t₀ t₁ 0xD2]) s fun s' =>
      Same s s' ∧ (∀ r, r ∉ [a₀, a₁, a₂, a₃, a₄, t₀, t₁] → ∀ k < 4, qy s' r k = qy s r k) ∧
      ∀ x < 5, ∀ k < 4, qy s' ([a₀, a₁, a₂, a₃, a₄].getD x a₀) k =
        (b ((x + 1) % 5) k ^^^ 0xffffffffffffffff) &&& b ((x + 2) % 5) k ^^^ b x k := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at p0 p1
  obtain ⟨q0, q1, q2, q3, q4⟩ := p0
  obtain ⟨r0, r1, r2, r3, r4⟩ := p1
  refine wp_ecopy fun s₁ u₁ => wp_ecopy fun s₂ u₂ => wp_ternD2 fun s₃ u₃ => wp_ternD2 fun s₄ u₄ =>
    wp_ternD2 fun s₅ u₅ => wp_ternD2 fun s₆ u₆ => wp_ternD2 fun s₇ u₇ => wp_nil
      ⟨(((((u₁.same.trans u₂.same).trans u₃.same).trans u₄.same).trans u₅.same).trans u₆.same).trans u₇.same,
        fun r hr k hk => ?_, fun x hx k hk => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := hr
    rw [u₇.other _ e4 k hk, u₆.other _ e3 k hk, u₅.other _ e2 k hk, u₄.other _ e1 k hk, u₃.other _ e0 k hk,
      u₂.other _ e6 k hk, u₁.other _ e5 k hk]
  · -- Each register before its write.
    have z0 : qy s₂ a₀ k = b 0 k := by rw [u₂.other _ r0 k hk, u₁.other _ q0 k hk, h0 k hk]
    have z1 : qy s₂ a₁ k = b 1 k := by rw [u₂.other _ r1 k hk, u₁.other _ q1 k hk, h1 k hk]
    have z2 : qy s₂ a₂ k = b 2 k := by rw [u₂.other _ r2 k hk, u₁.other _ q2 k hk, h2 k hk]
    have z3 : qy s₂ a₃ k = b 3 k := by rw [u₂.other _ r3 k hk, u₁.other _ q3 k hk, h3 k hk]
    have z4 : qy s₂ a₄ k = b 4 k := by rw [u₂.other _ r4 k hk, u₁.other _ q4 k hk, h4 k hk]
    have zt0 : qy s₂ t₀ k = b 0 k := by rw [u₂.other _ m0 k hk, u₁.val k hk, h0 k hk]
    have zt1 : qy s₂ t₁ k = b 1 k := by rw [u₂.val k hk, u₁.other _ q1 k hk, h1 k hk]
    rcases (by omega_using [hx] : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd, Nat.reduceMod]
    · rw [u₇.other _ n04 k hk, u₆.other _ n03 k hk, u₅.other _ n02 k hk, u₄.other _ n01 k hk, u₃.val k hk, z0, z1, z2]
    · rw [u₇.other _ n14 k hk, u₆.other _ n13 k hk, u₅.other _ n12 k hk, u₄.val k hk, u₃.other _ n02.symm k hk,
        u₃.other _ n03.symm k hk, u₃.other _ n01.symm k hk, z1, z2, z3]
    · rw [u₇.other _ n24 k hk, u₆.other _ n23 k hk, u₅.val k hk, u₄.other _ n13.symm k hk, u₄.other _ n14.symm k hk,
        u₄.other _ n12.symm k hk, u₃.other _ n03.symm k hk, u₃.other _ n04.symm k hk, u₃.other _ n02.symm k hk,
        z2, z3, z4]
    · rw [u₇.other _ n34 k hk, u₆.val k hk, u₅.other _ n24.symm k hk, u₅.other _ q2.symm k hk,
        u₅.other _ n23.symm k hk, u₄.other _ n14.symm k hk, u₄.other _ q1.symm k hk, u₄.other _ n13.symm k hk,
        u₃.other _ n04.symm k hk, u₃.other _ q0.symm k hk, u₃.other _ n03.symm k hk, z4, zt0, z3]
    · rw [u₇.val k hk, u₆.other _ q3.symm k hk, u₆.other _ r3.symm k hk, u₆.other _ n34.symm k hk,
        u₅.other _ q2.symm k hk, u₅.other _ r2.symm k hk, u₅.other _ n24.symm k hk,
        u₄.other _ q1.symm k hk, u₄.other _ r1.symm k hk, u₄.other _ n14.symm k hk,
        u₃.other _ q0.symm k hk, u₃.other _ r0.symm k hk, u₃.other _ n04.symm k hk, zt0, zt1, z4]

/-- χ on plane `y`, from its lane `a` on. -/
theorem chiAt_ok (y a : Nat) (hy : y < 5) (ha : a < 5) (s : State) (A : Nat → KState)
    (hb : ∀ x < 5, ∀ k < 4, qy s (lreg (5 * y + x)) k = Bp (A k) (5 * y + x)) :
    WP isa (.block (chiAt y a)) s fun s' =>
      Same s s' ∧ (∀ i < 25, i / 5 ≠ y → ∀ k < 4, qy s' (lreg i) k = qy s (lreg i) k) ∧
      ∀ x < 5, ∀ k < 4, qy s' (lreg (5 * y + x)) k = Xp (A k) (5 * y + x) := by
  have l : ∀ x, 5 * y + (a + x) % 5 < 25 := fun x => by omega_using [hy]
  have ne : ∀ x < 5, ∀ x' < 5, x ≠ x' → lreg (5 * y + (a + x) % 5) ≠ lreg (5 * y + (a + x') % 5) :=
    fun x hx x' hx' h => lreg_ne (l x) (l x') (by omega_using [h, hx, hx'])
  have lc : ∀ x, ∀ c < 5, lreg (5 * y + (a + x) % 5) ≠ creg c := fun x c hc => lreg_creg (l x) hc
  have hb' : ∀ x, ∀ k < 4, qy s (lreg (5 * y + (a + x) % 5)) k = Bp (A k) (5 * y + (a + x) % 5) :=
    fun x k hk => hb _ (Nat.mod_lt _ (by decide)) k hk
  refine WP.mono (chi5_ok s (lreg (5 * y + (a + 0) % 5)) (lreg (5 * y + (a + 1) % 5)) (lreg (5 * y + (a + 2) % 5))
    (lreg (5 * y + (a + 3) % 5)) (lreg (5 * y + (a + 4) % 5)) (creg 0) (creg 1)
    (fun x k => Bp (A k) (5 * y + (a + x) % 5))
    (ne 0 (by decide) 1 (by decide) (by decide)) (ne 0 (by decide) 2 (by decide) (by decide))
    (ne 0 (by decide) 3 (by decide) (by decide)) (ne 0 (by decide) 4 (by decide) (by decide))
    (ne 1 (by decide) 2 (by decide) (by decide)) (ne 1 (by decide) 3 (by decide) (by decide))
    (ne 1 (by decide) 4 (by decide) (by decide)) (ne 2 (by decide) 3 (by decide) (by decide))
    (ne 2 (by decide) 4 (by decide) (by decide)) (ne 3 (by decide) 4 (by decide) (by decide))
    (creg_ne (by decide) (by decide) (by decide))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨lc 0 0 (by decide), lc 1 0 (by decide), lc 2 0 (by decide), lc 3 0 (by decide), lc 4 0 (by decide)⟩)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨lc 0 1 (by decide), lc 1 1 (by decide), lc 2 1 (by decide), lc 3 1 (by decide), lc 4 1 (by decide)⟩)
    (hb' 0) (hb' 1) (hb' 2) (hb' 3) (hb' 4))
    fun s' ⟨hs, ho, hv⟩ => ⟨hs, fun i hi hiy k hk => ho _ ?_ k hk, fun x hx k hk => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨lreg_ne hi (l 0) (by omega_using [hiy]), lreg_ne hi (l 1) (by omega_using [hiy]),
      lreg_ne hi (l 2) (by omega_using [hiy]), lreg_ne hi (l 3) (by omega_using [hiy]),
      lreg_ne hi (l 4) (by omega_using [hiy]), lreg_creg hi (by decide), lreg_creg hi (by decide)⟩
  · -- Lane `x` of the plane is the `x'`-th that `chiAt` writes.
    obtain ⟨x', hx', e1, e2, e3⟩ : ∃ x' < 5, (a + x') % 5 = x ∧ (a + (x' + 1) % 5) % 5 = (x + 1) % 5 ∧
        (a + (x' + 2) % 5) % 5 = (x + 2) % 5 :=
      ⟨(x + 5 - a) % 5, by omega_using [], by omega_using [hx, ha], by omega_using [hx, ha], by omega_using [hx, ha]⟩
    have e := hv x' hx' k hk
    have g : [lreg (5 * y + (a + 0) % 5), lreg (5 * y + (a + 1) % 5), lreg (5 * y + (a + 2) % 5),
        lreg (5 * y + (a + 3) % 5), lreg (5 * y + (a + 4) % 5)].getD x' (lreg (5 * y + (a + 0) % 5)) =
        lreg (5 * y + (a + x') % 5) := by
      rcases (by omega_using [hx'] : x' = 0 ∨ x' = 1 ∨ x' = 2 ∨ x' = 3 ∨ x' = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [g, e1, e2, e3] at e
    rw [e, Xp, show (5 * y + x) % 5 = x by omega_using [hx], show (5 * y + x) / 5 = y by omega_using [hx], ← chi_val]
    simp only [Bp]
    rw [show (5 * y + (x + 1) % 5) % 5 = (x + 1) % 5 by omega_using [], show (5 * y + (x + 1) % 5) / 5 = y by omega_using [],
      show (5 * y + (x + 2) % 5) % 5 = (x + 2) % 5 by omega_using [], show (5 * y + (x + 2) % 5) / 5 = y by omega_using [],
      show (5 * y + x) % 5 = x by omega_using [hx], show (5 * y + x) / 5 = y by omega_using [hx]]

/-- χ on plane `y`. -/
theorem chi_ok (y : Nat) (hy : y < 5) (s : State) (A : Nat → KState)
    (hb : ∀ x < 5, ∀ k < 4, qy s (lreg (5 * y + x)) k = Bp (A k) (5 * y + x)) :
    WP isa (.block (chi y)) s fun s' =>
      Same s s' ∧ (∀ i < 25, i / 5 ≠ y → ∀ k < 4, qy s' (lreg i) k = qy s (lreg i) k) ∧
      ∀ x < 5, ∀ k < 4, qy s' (lreg (5 * y + x)) k = Xp (A k) (5 * y + x) :=
  chiAt_ok y (chiStart y) hy (Nat.mod_lt _ (by decide)) s A hb

theorem chis_ok (s₀ : State) (A : Nat → KState) (hb : ∀ p < 25, ∀ k < 4, qy s₀ (lreg p) k = Bp (A k) p) :
    WP isa (.block ((List.range 5).flatMap chi)) s₀ (ChiInv s₀ A 5) := by
  refine wp_range_flatMap (M := isa) (ChiInv s₀ A) (fun y s hy ⟨hw, hl⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Same.refl _, fun i hi k hk => by rw [ite_f (show ¬ i / 5 < 0 by omega_using [])]; exact hb i hi k hk⟩
  refine WP.mono (chi_ok y hy s A fun x hx k hk => by
      rw [hl _ (by omega_using [hy, hx]) k hk, ite_f (show ¬ (5 * y + x) / 5 < y by omega_using [])])
    fun s' ⟨h, ho, hv⟩ => ⟨hw.trans h, fun i hi k hk => ?_⟩
  by_cases e : i / 5 = y
  · rw [ite_t (show i / 5 < y + 1 by omega_using [e]), show i = 5 * y + i % 5 by omega_using [e]]
    exact hv _ (Nat.mod_lt _ (by omega_using [])) k hk
  · rw [ho i hi e k hk, hl i hi k hk]
    by_cases e' : i / 5 < y
    · rw [ite_t e', ite_t (show i / 5 < y + 1 by omega_using [e'])]
    · rw [ite_f e', ite_f (show ¬ i / 5 < y + 1 by omega_using [e, e'])]

/-! ## ι, and the next round constant -/

theorem iota_ok (s : State) (rcp : Addr) (rc : Lane) (hrdx : s.gpr .rdx = rcp)
    (hin : InRegions (s.rd ++ s.wr) rcp 32) (hrc : ∀ k < 4, s.mem.readW (la rcp 0 k) 64 = rc) :
    WP isa (.block iota) s fun s' =>
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ k < 4, qy s' (lreg 0) k = qy s (lreg 0) k ^^^ rc) ∧
      (∀ i < 25, i ≠ 0 → ∀ k < 4, qy s' (lreg i) k = qy s (lreg i) k) ∧
      s'.gpr .rdx = rcp + 32 ∧ (∀ g, g ≠ .rdx → s'.gpr g = s.gpr g) ∧
      s'.zf = some (rcp + 32 - s.gpr .rcx == 0) := by
  have ha : s.ea (at_ .rdx 0) = rcp := by rw [VG.Proof.Sha3.X86_64.ea_at, hrdx]; exact BitVec.add_zero _
  unfold iota
  refine wp_evld ha hin fun s₁ u₁ => wp_exor fun s₂ u₂ => WP.cons rfl (WP.cons rfl (wp_nil ?_))
  have g : s₂.gpr = s.gpr := u₂.gpr.trans u₁.gpr
  refine ⟨u₂.mem.trans u₁.mem, u₂.rd.trans u₁.rd, u₂.wr.trans u₁.wr, fun k hk => ?_, fun i hi h0 k hk => ?_, ?_, ?_, ?_⟩
  · show qy s₂ (lreg 0) k = _
    rw [u₂.val k hk, u₁.other _ (lreg_T (by decide)) k hk, u₁.val k hk, ← hrc k hk]
    simp only [la, Nat.mul_zero, Nat.zero_add]
  · show qy s₂ (lreg i) k = _
    rw [u₂.other _ (lreg_ne hi (by decide) h0) k hk, u₁.other _ (lreg_T hi) k hk]
  · simp [State.setReg, g, hrdx]
  · intro r hr; simp [State.setReg, g, hr]
  · simp [State.setReg, g, hrdx]

end VG.Proof.Sha3.X86_64.X4R

end

end


/-!
# Keccak-f[1600] four times at once, in registers: the permutation

`permute4R` loads the four interleaved states at `rdi` into the registers
(`load_ok`), runs the 24 rounds on them (`round_ok`, one per iteration of
its loop), and stores them back (`store_ok`): Keccak-f[1600] on each of the
four states (`permute4R_ok`), with the interface of `X4.permute4_ok`.
-/

@[expose] public section

namespace VG.Proof.Sha3.X86_64.X4R

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4R
open VG.Spec.Sha3 (keccakF rnd RC)
open VG.Proof.Sha3 (outState outState_eq foldl_succ out)
open VG.Proof.Sha3.X86_64.X4 (KState Lane la la_eq Lanes4 Pre4 end_beq la_contains la_rc)
open VG.Proof.Sha3.X86_64 (wp_nil ea_at)
open VG.Impl.Sha3.X86_64 (at_)

/-! ## A round -/

theorem out_zero (A : KState) (rc : Lane) : out A rc 0 0 = out A 0 0 0 ^^^ rc := by
  simp [out]

theorem outState_get (A : KState) (rc : Lane) {i : Nat} (hi : i < 25) :
    (outState A rc)[i]! = out A rc (i % 5) (i / 5) := by
  simp [outState, hi]

theorem round_ok (s : State) (A : Nat → KState) (rcp : Addr) (rc : Lane) (hA : Regs4 s A)
    (hrdx : s.gpr .rdx = rcp) (hin : InRegions (s.rd ++ s.wr) rcp 32)
    (hrc : ∀ k < 4, s.mem.readW (la rcp 0 k) 64 = rc) :
    WP isa (.block round) s fun s' =>
      Regs4 s' (fun k => outState (A k) rc) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rdx = rcp + 32 ∧ (∀ g, g ≠ .rdx → s'.gpr g = s.gpr g) ∧
      s'.zf = some (rcp + 32 - s.gpr .rcx == 0) := by
  unfold round
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (columns_ok s A hA) fun s₁ ⟨k₁, r₁, c₁⟩ => ?_
  refine WP.mono (dcols_ok s₁ A r₁ c₁) fun s₂ ⟨k₂, _, d₂⟩ => ?_
  refine WP.mono (rhoPi_ok s₂ A fun i hi k hk => by rw [d₂ i hi k hk, ite_t (show i % 5 < 5 by omega_using [])])
    fun s₃ ⟨k₃, _, b₃⟩ => ?_
  refine WP.mono (chis_ok s₃ A b₃) fun s₄ ⟨k₄, x₄⟩ => ?_
  have k := ((k₁.trans k₂).trans k₃).trans k₄
  refine WP.mono (iota_ok s₄ rcp rc (by rw [k.gpr, hrdx]) (by rw [k.rd, k.wr]; exact hin)
    (by rw [k.mem]; exact hrc)) fun s₅ ⟨m₅, r₅, w₅, z₅, o₅, d₅, g₅, f₅⟩ => ?_
  refine ⟨fun i hi j hj => ?_, by rw [m₅, k.mem], by rw [r₅, k.rd], by rw [w₅, k.wr], d₅,
    fun g hg => by rw [g₅ g hg, k.gpr], by rw [f₅, k.gpr]⟩
  rw [outState_get _ _ hi]
  by_cases e : i = 0
  · subst e
    rw [z₅ j hj, x₄ 0 hi j hj, ite_t (show 0 / 5 < 5 by decide), out_zero]; rfl
  · rw [o₅ i hi e j hj, x₄ i hi j hj, ite_t (show i / 5 < 5 by omega_using [hi]), Xp,
      Proof.Sha3.X86_64.X4R.out_t _ rc _ _ (by omega_using [e])]

/-! ## Loading and storing the states -/

/-- After loading the first `n` lanes. -/
def LdInv (s₀ : State) (A : Nat → KState) (n : Nat) (s : State) : Prop :=
  Same s₀ s ∧ ∀ i < n, ∀ k < 4, qy s (lreg i) k = (A k)[i]!

theorem load_ok (s₀ : State) (src : Addr) (A : Nat → KState) (hdi : s₀.gpr .rdi = src)
    (hin : ∀ i < 25, InRegions s₀.wr (src + BitVec.ofNat 64 (32 * i)) 32) (hA : Lanes4 s₀.mem src A) :
    WP isa (.block load) s₀ fun s => Same s₀ s ∧ Regs4 s A := by
  refine WP.mono (wp_range_map (LdInv s₀ A) (fun i s hi ⟨hw, hl⟩ => ?_) s₀
    ⟨Same.refl _, fun _ h => absurd h (by omega_using [])⟩) fun s h => h
  refine wp_evld (by rw [ea_at, hw.gpr, hdi]) (by rw [hw.rd, hw.wr]; exact X4.in_append (hin i hi))
    fun s' u => wp_nil ⟨hw.trans u.same, fun j hj k hk => ?_⟩
  by_cases e : j = i
  · subst e; rw [u.val k hk, la_eq, hw.mem, hA j hi k hk]
  · rw [u.other _ (lreg_ne (by omega_using [hi, hj]) hi e) k hk, hl j (by omega_using [hj, e]) k hk]

/-- After storing the first `n` lanes. -/
def StInv (s₀ : State) (src : Addr) (n : Nat) (s : State) : Prop :=
  s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ (∀ r k, qy s r k = qy s₀ r k) ∧
    Frame [⟨src, 800⟩] s₀.mem s.mem ∧ ∀ i < n, ∀ k < 4, s.mem.readW (la src i k) 64 = qy s₀ (lreg i) k

theorem store_ok (s₀ : State) (src : Addr) (hdi : s₀.gpr .rdi = src)
    (hin : ∀ i < 25, InRegions s₀.wr (src + BitVec.ofNat 64 (32 * i)) 32) :
    WP isa (.block store) s₀ (StInv s₀ src 25) := by
  refine wp_range_map (StInv s₀ src) (fun i s hi ⟨hg, hrd, hwr, hq, hf, hl⟩ => ?_) s₀
    ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩
  refine wp_evst (by rw [ea_at, hg, hdi]) (by rw [hwr]; exact hin i hi) (wp_nil ⟨hg, hrd, hwr, hq, ?_, ?_⟩)
  · exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base src (by omega_using [hi]) (by omega_using [hi]))
  · intro j hj k hk
    by_cases e : j = i
    · subst e
      show (s.mem.writeW _ _).readW _ 64 = _
      rw [← la_eq, readW_evst _ _ _ _ hk, hq]
    · show (s.mem.writeW _ _).readW _ 64 = _
      have := readW_writeW_off s.mem src (s.vy (lreg i)) (d := 32 * j + 8 * k) (e := 32 * i) (n := 8)
        (by omega_using [hi, hj, hk]) (by omega_using [hi]) (by omega_using [hk, e])
      rw [this]
      exact hl j (by omega_using [hj, e]) k hk

/-! ## The 24 rounds -/

/-- Before round `r`. -/
structure RInv (s₀ : State) (tbl : Addr) (A : Nat → KState) (r : Nat) (s : State) : Prop where
  regs : Regs4 s fun k => (List.range r).foldl rnd (A k)
  rdx : s.gpr .rdx = tbl + BitVec.ofNat 64 (32 * r)
  rest : ∀ g, g ≠ .rdx → s.gpr g = s₀.gpr g
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem round_step {s₀ : State} {src oth tbl : Addr} {A : Nat → KState} (hp : Pre4 s₀ src oth tbl)
    (hcx : s₀.gpr .rcx = tbl + BitVec.ofNat 64 768) {r : Nat} (hr : r < 24) {s : State}
    (h : RInv s₀ tbl A r s) :
    WP isa (.block round) s fun s' => eval .ne s' = some (!decide (r + 1 = 24)) ∧ RInv s₀ tbl A (r + 1) s' := by
  refine WP.mono (round_ok s _ _ (RC r) h.regs h.rdx (by rw [h.rd, h.wr]; exact hp.tbl_in r hr)
    fun k hk => by rw [la_rc, h.mem]; exact hp.rc r hr k hk) fun s' ⟨hg, hm, hrd, hwr, hdx, ho, hz⟩ => ?_
  have hcx' : s.gpr .rcx = tbl + BitVec.ofNat 64 768 := by rw [h.rest _ (by decide), hcx]
  refine ⟨?_, ⟨fun i hi k hk => ?_, ?_, fun g hg' => by rw [ho g hg', h.rest g hg'], hm.trans h.mem,
    hrd.trans h.rd, hwr.trans h.wr⟩⟩
  · simp only [eval, hz, hcx', Option.map_some, end_beq tbl r hr]
  · rw [hg i hi k hk]; simp only [foldl_succ, ← outState_eq]
  · rw [hdx, BitVec.add_assoc, show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]; rfl

/-- The 24 rounds on each of the four states at `src` (with the table of
`X4.permute4`, and its interface): Keccak-f[1600] on each, with `rdx` at the
end of the table and every other register as it was. -/
theorem permute4R_ok {s₀ : State} {src oth tbl : Addr} (hp : Pre4 s₀ src oth tbl)
    (hdi : s₀.gpr .rdi = src) (hdx : s₀.gpr .rdx = tbl)
    (hcx : s₀.gpr .rcx = tbl + BitVec.ofNat 64 768) {A : Nat → KState} (hA : Lanes4 s₀.mem src A) :
    WP isa permute4R s₀ fun s =>
      Lanes4 s.mem src (fun k => keccakF (A k)) ∧ Frame [⟨src, 800⟩, ⟨oth, 800⟩] s₀.mem s.mem ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.gpr .rdx = tbl + BitVec.ofNat 64 768 ∧
      ∀ g, g ≠ .rax → g ≠ .rdx → s.gpr g = s₀.gpr g := by
  unfold permute4R
  refine WP.seq (WP.mono (load_ok s₀ src A hdi hp.src_in hA) fun s₁ ⟨k₁, r₁⟩ => ?_)
  have h₀ : RInv s₀ tbl A 0 s₁ := ⟨by simpa using r₁, by rw [k₁.gpr, hdx]; exact (BitVec.add_zero _).symm,
    fun g _ => by rw [k₁.gpr], k₁.mem, k₁.rd, k₁.wr⟩
  let Inv : Nat → State → Prop := fun n s => ∃ r, n = 24 - r ∧ r < 24 ∧ RInv s₀ tbl A r s
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := RInv s₀ tbl A 24) Inv (fun n s ⟨r, hn, hr, h⟩ => ?_)
    24 s₁ ⟨0, rfl, by omega_using [], h₀⟩) fun s₂ h₂ => ?_)
  · refine WP.mono (round_step hp hcx hr h) fun s' ⟨he, h'⟩ => ?_
    by_cases hlast : r + 1 = 24
    · exact .inl ⟨by show eval .ne s' = _; rw [he, hlast]; rfl, hlast ▸ h'⟩
    · exact .inr ⟨by show eval .ne s' = _; rw [he]; simp [hlast], 24 - (r + 1), by omega_using [hn, hr], r + 1, rfl, by omega_using [hr, hlast], h'⟩
  · refine WP.mono (store_ok s₂ src (by rw [h₂.rest _ (by decide), hdi]) (by rw [h₂.wr]; exact hp.src_in))
      fun s ⟨hg, hrd, hwr, _, hf, hl⟩ => ⟨fun i hi k hk => by rw [hl i hi k hk, h₂.regs i hi k hk]; rfl,
        ?_, hrd.trans h₂.rd, hwr.trans h₂.wr, by rw [hg, h₂.rdx], fun g _ hd => by rw [hg, h₂.rest g hd]⟩
    rw [← h₂.mem]
    refine hf.sub fun R hR => ?_
    simp only [List.mem_singleton] at hR; subst hR
    exact ⟨_, by simp, fun _ h => h⟩

end VG.Proof.Sha3.X86_64.X4R

namespace VG.Proof.Sha3.X86_64.X4

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4
open VG.Spec.Sha3 (keccakF)

/-- `permute4` (`permute4M`, or with `fast` `X4R.permute4R`): Keccak-f[1600]
on each of the four states at `src`, with `rdi`, `rsi` and every register but
`rax` and `rdx` as they were. -/
theorem permute4_ok {s₀ : State} {src oth tbl : Addr} (hp : Pre4 s₀ src oth tbl)
    (hdi : s₀.gpr .rdi = src) (hsi : s₀.gpr .rsi = oth) (hdx : s₀.gpr .rdx = tbl)
    (hcx : s₀.gpr .rcx = tbl + BitVec.ofNat 64 768) {A : Nat → KState} (hA : Lanes4 s₀.mem src A)
    (fast : Bool := false) :
    WP isa (permute4 fast) s₀ fun s =>
      Lanes4 s.mem src (fun k => keccakF (A k)) ∧ Frame [⟨src, 800⟩, ⟨oth, 800⟩] s₀.mem s.mem ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.gpr .rdx = tbl + BitVec.ofNat 64 768 ∧
      ∀ g, g ≠ .rax → g ≠ .rdx → s.gpr g = s₀.gpr g := by
  cases fast
  · exact permute4M_ok hp hdi hsi hdx hcx hA
  · exact X4R.permute4R_ok hp hdi hdx hcx hA

end VG.Proof.Sha3.X86_64.X4
