module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Run
public import VerifiedGarbage.Proof.Blowfish.Scan32
public import VerifiedGarbage.Proof.Blowfish.F
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Impl.Blowfish.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-!
# Blowfish on RISC-V: an S-box lookup

`lookup_run`: `lookup j` leaves S-box `j`'s entry for the byte `3 - j` of
xL's low word in the accumulator's low word, changing only the lookup's
registers. The structure of PPC64LE's (`Proof/Blowfish/PPC64LE/Lookup.lean`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- What a lookup needs: the schedule at `a7` readable and word-aligned. -/
structure LookEnv (s : State) : Prop where
  rd : ∀ o, o % 4 = 0 → o + 4 ≤ 4168 → InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 o) 4
  al : (s.gpr .a7).toNat % 4 = 0

/-- The registers a lookup writes. -/
def lookRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6]

theorem LookEnv.keep {s t : State} (E : LookEnv s) {rs : List Reg} (h : Keep rs s t)
    (h7 : Reg.a7 ∉ rs) : LookEnv t := by
  refine ⟨fun o ha ho => ?_, by rw [h.gpr h7]; exact E.al⟩
  rw [h.gpr h7, h.2.1, h.2.2]; exact E.rd o ha ho

/-- A 4-byte aligned offset of a 4-byte aligned base. -/
theorem al_add {p : Addr} (hp : p.toNat % 4 = 0) {d : Nat} (hd : d % 4 = 0) (hd' : d < 2 ^ 64) :
    (p + BitVec.ofNat 64 d).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) hd']
  have := p.isLt
  omega

/-! ## The index -/

theorem index_val (x : BitVec 64) {j : Nat} (hj : j < 4) :
    (x <<< (32 + 8 * j)) >>> 56 = (quarter (lo x) j).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [quarter, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft]
  by_cases h8 : i < 8
  · simp only [h8, decide_true, Bool.true_and, show 56 + i < 64 by omega,
      show ¬ (56 + i < 32 + 8 * j) by omega, decide_false, Bool.not_false,
      show 8 * (3 - j) + i < 32 by omega]
    rw [decide_eq_true hi, Bool.true_and]
    congr 1; omega
  · simp only [h8, decide_false, Bool.false_and]
    by_cases h : 56 + i < 64
    · omega
    · simp [h]

theorem index_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block (index j)) s fun t =>
      t.gpr .t1 = (quarter (lo (s.gpr .a3)) j).setWidth 64 ∧ t.mem = s.mem := by
  rw [← index_val _ hj]
  unfold index
  brun [show 32 + 8 * j < 64 by omega]

/-! ## Rotations selected by a bit of the index -/

theorem condRot_run (s : State) (x : Reg) {c a : Nat} (hc : c < 64) (ha0 : 0 < a) (ha : a < 32)
    (x1 : x ≠ .t1) (x3 : x ≠ .t3) (x4 : x ≠ .t4) :
    WP isa (.block (condRot x c a)) s fun t =>
      lo (t.gpr x) = (if (s.gpr .t1).getLsbD c then (lo (s.gpr x)).rotateRight a else lo (s.gpr x)) ∧
        t.mem = s.mem := by
  have hx1 : Reg.t1 ≠ x := Ne.symm x1
  have hx3 : Reg.t3 ≠ x := Ne.symm x3
  have hx4 : Reg.t4 ≠ x := Ne.symm x4
  unfold condRot
  brun [x1, x3, x4, hx1, hx3, hx4, ha, show 32 - a < 32 by omega, show 63 - c < 64 by omega]
  rw [bit_mask _ hc, select_eq, lo_ite, lo_rotr _ ha]

/-- The low two bits of `q`, by `q`'s residue mod 4. -/
theorem bit01 (q : BitVec 64) :
    q.getLsbD 0 = decide (q.toNat % 4 % 2 = 1) ∧ q.getLsbD 1 = decide (q.toNat % 4 / 2 = 1) := by
  simp only [BitVec.getLsbD, Nat.testBit_zero, Nat.testBit_succ]
  constructor <;> congr 1 <;> apply propext <;> omega

theorem lo_ite_bool {b : Bool} (x y : BitVec 32) : (if b then x else y) = if b = true then x else y := rfl

/-- The lane mask, the accumulator and the row pointer. -/
theorem start_run (s : State) {j : Nat} (hj : j < 4) {L : Nat} (hL : (s.gpr .t1).toNat % 4 = L) :
    WP isa (.block (lookupStart j)) s fun t =>
      lo (t.gpr .t6) = laneMask L ∧ t.gpr .t2 = 0#64 ∧
        t.gpr .t0 = s.gpr .a7 + BitVec.ofNat 64 (1024 * j) ∧ t.mem = s.mem := by
  have hl : L < 4 := by omega
  obtain ⟨b0, b1⟩ := bit01 (s.gpr .t1)
  rw [hL] at b0 b1
  unfold lookupStart
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have hA : WP isa (.block [.li lane 255]) s fun t =>
      t.gpr .t6 = BitVec.ofNat 64 255 ∧ t.mem = s.mem := by brun
  refine WP.mono (WP.keep [.t6] hA (by decide) rfl) fun t₀ ⟨⟨t6, tm⟩, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t3, .t4, .t6] (condRot_run t₀ .t6 (c := 0) (a := 24) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) (by decide) rfl) fun t₁ ⟨⟨u6, um⟩, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t3, .t4, .t6] (condRot_run t₁ .t6 (c := 1) (a := 16) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) (by decide) rfl) fun t₂ ⟨⟨v6, vm⟩, vk⟩ => ?_
  have q1 : t₀.gpr .t1 = s.gpr .t1 := tk.gpr (by decide)
  have q2 : t₁.gpr .t1 = s.gpr .t1 := (uk.gpr (by decide)).trans q1
  have z7 : t₂.gpr .a7 = s.gpr .a7 := by rw [vk.gpr (by decide), uk.gpr (by decide), tk.gpr (by decide)]
  have e6 : lo (t₂.gpr .t6) = laneMask L := by
    rw [v6, u6, q2, q1, t6, b0, b1, ← laneMask_rot hl, lo_ofNat]
  have em : t₂.mem = s.mem := by rw [vm, um, tm]
  brun [z7, em, show 512 * j < 2048 by omega]
  refine ⟨e6, ?_⟩
  rw [Offset.add_add]
  congr 2
  omega

/-! ## The rows -/

theorem ite_ones_and (c : Prop) [Decidable c] (y : BitVec 64) :
    (if c then BitVec.allOnes 64 else 0) &&& y = if c then y else 0 := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h, BitVec.allOnes_and]
  · simp [h]

theorem lo_zero : lo 0#64 = 0#32 := rfl

theorem lo_ite' (c : Prop) [Decidable c] (x y : BitVec 64) :
    lo (if c then x else y) = if c then lo x else lo y := by
  by_cases h : c <;> simp [h]

/-- A word rotated right by `r`, from the two word shifts. -/
theorem plane_rot (x : BitVec 32) {r : Nat} (h : r < 32) :
    lo (sext32 (x <<< (32 - r)) ^^^ sext32 (x >>> r)) = x.rotateRight r := by
  rw [lo_xor, lo_sext, lo_sext, BitVec.xor_comm, RISCV64.ByteLoad.rotr_shifts _ h]

theorem row_run (u : State) {j : Nat} (hj : j < 4) {q rp S : BitVec 64} {acc lm : BitVec 32}
    (h1 : u.gpr .t1 = q) (h2 : lo (u.gpr .t2) = acc) (h6 : lo (u.gpr .t6) = lm)
    (h0 : u.gpr .t0 = rp) (h7 : u.gpr .a7 = S)
    (r0 : InRegions (u.rd ++ u.wr) rp 4) (r1 : InRegions (u.rd ++ u.wr) (rp + 256#64) 4)
    (r2 : InRegions (u.rd ++ u.wr) (rp + 512#64) 4) (r3 : InRegions (u.rd ++ u.wr) (rp + 768#64) 4)
    (a0 : rp.toNat % 4 = 0) (a1 : (rp + 256#64).toNat % 4 = 0) (a2 : (rp + 512#64).toNat % 4 = 0)
    (a3 : (rp + 768#64).toNat % 4 = 0) :
    WP isa (.block (row j)) u fun t =>
      let M := if (q >>> 2).toNat = 0 then lm else 0
      let w := fun (o : Addr) => u.mem.readW (rp + o) 32 &&& M
      lo (t.gpr .t2) = (((acc ||| w 0) ||| (w 256#64).rotateRight 24) ||| (w 512#64).rotateRight 16) |||
        (w 768#64).rotateRight 8 ∧
      t.gpr .t1 = q - 4#64 ∧ t.gpr .t0 = rp + 4#64 ∧
      t.gpr .t4 = rp + 4#64 - S - BitVec.ofNat 64 (512 * j) - BitVec.ofNat 64 (512 * j + 256) ∧
      t.mem = u.mem := by
  have hq : (q >>> 2).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := q.isLt; omega
  unfold row rowMask plane
  brun [h1, h0, h7, r0, r1, r2, r3, a0, a1, a2, a3, show 512 * j ≤ 2048 by omega,
    show 512 * j + 256 ≤ 2048 by omega]
  have p1 : ∀ x : BitVec 32, lo (sext32 (x <<< 8) ^^^ sext32 (x >>> 24)) = x.rotateRight 24 :=
    fun x => plane_rot x (r := 24) (by decide)
  have p2 : ∀ x : BitVec 32, lo (sext32 (x <<< 16) ^^^ sext32 (x >>> 16)) = x.rotateRight 16 :=
    fun x => plane_rot x (r := 16) (by decide)
  have p3 : ∀ x : BitVec 32, lo (sext32 (x <<< 24) ^^^ sext32 (x >>> 8)) = x.rotateRight 8 :=
    fun x => plane_rot x (r := 8) (by decide)
  simp only [lo_or, sra_mask _ hq, lo_and, lo_ext, lo_ite', ite_ones_and, h2, h6, p1, p2, p3,
    show lo (0 : BitVec 64) = 0 from rfl, show rp + (0 : BitVec 64) = rp from BitVec.add_zero rp]

/-- `(q - 4k) >> 2` is zero iff row `k` holds the index. -/
theorem row_hit (x : Byte) {k : Nat} (hk : k < 64) :
    ((x.setWidth 64 - BitVec.ofNat 64 (4 * k)) >>> 2).toNat = 0 ↔ x.toNat / 4 = k := by
  have := x.isLt
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 4 * k < 2 ^ 64 by omega),
    Nat.shiftRight_eq_div_pow]
  omega

/-- `a - c` (as doublewords, both below `2 ^ 64`) is nonzero iff `a ≠ c`. -/
theorem ofNat_sub_bne {a c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c != (0 : BitVec 64)) = !decide (a = c) := by
  by_cases h : a = c
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 c ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at this
      omega
    rw [decide_eq_false h, Bool.not_false]
    exact bne_iff_ne.mpr this

/-- The row pointer's end test, in the frame. -/
theorem row_end (S : Addr) (j k : Nat) :
    S + BitVec.ofNat 64 (1024 * j + 4 * k) + 4#64 - S - BitVec.ofNat 64 (512 * j) -
      BitVec.ofNat 64 (512 * j + 256) = BitVec.ofNat 64 (4 * (k + 1)) - BitVec.ofNat 64 256 := by
  rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add, Offset.add_sub_cancel_left]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- After `k` rows of S-box `j` for the index `idx`, from the lookup's start
`s₀`. -/
structure RowInv (s₀ : State) (j : Nat) (idx : Byte) (k : Nat) (u : State) : Prop where
  q : u.gpr .t1 = idx.setWidth 64 - BitVec.ofNat 64 (4 * k)
  acc : lo (u.gpr .t2) = scanAcc s₀.mem (s₀.gpr .a7) j idx.toNat k
  lane : lo (u.gpr .t6) = laneMask (idx.toNat % 4)
  rp : u.gpr .t0 = s₀.gpr .a7 + BitVec.ofNat 64 (1024 * j + 4 * k)
  keep : Keep lookRegs s₀ u
  mem : u.mem = s₀.mem

theorem row_step {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) (idx : Byte) {k : Nat}
    (hk : k < 64) {u : State} (I : RowInv s₀ j idx k u) :
    WP isa (.block (row j)) u fun u' =>
      RowInv s₀ j idx (k + 1) u' ∧ u'.gpr .t4 = BitVec.ofNat 64 (4 * (k + 1)) - BitVec.ofNat 64 256 := by
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2]
  let rp := s₀.gpr .a7 + BitVec.ofNat 64 (1024 * j + 4 * k)
  have ha : ∀ b < 4, rp + BitVec.ofNat 64 (256 * b) =
      s₀.gpr .a7 + BitVec.ofNat 64 (1024 * j + 256 * b + 4 * k) := fun b _ =>
    Offset.add_add_eq _ (by omega)
  have hr : ∀ b < 4, InRegions (u.rd ++ u.wr) (rp + BitVec.ofNat 64 (256 * b)) 4 :=
    fun b hb => by rw [ha b hb, hrd]; exact E.rd _ (by omega) (by omega)
  have hal : ∀ b < 4, (rp + BitVec.ofNat 64 (256 * b)).toNat % 4 = 0 :=
    fun b hb => by rw [ha b hb]; exact al_add E.al (by omega) (by omega)
  have h7 : u.gpr .a7 = s₀.gpr .a7 := I.keep.gpr (by decide)
  have r0 := hr 0 (by decide)
  have l0 := hal 0 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero] at r0 l0
  refine WP.mono (WP.keep [.t1, .t2, .t3, .t4, .t5, .t0]
    (row_run u hj I.q I.acc I.lane I.rp h7 r0 (hr 1 (by decide)) (hr 2 (by decide)) (hr 3 (by decide))
      l0 (hal 1 (by decide)) (hal 2 (by decide)) (hal 3 (by decide))) (by
      rfl) rfl) fun u' ⟨⟨a2, a1, a0, a4, am⟩, ak⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_, I.keep.trans ak |>.mono (by decide), am.trans I.mem⟩, ?_⟩
  · rw [a1, BitVec.sub_sub, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat]
    congr 2
  · dsimp only at a2
    rw [a2, I.mem]
    have hb : ∀ b < 4, rp + BitVec.ofNat 64 (256 * b) =
        s₀.gpr .a7 + BitVec.ofNat 64 (1024 * j + 256 * b + 4 * k) := ha
    have e0 : rp + 0 = s₀.gpr .a7 + BitVec.ofNat 64 (1024 * j + 256 * 0 + 4 * k) := by
      rw [← hb 0 (by decide)]; rfl
    have e1 := hb 1 (by decide)
    have e2 := hb 2 (by decide)
    have e3 := hb 3 (by decide)
    simp only [Nat.mul_one, show 256 * 2 = 512 from rfl, show 256 * 3 = 768 from rfl] at e1 e2 e3
    rw [e0, show (256#64 : BitVec 64) = BitVec.ofNat 64 256 from rfl, e1,
      show (512#64 : BitVec 64) = BitVec.ofNat 64 512 from rfl, e2,
      show (768#64 : BitVec 64) = BitVec.ofNat 64 768 from rfl, e3]
    refine scanAcc_succ _ _ _ _ _ _ ?_
    by_cases e : idx.toNat / 4 = k
    · rw [ite_eq_left ((row_hit idx hk).mpr e), ite_eq_left e]
    · rw [ite_eq_right (fun h => e ((row_hit idx hk).mp h)), ite_eq_right e]
  · rw [ak.gpr (by decide), I.lane]
  · rw [a0, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]
    congr 2
  · rw [a4, row_end]

theorem rows_run {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) (idx : Byte) {u : State}
    (I : RowInv s₀ j idx 0 u) : WP isa (.loop (.block (row j)) (.nonzero .t4)) u (RowInv s₀ j idx 64) := by
  refine WP.loop (M := isa) (Q := RowInv s₀ j idx 64)
    (fun (n : Nat) (v : State) => ∃ k, k < 64 ∧ n = 64 - k ∧ RowInv s₀ j idx k v) ?_ 64 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨k, hk, hn, J⟩
  refine WP.mono (row_step E hj idx hk J) fun v' ⟨J', hz⟩ => ?_
  rw [Steps.eval_nonzero, hz, ofNat_sub_bne (by omega) (by decide)]
  by_cases e : k + 1 = 64
  · left
    exact ⟨by rw [e]; rfl, e ▸ J'⟩
  · right
    exact ⟨by simp; omega, n - 1, by omega, k + 1, by omega, by omega, J'⟩

/-- The lookup of S-box `j` for the byte `3 - j` of xL's low word. -/
theorem lookup_run {s : State} (E : LookEnv s) {j : Nat} (hj : j < 4) :
    WP isa (lookup j) s fun t =>
      lo (t.gpr .t2) = sEntry (scheduleAt s.mem (s.gpr .a7)) j (quarter (lo (s.gpr .a3)) j) ∧
        Keep lookRegs s t ∧ t.mem = s.mem := by
  let idx := quarter (lo (s.gpr .a3)) j
  unfold lookup
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t1] (index_run s hj) (by rfl) rfl) fun t ⟨⟨t1, tm⟩, tk⟩ => ?_
  have hL : (t.gpr .t1).toNat % 4 = idx.toNat % 4 := by rw [t1, BitVec.toNat_setWidth]; simp [idx]
  refine WP.mono (WP.keep [.t2, .t3, .t4, .t6, .t0] (start_run t hj hL) (by rfl) rfl)
    fun u ⟨⟨u6, u2, u0, um⟩, uk⟩ => ?_
  have K0 : Keep lookRegs s u := (tk.trans uk).mono (by decide)
  have I0 : RowInv s j idx 0 u := by
    refine ⟨?_, by rw [u2, scanAcc_zero]; rfl, u6, ?_, K0, by rw [um]; exact tm⟩
    · rw [uk.gpr (by decide), t1]; simp [idx]
    · rw [u0, tk.gpr (by decide)]; simp
  apply WP.seq
  refine WP.mono (rows_run E hj idx I0) fun v V => ?_
  unfold lookupEnd
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2, .t3, .t4] (condRot_run v .t2 (c := 0) (a := 8) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) (by decide) rfl) fun w ⟨⟨w2, wm⟩, wk⟩ => ?_
  refine WP.mono (WP.keep [.t2, .t3, .t4] (condRot_run w .t2 (c := 1) (a := 16) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) (by decide) rfl)
    fun x ⟨⟨x2, xm⟩, xk⟩ => ?_
  have hL4 : idx.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨b0, b1⟩ := bit01 (v.gpr .t1)
  have hq : (v.gpr .t1).toNat % 4 = idx.toNat % 4 := by
    rw [V.q, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := idx.isLt
    rw [Nat.mod_eq_of_lt (show idx.toNat < 2 ^ 64 by omega)]
    omega
  rw [hq] at b0 b1
  refine ⟨?_, (V.keep.trans wk).trans xk |>.mono (by decide), by rw [xm, wm, V.mem]⟩
  rw [x2, wk.gpr (by decide), w2, b0, b1, acc_rot _ hL4, V.acc, scanAcc_all]
  exact hitWord_ror _ _ hj idx

end VG.Proof.Blowfish.RISCV64
