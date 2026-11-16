module

public import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Step
public import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Absorb
public import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Setup
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
public import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Reduce
public import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Poly1305.AArch64.Buffer
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Poly1305.AArch64.Blocks
public import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Steps
public import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Impl.Poly1305.AArch64.Vector

/-! ### `Poly1305.AArch64.Vector.Finish`, which only this module used -/

section

/-! ### `Poly1305.AArch64.Vector.Loop`, which only this module used -/

section

/-! ### `Poly1305.AArch64.Vector.Init`, which only this module used -/

section

/-! ### `Poly1305.AArch64.Vector.Setup`, which only this module used -/

section

/-!
# Poly1305 on AArch64 in AdvSIMD: the setup

Untrusted: everything here is checked by Lean. The 26-bit limbs of a number in
`x4:x5:x6` (`limbs`), and their insertion into vectors.
-/

@[expose] public section

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Poly1305.Limbs26 (val)
open VG.Spec.Poly1305 (P)
open VG.Proof.Poly1305.AArch64.Radix64 (hval Keeps absorbRegs mul_ok)

/-- Reads of the general-purpose registers through the writes of the steps so far. -/
macro "gstep" : tactic =>
  `(tactic| plain_simp_names simp (disch := decide) only [RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.v_write,
                     RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, State.read, Size.bits,
                     BitVec.setWidth_eq])

/-- The limbs of `w0 + 2⁶⁴ w1 + 2¹²⁸ w2`, as `limbs` computes them. -/
def lim (w0 w1 w2 : Nat) : Nat → Nat
  | 0 => w0 % 2 ^ 26
  | 1 => w0 / 2 ^ 26 % 2 ^ 26
  | 2 => w0 / 2 ^ 52 + w1 % 2 ^ 14 * 2 ^ 12
  | 3 => w1 / 2 ^ 14 % 2 ^ 26
  | _ => w1 / 2 ^ 40 + w2 * 2 ^ 24

theorem lim_val {w0 w1 : Nat} (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64) (w2 : Nat) :
    val (lim w0 w1 w2) = w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 := by
  have := h0; have := h1
  simp only [val, lim]; omega_arith

theorem lim_lt {w0 w1 w2 : Nat} (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64) (h2 : w2 ≤ 4) :
    ∀ i < 5, lim w0 w1 w2 i < 2 ^ 27 := by
  have := h0; have := h1; have := h2
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_arith) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [lim] <;> omega_arith

theorem or_low {a n : Nat} (ha : a < 2 ^ n) (x : Nat) : (a ||| 2 ^ n * x) = a + 2 ^ n * x := by
  rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt ha, Nat.add_comm]

theorem and_mask26 (x : Nat) : (x &&& (2 ^ 26 - 1) % 2 ^ 64) = x % 2 ^ 26 := by
  rw [show (2 ^ 26 - 1) % 2 ^ 64 = 2 ^ 26 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

/-- The limbs of the number in `x4:x5:x6`. -/
abbrev limOf (s : State) : Nat → Nat := lim (s.gpr .x4).toNat (s.gpr .x5).toNat (s.gpr .x6).toNat

/-- The registers `limbs` writes. -/
def limbRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14]

theorem limbs_ok (s : State) (hm : (s.gpr .x16).toNat = 2 ^ 26 - 1) :
    WP isa (.block limbs) s fun t =>
      ((s.gpr .x6).toNat ≤ 4 → ∀ i < 5, (t.gpr (X i)).toNat = limOf s i) ∧ (∀ r ∉ limbRegs, t.gpr r = s.gpr r) ∧
        t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [limbs]
  iterate 12
    refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
    gstep
  refine WP.block_nil_iff.mpr ⟨fun h6 i hi => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have w0 := (s.gpr .x4).isLt; have w1 := (s.gpr .x5).isLt
    obtain hm' : s.gpr .x16 = BitVec.ofNat 64 (2 ^ 26 - 1) := by
      apply BitVec.eq_of_toNat_eq; rw [hm]; rfl
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_arith) with rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [X, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, Size.bits,
        BitVec.setWidth_eq, hm', BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
        BitVec.toNat_or, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, lim] <;>
      try simp only [and_mask26]
    · rw [show (s.gpr .x5).toNat * 2 ^ 12 % 2 ^ 64 = 2 ^ 12 * ((s.gpr .x5).toNat % 2 ^ 52) by omega_arith,
        or_low (by omega_arith)]
      omega_arith
    · rw [show (s.gpr .x6).toNat * 2 ^ 24 % 2 ^ 64 = 2 ^ 24 * (s.gpr .x6).toNat by omega_arith, or_low (by omega_arith)]
      omega_arith
  · simp only [limbRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h10, h11, h12, h13, h14⟩ := hr
    simp (disch := assumption) only [RegUpd.gpr_write_of_ne]
  all_goals rfl

/-! ## Inserting limbs into words -/

theorem exec_ins (s : State) (d : VReg) {j : Nat} (hj : j < 4) (n : Reg) :
    isa.exec (vo (.ins .s4 d j n)) s = some (s.setV d (setLane (s.v d) 32 j ((s.gpr n).setWidth 32))) :=
  exec_vo (by simp only [VOp.eval, hj, ite_true])

theorem wd_ins (v : BitVec 128) {j c : Nat} (hj : j < 4) (hc : c < 4) (x : BitVec 64) :
    wd (setLane v 32 j (x.setWidth 32)) c = if c = j then x.toNat % 2 ^ 32 else wd v c := by
  rw [wd, vword_setLane v hj hc]
  split <;> simp only [BitVec.toNat_setWidth, wd]

/-- What inserting words keeps. -/
structure WKeep (dst : Nat → VReg) (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : ∀ r, (∀ i < 5, r ≠ dst i) → t.v r = s.v r

theorem ins_aux (dst : Nat → VReg) (hd : ∀ i < 5, ∀ k < 5, i ≠ k → dst i ≠ dst k) {j : Nat} (hj : j < 4) :
    ∀ (is : List Nat), (∀ i ∈ is, i < 5) → is.Nodup → ∀ s : State,
      WP isa (.block (is.map fun i => vo (.ins .s4 (dst i) j (X i)))) s fun t =>
        (∀ i ∈ is, ∀ c < 4, wd (t.v (dst i)) c = if c = j then (s.gpr (X i)).toNat % 2 ^ 32 else wd (s.v (dst i)) c) ∧
        (∀ i < 5, i ∉ is → t.v (dst i) = s.v (dst i)) ∧ WKeep dst s t := by
  intro is
  induction is with
  | nil =>
    intro _ _ s
    exact WP.block_nil_iff.mpr ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  | cons k is ih =>
    intro his hnd s
    obtain hk : k < 5 := his k List.mem_cons_self
    obtain his' : ∀ i ∈ is, i < 5 := fun i hi => his i (List.mem_cons_of_mem _ hi)
    obtain ⟨hnk, hnd'⟩ := List.nodup_cons.mp hnd
    refine WP.block_cons_iff.mpr ⟨_, exec_ins s (dst k) hj (X k), ?_⟩
    refine WP.mono (ih his' hnd' _) fun t ⟨hr, hn, hkp⟩ => ⟨?_, ?_, ?_⟩
    · intro i hi c hc
      rcases List.mem_cons.mp hi with rfl | hi'
      · rw [hn i hk hnk, RegUpd.v_setV_self, wd_ins _ hj hc]
      · have hik : i ≠ k := fun h => hnk (h ▸ hi')
        rw [hr i hi' c hc, RegUpd.v_setV_of_ne _ _ (hd i (his' i hi') k hk hik), RegUpd.gpr_setV]
    · intro i hi hin
      obtain hik : i ≠ k := fun h => hin (h ▸ List.mem_cons_self)
      rw [hn i hi (fun h => hin (List.mem_cons_of_mem _ h)), RegUpd.v_setV_of_ne _ _ (hd i hi k hk hik)]
    · exact ⟨hkp.gpr, hkp.mem, hkp.rd, hkp.wr, hkp.sp, fun r hr' => by
        rw [hkp.v r hr', RegUpd.v_setV_of_ne _ _ (hr' k hk)]⟩

theorem insLimbs_ok (dst : Nat → VReg) (hd : ∀ i < 5, ∀ k < 5, i ≠ k → dst i ≠ dst k) {j : Nat} (hj : j < 4)
    (s : State) :
    WP isa (.block (insLimbs dst j)) s fun t =>
      (∀ i < 5, ∀ c < 4, wd (t.v (dst i)) c = if c = j then (s.gpr (X i)).toNat % 2 ^ 32 else wd (s.v (dst i)) c) ∧
        WKeep dst s t :=
  WP.mono (ins_aux dst hd hj (List.range 5) (fun _ h => List.mem_range.mp h) List.nodup_range s)
    fun _ ⟨h, _, k⟩ => ⟨fun i hi => h i (List.mem_range.mpr hi), k⟩

/-! ## The powers of `r` -/

/-- The instruction writes no vector register. -/
def noV (i : Instr) : Bool := (vdstOf i).isNone

/-- Code that writes no vector register keeps them all. -/
theorem WP.keepV {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : c.allInstrs noV = true := by decide +kernel) : WP isa c s fun t => Q t ∧ t.v = s.v := by
  obtain ⟨tr, s', he, hq⟩ := h
  refine ⟨tr, s', he, hq, funext fun r => Exec.vec (fun i hi => ?_) he⟩
  have := List.all_eq_true.mp ((Code.allInstrs_eq noV c) ▸ hc) i hi
  simp only [noV, Option.isNone_iff_eq_none] at this
  rw [this]; intro h; cases h

/-- `r^k` (modulo `p`), in limbs below `2²⁷`. -/
structure Pow (r k : Nat) (L : Nat → Nat) : Prop where
  val : val L % P = r ^ k % P
  lt : ∀ i < 5, L i < 2 ^ 27

theorem mod_mul_pow {x R k : Nat} (h : x % P = R ^ k % P) : x * R % P = R ^ (k + 1) % P := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod, Nat.pow_succ]

theorem rV_inj : ∀ i < 5, ∀ k < 5, i ≠ k → rV i ≠ rV k := by decide
theorem fV_inj : ∀ i < 5, ∀ k < 5, i ≠ k → fV i ≠ fV k := by decide
theorem rV_fV : ∀ i < 5, ∀ k < 5, rV i ≠ fV k := by decide

/-- The limbs inserted: words of a vector. -/
theorem lim_word {s : State} (h6 : (s.gpr .x6).toNat ≤ 4) {i : Nat} (hi : i < 5) :
    limOf s i % 2 ^ 32 = limOf s i :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (lim_lt (s.gpr .x4).isLt (s.gpr .x5).isLt h6 i hi) (by decide))

/-- `x4:x5:x6 ← r`. -/
def rset : List Instr := [.addImm .x .x4 .x7 0, .addImm .x .x5 .x8 0, .movz .x .x6 0 0]

theorem rset_ok (s : State) :
    WP isa (.block rset) s fun t =>
      t.gpr .x4 = s.gpr .x7 ∧ t.gpr .x5 = s.gpr .x8 ∧ (t.gpr .x6).toNat = 0 ∧
      (∀ r ∉ [Reg.x4, .x5, .x6], t.gpr r = s.gpr r) ∧ t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  simp only [rset]
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  gstep
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  gstep
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  gstep
  refine WP.block_nil_iff.mpr ⟨?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · gstep; exact BitVec.add_zero _
  · gstep; exact BitVec.add_zero _
  · gstep; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h4, h5, h6⟩ := hr
    simp (disch := assumption) only [RegUpd.gpr_write_of_ne]

theorem powers_eq : powers = rset ++ (limbs ++ (insLimbs fV 3 ++ (mulKey ++ (limbs ++ (insLimbs rV 2 ++
    (insLimbs rV 3 ++ (insLimbs fV 2 ++ (mulKey ++ (limbs ++ (insLimbs fV 1 ++ (mulKey ++ (limbs ++
    (insLimbs rV 0 ++ (insLimbs rV 1 ++ insLimbs fV 0)))))))))))))) := by
  simp only [powers, rset, List.append_assoc, List.cons_append, List.nil_append]

theorem powers_ok {s : State} {R : Nat} (hk : Radix64.Keys R s) (hm : (s.gpr .x16).toNat = 2 ^ 26 - 1) :
    WP isa (.block powers) s fun t => ∃ L1 L2 L3 L4 : Nat → Nat,
      Pow R 1 L1 ∧ Pow R 2 L2 ∧ Pow R 3 L3 ∧ Pow R 4 L4 ∧
      (∀ i < 5, ∀ c < 4, wd (t.v (rV i)) c = (if c < 2 then L4 else L2) i) ∧
      (∀ i < 5, ∀ c < 4, wd (t.v (fV i)) c =
        (if c = 0 then L4 else if c = 1 then L3 else if c = 2 then L2 else L1) i) ∧
      (∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, (∀ i < 5, r ≠ rV i ∧ r ≠ fV i) → t.v r = s.v r) := by
  obtain ⟨q, hr0, hr1, hq, hs1, hR⟩ := hk
  rw [powers_eq]
  refine WP.block_append (WP.mono (rset_ok s) fun s0 ⟨a4, a5, a6, ag, av, am, ard, awr⟩ => ?_)
  obtain k0 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s0.gpr r = s.gpr r := fun r hr =>
    ag r (by revert hr; decide +revert)
  refine WP.block_append (WP.mono (limbs_ok s0 (by rw [k0 .x16 (by decide)]; exact hm))
    fun s1 ⟨l1, g1, v1, m1, rd1, wr1, _⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok fV fV_inj (by decide) s1) fun s2 ⟨i2, k2⟩ => ?_)
  -- the registers `mul_ok` and `limbs` need, through each state
  obtain g02 : ∀ r ∉ limbRegs, s2.gpr r = s0.gpr r := fun r hr => by rw [congrFun k2.gpr r, g1 r hr]
  obtain key2 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s2.gpr r = s.gpr r := fun r hr => by
    rw [g02 r (by revert hr; decide +revert), k0 r hr]
  obtain h2 : hval s2 = R := by
    simp only [hval]
    rw [g02 .x4 (by decide), g02 .x5 (by decide), g02 .x6 (by decide), a4, a5, a6,
      ← key2 .x7 (by decide), ← key2 .x8 (by decide)] at *
    rw [← hR, key2 .x7 (by decide), key2 .x8 (by decide)]; omega_arith
  obtain x62 : (s2.gpr .x6).toNat = 0 := by rw [g02 .x6 (by decide), a6]
  -- the keys, in any state that keeps them
  obtain keyOf : ∀ u : State, u.gpr .x7 = s.gpr .x7 → u.gpr .x8 = s.gpr .x8 → u.gpr .x17 = s.gpr .x17 →
      (u.gpr .x7).toNat < 2 ^ 60 ∧ (u.gpr .x8).toNat = 4 * q ∧ (u.gpr .x17).toNat = 5 * q ∧
        (u.gpr .x7).toNat + 2 ^ 64 * (u.gpr .x8).toNat = R := fun u e7 e8 e17 => by
    rw [e7, e8, e17]; exact ⟨hr0, hr1, hs1, hR⟩
  -- r²
  obtain ⟨kr0, kr1, ks1, kR⟩ := keyOf s2 (key2 .x7 (by decide)) (key2 .x8 (by decide)) (key2 .x17 (by decide))
  refine WP.block_append (WP.mono (WP.keepV (mul_ok s2 kr0 kr1 hq ks1)) fun s3 ⟨⟨hm3, k3⟩, v3⟩ => ?_)
  obtain ⟨e3, b3⟩ := hm3 (by omega_arith)
  rw [kR, h2] at e3
  obtain key3 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s3.gpr r = s.gpr r := fun r hr => by
    rw [k3.1 r (by revert hr; decide +revert), key2 r hr]
  refine WP.block_append (WP.mono (limbs_ok s3 (by rw [key3 .x16 (by decide)]; exact hm))
    fun s4 ⟨l4, g4, v4, m4, rd4, wr4, _⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok rV rV_inj (by decide) s4) fun s5 ⟨i5, k5⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok rV rV_inj (by decide) s5) fun s6 ⟨i6, k6⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok fV fV_inj (by decide) s6) fun s7 ⟨i7, k7⟩ => ?_)
  obtain g37 : ∀ r ∉ limbRegs, s7.gpr r = s3.gpr r := fun r hr => by
    rw [congrFun k7.gpr r, congrFun k6.gpr r, congrFun k5.gpr r, g4 r hr]
  obtain key7 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s7.gpr r = s.gpr r := fun r hr => by
    rw [g37 r (by revert hr; decide +revert), key3 r hr]
  obtain h7 : hval s7 = hval s3 := by simp only [hval, g37 .x4 (by decide), g37 .x5 (by decide), g37 .x6 (by decide)]
  -- r³
  obtain ⟨kr0, kr1, ks1, kR⟩ := keyOf s7 (key7 .x7 (by decide)) (key7 .x8 (by decide)) (key7 .x17 (by decide))
  refine WP.block_append (WP.mono (WP.keepV (mul_ok s7 kr0 kr1 hq ks1)) fun s8 ⟨⟨hm8, k8⟩, v8⟩ => ?_)
  obtain ⟨e8, b8⟩ := hm8 (by rw [g37 .x6 (by decide)]; omega_arith)
  rw [kR, h7] at e8
  obtain key8 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s8.gpr r = s.gpr r := fun r hr => by
    rw [k8.1 r (by revert hr; decide +revert), key7 r hr]
  refine WP.block_append (WP.mono (limbs_ok s8 (by rw [key8 .x16 (by decide)]; exact hm))
    fun s9 ⟨l9, g9, v9, m9, rd9, wr9, _⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok fV fV_inj (by decide) s9) fun s10 ⟨i10, k10⟩ => ?_)
  obtain g810 : ∀ r ∉ limbRegs, s10.gpr r = s8.gpr r := fun r hr => by rw [congrFun k10.gpr r, g9 r hr]
  obtain key10 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s10.gpr r = s.gpr r := fun r hr => by
    rw [g810 r (by revert hr; decide +revert), key8 r hr]
  obtain h10 : hval s10 = hval s8 := by
    simp only [hval, g810 .x4 (by decide), g810 .x5 (by decide), g810 .x6 (by decide)]
  -- r⁴
  obtain ⟨kr0, kr1, ks1, kR⟩ := keyOf s10 (key10 .x7 (by decide)) (key10 .x8 (by decide)) (key10 .x17 (by decide))
  refine WP.block_append (WP.mono (WP.keepV (mul_ok s10 kr0 kr1 hq ks1)) fun s11 ⟨⟨hm11, k11⟩, v11⟩ => ?_)
  obtain ⟨e11, b11⟩ := hm11 (by rw [g810 .x6 (by decide)]; omega_arith)
  rw [kR, h10] at e11
  obtain key11 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s11.gpr r = s.gpr r := fun r hr => by
    rw [k11.1 r (by revert hr; decide +revert), key10 r hr]
  refine WP.block_append (WP.mono (limbs_ok s11 (by rw [key11 .x16 (by decide)]; exact hm))
    fun s12 ⟨l12, g12, v12, m12, rd12, wr12, _⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok rV rV_inj (by decide) s12) fun s13 ⟨i13, k13⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok rV rV_inj (by decide) s13) fun s14 ⟨i14, k14⟩ => ?_)
  refine WP.mono (insLimbs_ok fV fV_inj (by decide) s14) fun t ⟨it, kt⟩ => ?_
  obtain b0 : (s0.gpr .x6).toNat ≤ 4 := by omega_arith
  obtain lv : ∀ u : State, val (limOf u) = hval u := fun u => lim_val (u.gpr .x4).isLt (u.gpr .x5).isLt _
  obtain h0 : hval s0 = R := by
    show (s0.gpr .x4).toNat + 2 ^ 64 * (s0.gpr .x5).toNat + 2 ^ 128 * (s0.gpr .x6).toNat = R
    rw [a4, a5, a6]; omega_arith
  -- the limbs' registers at each insertion
  obtain x1 : ∀ i < 5, (s1.gpr (X i)).toNat % 2 ^ 32 = limOf s0 i := fun i hi => by rw [l1 b0 i hi, lim_word b0 hi]
  obtain x4' : ∀ i < 5, (s4.gpr (X i)).toNat % 2 ^ 32 = limOf s3 i := fun i hi => by rw [l4 b3 i hi, lim_word b3 hi]
  obtain x5 : ∀ i < 5, (s5.gpr (X i)).toNat % 2 ^ 32 = limOf s3 i := fun i hi => by rw [k5.gpr]; exact x4' i hi
  obtain x6' : ∀ i < 5, (s6.gpr (X i)).toNat % 2 ^ 32 = limOf s3 i := fun i hi => by rw [k6.gpr]; exact x5 i hi
  obtain x9 : ∀ i < 5, (s9.gpr (X i)).toNat % 2 ^ 32 = limOf s8 i := fun i hi => by rw [l9 b8 i hi, lim_word b8 hi]
  obtain x12 : ∀ i < 5, (s12.gpr (X i)).toNat % 2 ^ 32 = limOf s11 i := fun i hi => by rw [l12 b11 i hi, lim_word b11 hi]
  obtain x13 : ∀ i < 5, (s13.gpr (X i)).toNat % 2 ^ 32 = limOf s11 i := fun i hi => by rw [k13.gpr]; exact x12 i hi
  obtain x14 : ∀ i < 5, (s14.gpr (X i)).toNat % 2 ^ 32 = limOf s11 i := fun i hi => by rw [k14.gpr]; exact x13 i hi
  have rf : ∀ i < 5, ∀ j < 5, rV i ≠ fV j := rV_fV
  obtain fr : ∀ i < 5, ∀ j < 5, fV i ≠ rV j := fun i hi j hj => (rV_fV j hj i hi).symm
  refine ⟨limOf s0, limOf s3, limOf s8, limOf s11, ⟨?_, lim_lt (s0.gpr .x4).isLt (s0.gpr .x5).isLt b0⟩,
    ⟨?_, lim_lt (s3.gpr .x4).isLt (s3.gpr .x5).isLt b3⟩, ⟨?_, lim_lt (s8.gpr .x4).isLt (s8.gpr .x5).isLt b8⟩,
    ⟨?_, lim_lt (s11.gpr .x4).isLt (s11.gpr .x5).isLt b11⟩, fun i hi c hc => ?_, fun i hi c hc => ?_,
    ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [lv, h0, Nat.pow_one]
  · rw [lv, e3, Nat.pow_two]
  · rw [lv, e8]; exact mod_mul_pow (k := 2) (by rw [e3, Nat.pow_two])
  · rw [lv, e11]; exact mod_mul_pow (k := 3) (by rw [e8]; exact mod_mul_pow (k := 2) (by rw [e3, Nat.pow_two]))
  · -- the words of `R`
    rw [kt.v _ fun j hj => rf i hi j hj, i14 i hi c hc, x13 i hi, i13 i hi c hc, x12 i hi,
      congrFun v12 (rV i), congrFun v11 (rV i), k10.v _ fun j hj => rf i hi j hj, congrFun v9 (rV i),
      congrFun v8 (rV i), k7.v _ fun j hj => rf i hi j hj, i6 i hi c hc, x5 i hi, i5 i hi c hc, x4' i hi]
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> rfl
  · -- the words of the last group's multipliers
    rw [it i hi c hc, x14 i hi, k14.v _ fun j hj => fr i hi j hj, k13.v _ fun j hj => fr i hi j hj,
      congrFun v12 (fV i), congrFun v11 (fV i), i10 i hi c hc, x9 i hi, congrFun v9 (fV i), congrFun v8 (fV i),
      i7 i hi c hc, x6' i hi, k6.v _ fun j hj => fr i hi j hj, k5.v _ fun j hj => fr i hi j hj,
      congrFun v4 (fV i), congrFun v3 (fV i), i2 i hi c hc, x1 i hi]
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> rfl
  · intro r hr
    rw [congrFun kt.gpr r, congrFun k14.gpr r, congrFun k13.gpr r, g12 r (by revert hr; decide +revert),
      key11 r hr]
  · rw [kt.mem, k14.mem, k13.mem, m12, k11.2.1, k10.mem, m9, k8.2.1, k7.mem, k6.mem, k5.mem, m4, k3.2.1,
      k2.mem, m1, am]
  · rw [kt.rd, k14.rd, k13.rd, rd12, k11.2.2.1, k10.rd, rd9, k8.2.2.1, k7.rd, k6.rd, k5.rd, rd4, k3.2.2.1,
      k2.rd, rd1, ard]
  · rw [kt.wr, k14.wr, k13.wr, wr12, k11.2.2.2, k10.wr, wr9, k8.2.2.2, k7.wr, k6.wr, k5.wr, wr4, k3.2.2.2,
      k2.wr, wr1, awr]
  · have nr : ∀ j < 5, r ≠ rV j := fun j hj => (hr j hj).1
    obtain nf : ∀ j < 5, r ≠ fV j := fun j hj => (hr j hj).2
    rw [kt.v r nf, k14.v r nr, k13.v r nr, congrFun v12 r, congrFun v11 r, k10.v r nf, congrFun v9 r,
      congrFun v8 r, k7.v r nf, k6.v r nr, k5.v r nr, congrFun v4 r, congrFun v3 r, k2.v r nf,
      congrFun v1 r, congrFun av r]

end VG.Proof.Poly1305.AArch64.Vector

end

end


/-!
# Poly1305 on AArch64 in AdvSIMD: saving registers, the accumulator, the constants

Untrusted: everything here is checked by Lean. `save` stores the low halves of
`v8`–`v14` in the state's working space (bytes 72–127) and `restore` loads
them back; `loadH` puts the accumulator's limbs in lane 0 of `H` (lane 1
zero); `times5 R S` makes `S j` five times `R j`.
-/

@[expose] public section

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Poly1305.Limbs26 (val)

/-! ## `5 R` -/

theorem times5_aux (R S : Nat → VReg) (hRS : ∀ i < 5, 1 ≤ i → ∀ j < 5, 1 ≤ j → R i ≠ S j)
    (hS : ∀ i < 5, 1 ≤ i → ∀ j < 5, 1 ≤ j → i ≠ j → S i ≠ S j) :
    ∀ (js : List Nat), (∀ j ∈ js, 1 ≤ j ∧ j < 5) → js.Nodup → ∀ s : State,
      (∀ j ∈ js, ∀ c < 4, wd (s.v (R j)) c < 2 ^ 29) →
      WP isa (.block (js.flatMap fun j =>
          [vo (.shift .shl .s4 (S j) (R j) 2), vo (.add .s4 (S j) (S j) (R j))])) s fun t =>
        (∀ j ∈ js, ∀ c < 4, wd (t.v (S j)) c = 5 * wd (s.v (R j)) c) ∧
        (∀ r, (∀ j ∈ js, r ≠ S j) → t.v r = s.v r) ∧
        t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  intro js
  induction js with
  | nil =>
    intro _ _ s _
    exact WP.block_nil_iff.mpr ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons j js ih =>
    intro hjs hnd s hb
    obtain ⟨hj1, hj5⟩ := hjs j List.mem_cons_self
    obtain hjs' : ∀ k ∈ js, 1 ≤ k ∧ k < 5 := fun k hk => hjs k (List.mem_cons_of_mem _ hk)
    obtain ⟨hnj, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
    obtain nRS := hRS j hj5 hj1 j hj5 hj1
    rw [RegUpd.v_setV_self, RegUpd.v_setV_of_ne _ _ nRS]
    set u := (s.setV (S j) (VArr.s4.map2 (fun w x y => VShiftOp.shl.eval 2 w x y) (s.v (S j)) (s.v (R j)))).setV
      (S j) (VArr.s4.map2 (fun _ a b => a + b)
        (VArr.s4.map2 (fun w x y => VShiftOp.shl.eval 2 w x y) (s.v (S j)) (s.v (R j))) (s.v (R j))) with hu
    obtain uR : ∀ k ∈ js, u.v (R k) = s.v (R k) := fun k hk => by
      obtain hk := hjs' k hk
      rw [hu, RegUpd.v_setV_of_ne _ _ (hRS k hk.2 hk.1 j hj5 hj1),
        RegUpd.v_setV_of_ne _ _ (hRS k hk.2 hk.1 j hj5 hj1)]
    refine WP.mono (ih hjs' hnd' u fun k hk c hc => by rw [uR k hk]; exact hb k (List.mem_cons_of_mem _ hk) c hc)
      fun t ⟨h5, hv, hg, hm, hrd, hwr, hsp⟩ => ⟨fun k hk c hc => ?_, fun r hr => ?_, hg, hm, hrd, hwr, hsp⟩
    · rcases List.mem_cons.mp hk with rfl | hk'
      · rw [hv _ fun l hl => hS k hj5 hj1 l (hjs' l hl).2 (hjs' l hl).1 fun h => hnj (h ▸ hl), hu,
          RegUpd.v_setV_self]
        exact wd_times5 _ _ hc (hb k List.mem_cons_self c hc)
      · rw [h5 k hk' c hc, uR k hk']
    · rw [hv r fun l hl => hr l (List.mem_cons_of_mem _ hl), hu,
        RegUpd.v_setV_of_ne _ _ (hr j List.mem_cons_self), RegUpd.v_setV_of_ne _ _ (hr j List.mem_cons_self)]

theorem times5_ok (R S : Nat → VReg) (hRS : ∀ i < 5, 1 ≤ i → ∀ j < 5, 1 ≤ j → R i ≠ S j)
    (hS : ∀ i < 5, 1 ≤ i → ∀ j < 5, 1 ≤ j → i ≠ j → S i ≠ S j) (s : State)
    (hb : ∀ j < 5, 1 ≤ j → ∀ c < 4, wd (s.v (R j)) c < 2 ^ 29) :
    WP isa (.block (times5 R S)) s fun t =>
      (∀ j < 5, 1 ≤ j → ∀ c < 4, wd (t.v (S j)) c = 5 * wd (s.v (R j)) c) ∧
      (∀ r, (∀ j < 5, 1 ≤ j → r ≠ S j) → t.v r = s.v r) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain hmem : ∀ j, j ∈ [1, 2, 3, 4] ↔ 1 ≤ j ∧ j < 5 := by
    intro j; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega_using []
  refine WP.mono (times5_aux R S hRS hS [1, 2, 3, 4] (fun j hj => (hmem j).mp hj) (by decide) s
    fun j hj => hb j ((hmem j).mp hj).2 ((hmem j).mp hj).1)
    fun t ⟨h5, hv, hk⟩ => ⟨fun j hj h1 => h5 j ((hmem j).mpr ⟨h1, hj⟩),
      fun r hr => hv r fun j hj => hr j ((hmem j).mp hj).2 ((hmem j).mp hj).1, hk⟩

/-! ## Saving and restoring `v8`–`v14` -/

/-- The slot of `v(8 + k)`. -/
abbrev svA (st : Addr) (k : Nat) : Addr := st + BitVec.ofNat 64 (72 + 8 * k)

/-- The slots. -/
abbrev svR (st : Addr) : Region := ⟨st + BitVec.ofNat 64 72, 56⟩

theorem readW_write8 (m : Mem) (a : Addr) (v : BitVec 64) : (m.write a 8 v).readW a 64 = v := by
  have := Mem.readW_writeW_self m a 8 v (by decide)
  simpa only [Mem.writeW, BitVec.setWidth_eq] using this

theorem readW_write8_sep {m : Mem} {a b : Addr} (h : Mem.Sep a 8 b 8) (v : BitVec (8 * 8)) :
    (m.write b 8 v).readW a 64 = m.readW a 64 := by
  simp only [Mem.readW]
  rw [Mem.read_write_sep h (by decide)]

theorem svA_sep (st : Addr) {j k : Nat} (hj : j < 7) (hk : k < 7) (h : j ≠ k) :
    Mem.Sep (svA st j) 8 (svA st k) 8 := Offset.sep st (by omega_using [h]) (by omega_using [hj]) (by omega_using [hk])

theorem svA_in (st : Addr) {k : Nat} (hk : k < 7) : (svR st).Contains (svA st k) 8 :=
  Offset.contains st (by omega_using []) (by omega_using [hk]) (by omega_using [])

theorem save_aux (st : Addr) :
    ∀ (ks : List Nat), (∀ k ∈ ks, k < 7) → ks.Nodup → ∀ s : State, s.gpr .x0 = st →
      (∀ k ∈ ks, InRegions s.wr (svA st k) 8) →
      WP isa (.block (ks.flatMap fun k => [.umov .x .x9 (V (8 + k)) 0, .str .x .x9 .x0 (72 + 8 * k)])) s
        fun t => (∀ k ∈ ks, t.mem.readW (svA st k) 64 = vdword (s.v (V (8 + k))) 0) ∧
          (∀ k < 7, k ∉ ks → t.mem.readW (svA st k) 64 = s.mem.readW (svA st k) 64) ∧
          Frame [svR st] s.mem t.mem ∧ (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.v = s.v ∧
          t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  intro ks
  induction ks with
  | nil =>
    intro _ _ s _ _
    exact WP.block_nil_iff.mpr ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl, Frame.refl _ _,
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons k ks ih =>
    intro hks hnd s hx0 hw
    obtain hk : k < 7 := hks k List.mem_cons_self
    obtain hks' : ∀ j ∈ ks, j < 7 := fun j hj => hks j (List.mem_cons_of_mem _ hj)
    obtain ⟨hnk, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    refine WP.block_cons_iff.mpr ⟨_, exec_umov s .x9 (V (8 + k)) (by decide), ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_str ⟨by omega_using [], by omega_using [hk]⟩ (by
      simp only [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ _ (show ¬ Reg.x0 = Reg.x9 by decide), hx0]
      exact hw k List.mem_cons_self), ?_⟩
    simp only [RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ _ (show ¬ Reg.x0 = Reg.x9 by decide), hx0,
      RegUpd.mem_write, Size.bits, BitVec.setWidth_eq]
    set u : State := { s.write .x .x9 (vdword (s.v (V (8 + k))) 0) with
      mem := s.mem.write (svA st k) 8 (vdword (s.v (V (8 + k))) 0) } with hu
    obtain ux0 : u.gpr .x0 = st := by
      show (s.write .x .x9 (vdword (s.v (V (8 + k))) 0)).gpr .x0 = st
      rw [RegUpd.gpr_write_of_ne _ _ _ (show ¬ Reg.x0 = Reg.x9 by decide)]; exact hx0
    refine WP.mono (ih hks' hnd' u ux0 fun j hj => hw j (List.mem_cons_of_mem _ hj))
      fun t ⟨hs, hn, hf, hg, hv, hrd, hwr, hsp⟩ => ⟨fun j hj => ?_, fun j hj hjn => ?_, ?_, fun r hr => ?_,
        hv, hrd, hwr, hsp⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · rw [hn j hk hnk, hu]; exact readW_write8 _ _ _
      · rw [hs j hj', hu]; rfl
    · have hjk : j ≠ k := fun h => hjn (h ▸ List.mem_cons_self)
      rw [hn j hj (fun h => hjn (List.mem_cons_of_mem _ h)), hu]
      exact readW_write8_sep (svA_sep st hj hk hjk) _
    · exact ((Frame.refl _ _).write List.mem_cons_self _ (svA_in st hk)).trans hf
    · rw [hg r hr]
      show (s.write .x .x9 (vdword (s.v (V (8 + k))) 0)).gpr r = s.gpr r
      exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem save_ok (s : State) (hw : ∀ k < 7, InRegions s.wr (svA (s.gpr .x0) k) 8) :
    WP isa (.block save) s fun t =>
      (∀ k < 7, t.mem.readW (svA (s.gpr .x0) k) 64 = vdword (s.v (V (8 + k))) 0) ∧
      Frame [svR (s.gpr .x0)] s.mem t.mem ∧ (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.v = s.v ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp :=
  WP.mono (save_aux (s.gpr .x0) (List.range 7) (fun _ h => List.mem_range.mp h) List.nodup_range s rfl
    fun k hk => hw k (List.mem_range.mp hk))
    fun _ ⟨h, _, k⟩ => ⟨fun k hk => h k (List.mem_range.mpr hk), k⟩

theorem V8_ne : ∀ j < 7, ∀ k < 7, j ≠ k → V (8 + j) ≠ V (8 + k) := by decide

theorem restore_aux (st : Addr) :
    ∀ (ks : List Nat), (∀ k ∈ ks, k < 7) → ks.Nodup → ∀ s : State, s.gpr .x0 = st →
      (∀ k ∈ ks, InRegions (s.rd ++ s.wr) (svA st k) 8) →
      WP isa (.block (ks.flatMap fun k => [.ldr .x .x9 .x0 (72 + 8 * k), vo (.ins .d2 (V (8 + k)) 0 .x9)])) s
        fun t => (∀ k ∈ ks, vdword (t.v (V (8 + k))) 0 = s.mem.readW (svA st k) 64) ∧
          (∀ r, (∀ k ∈ ks, r ≠ V (8 + k)) → t.v r = s.v r) ∧ (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧
          t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  intro ks
  induction ks with
  | nil =>
    intro _ _ s _ _
    exact WP.block_nil_iff.mpr ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, fun _ _ => rfl,
      rfl, rfl, rfl, rfl⟩
  | cons k ks ih =>
    intro hks hnd s hx0 hr
    obtain hk : k < 7 := hks k List.mem_cons_self
    obtain hks' : ∀ j ∈ ks, j < 7 := fun j hj => hks j (List.mem_cons_of_mem _ hj)
    obtain ⟨hnk, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    refine WP.block_cons_iff.mpr ⟨_, exec_ldr ⟨by omega_using [], by omega_using [hk]⟩ (by rw [hx0]; exact hr k List.mem_cons_self), ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
    set u := (s.write .x .x9 (s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (72 + 8 * k)) 8)).setV (V (8 + k))
      (setLane ((s.write .x .x9 (s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (72 + 8 * k)) 8)).v (V (8 + k))) 64 0
        ((s.write .x .x9 (s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (72 + 8 * k)) 8)).gpr .x9)) with hu
    obtain ug : ∀ r, r ≠ .x9 → u.gpr r = s.gpr r := fun r hr => by
      rw [hu, RegUpd.gpr_setV]; exact RegUpd.gpr_write_of_ne _ _ _ hr
    have um : u.mem = s.mem := rfl
    refine WP.mono (ih hks' hnd' u (by rw [ug _ (by decide)]; exact hx0) fun j hj => by
        rw [show u.rd = s.rd from rfl, show u.wr = s.wr from rfl]; exact hr j (List.mem_cons_of_mem _ hj))
      fun t ⟨hs, hv, hg, hm, hrd, hwr, hsp⟩ => ⟨fun j hj => ?_, fun r hr' => ?_, fun r hr' => ?_,
        hm.trans um, hrd, hwr, hsp⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · rw [hv _ fun l hl => V8_ne j hk l (hks' l hl) fun h => hnk (h ▸ hl), hu, RegUpd.v_setV_self,
          vdword_setLane _ (by decide) (by decide), ite_eq_left (rfl : 0 = 0), RegUpd.gpr_write_self, hx0]
        rfl
      · rw [hs j hj', um]
    · rw [hv r fun l hl => hr' l (List.mem_cons_of_mem _ hl), hu,
        RegUpd.v_setV_of_ne _ _ (hr' k List.mem_cons_self)]
      rfl
    · rw [hg r hr', ug r hr']

theorem restore_ok (s : State) (hr : ∀ k < 7, InRegions (s.rd ++ s.wr) (svA (s.gpr .x0) k) 8) :
    WP isa (.block restore) s fun t =>
      (∀ k < 7, vdword (t.v (V (8 + k))) 0 = s.mem.readW (svA (s.gpr .x0) k) 64) ∧
      (∀ r, (∀ k < 7, r ≠ V (8 + k)) → t.v r = s.v r) ∧ (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp :=
  WP.mono (restore_aux (s.gpr .x0) (List.range 7) (fun _ h => List.mem_range.mp h) List.nodup_range s rfl
    fun k hk => hr k (List.mem_range.mp hk))
    fun _ ⟨h, hv, k⟩ => ⟨fun k hk => h k (List.mem_range.mpr hk),
      fun r hr => hv r fun k hk => hr k (List.mem_range.mp hk), k⟩

/-! ## The accumulator into the vectors -/

theorem loadH_ok (s : State) (hm : (s.gpr .x16).toNat = 2 ^ 26 - 1) :
    WP isa (.block loadH) s fun t =>
      ((s.gpr .x6).toNat ≤ 4 → ∀ i < 5, ln (t.v (hV i)) 0 = limOf s i) ∧ (∀ i < 5, ln (t.v (hV i)) 1 = 0) ∧
      (∀ r, (∀ i < 5, r ≠ hV i) → t.v r = s.v r) ∧ (∀ r ∉ limbRegs, t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [loadH]
  refine WP.block_append (WP.mono (limbs_ok s hm) fun s1 ⟨l1, g1, v1, m1, rd1, wr1, sp1⟩ => ?_)
  simp only [List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil]
  iterate 10
    refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
    vstep
  refine WP.block_nil_iff.mpr ⟨fun h6 i hi => ?_, fun i hi => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← l1 h6 i hi]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl <;>
      vstep <;> simp only [ln, vdword_setLane _ (show 0 < 2 by decide) (show 0 < 2 by decide), ite_true, X,
        RegUpd.gpr_setV]
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl <;>
      vstep <;> simp only [ln, vdword_setLane _ (show 0 < 2 by decide) (show 1 < 2 by decide),
        show (1 : Nat) ≠ 0 by decide, ite_false] <;> rfl
  · have := hr 0 (by decide); have := hr 1 (by decide); have := hr 2 (by decide)
    have := hr 3 (by decide); have := hr 4 (by decide)
    simp (disch := assumption) only [RegUpd.v_setV_of_ne]
    exact congrFun v1 r
  · intro r hr; simp only [RegUpd.gpr_setV]; exact g1 r hr
  · simp only [RegUpd.mem_setV]; exact m1
  · simp only [RegUpd.rd_setV]; exact rd1
  · simp only [RegUpd.wr_setV]; exact wr1
  · simp only [RegUpd.sp_setV]; exact sp1

/-! ## The constants and the count -/

/-- Reads of every register through the writes so far. -/
macro "allstep" : tactic =>
  `(tactic| plain_simp_names simp (disch := first | decide | with_reducible assumption) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne,
                     RegUpd.gpr_setV, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.v_write, State.read, Size.bits,
                     BitVec.setWidth_eq])

/-- The end of `setup`. -/
def tail : List Instr :=
  [vo (.dup .d2 maskV .x16), .movz .x .x9 0x100 1, vo (.dup .d2 padV .x9), .lsr .x .x9 .x3 6, .subImm .x .x9 .x9 1]

theorem tail_ok (s : State) :
    WP isa (.block tail) s fun t =>
      (∀ e < 2, ln (t.v maskV) e = (s.gpr .x16).toNat) ∧ (∀ e < 2, ln (t.v padV) e = 2 ^ 24) ∧
      t.gpr .x9 = (s.gpr .x3 >>> 6) - 1 ∧ (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧
      (∀ r, r ≠ maskV → r ≠ padV → t.v r = s.v r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [tail]
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_nil_iff.mpr ⟨fun e he => ?_, fun e he => ?_, ?_, fun r hr => ?_, fun r h1 h2 => ?_,
    rfl, rfl, rfl, rfl⟩
  · allstep
    rcases (show e = 0 ∨ e = 1 by omega_using [he]) with rfl | rfl
    · simp only [ln, vdword_ofVDwords_0]
    · simp only [ln, vdword_ofVDwords_1]
  · allstep
    rcases (show e = 0 ∨ e = 1 by omega_using [he]) with rfl | rfl
    · simp only [ln, vdword_ofVDwords_0]; rfl
    · simp only [ln, vdword_ofVDwords_1]; rfl
  · allstep; rfl
  · allstep
  · allstep

end VG.Proof.Poly1305.AArch64.Vector

end

end


/-!
# Poly1305 on AArch64 in AdvSIMD: the setup and the loop

Untrusted: everything here is checked by Lean. After `setup` and each group of
the loop, `LInv` holds: the registers and the memory `vec` keeps, the
multipliers (`[r⁴, r⁴, r², r²]` in `R`, `[r⁴, r³, r², r]` in the last group's),
the constants, and (if the accumulator on entry is below `2¹³⁰ + 2¹²⁹`, as
`Radix64` keeps it) the lanes `A`, `B` with `A r + B ≡ r a` for the
accumulator `a` of the blocks so far.
-/

@[expose] public section

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Poly1305.Limbs26 (val)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305.AArch64.Radix64 (hval)

/-- The multipliers' limbs: `yL c` is `r⁴` (words 0, 1) or `r²` (words 2, 3), `yF c` is `r^(4-c)`. -/
structure Ys (R : Nat) (yL yF : Nat → Nat → Nat) : Prop where
  ltL : ∀ c < 4, ∀ i < 5, yL c i < 2 ^ 27
  ltF : ∀ c < 4, ∀ i < 5, yF c i < 2 ^ 27
  valL : ∀ c < 4, val (yL c) % P = R ^ (if c < 2 then 4 else 2) % P
  valF : ∀ c < 4, val (yF c) % P = R ^ (4 - c) % P

/-- The slots of the low halves of `v8`–`v14` in `M`, which is `m` elsewhere. -/
structure Saved (s₀ : State) (M : Mem) : Prop where
  slots : ∀ k < 7, M.readW (svA (s₀.gpr .x0) k) 64 = vdword (s₀.v (V (8 + k))) 0
  frame : Frame [svR (s₀.gpr .x0)] s₀.mem M

/-- The number of groups. -/
abbrev nq (s₀ : State) : Nat := (s₀.gpr .x3).toNat / 64

/-- After `j` groups. -/
structure LInv (s₀ : State) (R : Nat) (M : Mem) (yL yF : Nat → Nat → Nat) (j : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0
  x2 : s.gpr .x2 = s₀.gpr .x2 + BitVec.ofNat 64 (64 * j)
  x3 : s.gpr .x3 = s₀.gpr .x3
  x9 : s.gpr .x9 = BitVec.ofNat 64 (nq s₀ - 1 - j)
  x7 : s.gpr .x7 = s₀.gpr .x7
  x8 : s.gpr .x8 = s₀.gpr .x8
  x17 : s.gpr .x17 = s₀.gpr .x17
  mem : s.mem = M
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mul : Mults s rV sV yL
  fw : ∀ i < 5, ∀ c < 4, wd (s.v (fV i)) c = yF c i
  mask : ∀ e < 2, ln (s.v maskV) e = 2 ^ 26 - 1
  pad : ∀ e < 2, ln (s.v padV) e = 2 ^ 24
  v15 : s.v .v15 = s₀.v .v15
  acc : (s₀.gpr .x6).toNat ≤ 4 → (∀ e < 2, ∀ i < 5, hl s e i < 2 ^ 27) ∧
    val (hl s 0) * R + val (hl s 1) ≡ R * absorbAll R (hval s₀) (bytesAt M (s₀.gpr .x2) (64 * j)) [MOD P]

/-! ## The setup -/

theorem mask_ok (s : State) :
    WP isa (.block Impl.Poly1305.AArch64.Vector.mask) s fun t =>
      (t.gpr .x16).toNat = 2 ^ 26 - 1 ∧ (∀ r, r ≠ .x16 → t.gpr r = s.gpr r) ∧ t.v = s.v ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [Impl.Poly1305.AArch64.Vector.mask]
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_nil_iff.mpr ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · allstep; rfl
  · allstep

theorem setup_eq : setup = Impl.Poly1305.AArch64.Vector.mask ++ (save ++ (loadH ++ (powers ++
    (times5 rV sV ++ tail)))) := by
  simp only [setup, tail, List.append_assoc]

theorem rV_sV : ∀ i < 5, 1 ≤ i → ∀ j < 5, 1 ≤ j → rV i ≠ sV j := by decide
theorem sV_inj : ∀ i < 5, 1 ≤ i → ∀ j < 5, 1 ≤ j → i ≠ j → sV i ≠ sV j := by
  intro i hi h1 j hj h2 hij
  rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_arith) with rfl | rfl | rfl | rfl <;>
    rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega_arith) with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hij | decide

theorem setup_ok {s₀ : State} {R : Nat} (hk : Radix64.Keys R s₀) (hn : 128 ≤ (s₀.gpr .x3).toNat)
    (hw : ∀ k < 7, InRegions s₀.wr (svA (s₀.gpr .x0) k) 8) :
    WP isa (.block setup) s₀ fun t => ∃ yL yF M, Ys R yL yF ∧ Saved s₀ M ∧ LInv s₀ R M yL yF 0 t := by
  rw [setup_eq]
  refine WP.block_append (WP.mono (mask_ok s₀) fun s1 ⟨m1, g1, v1, mm1, rd1, wr1, _⟩ => ?_)
  refine WP.block_append (WP.mono (save_ok s1 fun k hk => by
      rw [g1 .x0 (by decide), wr1]; exact hw k hk) fun s2 ⟨sl2, f2, g2, v2, rd2, wr2, _⟩ => ?_)
  refine WP.block_append (WP.mono (loadH_ok s2 (by rw [g2 .x16 (by decide)]; exact m1))
    fun s3 ⟨h3, z3, v3, g3, m3, rd3, wr3, _⟩ => ?_)
  refine WP.block_append (WP.mono (powers_ok (s := s3) (R := R) ?keys (by
      rw [g3 .x16 (by decide), g2 .x16 (by decide)]; exact m1))
    fun s4 ⟨L1, L2, L3, L4, p1, p2, p3, p4, w4r, w4f, g4, m4, rd4, wr4, v4⟩ => ?_)
  case keys =>
    obtain ⟨q, a, b, c, d, e⟩ := hk
    obtain e7 : s3.gpr .x7 = s₀.gpr .x7 := by rw [g3 .x7 (by decide), g2 .x7 (by decide), g1 .x7 (by decide)]
    obtain e8 : s3.gpr .x8 = s₀.gpr .x8 := by rw [g3 .x8 (by decide), g2 .x8 (by decide), g1 .x8 (by decide)]
    obtain e17 : s3.gpr .x17 = s₀.gpr .x17 := by
      rw [g3 .x17 (by decide), g2 .x17 (by decide), g1 .x17 (by decide)]
    exact ⟨q, by rw [e7]; exact a, by rw [e8]; exact b, c, by rw [e17]; exact d, by rw [e7, e8]; exact e⟩
  refine WP.block_append (WP.mono (times5_ok rV sV rV_sV sV_inj s4 fun j hj _ c hc => by
      rw [w4r j hj c hc]; split
      · exact Nat.lt_trans (p4.lt j hj) (by decide)
      · exact Nat.lt_trans (p2.lt j hj) (by decide))
    fun s5 ⟨t5, v5, g5, m5, rd5, wr5, _⟩ => ?_)
  refine WP.mono (tail_ok s5) fun t ⟨tm, tp, t9, tg, tv, tmm, trd, twr, _⟩ => ?_
  -- the general-purpose registers
  obtain gs : ∀ r ∈ [Reg.x0, .x2, .x3, .x7, .x8, .x17, .x4, .x5, .x6], s3.gpr r = s₀.gpr r := fun r hr => by
    rw [g3 r (by revert hr; decide +revert), g2 r (by revert hr; decide +revert),
      g1 r (by revert hr; decide +revert)]
  obtain gt : ∀ r ∈ [Reg.x0, .x2, .x3, .x7, .x8, .x17], t.gpr r = s₀.gpr r := fun r hr => by
    rw [tg r (by revert hr; decide +revert), congrFun g5 r, g4 r (by revert hr; decide +revert),
      gs r (by revert hr; decide +revert)]
  -- the vectors kept since `s3` (all but the multipliers, `5 R` and the constants)
  obtain vt : ∀ r, (∀ i < 5, r ≠ rV i ∧ r ≠ fV i) → (∀ j < 5, 1 ≤ j → r ≠ sV j) → r ≠ maskV → r ≠ padV →
      t.v r = s3.v r := fun r h1 h2 h3 h4 => by rw [tv r h3 h4, v5 r h2, v4 r h1]
  obtain hvt : ∀ i < 5, t.v (hV i) = s3.v (hV i) := fun i hi => vt _
    (fun j hj => (show ∀ i < 5, ∀ j < 5, hV i ≠ rV j ∧ hV i ≠ fV j by decide) i hi j hj)
    (fun j hj h1 => (show ∀ i < 5, ∀ j < 5, 1 ≤ j → hV i ≠ sV j by decide) i hi j hj h1)
    ((show ∀ i < 5, hV i ≠ maskV by decide) i hi) ((show ∀ i < 5, hV i ≠ padV by decide) i hi)
  obtain hrt : ∀ i < 5, t.v (rV i) = s4.v (rV i) := fun i hi => by
    rw [tv _ ((show ∀ i < 5, rV i ≠ maskV by decide) i hi) ((show ∀ i < 5, rV i ≠ padV by decide) i hi),
      v5 _ fun j hj h1 => (show ∀ i < 5, ∀ j < 5, 1 ≤ j → rV i ≠ sV j by decide) i hi j hj h1]
  obtain hft : ∀ i < 5, t.v (fV i) = s4.v (fV i) := fun i hi => by
    rw [tv _ ((show ∀ i < 5, fV i ≠ maskV by decide) i hi) ((show ∀ i < 5, fV i ≠ padV by decide) i hi),
      v5 _ fun j hj h1 => (show ∀ i < 5, ∀ j < 5, 1 ≤ j → fV i ≠ sV j by decide) i hi j hj h1]
  obtain hst : ∀ j < 5, 1 ≤ j → t.v (sV j) = s5.v (sV j) := fun j hj h1 =>
    tv _ ((show ∀ j < 5, 1 ≤ j → sV j ≠ maskV by decide) j hj h1)
      ((show ∀ j < 5, 1 ≤ j → sV j ≠ padV by decide) j hj h1)
  obtain yL_def : ∀ c < 4, ∀ i < 5, (fun c i => (if c < 2 then L4 else L2) i) c i < 2 ^ 27 := fun c _ i hi => by
    simp only; split
    · exact p4.lt i hi
    · exact p2.lt i hi
  refine ⟨fun c i => (if c < 2 then L4 else L2) i,
    fun c i => (if c = 0 then L4 else if c = 1 then L3 else if c = 2 then L2 else L1) i, s2.mem,
    ⟨yL_def, fun c _ i hi => ?_, fun c _ => ?_, fun c hc => ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · show (if c = 0 then L4 else if c = 1 then L3 else if c = 2 then L2 else L1) i < 2 ^ 27
    split
    · exact p4.lt i hi
    · split
      · exact p3.lt i hi
      · split
        · exact p2.lt i hi
        · exact p1.lt i hi
  · show val (if c < 2 then L4 else L2) % P = _
    split
    · rw [p4.val]
    · rw [p2.val]
  · show val (if c = 0 then L4 else if c = 1 then L3 else if c = 2 then L2 else L1) % P = _
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · exact p4.val
    · exact p3.val
    · exact p2.val
    · exact p1.val
  · intro k hk
    have := sl2 k hk
    rw [g1 .x0 (by decide), v1] at this
    exact this
  · rw [g1 .x0 (by decide), mm1] at f2; exact f2
  obtain x16 : (s5.gpr .x16).toNat = 2 ^ 26 - 1 := by
    rw [congrFun g5 .x16, g4 .x16 (by decide), g3 .x16 (by decide), g2 .x16 (by decide)]; exact m1
  obtain x3t : s5.gpr .x3 = s₀.gpr .x3 := by rw [congrFun g5 .x3, g4 .x3 (by decide), gs .x3 (by decide)]
  obtain hv2 : ∀ r, s2.v r = s₀.v r := fun r => by rw [v2, v1]
  obtain g20 : ∀ r ∈ [Reg.x4, .x5, .x6], s2.gpr r = s₀.gpr r := fun r hr => by
    rw [g2 r (by revert hr; decide +revert), g1 r (by revert hr; decide +revert)]
  refine ⟨gt .x0 (by decide), ?_, gt .x3 (by decide), ?_, gt .x7 (by decide), gt .x8 (by decide),
    gt .x17 (by decide), by rw [tmm, m5, m4, m3], by rw [trd, rd5, rd4, rd3, rd2, rd1],
    by rw [twr, wr5, wr4, wr3, wr2, wr1], ⟨fun i hi c hc => ?_, fun j hj h1 c hc => ?_, yL_def,
      by decide, fun i hi h1 j hj => by revert i; decide +revert⟩, fun i hi c hc => ?_,
    fun e he => by rw [tm e he, x16], tp, ?_, fun h6 => ?_⟩
  · rw [gt .x2 (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [t9, x3t]
    apply BitVec.eq_of_toNat_eq
    obtain h64 : ((s₀.gpr .x3) >>> 6).toNat = nq s₀ := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [BitVec.toNat_sub, h64, show (1 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat]
    have := (s₀.gpr .x3).isLt
    simp only [nq] at *
    omega_arith
  · rw [hrt i hi, w4r i hi c hc]
  · rw [hst j hj h1, t5 j hj h1 c hc, w4r j hj c hc]
  · rw [hft i hi, w4f i hi c hc]
  · rw [vt _ (by decide) (by decide) (by decide) (by decide), v3 _ (by decide), hv2]
  · have h62 : (s2.gpr .x6).toNat ≤ 4 := by rw [g20 .x6 (by decide)]; exact h6
    obtain hl0 : ∀ i < 5, hl t 0 i = limOf s2 i := fun i hi => by
      show ln (t.v (hV i)) 0 = _; rw [hvt i hi]; exact h3 h62 i hi
    obtain hl1 : ∀ i < 5, hl t 1 i = 0 := fun i hi => by
      show ln (t.v (hV i)) 1 = _; rw [hvt i hi]; exact z3 i hi
    refine ⟨fun e he i hi => ?_, ?_⟩
    · rcases (show e = 0 ∨ e = 1 by omega_arith) with rfl | rfl
      · rw [hl0 i hi]; exact lim_lt (s2.gpr .x4).isLt (s2.gpr .x5).isLt h62 i hi
      · rw [hl1 i hi]; decide
    · have v0 : val (hl t 0) = hval s₀ := by
        rw [val_congr hl0, lim_val (s2.gpr .x4).isLt (s2.gpr .x5).isLt]
        simp only [hval, g20 .x4 (by decide), g20 .x5 (by decide), g20 .x6 (by decide)]
      obtain v1' : val (hl t 1) = 0 := by rw [val_congr hl1]; rfl
      rw [v0, v1', Nat.mul_zero, show bytesAt s2.mem (s₀.gpr .x2) 0 = [] from rfl, Poly1305.absorbAll_nil]
      exact Poly1305.pair_init R (hval s₀)

/-! ## A group of the loop -/

/-- The bytes of a group, in four blocks. -/
theorem group_bytes (m : Mem) (p : Addr) (j : Nat) :
    bytesAt m p (64 * (j + 1)) = bytesAt m p (64 * j) ++
      (bytesAt m (p + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * 0)) 16 ++
        bytesAt m (p + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * 1)) 16 ++
        bytesAt m (p + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * 2)) 16 ++
        bytesAt m (p + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * 3)) 16) := by
  rw [show 64 * (j + 1) = 64 * j + 64 from by omega_arith, Poly1305.bytesAt_add]
  generalize p + BitVec.ofNat 64 (64 * j) = q
  rw [show bytesAt m q 64 = bytesAt m q (16 + (16 + (16 + 16))) from rfl, Poly1305.bytesAt_add,
    Poly1305.bytesAt_add, Poly1305.bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc, Nat.mul_zero, Nat.mul_one,
    BitVec.add_zero]

theorem step_ok {s₀ s : State} {R : Nat} {M : Mem} {yL yF : Nat → Nat → Nat} {j : Nat} (hY : Ys R yL yF)
    (hL : LInv s₀ R M yL yF j s) (hj : j + 2 ≤ nq s₀)
    (hd : ∀ d, d + 16 ≤ (s₀.gpr .x3).toNat → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x2 + BitVec.ofNat 64 d) 16) :
    WP isa (.block (group rV sV ++ ([.addImm .x .x2 .x2 64, .subImm .x .x9 .x9 1] : List Instr))) s
      (LInv s₀ R M yL yF (j + 1)) := by
  obtain hn := (s₀.gpr .x3).isLt
  obtain ga : ∀ j' < 4, gAddr s j' = s₀.gpr .x2 + BitVec.ofNat 64 (64 * j) + BitVec.ofNat 64 (16 * j') :=
    fun j' _ => by rw [gAddr, hL.x2]
  refine WP.block_append (WP.mono (group_ok hL.mul hL.mask hL.pad fun j' hj' => by
      rw [ga j' hj', hL.rd, hL.wr, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hd _ (by simp only [nq] at hj; omega_arith)) fun t ⟨hg, gk⟩ => ?_)
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_nil_iff.mpr ?_
  have tv : ∀ r, (∀ i < 5, r ≠ hV i ∧ r ≠ dV i ∧ r ≠ iV i) → t.v r = s.v r := gk.v
  obtain gt : ∀ r, t.gpr r = s.gpr r := fun r => congrFun gk.gpr r
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi c hc => ?_, fun e he => ?_, fun e he => ?_, ?_,
    fun h6 => ?_⟩
  · allstep; rw [gt, hL.x0]
  · allstep; rw [gt, hL.x2, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2
  · allstep; rw [gt, hL.x3]
  · allstep; rw [gt, hL.x9]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [nq] at *; omega_arith
  · allstep; rw [gt, hL.x7]
  · allstep; rw [gt, hL.x8]
  · allstep; rw [gt, hL.x17]
  · simp only [RegUpd.mem_write]; rw [gk.mem, hL.mem]
  · simp only [RegUpd.rd_write]; rw [gk.rd, hL.rd]
  · simp only [RegUpd.wr_write]; rw [gk.wr, hL.wr]
  · exact hL.mul.of_v fun r h => tv r fun i hi => ⟨(h i hi).2.2, (h i hi).2.1, (h i hi).1⟩
  · show wd (t.v (fV i)) c = _
    rw [tv _ fun i' hi' => (show ∀ i < 5, ∀ i' < 5, fV i ≠ hV i' ∧ fV i ≠ dV i' ∧ fV i ≠ iV i' by decide) i hi i' hi']
    exact hL.fw i hi c hc
  · show ln (t.v maskV) e = _; rw [tv _ (by decide)]; exact hL.mask e he
  · show ln (t.v padV) e = _; rw [tv _ (by decide)]; exact hL.pad e he
  · show t.v .v15 = _; rw [tv _ (by decide)]; exact hL.v15
  · obtain ⟨hb, hS⟩ := hL.acc h6
    obtain hg' := hg hb
    obtain hlt : ∀ e < 2, ∀ i < 5, hl t e i < 2 ^ 27 := fun e he i hi => (hg' e he i hi).2
    -- the lanes after the group
    obtain l0 := group_lane (s := s) (t := t) (y := yL) (e := 0) fun i hi => (hg' 0 (by decide) i hi).1
    obtain l1 := group_lane (s := s) (t := t) (y := yL) (e := 1) fun i hi => (hg' 1 (by decide) i hi).1
    obtain y0 : val (yL 0) ≡ R ^ 4 [MOD P] := hY.valL 0 (by decide)
    obtain y1 : val (yL 1) ≡ R ^ 4 [MOD P] := hY.valL 1 (by decide)
    obtain y2 : val (yL 2) ≡ R ^ 2 [MOD P] := hY.valL 2 (by decide)
    obtain y3 : val (yL 3) ≡ R ^ 2 [MOD P] := hY.valL 3 (by decide)
    obtain len : ∀ j' : Nat, (gbytes s j').length = 16 := fun _ => Poly1305.length_bytesAt _ _ _
    obtain eA := l0.trans ((y2.mul_left _).add (y0.mul_left _))
    obtain eB := l1.trans ((y3.mul_left _).add (y1.mul_left _))
    obtain hstep := Poly1305.pair_step (len 0) (len 1) (len 2) (len 3) hS
      (eA.trans (by rw [Nat.add_comm]))
      (eB.trans (by rw [Nat.add_comm]))
    refine ⟨fun e he i hi => ?_, ?_⟩
    · exact hlt e he i hi
    · show val (hl t 0) * R + val (hl t 1) ≡ _ [MOD P]
      refine hstep.trans ?_
      rw [← Poly1305.absorbAll_append (by rw [Poly1305.length_bytesAt]; omega_arith), group_bytes]
      simp only [gbytes, ga 0 (by decide), ga 1 (by decide), ga 2 (by decide), ga 3 (by decide), hL.mem,
        List.append_assoc]
      exact Nat.ModEq.refl _

/-! ## The loop -/

theorem loop_ok {s₀ s : State} {R : Nat} {M : Mem} {yL yF : Nat → Nat → Nat} (hY : Ys R yL yF)
    (hL : LInv s₀ R M yL yF 0 s) (hq : 2 ≤ nq s₀)
    (hd : ∀ d, d + 16 ≤ (s₀.gpr .x3).toNat → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x2 + BitVec.ofNat 64 d) 16) :
    WP isa (.loop (.block (group rV sV ++ ([.addImm .x .x2 .x2 64, .subImm .x .x9 .x9 1] : List Instr)))
      (.nonzero .x .x9)) s (LInv s₀ R M yL yF (nq s₀ - 1)) := by
  obtain hn := (s₀.gpr .x3).isLt
  refine WP.loop (M := isa) (fun k s => ∃ j, k = nq s₀ - 1 - j ∧ LInv s₀ R M yL yF j s ∧ j + 2 ≤ nq s₀) ?_ _ s
    ⟨0, rfl, hL, hq⟩
  rintro k s ⟨j, rfl, h, hj⟩
  refine WP.mono (step_ok hY h hj hd) fun s' h' => ?_
  obtain hev : isa.eval (.nonzero .x .x9) s' = some (!decide (nq s₀ - 1 - (j + 1) = 0)) := by
    rw [AArch64.eval_nonzero, h'.x9, show (BitVec.ofNat 64 (nq s₀ - 1 - (j + 1)) != 0) =
      !(BitVec.ofNat 64 (nq s₀ - 1 - (j + 1)) == 0) from rfl, Poly1305.ofNat_beq_zero (by simp only [nq] at *; omega_arith)]
  by_cases hl : nq s₀ - 1 - (j + 1) = 0
  · refine .inl ⟨by rw [hev, hl]; rfl, ?_⟩
    rw [show nq s₀ - 1 = j + 1 by omega_arith]; exact h'
  · exact .inr ⟨by rw [hev]; simp only [hl, decide_false, Bool.not_false], _, by omega_arith, j + 1, rfl, h',
      by omega_arith⟩

end VG.Proof.Poly1305.AArch64.Vector

end

end


/-!
# Poly1305 on AArch64 in AdvSIMD: the last group and the end

Untrusted: everything here is checked by Lean. The lanes are added
(`sumLanes`), the limbs put back into three words (`pack`), the third reduced
to at most 4 (`fold6`), and `v8`–`v14` restored.
-/

@[expose] public section

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Poly1305.Limbs26 (val)
open VG.Proof.Poly1305.Limbs64 (add3_toNat)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305.AArch64.Radix64 (hval Keeps ofNat_bool zero_nat)

/-! ## The lanes added -/

theorem sumLanes_ok (s : State) :
    WP isa (.block sumLanes) s fun t =>
      (∀ i < 5, (t.gpr (X i)).toNat = (ln (s.v (hV i)) 0 + ln (s.v (hV i)) 1) % 2 ^ 64) ∧
      (∀ r ∉ limbRegs, t.gpr r = s.gpr r) ∧ t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  simp only [sumLanes, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil]
  iterate 15
    refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
    gstep
  refine WP.block_nil_iff.mpr ⟨fun i hi => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_arith) with rfl | rfl | rfl | rfl | rfl <;>
      gstep <;> simp only [BitVec.toNat_add, ln] <;> rfl
  · simp only [limbRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h10, h11, h12, h13, h14⟩ := hr
    simp (disch := assumption) only [show X 0 = Reg.x9 from rfl, show X 1 = Reg.x10 from rfl,
      show X 2 = Reg.x11 from rfl, show X 3 = Reg.x12 from rfl, show X 4 = Reg.x13 from rfl,
      RegUpd.gpr_write_of_ne]

/-! ## Three words -/

/-- Reads of the general-purpose registers and the carry through the writes so far. -/
macro "cstep" : tactic =>
  `(tactic| plain_simp_names simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
                     State.read, Size.bits, BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte, Bool.toNat_false, Nat.add_zero,
                     BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.setWidth_zero,
                     ofNat_bool])

theorem pack_ok (s : State) :
    WP isa (.block pack) s fun t =>
      ((∀ i < 5, (s.gpr (X i)).toNat < 2 ^ 28) →
        hval t = val fun i => (s.gpr (X i)).toNat) ∧ Keeps [.x4, .x5, .x6, .x14, .x15] s t := by
  simp only [pack]
  iterate 12
    refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_nil_iff.mpr ?_
  simp only [hval]
  cstep
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h0 : (s.gpr .x9).toNat < 2 ^ 28 := h 0 (by decide)
    have h1 : (s.gpr .x10).toNat < 2 ^ 28 := h 1 (by decide)
    have h2 : (s.gpr .x11).toNat < 2 ^ 28 := h 2 (by decide)
    have h3 : (s.gpr .x12).toNat < 2 ^ 28 := h 3 (by decide)
    have h4 : (s.gpr .x13).toNat < 2 ^ 28 := h 4 (by decide)
    have ea : (s.gpr .x9 + s.gpr .x10 <<< 26).toNat = (s.gpr .x9).toNat + (s.gpr .x10).toNat * 2 ^ 26 := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega_arith
    have eb : (s.gpr .x11 <<< 52).toNat = (s.gpr .x11).toNat * 2 ^ 52 % 2 ^ 64 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have ec : (s.gpr .x11 >>> 12 + s.gpr .x12 <<< 14).toNat =
        (s.gpr .x11).toNat / 2 ^ 12 + (s.gpr .x12).toNat * 2 ^ 14 := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow]; omega_arith
    have ed : (s.gpr .x13 <<< 40).toNat = (s.gpr .x13).toNat * 2 ^ 40 % 2 ^ 64 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have ee : (s.gpr .x13 >>> 24).toNat = (s.gpr .x13).toNat / 2 ^ 24 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have e := add3_toNat (s.gpr .x9 + s.gpr .x10 <<< 26) (s.gpr .x11 <<< 52)
      (s.gpr .x11 >>> 12 + s.gpr .x12 <<< 14) (s.gpr .x13 <<< 40) (s.gpr .x13 >>> 24) 0#64
      (by rw [ea, eb, ec, ed, ee, show (0#64).toNat = 0 from rfl]; omega_arith)
    simp only [BitVec.add_zero] at e
    rw [e, ea, eb, ec, ed, ee, show (0#64).toNat = 0 from rfl]
    simp only [val, show X 0 = Reg.x9 from rfl, show X 1 = Reg.x10 from rfl, show X 2 = Reg.x11 from rfl,
      show X 3 = Reg.x12 from rfl, show X 4 = Reg.x13 from rfl]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-! ## The third word reduced -/

theorem fold6_ok (s : State) :
    WP isa (.block fold6) s fun t =>
      ((s.gpr .x6).toNat < 2 ^ 20 → hval t + P * ((s.gpr .x6).toNat / 4) = hval s ∧ (t.gpr .x6).toNat ≤ 4) ∧
        Keeps [.x4, .x5, .x6, .x14, .x15] s t := by
  simp only [fold6]
  iterate 9
    refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_nil_iff.mpr ?_
  simp only [hval]
  cstep
  refine ⟨fun h => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have w4 := (s.gpr .x4).isLt; have w5 := (s.gpr .x5).isLt
    obtain eT : (s.gpr .x6 >>> 2 + s.gpr .x6 >>> 2 <<< 2).toNat = 5 * ((s.gpr .x6).toNat / 4) := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow]; omega_arith
    obtain eE : (s.gpr .x6 &&& BitVec.setWidth 64 3#16).toNat = (s.gpr .x6).toNat % 4 := by
      rw [BitVec.toNat_and, show (BitVec.setWidth 64 3#16).toNat = 2 ^ 2 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
    obtain e := add3_toNat (s.gpr .x4) (s.gpr .x6 >>> 2 + s.gpr .x6 >>> 2 <<< 2) (s.gpr .x5) 0#64
      (s.gpr .x6 &&& BitVec.setWidth 64 3#16) 0#64
      (by rw [eT, eE, show (0#64).toNat = 0 from rfl]; omega_arith)
    simp only [BitVec.add_zero] at e
    have z : (0#64).toNat = 0 := rfl
    refine ⟨?_, ?_⟩
    · rw [e, Limbs26.P_eq]; omega_arith
    · omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-! ## The end of `vec` -/

theorem finish_eq : finish = times5 fV sV ++ (group fV sV ++
    (([.addImm .x .x2 .x2 64, .movz .x .x9 63 0, .logic .and .x .x3 .x3 .x9] : List Instr) ++
    (sumLanes ++ (pack ++ (fold6 ++ restore))))) := by
  simp only [finish, List.append_assoc]

theorem adv_ok (s : State) :
    WP isa (.block ([.addImm .x .x2 .x2 64, .movz .x .x9 63 0, .logic .and .x .x3 .x3 .x9] : List Instr)) s
      fun t => t.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 64 ∧ (t.gpr .x3).toNat = (s.gpr .x3).toNat % 64 ∧
        (∀ r ∉ [Reg.x2, .x3, .x9], t.gpr r = s.gpr r) ∧ t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr ∧ t.sp = s.sp := by
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_nil_iff.mpr ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · allstep
  · allstep
    rw [BitVec.toNat_and, show (BitVec.setWidth 64 (63 : BitVec 16) <<< (16 * 0)).toNat = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h2, h3, h9⟩ := hr
    allstep

theorem nmem_of {r : Reg} {l l' : List Reg} (hr : r ∉ l) (hs : ∀ x ∈ l', x ∈ l := by decide) : r ∉ l' :=
  fun h => hr (hs r h)

theorem fV_sV : ∀ i < 5, ∀ j < 5, 1 ≤ j → fV i ≠ sV j := by decide

/-- What `vec` leaves: the registers and memory it keeps, `v8`–`v15`, and the accumulator. -/
structure VEnd (s₀ : State) (R : Nat) (M : Mem) (t : State) : Prop where
  x0 : t.gpr .x0 = s₀.gpr .x0
  x2 : t.gpr .x2 = s₀.gpr .x2 + BitVec.ofNat 64 (64 * nq s₀)
  x3 : (t.gpr .x3).toNat = (s₀.gpr .x3).toNat % 64
  x7 : t.gpr .x7 = s₀.gpr .x7
  x8 : t.gpr .x8 = s₀.gpr .x8
  x17 : t.gpr .x17 = s₀.gpr .x17
  mem : t.mem = M
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  vlow : ∀ k < 7, vdword (t.v (V (8 + k))) 0 = vdword (s₀.v (V (8 + k))) 0
  v15 : t.v .v15 = s₀.v .v15
  acc : (s₀.gpr .x6).toNat ≤ 4 →
    hval t % P = absorbAll R (hval s₀) (bytesAt M (s₀.gpr .x2) (64 * nq s₀)) % P ∧ (t.gpr .x6).toNat ≤ 4

theorem finish_ok {s₀ s : State} {R : Nat} {M : Mem} {yL yF : Nat → Nat → Nat} (hY : Ys R yL yF)
    (hS : Saved s₀ M) (hL : LInv s₀ R M yL yF (nq s₀ - 1) s) (hq : 2 ≤ nq s₀)
    (hd : ∀ d, d + 16 ≤ (s₀.gpr .x3).toNat → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x2 + BitVec.ofNat 64 d) 16)
    (hw : ∀ k < 7, InRegions (s₀.rd ++ s₀.wr) (svA (s₀.gpr .x0) k) 8) :
    WP isa (.block finish) s (VEnd s₀ R M) := by
  have hn := (s₀.gpr .x3).isLt
  rw [finish_eq]
  -- `5 F`
  refine WP.block_append (WP.mono (times5_ok fV sV (fun i hi _ j hj h1 => fV_sV i hi j hj h1) sV_inj s
      fun j hj _ c hc => by rw [hL.fw j hj c hc]; exact Nat.lt_trans (hY.ltF c hc j hj) (by decide))
    fun s1 ⟨t1, v1, g1, m1, rd1, wr1, _⟩ => ?_)
  have fV1 : ∀ i < 5, s1.v (fV i) = s.v (fV i) := fun i hi => v1 _ fun j hj h1 => fV_sV i hi j hj h1
  have nS : ∀ r, (∀ j < 5, 1 ≤ j → r ≠ sV j) → s1.v r = s.v r := v1
  have mul1 : Mults s1 fV sV yF :=
    { r := fun i hi c hc => by rw [fV1 i hi]; exact hL.fw i hi c hc
      s5 := fun j hj h1 c hc => by rw [t1 j hj h1 c hc, hL.fw j hj c hc]
      lt := hY.ltF
      regR := by decide
      regS := by decide }
  have x2s1 : s1.gpr .x2 = s₀.gpr .x2 + BitVec.ofNat 64 (64 * (nq s₀ - 1)) := by rw [g1, hL.x2]
  -- the last group
  refine WP.block_append (WP.mono (group_ok mul1 (fun e he => by rw [nS _ (by decide)]; exact hL.mask e he)
      (fun e he => by rw [nS _ (by decide)]; exact hL.pad e he) fun j' hj' => by
        rw [gAddr, x2s1, rd1, wr1, hL.rd, hL.wr, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact hd _ (by simp only [nq] at hq ⊢; omega_arith)) fun s2 ⟨hg, gk⟩ => ?_)
  -- `x2`, `x3`
  refine WP.block_append (WP.mono (adv_ok s2) fun s3 ⟨a2, a3, ag, av, am, ard, awr, _⟩ => ?_)
  refine WP.block_append (WP.mono (sumLanes_ok s3) fun s4 ⟨l4, g4, v4, m4, rd4, wr4, _⟩ => ?_)
  refine WP.block_append (WP.mono (WP.keepV (pack_ok s4)) fun s5 ⟨⟨p5, k5⟩, v5⟩ => ?_)
  refine WP.block_append (WP.mono (WP.keepV (fold6_ok s5)) fun s6 ⟨⟨f6, k6⟩, v6⟩ => ?_)
  -- the state pointer and the slots, at `s6`
  have gpr26 : ∀ r ∉ [Reg.x2, .x3, .x9, .x4, .x5, .x6, .x10, .x11, .x12, .x13, .x14, .x15],
      s6.gpr r = s2.gpr r := fun r hr => by
    rw [k6.1 r (nmem_of hr), k5.1 r (nmem_of hr), g4 r (nmem_of hr), ag r (nmem_of hr)]
  have gpr0 : ∀ r ∈ [Reg.x0, .x7, .x8, .x17], s6.gpr r = s₀.gpr r := fun r hr => by
    rw [gpr26 r (by revert hr; decide +revert), congrFun gk.gpr r, g1]
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hL.x0
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hL.x7
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hL.x8
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hL.x17
    · exact absurd hr List.not_mem_nil
  have mem6 : s6.mem = M := by rw [k6.2.1, k5.2.1, m4, am, gk.mem, m1, hL.mem]
  have rd6 : s6.rd = s₀.rd := by rw [k6.2.2.1, k5.2.2.1, rd4, ard, gk.rd, rd1, hL.rd]
  have wr6 : s6.wr = s₀.wr := by rw [k6.2.2.2, k5.2.2.2, wr4, awr, gk.wr, wr1, hL.wr]
  have v26 : s6.v = s2.v := by rw [v6, v5, v4, av]
  refine WP.mono (restore_ok s6 fun k hk => by rw [rd6, wr6, gpr0 .x0 (by decide)]; exact hw k hk)
    fun t ⟨rv, ro, rg, rm, rrd, rwr, _⟩ => ?_
  have gt : ∀ r, r ≠ .x9 → t.gpr r = s6.gpr r := rg
  refine ⟨by rw [gt _ (by decide)]; exact gpr0 .x0 (by decide), ?_, ?_, by rw [gt _ (by decide)]; exact gpr0 .x7 (by decide),
    by rw [gt _ (by decide)]; exact gpr0 .x8 (by decide), by rw [gt _ (by decide)]; exact gpr0 .x17 (by decide),
    by rw [rm, mem6], by rw [rrd, rd6], by rw [rwr, wr6], fun k hk => ?_, ?_, fun h6 => ?_⟩
  · rw [gt _ (by decide), k6.1 _ (by decide), k5.1 _ (by decide), g4 _ (by decide), a2, congrFun gk.gpr .x2, x2s1,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega_arith
  · rw [gt _ (by decide), k6.1 _ (by decide), k5.1 _ (by decide), g4 _ (by decide), a3, congrFun gk.gpr .x3, g1,
      hL.x3]
  · rw [rv k hk, mem6, gpr0 .x0 (by decide)]; exact hS.slots k hk
  · rw [ro _ (by decide), v26, gk.v _ (by decide), nS _ (by decide)]; exact hL.v15
  · obtain ⟨hb, hSc⟩ := hL.acc h6
    have hl1 : ∀ e < 2, ∀ i < 5, hl s1 e i = hl s e i := fun e _ i hi => by
      show ln (s1.v (hV i)) e = ln (s.v (hV i)) e; rw [nS _ (by revert i; decide +revert)]
    have hg' := hg fun e he i hi => by rw [hl1 e he i hi]; exact hb e he i hi
    -- the lanes after the last group
    have l0 := group_lane (s := s1) (t := s2) (y := yF) (e := 0) fun i hi => (hg' 0 (by decide) i hi).1
    have l1 := group_lane (s := s1) (t := s2) (y := yF) (e := 1) fun i hi => (hg' 1 (by decide) i hi).1
    rw [val_congr (hl1 0 (by decide))] at l0
    rw [val_congr (hl1 1 (by decide))] at l1
    have y0 : val (yF 0) ≡ R ^ 4 [MOD P] := hY.valF 0 (by decide)
    have y1 : val (yF 1) ≡ R ^ 3 [MOD P] := hY.valF 1 (by decide)
    have y2 : val (yF 2) ≡ R ^ 2 [MOD P] := hY.valF 2 (by decide)
    have y3 : val (yF 3) ≡ R [MOD P] := (hY.valF 3 (by decide)).trans (by rw [Nat.pow_one])
    have len : ∀ j' : Nat, (gbytes s1 j').length = 16 := fun _ => Poly1305.length_bytesAt _ _ _
    have eA := l0.trans ((y2.mul_left _).add (y0.mul_left _))
    have eB := l1.trans ((y3.mul_left _).add (y1.mul_left _))
    have hlast := Poly1305.pair_last (len 0) (len 1) (len 2) (len 3) hSc
      (eA.trans (by rw [Nat.add_comm])) (eB.trans (by rw [Nat.add_comm]))
    -- the lanes added, packed and reduced
    have lt2 : ∀ e < 2, ∀ i < 5, hl s2 e i < 2 ^ 27 := fun e he i hi => (hg' e he i hi).2
    have x4v : ∀ i < 5, (s4.gpr (X i)).toNat = hl s2 0 i + hl s2 1 i := fun i hi => by
      rw [l4 i hi, av]
      have := lt2 0 (by decide) i hi; have := lt2 1 (by decide) i hi
      exact Nat.mod_eq_of_lt (by simp only [hl] at *; omega_arith)
    have hv5 : hval s5 = val (hl s2 0) + val (hl s2 1) := by
      rw [p5 fun i hi => by
        rw [x4v i hi]; have := lt2 0 (by decide) i hi; have := lt2 1 (by decide) i hi; omega_arith,
        ← val_add]
      exact val_congr x4v
    have b5 : (s5.gpr .x6).toNat < 2 ^ 20 := by
      have := (s5.gpr .x4).isLt; have := (s5.gpr .x5).isLt
      have h0 := lt2 0 (by decide); have h1 := lt2 1 (by decide)
      have a := h0 0 (by decide); have := h0 1 (by decide); have := h0 2 (by decide)
      have := h0 3 (by decide); have := h0 4 (by decide)
      have := h1 0 (by decide); have := h1 1 (by decide); have := h1 2 (by decide)
      have := h1 3 (by decide); have := h1 4 (by decide)
      simp only [hval, val] at hv5
      omega_arith
    obtain ⟨ef, bf⟩ := f6 b5
    have ht : hval t = hval s6 := by
      simp only [hval, gt .x4 (by decide), gt .x5 (by decide), gt .x6 (by decide)]
    refine ⟨?_, by rw [gt _ (by decide)]; exact bf⟩
    have e1 : hval t % P = hval s5 % P := by
      rw [ht, ← ef, Nat.add_mul_mod_self_left]
    rw [e1, hv5]
    refine hlast.trans ?_
    rw [← Poly1305.absorbAll_append (by rw [Poly1305.length_bytesAt]; omega_arith),
      show 64 * nq s₀ = 64 * (nq s₀ - 1 + 1) from by omega_arith, group_bytes]
    simp only [gbytes, gAddr, x2s1, m1, hL.mem, List.append_assoc]
    rfl

end VG.Proof.Poly1305.AArch64.Vector

end

end


/-!
# Poly1305 on AArch64 in AdvSIMD: `vec`

Untrusted: everything here is checked by Lean. From at least 128 bytes of
data at `x2` (`x3` of them), `vec` absorbs the first `64 ⌊x3 / 64⌋` into the
accumulator `x4:x5:x6` (`VEnd`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector

theorem vec_ok {s₀ : State} {R : Nat} (hk : Radix64.Keys R s₀) (hn : 128 ≤ (s₀.gpr .x3).toNat)
    (hw : ∀ k < 7, InRegions s₀.wr (svA (s₀.gpr .x0) k) 8)
    (hd : ∀ d, d + 16 ≤ (s₀.gpr .x3).toNat → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x2 + BitVec.ofNat 64 d) 16) :
    WP isa vec s₀ fun t => ∃ M, Saved s₀ M ∧ VEnd s₀ R M t := by
  obtain hq : 2 ≤ nq s₀ := by simp only [nq]; omega_using [hn]
  obtain hw' : ∀ k < 7, InRegions (s₀.rd ++ s₀.wr) (svA (s₀.gpr .x0) k) 8 := fun k hk => by
    obtain ⟨r, hr, hc⟩ := hw k hk
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.seq (WP.mono (setup_ok hk hn hw) fun s1 ⟨yL, yF, M, hY, hS, hL⟩ => ?_)
  exact WP.seq (WP.mono (loop_ok hY hL hq hd) fun s2 h2 =>
    WP.mono (finish_ok hY hS h2 hq hd hw') fun t ht => ⟨M, hS, ht⟩)

end VG.Proof.Poly1305.AArch64.Vector
