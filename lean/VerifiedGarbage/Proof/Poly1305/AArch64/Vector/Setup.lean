import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Step
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Absorb
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Setup
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# Poly1305 on AArch64 in AdvSIMD: the setup

Untrusted: everything here is checked by Lean. The 26-bit limbs of a number in
`x4:x5:x6` (`limbs`), and their insertion into vectors.
-/

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Poly1305.Limbs26 (val)
open VG.Spec.Poly1305 (P)
open VG.Proof.Poly1305.AArch64.Radix64 (hval Keeps absorbRegs mul_ok)

/-- Reads of the general-purpose registers through the writes of the steps so far. -/
macro "gstep" : tactic =>
  `(tactic| simp (disch := decide) only [RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.v_write,
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
  simp only [val, lim]; omega

theorem lim_lt {w0 w1 w2 : Nat} (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64) (h2 : w2 ≤ 4) :
    ∀ i < 5, lim w0 w1 w2 i < 2 ^ 27 := by
  have := h0; have := h1; have := h2
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [lim] <;> omega

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
    have hm' : s.gpr .x16 = BitVec.ofNat 64 (2 ^ 26 - 1) := by
      apply BitVec.eq_of_toNat_eq; rw [hm]; rfl
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [X, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, Size.bits,
        BitVec.setWidth_eq, hm', BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
        BitVec.toNat_or, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, lim] <;>
      try simp only [and_mask26]
    · rw [show (s.gpr .x5).toNat * 2 ^ 12 % 2 ^ 64 = 2 ^ 12 * ((s.gpr .x5).toNat % 2 ^ 52) by omega,
        or_low (by omega)]
      omega
    · rw [show (s.gpr .x6).toNat * 2 ^ 24 % 2 ^ 64 = 2 ^ 24 * (s.gpr .x6).toNat by omega, or_low (by omega)]
      omega
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
    have hk : k < 5 := his k List.mem_cons_self
    have his' : ∀ i ∈ is, i < 5 := fun i hi => his i (List.mem_cons_of_mem _ hi)
    obtain ⟨hnk, hnd'⟩ := List.nodup_cons.mp hnd
    refine WP.block_cons_iff.mpr ⟨_, exec_ins s (dst k) hj (X k), ?_⟩
    refine WP.mono (ih his' hnd' _) fun t ⟨hr, hn, hkp⟩ => ⟨?_, ?_, ?_⟩
    · intro i hi c hc
      rcases List.mem_cons.mp hi with rfl | hi'
      · rw [hn i hk hnk, RegUpd.v_setV_self, wd_ins _ hj hc]
      · have hik : i ≠ k := fun h => hnk (h ▸ hi')
        rw [hr i hi' c hc, RegUpd.v_setV_of_ne _ _ (hd i (his' i hi') k hk hik), RegUpd.gpr_setV]
    · intro i hi hin
      have hik : i ≠ k := fun h => hin (h ▸ List.mem_cons_self)
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
  have k0 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s0.gpr r = s.gpr r := fun r hr =>
    ag r (by revert hr; decide +revert)
  refine WP.block_append (WP.mono (limbs_ok s0 (by rw [k0 .x16 (by decide)]; exact hm))
    fun s1 ⟨l1, g1, v1, m1, rd1, wr1, _⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok fV fV_inj (by decide) s1) fun s2 ⟨i2, k2⟩ => ?_)
  -- the registers `mul_ok` and `limbs` need, through each state
  have g02 : ∀ r ∉ limbRegs, s2.gpr r = s0.gpr r := fun r hr => by rw [congrFun k2.gpr r, g1 r hr]
  have key2 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s2.gpr r = s.gpr r := fun r hr => by
    rw [g02 r (by revert hr; decide +revert), k0 r hr]
  have h2 : hval s2 = R := by
    simp only [hval]
    rw [g02 .x4 (by decide), g02 .x5 (by decide), g02 .x6 (by decide), a4, a5, a6,
      ← key2 .x7 (by decide), ← key2 .x8 (by decide)] at *
    rw [← hR, key2 .x7 (by decide), key2 .x8 (by decide)]; omega
  have x62 : (s2.gpr .x6).toNat = 0 := by rw [g02 .x6 (by decide), a6]
  -- the keys, in any state that keeps them
  have keyOf : ∀ u : State, u.gpr .x7 = s.gpr .x7 → u.gpr .x8 = s.gpr .x8 → u.gpr .x17 = s.gpr .x17 →
      (u.gpr .x7).toNat < 2 ^ 60 ∧ (u.gpr .x8).toNat = 4 * q ∧ (u.gpr .x17).toNat = 5 * q ∧
        (u.gpr .x7).toNat + 2 ^ 64 * (u.gpr .x8).toNat = R := fun u e7 e8 e17 => by
    rw [e7, e8, e17]; exact ⟨hr0, hr1, hs1, hR⟩
  -- r²
  obtain ⟨kr0, kr1, ks1, kR⟩ := keyOf s2 (key2 .x7 (by decide)) (key2 .x8 (by decide)) (key2 .x17 (by decide))
  refine WP.block_append (WP.mono (WP.keepV (mul_ok s2 kr0 kr1 hq ks1)) fun s3 ⟨⟨hm3, k3⟩, v3⟩ => ?_)
  obtain ⟨e3, b3⟩ := hm3 (by omega)
  rw [kR, h2] at e3
  have key3 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s3.gpr r = s.gpr r := fun r hr => by
    rw [k3.1 r (by revert hr; decide +revert), key2 r hr]
  refine WP.block_append (WP.mono (limbs_ok s3 (by rw [key3 .x16 (by decide)]; exact hm))
    fun s4 ⟨l4, g4, v4, m4, rd4, wr4, _⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok rV rV_inj (by decide) s4) fun s5 ⟨i5, k5⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok rV rV_inj (by decide) s5) fun s6 ⟨i6, k6⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok fV fV_inj (by decide) s6) fun s7 ⟨i7, k7⟩ => ?_)
  have g37 : ∀ r ∉ limbRegs, s7.gpr r = s3.gpr r := fun r hr => by
    rw [congrFun k7.gpr r, congrFun k6.gpr r, congrFun k5.gpr r, g4 r hr]
  have key7 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s7.gpr r = s.gpr r := fun r hr => by
    rw [g37 r (by revert hr; decide +revert), key3 r hr]
  have h7 : hval s7 = hval s3 := by simp only [hval, g37 .x4 (by decide), g37 .x5 (by decide), g37 .x6 (by decide)]
  -- r³
  obtain ⟨kr0, kr1, ks1, kR⟩ := keyOf s7 (key7 .x7 (by decide)) (key7 .x8 (by decide)) (key7 .x17 (by decide))
  refine WP.block_append (WP.mono (WP.keepV (mul_ok s7 kr0 kr1 hq ks1)) fun s8 ⟨⟨hm8, k8⟩, v8⟩ => ?_)
  obtain ⟨e8, b8⟩ := hm8 (by rw [g37 .x6 (by decide)]; omega)
  rw [kR, h7] at e8
  have key8 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s8.gpr r = s.gpr r := fun r hr => by
    rw [k8.1 r (by revert hr; decide +revert), key7 r hr]
  refine WP.block_append (WP.mono (limbs_ok s8 (by rw [key8 .x16 (by decide)]; exact hm))
    fun s9 ⟨l9, g9, v9, m9, rd9, wr9, _⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok fV fV_inj (by decide) s9) fun s10 ⟨i10, k10⟩ => ?_)
  have g810 : ∀ r ∉ limbRegs, s10.gpr r = s8.gpr r := fun r hr => by rw [congrFun k10.gpr r, g9 r hr]
  have key10 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s10.gpr r = s.gpr r := fun r hr => by
    rw [g810 r (by revert hr; decide +revert), key8 r hr]
  have h10 : hval s10 = hval s8 := by
    simp only [hval, g810 .x4 (by decide), g810 .x5 (by decide), g810 .x6 (by decide)]
  -- r⁴
  obtain ⟨kr0, kr1, ks1, kR⟩ := keyOf s10 (key10 .x7 (by decide)) (key10 .x8 (by decide)) (key10 .x17 (by decide))
  refine WP.block_append (WP.mono (WP.keepV (mul_ok s10 kr0 kr1 hq ks1)) fun s11 ⟨⟨hm11, k11⟩, v11⟩ => ?_)
  obtain ⟨e11, b11⟩ := hm11 (by rw [g810 .x6 (by decide)]; omega)
  rw [kR, h10] at e11
  have key11 : ∀ r ∈ [Reg.x7, .x8, .x16, .x17, .x0, .x1, .x2, .x3], s11.gpr r = s.gpr r := fun r hr => by
    rw [k11.1 r (by revert hr; decide +revert), key10 r hr]
  refine WP.block_append (WP.mono (limbs_ok s11 (by rw [key11 .x16 (by decide)]; exact hm))
    fun s12 ⟨l12, g12, v12, m12, rd12, wr12, _⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok rV rV_inj (by decide) s12) fun s13 ⟨i13, k13⟩ => ?_)
  refine WP.block_append (WP.mono (insLimbs_ok rV rV_inj (by decide) s13) fun s14 ⟨i14, k14⟩ => ?_)
  refine WP.mono (insLimbs_ok fV fV_inj (by decide) s14) fun t ⟨it, kt⟩ => ?_
  have b0 : (s0.gpr .x6).toNat ≤ 4 := by omega
  have lv : ∀ u : State, val (limOf u) = hval u := fun u => lim_val (u.gpr .x4).isLt (u.gpr .x5).isLt _
  have h0 : hval s0 = R := by
    show (s0.gpr .x4).toNat + 2 ^ 64 * (s0.gpr .x5).toNat + 2 ^ 128 * (s0.gpr .x6).toNat = R
    rw [a4, a5, a6]; omega
  -- the limbs' registers at each insertion
  have x1 : ∀ i < 5, (s1.gpr (X i)).toNat % 2 ^ 32 = limOf s0 i := fun i hi => by rw [l1 b0 i hi, lim_word b0 hi]
  have x4' : ∀ i < 5, (s4.gpr (X i)).toNat % 2 ^ 32 = limOf s3 i := fun i hi => by rw [l4 b3 i hi, lim_word b3 hi]
  have x5 : ∀ i < 5, (s5.gpr (X i)).toNat % 2 ^ 32 = limOf s3 i := fun i hi => by rw [k5.gpr]; exact x4' i hi
  have x6' : ∀ i < 5, (s6.gpr (X i)).toNat % 2 ^ 32 = limOf s3 i := fun i hi => by rw [k6.gpr]; exact x5 i hi
  have x9 : ∀ i < 5, (s9.gpr (X i)).toNat % 2 ^ 32 = limOf s8 i := fun i hi => by rw [l9 b8 i hi, lim_word b8 hi]
  have x12 : ∀ i < 5, (s12.gpr (X i)).toNat % 2 ^ 32 = limOf s11 i := fun i hi => by rw [l12 b11 i hi, lim_word b11 hi]
  have x13 : ∀ i < 5, (s13.gpr (X i)).toNat % 2 ^ 32 = limOf s11 i := fun i hi => by rw [k13.gpr]; exact x12 i hi
  have x14 : ∀ i < 5, (s14.gpr (X i)).toNat % 2 ^ 32 = limOf s11 i := fun i hi => by rw [k14.gpr]; exact x13 i hi
  have rf : ∀ i < 5, ∀ j < 5, rV i ≠ fV j := rV_fV
  have fr : ∀ i < 5, ∀ j < 5, fV i ≠ rV j := fun i hi j hj => (rV_fV j hj i hi).symm
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
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  · -- the words of the last group's multipliers
    rw [it i hi c hc, x14 i hi, k14.v _ fun j hj => fr i hi j hj, k13.v _ fun j hj => fr i hi j hj,
      congrFun v12 (fV i), congrFun v11 (fV i), i10 i hi c hc, x9 i hi, congrFun v9 (fV i), congrFun v8 (fV i),
      i7 i hi c hc, x6' i hi, k6.v _ fun j hj => fr i hi j hj, k5.v _ fun j hj => fr i hi j hj,
      congrFun v4 (fV i), congrFun v3 (fV i), i2 i hi c hc, x1 i hi]
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
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
    have nf : ∀ j < 5, r ≠ fV j := fun j hj => (hr j hj).2
    rw [kt.v r nf, k14.v r nr, k13.v r nr, congrFun v12 r, congrFun v11 r, k10.v r nf, congrFun v9 r,
      congrFun v8 r, k7.v r nf, k6.v r nr, k5.v r nr, congrFun v4 r, congrFun v3 r, k2.v r nf,
      congrFun v1 r, congrFun av r]

end VG.Proof.Poly1305.AArch64.Vector
