module
public import VerifiedGarbage.Proof.Rsa.BoolNat
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Candidate
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Instr
import VerifiedGarbage.Proof.RsaKeyGen.Table
import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.TrialP
import Mathlib.Tactic.Set
import Mathlib.Order.RelClasses

/-! ### `RsaKeyGen.Arm.Cand.Tab`, which only this module used -/

section

/-! # A candidate on ARMv7: the table of small primes written (`table_ok`)

`tabWrite a k` stores the words `a` to `a + k − 1` of the table, from a
`movw` and a `movt` each (`tabSteps_ok`); `table_ok`: the first 256 words,
and the other 256 for `w > 16`, over the key arrays 22–48 (`tabJs`), which
nothing else holds then.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen

/-- The arrays the table is written over. -/
def tabJs : List Nat := List.range' 22 27

/-- The table's words: 256, or 512 for `W ≥ 35` (`w > 16`). -/
def nT (W : Nat) : Nat := if 35 ≤ W then 512 else 256

theorem tabWord32_lo {j : Nat} (hj : j < 512) : tabWord32 j % 2 ^ 16 = tabEntry (2 * j) := by
  have := (tabEntry_facts (i := 2 * j) (by omega_arith)).2.2
  unfold tabWord32; omega_arith

theorem tabWord32_hi {j : Nat} (hj : j < 512) : tabWord32 j / 2 ^ 16 = tabEntry (2 * j + 1) := by
  have := (tabEntry_facts (i := 2 * j) (by omega_arith)).2.2
  unfold tabWord32; omega_arith

theorem tabWord32_lt {j : Nat} (hj : j < 512) : tabWord32 j < 2 ^ 32 := by
  have := (tabEntry_facts (i := 2 * j) (by omega_arith)).2.2
  have := (tabEntry_facts (i := 2 * j + 1) (by omega_arith)).2.2
  unfold tabWord32; omega_arith

theorem tab_movt {j : Nat} (hj : j < 512) :
    (BitVec.ofNat 16 (tabEntry (2 * j + 1)) ++
      ((BitVec.ofNat 16 (tabEntry (2 * j))).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 (tabWord32 j) := by
  have e0 := (tabEntry_facts (i := 2 * j) (by omega_arith)).2.2
  have e1 := (tabEntry_facts (i := 2 * j + 1) (by omega_arith)).2.2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega_arith), Nat.shiftLeft_eq]
  unfold tabWord32
  omega_arith

theorem wp_movt' {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- The words `a` to `a + k − 1` of the table, at offset `o` (in `r12`). -/
theorem tabSteps_ok {s : State} {B : BitVec 32} {Z W N : Nat} (hw : Ws s B Z W N) {o a : Nat}
    (r12 : s.gpr .r12 = B + BitVec.ofNat 32 o) :
    ∀ k, a + k ≤ 512 → o + 4 * (a + k) ≤ Z →
    WP isa (.block (tabWrite a k)) s fun s' =>
      (∀ j < k, w32 s'.mem (State.addr B) (o + 4 * (a + j)) = tabWord32 (a + j)) ∧ Rest [.r1] s s' ∧
      Outside (State.addr B) (o + 4 * a) (4 * k) s.mem s'.mem
  | 0, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, hk, hz => by
    have hn := hw.nowrap
    rw [tabWrite, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.append (tabSteps_ok hw r12 k (by omega_arith) (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    simp only [tabStore]
    refine wp_movw fun s₂ u₂ => wp_movt' fun s₃ u₃ => ?_
    have k₃ : Rest [.r1] s s₃ := k₁.trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))
    have hw₃ := hw.rest k₃
    have ea : State.addr (s₃.gpr .r12 + BitVec.ofNat 32 (4 * (a + k))) =
        off (State.addr B) (o + 4 * (a + k)) := by
      rw [k₃.gpr _ (by decide), r12, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hw.addr (by omega_arith)
    refine wp_str (by omega_arith) ea (hw₃.write (by omega_arith)) fun s₄ m₄ => WP.block_nil ?_
    have O₂ : Outside (State.addr B) (o + 4 * (a + k)) 4 s₁.mem s₄.mem := by
      rw [m₄.mem, u₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega_arith)
    refine ⟨fun j hj => ?_, k₃.trans (m₄.rest _),
      (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.w32 (by omega_arith) (by omega_arith), e₁ j h]
    · obtain rfl : j = k := by omega_arith
      rw [m₄.mem, u₃.mem, u₂.mem, w32_write_self, u₃.gpr, u₂.gpr, tab_movt (by omega_arith), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (tabWord32_lt (by omega_arith))]

/-- Memory that changed only within the arrays `a` to `a + k − 1`. -/
theorem keep_span {B : BitVec 32} {w a k o n : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Outside (State.addr B) o n m m') (ho : arr w a ≤ o) (hn : o + n ≤ arr w (a + k))
    (hjs : ∀ j, a ≤ j → j < a + k → j ∈ js) : Keep B w js ds m m' := by
  intro x hx
  refine h x ?_
  by_contra hc
  have hS : 0 < S w := by simp only [S]; omega_arith
  have hlo : hdr ≤ ofs (State.addr B) x := by
    have : hdr ≤ arr w a := Nat.le_add_right _ _
    omega_arith
  obtain ⟨q, r, hr, hq⟩ : ∃ q r, r < S w ∧ ofs (State.addr B) x = hdr + q * S w + r :=
    ⟨(ofs (State.addr B) x - hdr) / S w, (ofs (State.addr B) x - hdr) % S w, Nat.mod_lt _ hS, by
      have := Nat.div_add_mod (ofs (State.addr B) x - hdr) (S w)
      rw [Nat.mul_comm] at this; omega_arith⟩
  have h1 : a * S w < (q + 1) * S w := by
    have : arr w a = hdr + a * S w := rfl
    rw [Nat.add_mul]; omega_arith
  have h2 : q * S w < (a + k) * S w := by
    have : arr w (a + k) = hdr + (a + k) * S w := rfl
    omega_arith
  have qa := Nat.lt_of_mul_lt_mul_right h1
  have qk := Nat.lt_of_mul_lt_mul_right h2
  have := hx (arr w q, S w) (by
    simp only [ranges, List.mem_append, List.mem_map]
    exact .inl ⟨q, hjs q (by omega_arith) qk, rfl⟩)
  simp only [arr] at this
  omega_arith

theorem tabJs_mem {j : Nat} (h1 : 22 ≤ j) (h2 : j < 22 + 27) : j ∈ tabJs := by
  simp only [tabJs, List.mem_range'_1]; omega_arith

theorem nT_le {W : Nat} (hw : 10 ≤ W) : aTab * 4 * (W + 2) + 4 * nT W ≤ 49 * (4 * (W + 2)) := by
  simp only [nT, aTab]; split <;> omega_arith

/-- The table: its first `nT W` words at the key array 22, written over the
arrays `tabJs`. -/
theorem table_ok {s : State} {B : BitVec 32} {Z W : Nat} (hw : Ws s B Z W nArr) (hW : 10 ≤ W) :
    WP isa (seqs table) s fun t => Ws t B Z W nArr ∧ Keep B W tabJs [] s.mem t.mem ∧
      (∀ j < nT W, w32 t.mem (State.addr B) (arr W aTab + 4 * j) = tabWord32 j) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hfit := hw.fits
  have hz : arr W aTab + 4 * nT W ≤ Z := by
    have := nT_le hW; simp only [arr, S, nArr, aTab] at *; omega_arith
  simp only [table, seqs]
  rw [List.append_assoc, List.append_assoc]
  refine WP.seq (ptr_ok hw (r := .r12) (by decide) (by decide) fun s1 p1 r1 m1 hw1 => ?_)
  refine WP.append (tabSteps_ok hw1 (o := arr W aTab) (a := 0) p1 256 (by decide)
    (by have := nT_le hW; simp only [nT] at hz; split at hz <;> omega_arith)) fun s2 ⟨e2, k2, O2⟩ => ?_
  have hw2 := hw1.rest k2
  -- `r1 := W ≥ 35`, and Z iff not.
  unfold bigW
  refine wp_subsC (op2_imm (by decide)) fun s3 u3 c3 => wp_movC (op2_imm (by decide)) fun s4 u4 c4 =>
    wp_adc (op2_imm (by decide)) fun s5 u5 => wp_cmp (op2_imm (by decide)) fun s6 f6 z6 => WP.block_nil ?_
  have k6 : Rest [.r1] s2 s6 := (u3.rest (by simp)).trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans
    (f6.rest _)))
  have m6 : s6.mem = s2.mem := by rw [f6.mem, u5.mem, u4.mem, u3.mem]
  have hw6 := hw2.rest k6
  have r16 : (s5.gpr .r1).toNat = if 35 ≤ W then 1 else 0 := by
    rw [u5.gpr, u4.gpr, c4, c3, hw2.r9]
    have : W < 2 ^ 32 := by have := hw.wle; omega_arith
    have e : (BitVec.ofNat 32 W).toNat = W := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]
    by_cases h : 35 ≤ W <;> simp [h, e]
  have z6' : s6.z = decide (W < 35) := by
    rw [z6]
    by_cases h : 35 ≤ W
    · have : s5.gpr .r1 = 1 := BitVec.eq_of_toNat_eq (by rw [r16]; simp [h])
      rw [this]; simp; omega_arith
    · have : s5.gpr .r1 = 0 := BitVec.eq_of_toNat_eq (by rw [r16]; simp [h])
      rw [this]; simp; omega_arith
  have O0 : Outside (State.addr B) (arr W aTab) (4 * 256) s.mem s6.mem := by rw [m6, ← m1]; simpa using O2
  have sp6 : s6.sp = s.sp ∧ s6.rd = s.rd ∧ s6.wr = s.wr :=
    ⟨by rw [k6.sp, k2.sp, r1.sp], by rw [k6.rd, k2.rd, r1.rd], by rw [k6.wr, k2.wr, r1.wr]⟩
  refine WP.ite (s6.z) rfl (fun hz6 => ?_) (fun hz6 => ?_)
  · -- `W < 35`: the first 256 words alone.
    have hW' : ¬ 35 ≤ W := by
      intro h; rw [z6'] at hz6; simp at hz6; omega_arith
    refine WP.block_nil ⟨hw6, keep_span (a := aTab) (k := 27) O0 (Nat.le_refl _) ?_ fun j h1 h2 => tabJs_mem h1 h2,
      fun j hj => ?_, sp6⟩
    · have := nT_le hW; simp only [nT, hW', ↓reduceIte, arr, S, aTab] at *; omega_arith
    · simp only [nT, hW', ↓reduceIte] at hj
      rw [m6]; simpa using e2 j hj
  · -- `W ≥ 35`: the other 256 words too.
    have hW' : 35 ≤ W := by
      rw [z6'] at hz6; simp at hz6; omega_arith
    have hz' : arr W aTab + 4 * 512 ≤ Z := by simpa [nT, hW'] using hz
    have := hw.nowrap
    refine ptr_ok hw6 (r := .r12) (by decide) (by decide) (rest := tabWrite 256 256)
      fun s7 p7 r7 m7 hw7 => ?_
    rw [← List.append_nil (tabWrite 256 256)]
    refine WP.append (tabSteps_ok hw7 (o := arr W aTab) (a := 256) p7 256 (by decide)
      (by simp only [nT, hW', ↓reduceIte] at hz; omega_arith)) fun s8 ⟨e8, k8, O8⟩ => WP.block_nil ?_
    have O1 : Outside (State.addr B) (arr W aTab) (4 * 512) s.mem s8.mem :=
      (O0.mono (Nat.le_refl _) (by omega_arith)).trans (by rw [m7] at O8; exact O8.mono (by omega_arith) (by omega_arith))
    refine ⟨hw7.rest k8, keep_span (a := aTab) (k := 27) O1 (Nat.le_refl _) ?_ fun j h1 h2 => tabJs_mem h1 h2,
      fun j hj => ?_, ⟨by rw [k8.sp, r7.sp, sp6.1], by rw [k8.rd, r7.rd, sp6.2.1], by rw [k8.wr, r7.wr, sp6.2.2]⟩⟩
    · simp only [arr, S, aTab]; omega_arith
    · simp only [nT, hW', ↓reduceIte] at hj
      rcases Nat.lt_or_ge j 256 with h | h
      · rw [O8.w32 (by omega_arith) (by omega_arith), m7, m6]; simpa using e2 j h
      · have := e8 (j - 256) (by omega_arith)
        rwa [show 256 + (j - 256) = j by omega_arith] at this

end VG.Proof.RsaKeyGen.Arm.Cand

end

end


/-! # A candidate on ARMv7: trial division by the table (`trialLoop_ok`)

`TO … k`: after `k` words of the table (`2 k` primes), `r11` holds whether
one of them divides `c` (`tr`), `r12` points at word `k` and `lr` counts the
words left.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen
open VG.Proof.Rsa (b2n)

/-- Whether one of the first `n` entries of the table divides `c`. -/
def tr (n c : Nat) : Bool := (List.range n).any fun i => c % tabEntry i == 0

theorem tr_succ (n c : Nat) : tr (n + 1) c = (tr n c || decide (c % tabEntry n = 0)) := by
  simp only [tr, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  congr 1

theorem trialStep_eq : trialStep =
    .seq (.block [.ldr .r10 .r12 0, .dp .add .r12 .r12 (.imm 4)])
      (.seq (.block (([.mov .r3 (.shifted .r10 .lsl 16), .mov .r3 (.shifted .r3 .lsr 16)] : List Instr) ++ entryS))
        (.seq (.loop (.block trialWord) .ne) (.seq (.block trialFlag)
          (.seq (.block (([.mov .r3 (.shifted .r10 .lsr 16)] : List Instr) ++ entryS))
            (.seq (.loop (.block trialWord) .ne) (.seq (.block trialFlag) (.block [.subs .lr .lr (.imm 1)]))))))) :=
  rfl

/-- After `k` words of the table in `m`, for `c` the `W − 2` words at the key
array `aC`. -/
structure TO (B : BitVec 32) (Z W : Nat) (m : Mem) (u₀ : State) (k : Nat) (u : State) : Prop where
  ws : Ws u B Z W nArr
  mem : u.mem = m
  rest : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr] u₀ u
  r12 : u.gpr .r12 = B + BitVec.ofNat 32 (arr W aTab + 4 * k)
  lr : u.gpr .lr = BitVec.ofNat 32 (nT W - k)
  r11 : u.gpr .r11 = BitVec.ofNat 32 (b2n (tr (2 * k) (val32 m (State.addr B) (arr W aC) (W - 2))))

theorem w32_ofNat {m : Mem} {a : Addr} {x : Nat} (h : (m.readW a 32).toNat = x) : m.readW a 32 = BitVec.ofNat 32 x :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, ← h, Nat.mod_eq_of_lt (m.readW a 32).isLt])

/-- Word `k` of the table: its two primes. -/
theorem trialStep_ok {B : BitVec 32} {Z W : Nat} {m : Mem} {u₀ u : State} {k : Nat}
    (h : TO B Z W m u₀ k u) (hk : k < nT W) (hW : 10 ≤ W) (hWe : W % 2 = 0) (hZ : arr W nArr ≤ Z)
    (tab : ∀ j < nT W, w32 m (State.addr B) (arr W aTab + 4 * j) = tabWord32 j) :
    WP isa trialStep u fun u' => TO B Z W m u₀ (k + 1) u' ∧ u'.z = decide (nT W - (k + 1) = 0) := by
  obtain ⟨hw, mem, rest, r12, lr, r11⟩ := h
  have hn := hw.nowrap
  have hWl := hw.wle
  have hk512 : k < 512 := by simp only [nT] at hk; split at hk <;> omega_arith
  have hz : arr W aTab + 4 * nT W ≤ Z := by
    have := nT_le hW; simp only [arr, S, nArr, aTab] at *; omega_arith
  have hzc : arr W aC + 4 * W ≤ Z := by simp only [arr, S, nArr, aC] at *; omega_arith
  set c := val32 m (State.addr B) (arr W aC) (W - 2) with ec
  have ea : State.addr (u.gpr .r12 + BitVec.ofNat 32 0) = off (State.addr B) (arr W aTab + 4 * k) := by
    rw [r12, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hw.addr (by omega_arith)
  have rd : InRegions (u.rd ++ u.wr) (off (State.addr B) (arr W aTab + 4 * k)) 4 := hw.read (by omega_arith)
  have tk : u.mem.readW (off (State.addr B) (arr W aTab + 4 * k)) 32 = BitVec.ofNat 32 (tabWord32 k) :=
    w32_ofNat (by rw [mem]; exact tab k hk)
  have e0 := tabEntry_facts (i := 2 * k) (by omega_arith)
  have e1 := tabEntry_facts (i := 2 * k + 1) (by omega_arith)
  rw [trialStep_eq]
  refine WP.seq (wp_ldr (by decide) ea rd fun u1 v1 => wp_dp (op2_imm (by decide)) fun u2 v2 => WP.block_nil ?_)
  have k2 : Rest [.r10, .r12] u u2 := (v1.rest (by simp)).trans (v2.rest (by simp))
  have r10 : u2.gpr .r10 = BitVec.ofNat 32 (tabWord32 k) := by rw [v2.other _ (by decide), v1.gpr, tk]
  have r12' : u2.gpr .r12 = B + BitVec.ofNat 32 (arr W aTab + 4 * (k + 1)) := by
    rw [v2.gpr, dpVal, v1.other _ (by decide), r12, BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
      ← BitVec.ofNat_add]
    congr 2
  have hw2 := hw.rest k2
  -- The first prime.
  refine WP.seq ?_
  refine WP.block_append (wp_mov (op2_lsl (by decide)) fun u3 v3 => wp_mov (op2_lsr (by decide)) fun u4 v4 =>
    WP.block_nil ?_)
  have k4 : Rest [.r3] u2 u4 := (v3.rest (by simp)).trans (v4.rest (by simp))
  have r34 : u4.gpr .r3 = BitVec.ofNat 32 (tabEntry (2 * k)) := by
    apply BitVec.eq_of_toNat_eq
    rw [v4.gpr, v3.gpr, lo16, r10, ofNat_toNat_lt (tabWord32_lt hk512), tabWord32_lo hk512,
      ofNat_toNat_lt (by omega_arith)]
  refine prime_ok (f := tr (2 * k) c) (hw2.rest k4) (by omega_arith) hWe hzc (by rw [v4.mem, v3.mem, v2.mem, v1.mem, mem]) r34
    ⟨e0.1, e0.2.1, e0.2.2⟩ (ninv_tab (by omega_arith)) (by rw [k4.gpr _ (by decide), k2.gpr _ (by decide), r11])
    fun u5 k5 m5 r115 => ?_
  -- The second prime.
  refine WP.seq ?_
  refine WP.block_append (wp_mov (op2_lsr (by decide)) fun u6 v6 => WP.block_nil ?_)
  have k6 : Rest [.r3] u5 u6 := v6.rest (by simp)
  have r36 : u6.gpr .r3 = BitVec.ofNat 32 (tabEntry (2 * k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [v6.gpr, hi16, k5.gpr _ (by decide), k4.gpr _ (by decide), r10, ofNat_toNat_lt (tabWord32_lt hk512),
      tabWord32_hi hk512, ofNat_toNat_lt (by omega_arith)]
  have hw5 : Ws u5 B Z W nArr := (hw2.rest k4).rest k5
  refine prime_ok (f := tr (2 * k) c || decide (c % tabEntry (2 * k) = 0)) (hw5.rest k6) (by omega_arith) hWe hzc
    (by rw [v6.mem, m5]) r36 ⟨e1.1, e1.2.1, e1.2.2⟩ (ninv_tab (by omega_arith)) (by rw [k6.gpr _ (by decide), r115])
    fun u7 k7 m7 r117 => ?_
  -- The count.
  refine wp_subs (op2_imm (by decide)) fun u8 v8 z8 => WP.block_nil ?_
  have kall : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr] u u8 :=
    (k2.mono (by simp)).trans ((k4.mono (by simp)).trans ((k5.mono (by simp)).trans ((k6.mono (by simp)).trans
      ((k7.mono (by simp)).trans (v8.rest (by simp))))))
  have lr8 : u8.gpr .lr = BitVec.ofNat 32 (nT W - (k + 1)) := by
    rw [v8.gpr, k7.gpr _ (by decide), k6.gpr _ (by decide), k5.gpr _ (by decide), k4.gpr _ (by decide),
      k2.gpr _ (by decide), lr]
    apply BitVec.eq_of_toNat_eq
    have : nT W ≤ 512 := by simp only [nT]; split <;> omega_arith
    rw [BitVec.toNat_sub, ofNat_toNat_lt (by omega_arith), ofNat_toNat_lt (by omega_arith)]
    simp only [show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  refine ⟨⟨hw.rest kall, by rw [v8.mem, m7], rest.trans kall, ?_, lr8, ?_⟩, ?_⟩
  · rw [v8.other _ (by decide), k7.gpr _ (by decide), k6.gpr _ (by decide), k5.gpr _ (by decide),
      k4.gpr _ (by decide), r12']
  · rw [v8.other _ (by decide), r117, show 2 * (k + 1) = 2 * k + 1 + 1 by omega_arith, tr_succ, tr_succ]
  · rw [z8, ← v8.gpr, lr8]
    have : nT W ≤ 512 := by simp only [nT]; split <;> omega_arith
    by_cases h0 : nT W - (k + 1) = 0
    · simp [h0]
    · have : (BitVec.ofNat 32 (nT W - (k + 1))) ≠ 0 := fun e => h0 (by
        have := congrArg BitVec.toNat e; rw [ofNat_toNat_lt (by omega_arith)] at this; simpa using this)
      simpa [h0] using this

/-- All the words of the table. -/
theorem trialLoop_ok {B : BitVec 32} {Z W : Nat} {m : Mem} {u₀ u : State}
    (h : TO B Z W m u₀ 0 u) (hW : 10 ≤ W) (hWe : W % 2 = 0) (hZ : arr W nArr ≤ Z)
    (tab : ∀ j < nT W, w32 m (State.addr B) (arr W aTab + 4 * j) = tabWord32 j) :
    WP isa (.loop trialStep .ne) u (TO B Z W m u₀ (nT W)) := by
  have hT : 0 < nT W := by simp only [nT]; split <;> omega_arith
  refine WP.loop (M := isa) (fun n v => 0 < n ∧ n ≤ nT W ∧ TO B Z W m u₀ (nT W - n) v)
    (fun n v ⟨hn, hn2, hu⟩ => ?_) (nT W) u ⟨hT, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  refine WP.mono (trialStep_ok hu (by omega_arith) hW hWe hZ tab) fun u' ⟨hu', z⟩ => ?_
  rw [isa_ne, z]
  by_cases h0 : n = 1
  · subst h0
    refine .inl ⟨by simp; omega_arith, ?_⟩
    rwa [show nT W - 1 + 1 = nT W by omega_arith] at hu'
  · refine .inr ⟨by simp; omega_arith, n - 1, by omega_arith, by omega_arith, by omega_arith, ?_⟩
    rwa [show nT W - n + 1 = nT W - (n - 1) by omega_arith] at hu'

end VG.Proof.RsaKeyGen.Arm.Cand
