module

import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MlKem.X86_64.SampleLoop
import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.Sha3.X86_64.X4.Wp
public import VerifiedGarbage.Impl.MlKem.X86_64.Sample4
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.X86_64.Words

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the vector sampling

Eight iterations of `SampleNTT`'s loop, from fewer than 241 coefficients,
append the candidates less than `q` of their two halves of 12 bytes
(`sampleAfter_eight`). The candidates of a half (`cand4`, `candN`), the
mask of those less than `q` (`bsum`) and the order of its set bits
(`setBits_bsum`), and the steps of the vector code that `S4Wide` and the
AVX2 decoding use.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- Candidate `k < 8` of the four chunks of `out` from byte `p`: `d₁` (`k`
even) or `d₂` (`k` odd) of chunk `k / 2`. -/
def cand4 (out : Nat → Byte) (p k : Nat) : Nat :=
  if k % 2 = 0 then (out (p + 3 * (k / 2))).toNat + 256 * ((out (p + 3 * (k / 2) + 1)).toNat % 16)
  else (out (p + 3 * (k / 2) + 1)).toNat / 16 + 16 * (out (p + 3 * (k / 2) + 2)).toNat

/-- The candidates less than `q` of the four chunks from byte `p`, as coefficients. -/
def acc4 (out : Nat → Byte) (p : Nat) : List Zq :=
  ((List.range 8).filter fun k => decide (cand4 out p k < q)).map fun k => ofNat (cand4 out p k)

/-- The coefficients a chunk adds, if there is room for two. -/
def pair (c₀ c₁ c₂ : Byte) : List Zq :=
  (if c₀.toNat + 256 * (c₁.toNat % 16) < q then [ofNat (c₀.toNat + 256 * (c₁.toNat % 16))] else []) ++
    (if c₁.toNat / 16 + 16 * c₂.toNat < q then [ofNat (c₁.toNat / 16 + 16 * c₂.toNat)] else [])

theorem pair_length (c₀ c₁ c₂ : Byte) : (pair c₀ c₁ c₂).length ≤ 2 := by
  unfold pair; split <;> split <;> simp

theorem sampleStepCap_room {a : List Zq} (h : a.length + 2 ≤ n) (c₀ c₁ c₂ : Byte) :
    sampleStepCap a c₀ c₁ c₂ = a ++ pair c₀ c₁ c₂ := by
  unfold sampleStepCap sampleStep pair
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by bdd_omega))]
  dsimp only
  split <;> split <;> simp_all <;> omega

theorem fm2 {α : Type} (p : Nat → Bool) (f : Nat → α) (k : Nat) :
    ([k, k + 1].filter p).map f = (if p k then [f k] else []) ++ (if p (k + 1) then [f (k + 1)] else []) := by
  simp only [List.filter_cons, List.filter_nil]
  cases p k <;> cases p (k + 1) <;> rfl

theorem acc4_eq (out : Nat → Byte) (p : Nat) : acc4 out p =
    pair (out p) (out (p + 1)) (out (p + 2)) ++ pair (out (p + 3)) (out (p + 4)) (out (p + 5)) ++
      pair (out (p + 6)) (out (p + 7)) (out (p + 8)) ++ pair (out (p + 9)) (out (p + 10)) (out (p + 11)) := by
  rw [acc4, show List.range 8 = [0, 0 + 1] ++ [2, 2 + 1] ++ [4, 4 + 1] ++ [6, 6 + 1] from rfl]
  simp only [List.filter_append, List.map_append, fm2, decide_eq_true_eq, pair, cand4]
  simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul, ite_true, Nat.add_zero, Nat.add_assoc,
    Nat.zero_add, show (1 % 2 = 0) = False from by decide, ite_false, List.append_assoc, decide_eq_true_eq]

theorem sampleAfter_four {a : List Zq} {out : Nat → Byte} {t : Nat}
    (h : (sampleAfter a out t).length + 8 ≤ n) :
    sampleAfter a out (t + 4) = sampleAfter a out t ++ acc4 out (3 * t) := by
  have p0 := pair_length (out (3 * t)) (out (3 * t + 1)) (out (3 * t + 2))
  have p1 := pair_length (out (3 * (t + 1))) (out (3 * (t + 1) + 1)) (out (3 * (t + 1) + 2))
  have p2 := pair_length (out (3 * (t + 2))) (out (3 * (t + 2) + 1)) (out (3 * (t + 2) + 2))
  rw [sampleAfter_succ, sampleAfter_succ, sampleAfter_succ, sampleAfter_succ,
    sampleStepCap_room (a := sampleAfter a out t) (by bdd_omega),
    sampleStepCap_room (a := sampleAfter a out t ++ _) (by simp only [List.length_append]; omega),
    sampleStepCap_room (a := sampleAfter a out t ++ _ ++ _) (by simp only [List.length_append]; omega),
    sampleStepCap_room (a := sampleAfter a out t ++ _ ++ _ ++ _) (by simp only [List.length_append]; omega),
    acc4_eq]
  simp only [List.append_assoc, show 3 * (t + 1) = 3 * t + 3 by bdd_omega, show 3 * (t + 2) = 3 * t + 6 by bdd_omega,
    show 3 * (t + 3) = 3 * t + 9 by bdd_omega, Nat.add_assoc, Nat.reduceAdd]

theorem acc4_length (out : Nat → Byte) (p : Nat) : (acc4 out p).length ≤ 8 := by
  unfold acc4; rw [List.length_map]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem sampleAfter_eight {a : List Zq} {out : Nat → Byte} {t : Nat}
    (h : (sampleAfter a out t).length + 16 ≤ n) :
    sampleAfter a out (t + 8) = sampleAfter a out t ++ acc4 out (3 * t) ++ acc4 out (3 * t + 12) := by
  have e4 := sampleAfter_four (a := a) (out := out) (t := t) (by omega)
  have l := acc4_length out (3 * t)
  rw [show t + 8 = (t + 4) + 4 by omega, sampleAfter_four (by rw [e4, List.length_append]; omega), e4,
    show 3 * (t + 4) = 3 * t + 12 by omega]

end VG.Proof.MlKem

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Spec.MlKem

/-- The coefficients `L ++ A` are stored after a write of eight coefficients
`V` at `a[|L|]`, whose first `|A|` are `A`. -/
theorem stored_write8 {w16 : Bool} {m : Mem} {aP : Addr} {L A : List Zq} (h : Stored w16 m aP L)
    (hl : L.length + 8 ≤ 256) (hA : A.length ≤ 8) (V : BitVec (8 * cw w16))
    (hV : ∀ i < A.length, (V.extractLsb' (cw w16 * i) (cw w16)).toNat = (A.getD i 0).val) :
    Stored w16 (m.writeW (cAddr w16 aP L.length) V) aP (L ++ A) := by
  intro k hk
  rw [List.length_append] at hk
  rw [coeffAtW_eq]
  have hb := cw_bytes w16
  have e8 : cw w16 = 8 * (cw w16 / 8) := by cases w16 <;> rfl
  by_cases hkL : k < L.length
  · have := readW_writeW_off m aP V (d := cw w16 / 8 * k) (e := cw w16 / 8 * L.length) (n := cw w16 / 8)
      (by cases w16 <;> simp only [cw, Bool.false_eq_true, ↓reduceIte] <;> bdd_omega)
      (by cases w16 <;> simp only [cw, Bool.false_eq_true, ↓reduceIte] <;> bdd_omega)
      (by cases w16 <;> simp only [cw, Bool.false_eq_true, ↓reduceIte] <;> bdd_omega)
    rw [← e8] at this
    rw [this, show (L ++ A).getD k 0 = L.getD k 0 by simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hkL]]
    exact h k hkL
  · have e := readW_writeW_inside m (cAddr w16 aP L.length) V (k := cw w16 / 8 * (k - L.length)) (n := cw w16 / 8)
      (by cases w16 <;> simp only [cw, Bool.false_eq_true, ↓reduceIte] <;> bdd_omega) (by cases w16 <;> decide)
    rw [← e8, cAddr, Offset.add_add, show cw w16 / 8 * L.length + cw w16 / 8 * (k - L.length) = cw w16 / 8 * k by
      rw [← Nat.mul_add]; congr 1; bdd_omega] at e
    rw [e, show 8 * (cw w16 / 8 * (k - L.length)) = cw w16 * (k - L.length) by rw [← Nat.mul_assoc, ← e8],
      hV _ (by bdd_omega), show (L ++ A).getD k 0 = A.getD (k - L.length) 0 by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show L.length ≤ k by bdd_omega)]]

end VG.Proof.MlKem.X86_64

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64
open VG.Impl.MlKem.X86_64.Sample4 (setBits)
open VG.Proof.Sha3.X86_64 (WP.cons Upd)

def shuf0 : BitVec 128 := 0x80800504808004038080020180800100#128
def shuf1 : BitVec 128 := 0x80800b0a80800a098080080780800706#128
def shV : BitVec 128 := 0x00000004000000000000000400000000#128
def maskV : BitVec 128 := 0x00000fff00000fff00000fff00000fff#128

/-- The first byte of candidate `k`'s pair: `3 (k / 2) + k % 2`. -/
abbrev cb (k : Nat) : Nat := 3 * (k / 2) + k % 2

/-- Candidate `k` of the bytes `b`. -/
def candN (b : Nat → Nat) (k : Nat) : Nat :=
  if k % 2 = 0 then b (cb k) + 256 * (b (cb k + 1) % 16) else b (cb k) / 16 + 16 * b (cb k + 1)

theorem gb {f : Nat → BitVec 8} {a b c d : Nat} (h1 : a = c) (h2 : b = d) :
    (f a).getLsbD b = (f c).getLsbD d := by subst h1 h2; rfl

theorem toNat_dword_ofBytes (f : Nat → BitVec 8) {j : Nat} (hj : j < 4) :
    (dword (ofBytes f) j).toNat = (f (4 * j)).toNat + 256 * (f (4 * j + 1)).toNat +
      65536 * (f (4 * j + 2)).toNat + 16777216 * (f (4 * j + 3)).toNat := by
  have e : dword (ofBytes f) j = f (4 * j + 3) ++ f (4 * j + 2) ++ f (4 * j + 1) ++ f (4 * j) := by
    apply BitVec.eq_of_getLsbD_eq; intro m hm
    rw [getLsbD_dword_ofBytes _ hj hm]
    simp only [BitVec.getLsbD_append]
    have h8 := Nat.mod_lt m (show 8 > 0 by decide)
    by_cases a : m < 8
    · simp only [a, ite_true]; exact gb (by bdd_omega) (by bdd_omega)
    by_cases b : m - 8 < 8
    · simp only [a, b, ite_true, ite_false]; exact gb (by bdd_omega) (by bdd_omega)
    by_cases c : m - 8 - 8 < 8
    · simp only [a, b, c, ite_true, ite_false]; exact gb (by bdd_omega) (by bdd_omega)
    · simp only [a, b, c, ite_false]; exact gb (by bdd_omega) (by bdd_omega)
  rw [e]
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (f (4 * j + 2)).isLt, ← Nat.shiftLeft_add_eq_or_of_lt (f (4 * j + 1)).isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt (f (4 * j)).isLt]
  simp only [Nat.shiftLeft_eq]
  have := (f (4 * j)).isLt; have := (f (4 * j + 1)).isLt; have := (f (4 * j + 2)).isLt
  have := (f (4 * j + 3)).isLt
  omega

theorem pshufb_shuf0 (a : BitVec 128) : XBinOp.eval .pshufb a shuf0 =
    ofBytes fun i => if i % 4 < 2 then byte a (cb (i / 4) + i % 4) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem pshufb_shuf1 (a : BitVec 128) : XBinOp.eval .pshufb a shuf1 =
    ofBytes fun i => if i % 4 < 2 then byte a (6 + cb (i / 4) + i % 4) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

/-- The `vpshufb` mask of lane `l`. -/
abbrev shuf (l : Nat) : BitVec 128 := if l = 0 then shuf0 else shuf1

/-- The candidates in lane `l` of `ymm0`, from `a`, the 16 bytes in both. -/
abbrev candV (a : BitVec 128) (l : Nat) : BitVec 128 :=
  XBinOp.eval .pand (VVarOp.eval .vpsrlvd (XBinOp.eval .pshufb a (shuf l)) shV) maskV

theorem toNat_and_fff (x : BitVec 32) : (x &&& 0xfff#32).toNat = x.toNat % 4096 := by
  rw [BitVec.toNat_and, show (0xfff#32).toNat = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The value of an even candidate from its two bytes. -/
theorem cand_lo {x y : Nat} (hx : x < 256) (_hy : y < 256) :
    (x + 256 * y) / 2 ^ 0 % 4096 = (x + 256 * (y % 16)) % 2 ^ 32 := by
  omega

/-- The value of an odd candidate from its two bytes. -/
theorem cand_hi {x y : Nat} (hx : x < 256) (hy : y < 256) :
    (x + 256 * y) / 2 ^ 4 % 4096 = (x / 16 + 16 * y) % 2 ^ 32 := by
  omega

theorem cand_dword (a : BitVec 128) {l j : Nat} (hl : l < 2) (hj : j < 4) :
    dword (candV a l) j = BitVec.ofNat 32 (candN (fun i => (byte a i).toNat) (4 * l + j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [dword_pand, (show ∀ i < 4, dword maskV i = 0xfff#32 by decide) j hj, toNat_and_fff]
  have hb : ∀ i, (byte a i).toNat < 256 := fun i => (byte a i).isLt
  rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rcases cases4 hj with rfl | rfl | rfl | rfl <;>
  simp only [shuf, VVarOp.eval, pshufb_shuf0, pshufb_shuf1, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, ↓reduceIte, show (dword shV 0).toNat = 0 from rfl, show (dword shV 1).toNat = 4 from rfl,
    show (dword shV 2).toNat = 0 from rfl, show (dword shV 3).toNat = 4 from rfl, Nat.reduceLT,
    BitVec.toNat_ushiftRight,
    toNat_dword_ofBytes _ (show 0 < 4 by decide), toNat_dword_ofBytes _ (show 1 < 4 by decide),
    toNat_dword_ofBytes _ (show 2 < 4 by decide), toNat_dword_ofBytes _ (show 3 < 4 by decide),
    candN, cb, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show (0 : BitVec 8).toNat = 0 from rfl, Nat.reduceEqDiff, Nat.add_zero] <;>
  first | exact cand_lo (hb _) (hb _) | exact cand_hi (hb _) (hb _)

def qV4 : BitVec 128 := 0x00000d0100000d0100000d0100000d01#128
/-- `∑ i < n, f i · 2ⁱ`. -/
def bsum (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => bsum f n + (f n).toNat * 2 ^ n

theorem bsum_lt (f : Nat → Bool) : ∀ n, bsum f n < 2 ^ n
  | 0 => by simp [bsum]
  | n + 1 => by
    have := bsum_lt f n
    simp only [bsum, Nat.pow_succ]
    cases f n <;> simp <;> omega

theorem byteMask_eq (x : BitVec 256) {n : Nat} (hn : n ≤ 64) :
    byteMask x n = BitVec.ofNat 64 (bsum (fun i => x.getLsbD (8 * i + 7)) n) := by
  unfold byteMask
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih (by bdd_omega), List.foldl_cons, List.foldl_nil, bsum]
    have hl := bsum_lt (fun i => x.getLsbD (8 * i + 7)) n
    have h1 : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by bdd_omega)
    cases x.getLsbD (8 * n + 7)
    · simp
    · simp only [ite_true, Bool.toNat_true, Nat.one_mul]
      apply BitVec.eq_of_toNat_eq
      have h2 : 2 ^ n ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by bdd_omega)
      have e := Nat.two_pow_add_eq_or_of_lt hl 1
      rw [Nat.mul_one] at e
      rw [BitVec.toNat_or, BitVec.toNat_twoPow, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
        Nat.mod_eq_of_lt (by bdd_omega), Nat.mod_eq_of_lt (by bdd_omega), Nat.or_comm, ← e, Nat.add_comm]

theorem bsum_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = g i) : bsum f n = bsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bsum, bsum, ih fun i hi => h i (by bdd_omega), h n (by bdd_omega)]

theorem itT {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem itF {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

theorem bsum_add (f : Nat → Bool) (n : Nat) :
    ∀ m, bsum f (n + m) = bsum f n + 2 ^ n * bsum (fun i => f (n + i)) m
  | 0 => by rw [Nat.add_zero, bsum, Nat.mul_zero, Nat.add_zero]
  | m + 1 => by
    rw [← Nat.add_assoc, bsum, bsum_add f n m, bsum, Nat.pow_add, Nat.mul_add, Nat.add_assoc, Nat.mul_left_comm]

theorem dword_qV4 {j : Nat} (hj : j < 4) : dword qV4 j = 3329#32 := by
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl

theorem ext_app2 (h l : BitVec 128) {i : Nat} (hi : i < 8) :
    (h ++ l).extractLsb' (32 * i) 32 = dword (if i < 4 then l else h) (i % 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', getLsbD_dword, hj, decide_true, Bool.true_and, BitVec.getLsbD_append]
  by_cases h4 : i < 4
  · rw [itT (show 32 * i + j < 128 by bdd_omega), itT h4]; exact congrArg _ (by bdd_omega)
  · rw [itF (show ¬ 32 * i + j < 128 by bdd_omega), itF h4]; exact congrArg _ (by bdd_omega)

/-- `s'` is `s` with the two lanes of `d` set to `v 0` and `v 1` (flags aside). -/
structure LUpd (s s' : State) (d : XReg) (v : Nat → BitVec 128) : Prop where
  val : ∀ l < 2, s'.lane d l = v l
  other : ∀ r, r ≠ d → ∀ l < 2, s'.lane r l = s.lane r l
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms

theorem LUpd.setV256 (s : State) (d : XReg) (lo hi : BitVec 128) :
    LUpd s (s.setV .l256 d lo hi) d fun l => if l = 0 then lo else hi :=
  ⟨fun l _ => by rw [State.lane_setV256, ite_eq_left rfl], fun r hr l _ => by rw [State.lane_setV256, ite_eq_right hr],
    rfl, rfl, rfl, rfl, rfl⟩

theorem LUpd.setV128 (s : State) (d : XReg) (lo hi : BitVec 128) :
    LUpd s (s.setV .l128 d lo hi) d fun l => if l = 0 then lo else 0 :=
  ⟨fun l _ => by rw [State.lane_setV128, ite_eq_left rfl], fun r hr l _ => by rw [State.lane_setV128, ite_eq_right hr],
    rfl, rfl, rfl, rfl, rfl⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_vbin {op : VBinOp} {d a b : XReg}
    (k : ∀ s', LUpd s s' d (fun l => op.sse.eval (s.lane a l) (s.lane b l)) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vbin op .l256 d a b) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1)))
    rfl (k _ (by
    have h := LUpd.setV256 s d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1))
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩))

theorem wp_vvar {op : VVarOp} {d a b : XReg}
    (k : ∀ s', LUpd s s' d (fun l => op.eval (s.lane a l) (s.lane b l)) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vvar op .l256 d a b) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (op.eval (s.lane a 0) (s.lane b 0)) (op.eval (s.lane a 1) (s.lane b 1)))
    rfl (k _ (by
    have h := LUpd.setV256 s d (op.eval (s.lane a 0) (s.lane b 0)) (op.eval (s.lane a 1) (s.lane b 1))
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩))

theorem wp_vpbcastd {d a : XReg}
    (k : ∀ s', LUpd s s' d (fun _ => let v := dword (s.lane a 0) 0; ofDwords v v v v) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpbroadcastd .l256 d a) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (let v := dword (s.xmm a) 0; ofDwords v v v v)
      (let v := dword (s.xmm a) 0; ofDwords v v v v)) rfl (k _ (by
    have h := LUpd.setV256 s d (let v := dword (s.xmm a) 0; ofDwords v v v v)
      (let v := dword (s.xmm a) 0; ofDwords v v v v)
    exact ⟨fun l hl => by rw [h.val l hl]; split <;> rfl, h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩))

theorem wp_vpermd {d i a : XReg}
    (k : ∀ s', LUpd s s' d (fun l => (permDwords (s.ymm i) (s.ymm a)).extractLsb' (128 * l) 128) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpermd d i a) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 0 128)
      ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 128 128)) rfl (k _ (by
    have h := LUpd.setV256 s d ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 0 128)
      ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 128 128)
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩))

theorem wp_vbcast128 {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', LUpd s s' d (fun _ => s.mem.readW a 128) → WP isa (.block is) s' Q) :
    WP isa (.block (.vbroadcasti128 d m :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d (s.mem.readW a 128) (s.mem.readW a 128))
    (by simp [exec, ha, State.load128, hin]) (k _ ?_)
  have h := LUpd.setV256 s d (s.mem.readW a 128) (s.mem.readW a 128)
  exact ⟨fun l hl => by rw [h.val l hl]; split <;> rfl, h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩

theorem wp_vld256 {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 32)
    (k : ∀ s', LUpd s s' d (fun l => (s.mem.readW a 256).extractLsb' (128 * l) 128) → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquLoad .l256 d m :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d ((s.mem.readW a 256).extractLsb' 0 128)
    ((s.mem.readW a 256).extractLsb' 128 128)) (by simp [exec, ha, State.load256, hin]) (k _ ?_)
  have h := LUpd.setV256 s d ((s.mem.readW a 256).extractLsb' 0 128) ((s.mem.readW a 256).extractLsb' 128 128)
  exact ⟨fun l hl => by rw [h.val l hl]; rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
    h.other, h.gpr, h.mem, h.rd, h.wr, h.syms⟩

theorem wp_vst256 {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 32)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x l, s'.lane x l = s.lane x l) → s'.mem = s.mem.writeW a (s.ymm r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquStore .l256 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.ymm r) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl)
  simp [exec, State.store256, ha, hout]

theorem wp_vst128 {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x l, s'.lane x l = s.lane x l) → s'.mem = s.mem.writeW a (s.xmm r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquStore .l128 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.xmm r) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl)
  simp [exec, State.store128, ha, hout]

/-- `wp_vst128`, keeping the statics' addresses. -/
theorem wp_vst128s {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x l, s'.lane x l = s.lane x l) → s'.mem = s.mem.writeW a (s.xmm r) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquStore .l128 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.xmm r) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl rfl)
  simp [exec, State.store128, ha, hout]

theorem wp_vbin128 {op : VBinOp} {d a b : XReg}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then op.sse.eval (s.lane a 0) (s.lane b 0) else 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vbin op .l128 d a b) :: is)) s Q :=
  WP.cons (s' := s.setV .l128 d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1)))
    rfl (k _ (LUpd.setV128 s d _ _))

theorem wp_vext128 {d r : XReg}
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then s.lane r 1 else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vextracti128 d r 1) :: is)) s Q :=
  WP.cons (s' := s.setV .l128 d (s.lane r 1) 0) rfl (k _ (LUpd.setV128 s d _ _))

/-- `s'` is `s` with register `d` set to `v`, the vector registers as they were (flags aside). -/
structure GUpd (s s' : State) (d : Reg) (v : BitVec 64) : Prop extends Upd s s' d v where
  lane : ∀ x l, s'.lane x l = s.lane x l
  syms : s'.syms = s.syms

theorem GUpd.setReg (s : State) (d : Reg) (v : BitVec 64) : GUpd s (s.setReg d v) d v :=
  ⟨Upd.setReg s d v, fun _ _ => rfl, rfl⟩

theorem GUpd.withFlags (s : State) (cf o zf sf : Option Bool) (d : Reg) (v : BitVec 64) :
    GUpd s ((s.setFlags cf o zf sf).setReg d v) d v :=
  ⟨Upd.withFlags s cf o zf sf d v, fun _ _ => rfl, rfl⟩

theorem wp_vpmovmskb {d : Reg} {r : XReg}
    (k : ∀ s', GUpd s s' d (byteMask (s.ymm r) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.vpmovmskb .l256 d r :: is)) s Q :=
  WP.cons rfl (k _ (GUpd.setReg _ _ _))

theorem wp_addi' {d : Reg} {v : BitVec 32}
    (k : ∀ s', GUpd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (GUpd.withFlags _ _ _ _ _ _ _))

/-- `vmovdquTbl` of words `o` to `o + 3` of the static `name`. -/
theorem wp_vtbl {d : XReg} {m : MemOp} {name : String} {ws : List (BitVec 64)} {o : Nat}
    (hb : s.gpr m.base = s.syms name) (ho : (s.ea m - s.syms name).toNat = 8 * o) (hl : o + 4 ≤ ws.length)
    (k : ∀ s', LUpd s s' d (fun l => if l = 0 then ws.getD (o + 1) 0 ++ ws.getD o 0
      else ws.getD (o + 3) 0 ++ ws.getD (o + 2) 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquTbl d m name ws :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d (ws.getD (o + 1) 0 ++ ws.getD o 0) (ws.getD (o + 3) 0 ++ ws.getD (o + 2) 0))
    ?_ (k _ (LUpd.setV256 _ _ _ _))
  have h8 : 8 * o % 8 = 0 := by omega
  have hd : 8 * o / 8 = o := by omega
  simp only [exec, hb, ho, h8, hd, hl, and_self, ite_true, Nat.add_zero]

/-- `add d, QWORD PTR [m]` of word `o` of the static `name` (`aluTbl`). -/
theorem wp_addTbl {d : Reg} {m : MemOp} {name : String} {ws : List (BitVec 64)} {o : Nat}
    (hb : s.gpr m.base = s.syms name) (ho : (s.ea m - s.syms name).toNat = 8 * o) (hl : o < ws.length)
    (k : ∀ s', GUpd s s' d (s.gpr d + ws.getD o 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.aluTbl .add d m name ws :: is)) s Q := by
  let a := s.gpr d
  let b := ws.getD o 0
  refine WP.cons (s' := (arithFlags s (a + b) (2 ^ 64 ≤ a.toNat + b.toNat) (addOverflow a b (a + b))).setReg d
    (a + b)) ?_ (k _ (GUpd.withFlags _ _ _ _ _ _ _))
  have h8 : 8 * o % 8 = 0 := by omega
  have hd : 8 * o / 8 = o := by omega
  simp only [exec, hb, ho, h8, hd, hl, and_self, ite_true, execAluW, a, b]

end

/-! ## The candidates and their mask -/

theorem candN_lt (b : Nat → Nat) (hb : ∀ i, b i < 256) (k : Nat) : candN b k < 4096 := by
  unfold candN; have := hb (cb k); have := hb (cb k + 1); split <;> omega

/-- The mask of the candidates less than `q`. -/
abbrev maskN (b : Nat → Nat) : Nat := bsum (fun k => decide (candN b k < 3329)) 8

/-! ## The compaction -/

theorem bsum8_bit (f : Nat → Bool) {k : Nat} (hk : k < 8) : bsum f 8 / 2 ^ k % 2 = (f k).toNat := by
  have e : bsum f 8 = bsum f k + 2 ^ k * bsum (fun i => f (k + i)) (1 + (7 - k)) := by
    rw [← bsum_add, show k + (1 + (7 - k)) = 8 by bdd_omega]
  rw [e, bsum_add _ 1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt (bsum_lt f k),
    Nat.zero_add, Nat.pow_one, Nat.add_mul_mod_self_left]
  simp only [bsum, Nat.add_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  exact Nat.mod_eq_of_lt (Bool.toNat_lt _)

theorem setBits_bsum (f : Nat → Bool) : setBits (bsum f 8) = (List.range 8).filter f := by
  unfold setBits
  apply List.filter_congr
  intro k hk
  rw [bsum8_bit f (List.mem_range.mp hk)]
  cases f k <;> rfl

end VG.Proof.MlKem.X86_64.S4
