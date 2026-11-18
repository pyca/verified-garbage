module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Argon2.RISCV64.CompressLit
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
meta import VerifiedGarbage.Proof.Argon2.RISCV64.CompressLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Wp
meta import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Impl.Argon2.RISCV64.Compress
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Argon2.Spec
import VerifiedGarbage.Proof.Argon2.RISCV64.Ops
meta import VerifiedGarbage.Proof.Argon2.Contract
meta import VerifiedGarbage.Spec.Argon2
meta import VerifiedGarbage.TCB.Code
meta import VerifiedGarbage.Impl.Argon2.RISCV64.Compress
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Argon2.Spec
meta import VerifiedGarbage.Proof.Argon2.RISCV64.Ops

/-! ### `Argon2.RISCV64.Copy`, which this module and modules that import it used -/

section

/-! ### `Argon2.RISCV64.Rounds`, which this module and modules that import it used -/

section

/-! # Argon2 compression on RISC-V: the row and column permutations -/

@[expose] public section

/-! # Argon2's modified addition and GB on RISC-V registers -/

namespace VG.Proof.Argon2.RISCV64

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64
open VG.RISCV64.Wp (Upd WP.cons wp_add wp_xor)

theorem shr_or_shl (x : BitVec 64) {r : Nat} (hr : r < 64) :
    x >>> r ||| x <<< (64 - r) = x.rotateRight r := by
  simp only [BitVec.rotateRight, BitVec.rotateRightAux, Nat.mod_eq_of_lt hr]

theorem toNat_shl32 (a : BitVec 64) : (a <<< 32).toNat = a.toNat % 2 ^ 32 * 2 ^ 32 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := a.isLt
  rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by rw [← Nat.pow_add], Nat.mul_mod_mul_right]

theorem toNat_lo32 (a : BitVec 64) : (a &&& 0xffffffff).toNat = a.toNat % 2 ^ 32 := by
  rw [BitVec.toNat_and, show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- `mulhu` of the two low halves shifted up by 32 bits is their product. -/
theorem lo_mul (a b : BitVec 64) :
    BitVec.ofNat 64 ((a <<< 32).toNat * (b <<< 32).toNat / 2 ^ 64) =
      (a &&& 0xffffffff) * (b &&& 0xffffffff) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_mul, toNat_shl32, toNat_shl32, toNat_lo32, toNat_lo32]
  have e : a.toNat % 2 ^ 32 * 2 ^ 32 * (b.toNat % 2 ^ 32 * 2 ^ 32) =
      a.toNat % 2 ^ 32 * (b.toNat % 2 ^ 32) * 2 ^ 64 := by
    rw [Nat.mul_mul_mul_comm, ← Nat.pow_add]
  rw [e, Nat.mul_div_cancel _ (Nat.two_pow_pos 64)]

theorem addMul_value (a b : BitVec 64) :
    a + b + (a &&& 0xffffffff) * (b &&& 0xffffffff) + (a &&& 0xffffffff) * (b &&& 0xffffffff) =
      Spec.Argon2.addMul a b := by
  rw [Spec.Argon2.addMul, BitVec.mul_assoc]
  generalize (a &&& 0xffffffff) * (b &&& 0xffffffff) = p
  grind

end VG.Proof.Argon2.RISCV64

namespace VG.Proof.Argon2.RISCV64

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64 VG.Spec.Argon2
open VG.Proof.Argon2
open VG.RISCV64.Wp (Upd)

abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d
abbrev word (m : Mem) (p : Addr) (i : Nat) : BitVec 64 := m.readW (off p (1024 + 8 * i)) 64

/-- The permuted half of scratch. -/
def working (m : Mem) (p : Addr) : Block := Vector.ofFn fun i => word m p i.val

theorem working_get (m : Mem) (p : Addr) (i : Fin 128) :
    (working m p)[i] = word m p i.val := by
  simp only [working, Fin.getElem_fin, Vector.getElem_ofFn]

/-- Scratch permissions and its stable base register. -/
structure Scratch (s : State) (p : Addr) : Prop where
  reg : s.gpr .a3 = p
  wr : (⟨p, 4096⟩ : Region) ∈ s.wr
  al : p.toNat % 8 = 0

theorem Scratch.al_off {s : State} {p : Addr} (h : Scratch s p) {d : Nat} (hd : d % 8 = 0) :
    (s.gpr .a3 + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [h.reg]; exact Spill.al8 h.al hd

theorem Scratch.write {s : State} {p : Addr} (h : Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions s.wr (off p d) n :=
  ⟨_, h.wr, Offset.contains_base p hd (by omega_using [hd])⟩

theorem Scratch.read {s : State} {p : Addr} (h : Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions (s.rd ++ s.wr) (off p d) n :=
  ⟨_, List.mem_append_right _ h.wr, Offset.contains_base p hd (by omega_using [hd])⟩

theorem lane_injective : Function.Injective lane := by
  intro i j h
  revert i j
  decide

/-- The registers the rounds write. -/
abbrev roundRegs : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .a0, .a1, .a4, .a5, .a6, .a7, .s0, .s1, .s2, .s3, .s4, .t5, .t6, .s5]

theorem lane_mem (j : Fin 16) : lane j ∈ roundRegs := by revert j; decide

theorem lane_ne_r6 (j : Fin 16) : lane j ≠ .a3 := by revert j; decide
theorem word_offset (i : Nat) (hi : i < 128) : 1024 + 8 * i < 2048 := by
  omega_using [hi]

/-- A write changes exactly the selected word of the block. -/
theorem working_write (m : Mem) (p : Addr) (i : Fin 128) (v : Word) :
    working (m.writeW (off p (1024 + 8 * i.val)) v) p = (working m p).set i v := by
  apply Vector.ext
  intro j hj
  simp only [working, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : i.val = j
  · subst j
    simp only [ite_true, word, Mem.readW_writeW_self64]
  · simp only [h, ite_false, word]
    exact Mem.readW_writeW_sep
      (Offset.sep p (by omega_using [h]) (by omega_using [hj]) (by omega_using [])) (by decide)

/-- Load one word of the permuted block into its register. -/
theorem loadWord_ok (index : Fin 16 → Fin 128) (j : Fin 16) (s : State) {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block [loadWord index j]) s fun t =>
      t = s.write (lane j) (word s.mem p (index j).val) := by
  have ld := hs.read (d := 1024 + 8 * (index j).val) (n := 8) (by omega_using [])
  rw [← hs.reg] at ld
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (word_offset _ (index j).isLt) (hs.al_off (by omega_using [])) ld,
    WP.block_nil ?_⟩
  rw [hs.reg]

/-- Load the words `js` of a row or column, each into its own register. -/
theorem loads_ok (index : Fin 16 → Fin 128) (js : List (Fin 16)) (hn : js.Nodup)
    (s : State) {p : Addr} (hs : Scratch s p) :
    WP isa (.block (js.map (loadWord index))) s fun t =>
      (∀ j ∈ js, t.gpr (lane j) = word s.mem p (index j).val) ∧
      (∀ r, (∀ j ∈ js, lane j ≠ r) → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction js generalizing s with
  | nil =>
    exact WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons j js ih =>
    obtain ⟨hj, hn'⟩ := List.nodup_cons.mp hn
    rw [List.map_cons, ← List.singleton_append]
    apply WP.block_append
    refine (loadWord_ok index j s hs).mono ?_
    rintro s1 rfl
    have u := Upd.write s (lane j) (word s.mem p (index j).val)
    have hs1 : Scratch (s.write (lane j) (word s.mem p (index j).val)) p :=
      ⟨by rw [u.other _ (lane_ne_r6 j).symm, hs.reg], hs.wr, hs.al⟩
    refine (ih hn' _ hs1).mono ?_
    rintro t ⟨hl, hk, hm, hr, hw, hsp⟩
    refine ⟨?_, ?_, hm, hr, hw, hsp⟩
    · intro k hk'
      rcases List.mem_cons.mp hk' with rfl | hk'
      · rw [hk _ (fun i hi he => hj (by rw [← lane_injective he]; exact hi)), u.gpr]
      · exact hl k hk'
    · intro r hr
      rw [hk r (fun i hi => hr i (List.mem_cons_of_mem _ hi)),
        u.other _ (fun he => hr j (List.mem_cons_self ..) he.symm)]

/-- Store one register into its word of the permuted block. -/
theorem storeWord_ok (index : Fin 16 → Fin 128) (j : Fin 16) (s : State) {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block [storeWord index j]) s fun t =>
      t = { s with mem := s.mem.writeW (off p (1024 + 8 * (index j).val)) (s.gpr (lane j)) } := by
  have st := hs.write (d := 1024 + 8 * (index j).val) (n := 8) (by omega_using [])
  rw [← hs.reg] at st
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d (word_offset _ (index j).isLt) (hs.al_off (by omega_using [])) st,
    WP.block_nil ?_⟩
  rw [hs.reg]

/-- Store the registers of the words `js` of a row or column, in order. -/
theorem stores_ok (index : Fin 16 → Fin 128) (js : List (Fin 16)) (s : State) {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block (js.map (storeWord index))) s fun t =>
      working t.mem p =
        js.foldl (fun b j => b.set (index j) (s.gpr (lane j))) (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | cons j js ih =>
    rw [List.map_cons, ← List.singleton_append]
    apply WP.block_append
    refine (storeWord_ok index j s hs).mono ?_
    intro s1 h1
    have hs1 : Scratch s1 p := by subst h1; exact ⟨hs.reg, hs.wr, hs.al⟩
    refine (ih s1 hs1).mono ?_
    rintro t ⟨hw, hf, hg, hr, hwr, hsp⟩
    subst h1
    refine ⟨?_, ?_, hg, hr, hwr, hsp⟩
    · rw [hw, List.foldl_cons, working_write]
    · exact ((Frame.refl [⟨off p 1024, 1024⟩] s.mem).writeW (by simp) _
        (Offset.contains p (d := 1024 + 8 * (index j).val) (n := 8) (e := 1024) (k := 1024)
          (by omega_using []) (by omega_using []) (by omega_using []))).trans hf

/-- The sixteen words of a row or column, in their registers. -/
def InRegs (s : State) (v : Vector Word 16) : Prop := ∀ j : Fin 16, s.gpr (lane j) = v[j]

/-- Registers and permissions preserved throughout a scratch permutation. -/
def Keeps (s t : State) : Prop :=
  (∀ r, r ∉ roundRegs → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {s t u : State} (h : Keeps s t) (h' : Keeps t u) : Keeps s u :=
  ⟨fun r hr => (h'.1 r hr).trans (h.1 r hr),
    h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.trans h.2.2.2⟩

theorem Scratch.of_keeps {s t : State} {p : Addr} (hs : Scratch s p)
    (hk : Keeps s t) : Scratch t p :=
  ⟨(hk.1 .a3 (by decide)).trans hs.reg, hk.2.2.1 ▸ hs.wr, hs.al⟩

/-! ## P as lines, and as operations on nineteen slots

The code runs P's four column GBs side by side, then its four diagonal ones
(`step4`). P is proven on *lines*, half a GB step each
(`a ← addMul a b; d ← (d ⊕ a) ⋙ r`, `aline`): the spec's order of lines is
the code's after moving lines only past lines on other words (`LSame`,
decided); then on single operations (`Op`) on the sixteen words (slots 0–15),
`t5` (16), `t6` (17) and `s5` (18), each proven once (`op_ok`), whose order in the code
is that of the lines after moving operations only past operations on other
slots (`OSame`, decided). -/

/-- An index `i < 16` as a `Fin 16`. -/
def fin16 (i : Nat) : Fin 16 := ⟨i % 16, Nat.mod_lt _ (by decide)⟩

/-- A step of GB: `x[a] ← addMul x[a] x[b]; x[d] ← (x[d] ⊕ x[a]) ⋙ r`. -/
def aline (x : Vector Word 16) (a b d r : Nat) : Vector Word 16 :=
  let y := x.set (fin16 a) (addMul x[fin16 a] x[fin16 b])
  y.set (fin16 d) ((y[fin16 d] ^^^ y[fin16 a]).rotateRight r)

/-- The lines of a list in turn. -/
abbrev alines (l : List (Nat × Nat × Nat × Nat)) (v : Vector Word 16) : Vector Word 16 :=
  l.foldl (fun x (a, b, d, r) => aline x a b d r) v

theorem aline_get (x : Vector Word 16) {a b d r : Nat} (ha : a < 16) (hb : b < 16) (hd : d < 16) (had : a ≠ d)
    (m : Nat) (hm : m < 16) :
    (aline x a b d r)[m] =
      if d = m then (x[d] ^^^ addMul x[a] x[b]).rotateRight r else if a = m then addMul x[a] x[b] else x[m] := by
  simp only [aline, fin16, Vector.getElem_set, Fin.getElem_fin, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hd, had, ite_false, ite_true]

/-- A GB's lines. -/
def gbLines (a b c d : Nat) : List (Nat × Nat × Nat × Nat) :=
  [(a, b, d, 32), (c, d, b, 24), (a, b, d, 16), (c, d, b, 63)]

/-- P's lines in the spec's order. -/
def specLines : List (Nat × Nat × Nat × Nat) :=
  gbLines 0 4 8 12 ++ gbLines 1 5 9 13 ++ gbLines 2 6 10 14 ++ gbLines 3 7 11 15 ++
  gbLines 0 5 10 15 ++ gbLines 1 6 11 12 ++ gbLines 2 7 8 13 ++ gbLines 3 4 9 14

theorem permute_spec (v : Vector Word 16) : permute v = alines specLines v := rfl

/-- Lines `l` and `l'` touch disjoint words. -/
def LIndep : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Bool
  | (a, b, d, _), (a', b', d', _) =>
    decide (a < 16 ∧ b < 16 ∧ d < 16 ∧ a' < 16 ∧ b' < 16 ∧ d' < 16 ∧ a ≠ d ∧ a' ≠ d' ∧
      a ≠ a' ∧ a ≠ b' ∧ a ≠ d' ∧ b ≠ a' ∧ b ≠ d' ∧ d ≠ a' ∧ d ≠ b' ∧ d ≠ d')

theorem aline_comm {x : Vector Word 16} {a b d r a' b' d' r' : Nat}
    (h : LIndep (a, b, d, r) (a', b', d', r') = true) :
    aline (aline x a b d r) a' b' d' r' = aline (aline x a' b' d' r') a b d r := by
  simp only [LIndep, decide_eq_true_eq] at h
  obtain ⟨ha, hb, hd, ha', hb', hd', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  apply Vector.ext
  intro m hm
  have := Ne.symm h3; have := Ne.symm h4; have := Ne.symm h5; have := Ne.symm h6; have := Ne.symm h7
  have := Ne.symm h8; have := Ne.symm h9; have := Ne.symm h10
  simp only [aline_get, ha, hb, hd, ha', hb', hd', h1, h2, ne_eq, not_false_eq_true]
  by_cases e1 : d = m
  · subst e1; simp [*]
  by_cases e2 : a = m
  · subst e2; simp [*]
  by_cases e3 : d' = m
  · subst e3; simp [*]
  by_cases e4 : a' = m
  · subst e4; simp [*]
  simp [*]

/-- `l` without its first `p`, if every line before it touches other words. -/
def lpull (p : Nat × Nat × Nat × Nat) : List (Nat × Nat × Nat × Nat) → Option (List (Nat × Nat × Nat × Nat))
  | [] => none
  | q :: l => if q = p then some l else if LIndep q p then (lpull p l).map (q :: ·) else none

/-- `l'` runs the lines of `l`, each moved only past lines on other words. -/
def LSame : List (Nat × Nat × Nat × Nat) → List (Nat × Nat × Nat × Nat) → Bool
  | [], [] => true
  | p :: l', l => match lpull p l with
    | some r => LSame l' r
    | none => false
  | [], _ :: _ => false

theorem alines_cons (p : Nat × Nat × Nat × Nat) (l : List (Nat × Nat × Nat × Nat)) (v : Vector Word 16) :
    alines (p :: l) v = alines l (aline v p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  obtain ⟨a, b, d, r⟩ := p; rfl

theorem lpull_ok {p : Nat × Nat × Nat × Nat} :
    ∀ {l l₁ : List (Nat × Nat × Nat × Nat)}, lpull p l = some l₁ →
      ∀ v, alines l v = alines l₁ (aline v p.1 p.2.1 p.2.2.1 p.2.2.2)
  | [], _, h, _ => by simp [lpull] at h
  | q :: l, l₁, h, v => by
    unfold lpull at h
    by_cases e : q = p
    · subst e; simp only [ite_true, Option.some.injEq] at h; subst h; exact alines_cons _ _ _
    · simp only [e, ite_false] at h
      by_cases hq : LIndep q p = true
      · simp only [hq, ite_true] at h
        obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h
        rw [alines_cons, lpull_ok hl', alines_cons]
        obtain ⟨a, b, d, r⟩ := q; obtain ⟨a', b', d', r'⟩ := p
        exact congrArg _ (aline_comm hq)
      · simp only [hq, Bool.false_eq_true, ite_false, reduceCtorEq] at h

theorem lsame_ok : ∀ {l' l : List (Nat × Nat × Nat × Nat)}, LSame l' l = true → ∀ v, alines l' v = alines l v
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [LSame] at h
  | p :: l', l, h, v => by
    unfold LSame at h
    split at h
    · rename_i l₁ hl
      rw [alines_cons, lpull_ok hl, lsame_ok h]
    · simp at h

/-- P's GBs, as numbers. -/
def ncolumns : List (Nat × Nat × Nat × Nat) := [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15)]
def ndiagonals : List (Nat × Nat × Nat × Nat) := [(0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]

/-- The lines of four GBs as the code runs them: each step of the four in turn. -/
def roundLines (qs : List (Nat × Nat × Nat × Nat)) : List (Nat × Nat × Nat × Nat) :=
  qs.map (fun (a, b, _, d) => (a, b, d, 32)) ++ qs.map (fun (_, b, c, d) => (c, d, b, 24)) ++
  qs.map (fun (a, b, _, d) => (a, b, d, 16)) ++ qs.map (fun (_, b, c, d) => (c, d, b, 63))

theorem permute_lines (v : Vector Word 16) :
    permute v = alines (roundLines ncolumns ++ roundLines ndiagonals) v := by
  rw [permute_spec, lsame_ok (l := roundLines ncolumns ++ roundLines ndiagonals) (by decide) v]

/-- The register of slot `i`: the sixteen words, `t5`, `t6` and `s5`. -/
def sreg (i : Nat) : Reg :=
  if h : i < 16 then lane ⟨i, h⟩ else if i = 16 then .t5 else if i = 17 then .t6 else .s5

theorem sreg_inj {i j : Nat} (hi : i < 19) (hj : j < 19) (h : sreg i = sreg j) : i = j := by
  have key : ∀ i < 19, ∀ j < 19, sreg i = sreg j → i = j := by decide
  exact key i hi j hj h

theorem sreg_lane (j : Fin 16) : sreg j.1 = lane j := by simp [sreg, j.2]

theorem sreg_mem : ∀ i < 19, sreg i ∈ roundRegs := by decide

/-- One instruction of P, on slots. -/
inductive Op
  | sll (d n k : Nat)
  | srl (d n k : Nat)
  | mulhu (d n m : Nat)
  | add (d n m : Nat)
  | xor (d n m : Nat)
  | or (d n m : Nat)
  deriving DecidableEq

def Op.code : Op → Instr
  | .sll d n k => .shift .sll .d (sreg d) (sreg n) k
  | .srl d n k => .shift .srl .d (sreg d) (sreg n) k
  | .mulhu d n m => .mulhu (sreg d) (sreg n) (sreg m)
  | .add d n m => .add (sreg d) (sreg n) (sreg m)
  | .xor d n m => .logic .xor (sreg d) (sreg n) (sreg m)
  | .or d n m => .logic .or (sreg d) (sreg n) (sreg m)

/-- The slot an operation writes, and those it reads. -/
def Op.dst : Op → Nat
  | .sll d _ _ | .srl d _ _ | .mulhu d _ _ | .add d _ _ | .xor d _ _ | .or d _ _ => d
def Op.srcs : Op → List Nat
  | .sll _ n _ | .srl _ n _ => [n]
  | .mulhu _ n m | .add _ n m | .xor _ n m | .or _ n m => [n, m]

/-- The value an operation writes. -/
def Op.val (x : Nat → Word) : Op → Word
  | .sll _ n k => x n <<< k
  | .srl _ n k => x n >>> k
  | .mulhu _ n m => BitVec.ofNat 64 ((x n).toNat * (x m).toNat / 2 ^ 64)
  | .add _ n m => x n + x m
  | .xor _ n m => x n ^^^ x m
  | .or _ n m => x n ||| x m

def Op.step (x : Nat → Word) (op : Op) : Nat → Word := fun j => if j = op.dst then op.val x else x j

/-- The slots exist and the shifts are below 64. -/
def Op.Valid : Op → Bool
  | .sll d n k | .srl d n k => decide (d < 19 ∧ n < 19 ∧ k < 64)
  | .mulhu d n m | .add d n m | .xor d n m | .or d n m => decide (d < 19 ∧ n < 19 ∧ m < 19)

theorem Op.val_congr {x y : Nat → Word} (op : Op) (h : ∀ i ∈ op.srcs, x i = y i) : op.val x = op.val y := by
  cases op <;> simp only [Op.srcs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h <;>
    simp only [Op.val, h]

/-- The slots hold `x`. -/
def Holds19 (x : Nat → Word) (s : State) : Prop := ∀ i < 19, s.gpr (sreg i) = x i

/-- What an operation leaves. -/
structure OpPost (x : Nat → Word) (s s' : State) : Prop where
  holds : Holds19 x s'
  keep : ∀ r, (∀ i < 19, r ≠ sreg i) → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem op_ok (op : Op) (hv : op.Valid = true) {x : Nat → Word} {s : State} (h : Holds19 x s) :
    WP isa (.block [op.code]) s (OpPost (op.step x) s) := by
  have hd : op.dst < 19 := by cases op <;> simp_all [Op.Valid, Op.dst]
  have hs : ∀ i ∈ op.srcs, i < 19 := by cases op <;> simp_all [Op.Valid, Op.srcs]
  -- The instruction writes the value of `op` into its slot's register, and nothing else.
  have hw : exec op.code s = some (s.write (sreg op.dst) (op.val x)) := by
    cases op with
    | sll d n k =>
      have hk : k < 64 := by simp_all [Op.Valid]
      rw [Op.code, exec_shift_d hk, Op.val, ← h n (hs n (by simp [Op.srcs]))]; rfl
    | srl d n k =>
      have hk : k < 64 := by simp_all [Op.Valid]
      rw [Op.code, exec_shift_d hk, Op.val, ← h n (hs n (by simp [Op.srcs]))]; rfl
    | mulhu d n m =>
      rw [Op.code, exec_mulhu, Op.val, ← h n (hs n (by simp [Op.srcs])), ← h m (hs m (by simp [Op.srcs]))]; rfl
    | add d n m =>
      rw [Op.code, exec_add, Op.val, ← h n (hs n (by simp [Op.srcs])), ← h m (hs m (by simp [Op.srcs]))]; rfl
    | xor d n m =>
      rw [Op.code, exec_logic, Op.val, ← h n (hs n (by simp [Op.srcs])), ← h m (hs m (by simp [Op.srcs]))]; rfl
    | or d n m =>
      rw [Op.code, exec_logic, Op.val, ← h n (hs n (by simp [Op.srcs])), ← h m (hs m (by simp [Op.srcs]))]; rfl
  have u := Upd.write s (sreg op.dst) (op.val x)
  apply WP.of_runBlock
  refine ⟨_, by rw [runBlock_cons, hw]; rfl, ⟨fun i hi => ?_, fun r hr => u.other r (hr _ hd), u.mem, u.rd,
    u.wr, u.sp⟩⟩
  by_cases e : i = op.dst
  · subst e; rw [u.gpr]; simp only [Op.step, ↓reduceIte]
  · rw [u.other _ (fun e' => e (sreg_inj hi hd e')), h i hi]
    simp only [Op.step, e, ↓reduceIte]

/-- The operations of `ops` in turn. -/
def stepAll (x : Nat → Word) (ops : List Op) : Nat → Word := ops.foldl Op.step x

theorem ops_ok : ∀ (ops : List Op), (ops.all Op.Valid) = true → ∀ {x : Nat → Word} {s : State}, Holds19 x s →
    WP isa (.block (ops.map Op.code)) s (OpPost (stepAll x ops) s)
  | [], _, _, s, h => WP.block_nil ⟨h, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | op :: ops, hv, x, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hv
    rw [List.map_cons, show op.code :: ops.map Op.code = [op.code] ++ ops.map Op.code from rfl, WP.block_append_iff]
    refine WP.mono (op_ok op hv.1 h) fun s₁ h₁ => WP.mono (ops_ok ops hv.2 h₁.holds) fun s₂ h₂ =>
      ⟨h₂.holds, fun r hr => (h₂.keep r hr).trans (h₁.keep r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
        h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

/-- Two operations on separate slots: neither writes what the other reads or writes. -/
def OIndep (o o' : Op) : Bool :=
  decide (o.dst ≠ o'.dst ∧ o.dst ∉ o'.srcs ∧ o'.dst ∉ o.srcs)

theorem op_comm {x : Nat → Word} {o o' : Op} (h : OIndep o o' = true) :
    Op.step (Op.step x o) o' = Op.step (Op.step x o') o := by
  simp only [OIndep, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have v1 : o'.val (Op.step x o) = o'.val x :=
    o'.val_congr fun i hi => by
      have : i ≠ o.dst := fun e => h2 (e ▸ hi)
      simp only [Op.step, this, ↓reduceIte]
  have v2 : o.val (Op.step x o') = o.val x :=
    o.val_congr fun i hi => by
      have : i ≠ o'.dst := fun e => h3 (e ▸ hi)
      simp only [Op.step, this, ↓reduceIte]
  funext j
  show (if j = o'.dst then o'.val (Op.step x o) else Op.step x o j) =
    (if j = o.dst then o.val (Op.step x o') else Op.step x o' j)
  rw [v1, v2]
  simp only [Op.step]
  by_cases e1 : j = o'.dst <;> by_cases e2 : j = o.dst
  · exact absurd (e2.symm.trans e1) h1
  all_goals simp_all

/-- `l` without its first `o`, if every operation before it is on other slots. -/
def opull (o : Op) : List Op → Option (List Op)
  | [] => none
  | p :: l => if p = o then some l else if OIndep p o then (opull o l).map (p :: ·) else none

/-- `l'` runs the operations of `l`, each moved only past operations on other slots. -/
def OSame : List Op → List Op → Bool
  | [], [] => true
  | o :: l', l => match opull o l with
    | some r => OSame l' r
    | none => false
  | [], _ :: _ => false

theorem opull_ok {o : Op} : ∀ {l l₁ : List Op}, opull o l = some l₁ → ∀ x, stepAll x l = stepAll (Op.step x o) l₁
  | [], _, h, _ => by simp [opull] at h
  | p :: l, l₁, h, x => by
    unfold opull at h
    by_cases e : p = o
    · subst e; simp only [ite_true, Option.some.injEq] at h; subst h; rfl
    · simp only [e, ite_false] at h
      by_cases hp : OIndep p o = true
      · simp only [hp, ite_true] at h
        obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h
        show stepAll (Op.step x p) l = stepAll (Op.step (Op.step x o) p) l'
        rw [opull_ok hl', op_comm hp]
      · simp only [hp, Bool.false_eq_true, ite_false, reduceCtorEq] at h

theorem osame_ok : ∀ {l' l : List Op}, OSame l' l = true → ∀ x, stepAll x l' = stepAll x l
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [OSame] at h
  | o :: l', l, h, x => by
    unfold OSame at h
    split at h
    · rename_i l₁ hl
      show stepAll (Op.step x o) l' = stepAll x l
      rw [opull_ok hl, osame_ok h]
    · simp at h

/-- A line's operations. -/
def lineOps : Nat × Nat × Nat × Nat → List Op
  | (a, b, d, r) =>
    [.sll 16 a 32, .sll 17 b 32, .mulhu 16 16 17, .add a a b, .add a a 16, .add a a 16,
     .xor d d a, .srl 18 d r, .sll d d (64 - r), .or d d 18]

/-- The words of the slots. -/
def words (x : Nat → Word) : Vector Word 16 := Vector.ofFn fun i => x i.1

theorem lineOps_words (x : Nat → Word) {a b d r : Nat} (ha : a < 16) (hb : b < 16) (hd : d < 16)
    (had : a ≠ d) (hr : r < 64) :
    words (stepAll x (lineOps (a, b, d, r))) = aline (words x) a b d r := by
  apply Vector.ext
  intro m hm
  rw [aline_get _ ha hb hd had m hm]
  have key : x a + x b + BitVec.ofNat 64 ((x a <<< 32).toNat * (x b <<< 32).toNat / 2 ^ 64) +
      BitVec.ofNat 64 ((x a <<< 32).toNat * (x b <<< 32).toNat / 2 ^ 64) = addMul (x a) (x b) := by
    rw [lo_mul]; exact addMul_value _ _
  have h1617 : (16 : Nat) ≠ 17 := by decide
  have h1618 : (16 : Nat) ≠ 18 := by decide
  have h1718 : (17 : Nat) ≠ 18 := by decide
  have h1716 : (17 : Nat) ≠ 16 := by decide
  have h1816 : (18 : Nat) ≠ 16 := by decide
  have h1817 : (18 : Nat) ≠ 17 := by decide
  have hda : d ≠ a := Ne.symm had
  have na16 : a ≠ 16 := by omega_using [ha]
  have na17 : a ≠ 17 := by omega_using [ha]
  have na18 : a ≠ 18 := by omega_using [ha]
  have nb16 : b ≠ 16 := by omega_using [hb]
  have nb17 : b ≠ 17 := by omega_using [hb]
  have nb18 : b ≠ 18 := by omega_using [hb]
  have nd16 : d ≠ 16 := by omega_using [hd]
  have nd17 : d ≠ 17 := by omega_using [hd]
  have nd18 : d ≠ 18 := by omega_using [hd]
  have nm16 : m ≠ 16 := by omega_using [hm]
  have nm17 : m ≠ 17 := by omega_using [hm]
  have nm18 : m ≠ 18 := by omega_using [hm]
  have sa16 := Ne.symm na16; have sa17 := Ne.symm na17; have sa18 := Ne.symm na18
  have sb16 := Ne.symm nb16; have sb17 := Ne.symm nb17; have sb18 := Ne.symm nb18
  have sd16 := Ne.symm nd16; have sd17 := Ne.symm nd17; have sd18 := Ne.symm nd18
  simp only [words, stepAll, lineOps, List.foldl_cons, List.foldl_nil, Op.step, Op.dst, Op.val,
    Vector.getElem_ofFn]
  by_cases e1 : m = d
  · subst e1
    simp only [*, ↓reduceIte]
    rw [BitVec.or_comm, shr_or_shl _ hr]
  · have s1 := Ne.symm e1
    by_cases e2 : m = a
    · subst e2
      simp only [*, ↓reduceIte]
    · have s2 := Ne.symm e2
      simp only [*, ↓reduceIte]

/-- The lines in turn, as operations. -/
def linesOps (l : List (Nat × Nat × Nat × Nat)) : List Op := l.flatMap lineOps

theorem linesOps_words : ∀ (l : List (Nat × Nat × Nat × Nat)) (x : Nat → Word),
    (l.all fun (a, b, d, r) => decide (a < 16 ∧ b < 16 ∧ d < 16 ∧ a ≠ d ∧ r < 64)) = true →
    words (stepAll x (linesOps l)) = alines l (words x)
  | [], _, _ => rfl
  | (a, b, d, r) :: l, x, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ha, hb, hd, had, hr⟩, hl⟩ := h
    rw [linesOps, List.flatMap_cons, stepAll, List.foldl_append, ← stepAll, ← stepAll, ← linesOps,
      linesOps_words l _ hl, lineOps_words _ ha hb hd had hr]
    simp only [alines, List.foldl_cons]

/-- Four GBs' operations as the code runs them. -/
def roundOps (qs : List (Nat × Nat × Nat × Nat)) : List Op :=
  let step (r : Nat) (ls : List (Nat × Nat × Nat)) : List Op :=
    ls.flatMap (fun (a, b, _) => [.sll 16 a 32, .sll 17 b 32, .mulhu 16 16 17, .add a a b, .add a a 16, .add a a 16]) ++
    ls.map (fun (a, _, d) => .xor d d a) ++
    ls.flatMap (fun (_, _, d) => [.srl 18 d r, .sll d d (64 - r), .or d d 18])
  step 32 (qs.map fun (a, b, _, d) => (a, b, d)) ++ step 24 (qs.map fun (_, b, c, d) => (c, d, b)) ++
    step 16 (qs.map fun (a, b, _, d) => (a, b, d)) ++ step 63 (qs.map fun (_, b, c, d) => (c, d, b))

/-- The code of P is its operations. -/
theorem permute_code :
    Impl.Argon2.RISCV64.permute = .block ((roundOps ncolumns ++ roundOps ndiagonals).map Op.code) := by
  rw [Impl.Argon2.RISCV64.permute, List.map_append]
  congr 2 <;> decide

theorem roundOps_fold (x : Nat → Word) :
    words (stepAll x (roundOps ncolumns ++ roundOps ndiagonals)) =
      alines (roundLines ncolumns ++ roundLines ndiagonals) (words x) := by
  rw [osame_ok (l := linesOps (roundLines ncolumns ++ roundLines ndiagonals)) (by decide) x]
  exact linesOps_words _ x (by decide)

theorem roundOps_valid : (roundOps ncolumns ++ roundOps ndiagonals).all Op.Valid = true := by
  rw [List.all_append, Bool.and_eq_true]
  exact ⟨by decide, by decide⟩

/-- The slots of a state. -/
def slots (s : State) (i : Nat) : Word := s.gpr (sreg i)

/-- P on the sixteen registers. -/
theorem permute_ok (s : State) (v : Vector Word 16) (hv : InRegs s v) :
    WP isa Impl.Argon2.RISCV64.permute s fun t =>
      InRegs t (permute v) ∧ Keeps s t ∧ t.mem = s.mem := by
  have hw : words (slots s) = v := by
    apply Vector.ext; intro k hk
    simp only [words, Vector.getElem_ofFn, slots]
    have := hv ⟨k, hk⟩
    rw [← sreg_lane] at this
    exact this
  rw [permute_code]
  refine WP.mono (ops_ok _ roundOps_valid (x := slots s) fun i _ => rfl) fun t h' =>
    ⟨fun j => ?_, ⟨fun r hr => h'.keep r fun i hi e => hr (e ▸ sreg_mem i hi), h'.rd, h'.wr, h'.sp⟩, h'.mem⟩
  rw [Fin.getElem_fin, permute_lines, ← hw, ← sreg_lane]
  have e' : stepAll (slots s) (roundOps ncolumns ++ roundOps ndiagonals) j.1 =
      (alines (roundLines ncolumns ++ roundLines ndiagonals) (words (slots s)))[j.1] := by
    simpa only [words, Vector.getElem_ofFn] using congrArg (·[j.1]'j.2) (roundOps_fold (slots s))
  rw [← e']
  exact h'.holds j.1 (by omega_using [])

/-- The row/column code meets the specification's gather, P, scatter definition. -/
theorem permuteAt_ok (index : Fin 16 → Fin 128) (s : State) {p : Addr} (hs : Scratch s p) :
    WP isa (Impl.Argon2.RISCV64.permuteAt index) s fun t =>
      working t.mem p = Spec.Argon2.permuteAt index (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  unfold Impl.Argon2.RISCV64.permuteAt
  apply WP.seq
  refine (loads_ok index (List.finRange 16) (List.nodup_finRange 16) s hs).mono ?_
  rintro s1 ⟨hl, hk1, hm1, hr1, hw1, hsp1⟩
  have k1 : Keeps s s1 := ⟨fun r hr => hk1 r (fun j _ he => hr (he ▸ lane_mem j)), hr1, hw1, hsp1⟩
  have in1 : InRegs s1 (gather index (working s.mem p)) := by
    intro j
    rw [hl j (List.mem_finRange j)]
    simp only [gather, working, Fin.getElem_fin, Vector.getElem_ofFn]
  apply WP.seq
  refine (permute_ok s1 _ in1).mono ?_
  rintro s2 ⟨in2, k2, hm2⟩
  refine (stores_ok index (List.finRange 16) s2 ((hs.of_keeps k1).of_keeps k2)).mono ?_
  rintro t ⟨hw, hf, hg, hr, hwr, hsp⟩
  refine ⟨?_, ?_, (k1.trans k2).trans ⟨fun r _ => congrFun hg r, hr, hwr, hsp⟩⟩
  · rw [hw, hm2, hm1]
    simp only [in2 _]
    rfl
  · rw [hm2, hm1] at hf
    exact hf

/-- Compose a list of row or column permutations. -/
theorem rounds_ok (index : Fin 8 → Fin 16 → Fin 128) (is : List (Fin 8))
    (s : State) {p : Addr} (hs : Scratch s p) :
    WP isa (is.foldr (fun i rest => .seq (Impl.Argon2.RISCV64.permuteAt (index i)) rest)
      (.block [])) s fun t =>
      working t.mem p = is.foldl (fun b i => Spec.Argon2.permuteAt (index i) b) (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, Keeps.refl s⟩
  | cons i is ih =>
    apply WP.seq
    refine (permuteAt_ok (index i) s hs).mono ?_
    rintro t ⟨ht, hf, hk⟩
    refine (ih t (hs.of_keeps hk)).mono ?_
    rintro u ⟨hu, hf', hk'⟩
    refine ⟨?_, hf.trans hf', hk.trans hk'⟩
    simpa only [List.foldl_cons, ht] using hu

end VG.Proof.Argon2.RISCV64

end

end

/-! # Argon2 compression on RISC-V: the initial and final XORs -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64 VG.Spec.Argon2
open VG.RISCV64.Wp (Upd)

theorem blockAt_get (m : Mem) (p : Addr) (i : Fin 128) :
    (blockAt m p)[i] = m.readW (off p (8 * i.val)) 64 := by
  simp only [blockAt, Fin.getElem_fin, Vector.getElem_ofFn, Mem.readW, BitVec.setWidth_eq]

theorem xorBlock_get (a b : Block) (i : Fin 128) :
    (xorBlock a b)[i] = a[i] ^^^ b[i] := by
  simp only [xorBlock, Fin.getElem_fin, Vector.getElem_zipWith]

/-- The copying blocks change only `t0`, `t1` and memory. -/
def CopyKeeps (s t : State) : Prop :=
  (∀ r, r ≠ .t0 → r ≠ .t1 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp

theorem CopyKeeps.refl (s : State) : CopyKeeps s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem CopyKeeps.trans {s t u : State} (h : CopyKeeps s t) (h' : CopyKeeps t u) : CopyKeeps s u :=
  ⟨fun r h0 h22 => (h'.1 r h0 h22).trans (h.1 r h0 h22), h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.trans h.2.2.2⟩

theorem Scratch.of_copy {s t : State} {p : Addr} (hs : Scratch s p) (h : CopyKeeps s t) :
    Scratch t p := ⟨(h.1 .a3 (by decide) (by decide)).trans hs.reg, h.2.2.1 ▸ hs.wr, hs.al⟩

theorem off8 (i : Nat) (hi : i < 128) : 8 * i < 2048 := by omega_arith

theorem al_reg {s : State} {r : Reg} {x : Addr} (h : s.gpr r = x) (hx : x.toNat % 8 = 0) (d : Nat)
    (hd : d % 8 = 0) : (s.gpr r + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [h]; exact Spill.al8 hx hd

theorem initWord_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Nat) (hi : i < 128)
    (hx : InRegions (s.rd ++ s.wr) (off (s.gpr .a0) (8 * i)) 8)
    (hy : InRegions (s.rd ++ s.wr) (off (s.gpr .a1) (8 * i)) 8)
    (ax : (s.gpr .a0).toNat % 8 = 0) (ay : (s.gpr .a1).toNat % 8 = 0) :
    let a := s.mem.readW (off (s.gpr .a0) (8 * i)) 64 ^^^ s.mem.readW (off (s.gpr .a1) (8 * i)) 64
    WP isa (.block (initWord i)) s fun t =>
      t.mem = (s.mem.writeW (off p (8 * i)) a).writeW (off p (1024 + 8 * i)) a ∧
      CopyKeeps s t := by
  dsimp only
  have w1 := hs.write (d := 8 * i) (n := 8) (by omega_arith)
  have w2 := hs.write (d := 1024 + 8 * i) (n := 8) (by omega_arith)
  rw [← hs.reg] at w1 w2
  unfold initWord
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (off8 i hi) (al_reg rfl ax _ (by omega_arith)) hx, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (off8 i hi)
    (al_reg (by simp [State.write]) ay _ (by omega_arith)) (by simpa [State.write] using hy), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_logic (op := .xor), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d (off8 i hi)
    (al_reg (by simp [State.write]; exact hs.reg) hs.al _ (by omega_arith)) (by simpa [State.write] using w1), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d (word_offset i hi)
    (al_reg (by simp [State.write]; exact hs.reg) hs.al _ (by omega_arith)) (by simpa [State.write] using w2), ?_⟩
  refine WP.block_nil ⟨?_, fun r h0 h22 => ?_, rfl, rfl, rfl⟩
  · simp [State.write, hs.reg]
  · simp [State.write, h0, h22]

theorem finishWord_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Nat) (hi : i < 128)
    (hout : InRegions s.wr (off (s.gpr .a2) (8 * i)) 8) (ao : (s.gpr .a2).toNat % 8 = 0) :
    WP isa (.block (finishWord i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .a2) (8 * i))
          (word s.mem p i ^^^ s.mem.readW (off p (8 * i)) 64) ∧
      CopyKeeps s t := by
  have r1 := hs.read (d := 8 * i) (n := 8) (by omega_arith)
  have r2 := hs.read (d := 1024 + 8 * i) (n := 8) (by omega_arith)
  rw [← hs.reg] at r1 r2
  unfold finishWord
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (word_offset i hi)
    (al_reg hs.reg hs.al _ (by omega_arith)) r2, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (off8 i hi)
    (al_reg (by simp [State.write]; exact hs.reg) hs.al _ (by omega_arith)) (by simpa [State.write] using r1), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_logic (op := .xor), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d (off8 i hi)
    (al_reg (by simp [State.write]) ao _ (by omega_arith)) (by simpa [State.write] using hout), ?_⟩
  refine WP.block_nil ⟨?_, fun r h0 h22 => ?_, rfl, rfl, rfl⟩
  · simp [State.write, hs.reg]
  · simp [State.write, h0, h22]

structure Inputs (s : State) (x y p : Addr) : Prop where
  xreg : s.gpr .a0 = x
  yreg : s.gpr .a1 = y
  xread : (⟨x, 1024⟩ : Region) ∈ s.rd ++ s.wr
  yread : (⟨y, 1024⟩ : Region) ∈ s.rd ++ s.wr
  xsep : (⟨x, 1024⟩ : Region).Disjoint ⟨p, 4096⟩
  ysep : (⟨y, 1024⟩ : Region).Disjoint ⟨p, 4096⟩
  xal : x.toNat % 8 = 0
  yal : y.toNat % 8 = 0

theorem Inputs.of_copy {s t : State} {x y p : Addr} (h : Inputs s x y p) (hk : CopyKeeps s t) :
    Inputs t x y p := ⟨(hk.1 .a0 (by decide) (by decide)).trans h.xreg,
      (hk.1 .a1 (by decide) (by decide)).trans h.yreg, by simpa only [hk.2.1, hk.2.2.1] using h.xread,
      by simpa only [hk.2.1, hk.2.2.1] using h.yread, h.xsep, h.ysep, h.xal, h.yal⟩

theorem input_unchanged {m m' : Mem} {x p : Addr} {n : Nat} (hf : Frame [⟨p, n⟩] m m')
    (hd : (⟨x, 1024⟩ : Region).Disjoint ⟨p, n⟩) (i : Fin 128) :
    m'.readW (off x (8 * i.val)) 64 = m.readW (off x (8 * i.val)) 64 :=
  hf.readW (r := ⟨x, 1024⟩) (Offset.contains_base x (by omega_arith) (by omega_arith))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

/-- A prefix of the two scratch copies is initialized. -/
def Initialized (m : Mem) (p : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val < n →
    m.readW (off p (8 * i.val)) 64 = r[i] ∧ word m p i.val = r[i]

theorem initialized_step {m : Mem} {p : Addr} {r : Block} {n : Nat}
    (hn : n < 128) (h : Initialized m p r n) :
    Initialized ((m.writeW (off p (8 * n)) r[n]).writeW (off p (1024 + 8 * n)) r[n]) p r (n + 1) := by
  intro i hi
  obtain ⟨k, hk⟩ := i
  simp only at hi
  simp only [word]
  rcases (by omega_arith : k = n ∨ k < n) with rfl | he
  · refine ⟨?_, Mem.readW_writeW_self64 _ _ _⟩
    rw [Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self64]
    rfl
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    exact h ⟨k, hk⟩ he

/-- Initialize a prefix of the words, framing the first half of scratch. -/
theorem init_prefix (n : Nat) (hn : n ≤ 128) (s : State) {x y p : Addr}
    (hs : Scratch s p) (hin : Inputs s x y p) :
    WP isa (.block ((List.range n).flatMap initWord)) s fun t =>
      Initialized t.mem p (xorBlock (blockAt s.mem x) (blockAt s.mem y)) n ∧
      Frame [⟨p, 2048⟩] s.mem t.mem ∧ CopyKeeps s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨fun i hi => by omega_arith, Frame.refl _ _, CopyKeeps.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega_arith)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    have hn' : n < 128 := by omega_arith
    have htIn := hin.of_copy hk
    have lx : InRegions (t.rd ++ t.wr) (off (t.gpr .a0) (8 * n)) 8 := by
      rw [htIn.xreg]
      exact ⟨_, htIn.xread, Offset.contains_base x (by omega_arith) (by omega_arith)⟩
    have ly : InRegions (t.rd ++ t.wr) (off (t.gpr .a1) (8 * n)) 8 := by
      rw [htIn.yreg]
      exact ⟨_, htIn.yread, Offset.contains_base y (by omega_arith) (by omega_arith)⟩
    refine (initWord_ok t (hs.of_copy hk) n hn' lx ly (by rw [htIn.xreg]; exact hin.xal)
      (by rw [htIn.yreg]; exact hin.yal)).mono ?_
    rintro u ⟨hm, hk'⟩
    have hv : t.mem.readW (off x (8 * n)) 64 ^^^ t.mem.readW (off y (8 * n)) 64 =
        (xorBlock (blockAt s.mem x) (blockAt s.mem y))[n] := by
      rw [show (xorBlock (blockAt s.mem x) (blockAt s.mem y))[n] =
          (xorBlock (blockAt s.mem x) (blockAt s.mem y))[(⟨n, hn'⟩ : Fin 128)] from rfl,
        xorBlock_get, blockAt_get, blockAt_get,
        input_unchanged hf (hin.xsep.sub_right (Region.sub_prefix (by omega_arith))) ⟨n, hn'⟩,
        input_unchanged hf (hin.ysep.sub_right (Region.sub_prefix (by omega_arith))) ⟨n, hn'⟩]
    refine ⟨?_, ?_, hk.trans hk'⟩
    · rw [hm, htIn.xreg, htIn.yreg, hv]
      exact initialized_step hn' ht
    · rw [hm]
      exact (hf.writeW (r := ⟨p, 2048⟩) (by simp) _
        (Offset.contains_base p (by omega_arith) (by omega_arith))).writeW (r := ⟨p, 2048⟩) (by simp) _
        (Offset.contains_base p (by omega_arith) (by omega_arith))

/-- The initialized copies both contain X XOR Y. -/
theorem initialized_blocks {m : Mem} {p : Addr} {r : Block} (h : Initialized m p r 128) :
    blockAt m p = r ∧ working m p = r := by
  constructor
  · apply Vector.ext
    intro i hi
    have he := (h ⟨i, hi⟩ hi).1
    rw [← blockAt_get m p ⟨i, hi⟩] at he
    exact he
  · apply Vector.ext
    intro i hi
    have he := (h ⟨i, hi⟩ hi).2
    rw [← working_get m p ⟨i, hi⟩] at he
    exact he

/-- A prefix of the output block has been written. -/
def Written (m : Mem) (out : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val < n → m.readW (off out (8 * i.val)) 64 = r[i]

theorem written_step {m : Mem} {out : Addr} {r : Block} {n : Nat}
    (hn : n < 128) (h : Written m out r n) :
    Written (m.writeW (off out (8 * n)) r[n]) out r (n + 1) := by
  intro i hi
  by_cases he : i.val = n
  · subst n
    exact Mem.readW_writeW_self64 _ _ _
  · rw [Mem.readW_writeW_sep (Offset.sep out (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    exact h i (by omega_arith)

theorem scratch_unchanged {m m' : Mem} {out p : Addr} (hf : Frame [⟨out, 1024⟩] m m')
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) {d : Nat} (hd' : d + 8 ≤ 4096) :
    m'.readW (off p d) 64 = m.readW (off p d) 64 :=
  hf.readW (r := ⟨p, 4096⟩) (Offset.contains_base p hd' (by omega_arith))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

/-- Finish a prefix of the words. -/
theorem finish_prefix (n : Nat) (hn : n ≤ 128) (s : State) {p out : Addr}
    (hs : Scratch s p) (ho : s.gpr .a2 = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) (hal : out.toNat % 8 = 0) :
    WP isa (.block ((List.range n).flatMap finishWord)) s fun t =>
      Written t.mem out (xorBlock (working s.mem p) (blockAt s.mem p)) n ∧
      Frame [⟨out, 1024⟩] s.mem t.mem ∧ CopyKeeps s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega_arith, Frame.refl _ _, CopyKeeps.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega_arith)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    have hn' : n < 128 := by omega_arith
    have ho' : t.gpr .a2 = out := (hk.1 .a2 (by decide) (by decide)).trans ho
    have hout : InRegions t.wr (off (t.gpr .a2) (8 * n)) 8 := by
      rw [ho', hk.2.2.1]
      exact ⟨_, hw, Offset.contains_base out (by omega_arith) (by omega_arith)⟩
    refine (finishWord_ok t (hs.of_copy hk) n hn' hout (by rw [ho']; exact hal)).mono ?_
    rintro u ⟨hm, hk'⟩
    have hv : word t.mem p n ^^^ t.mem.readW (off p (8 * n)) 64 =
        (xorBlock (working s.mem p) (blockAt s.mem p))[n] := by
      rw [show (xorBlock (working s.mem p) (blockAt s.mem p))[n] =
          (xorBlock (working s.mem p) (blockAt s.mem p))[(⟨n, hn'⟩ : Fin 128)] from rfl,
        xorBlock_get, working_get, blockAt_get]
      simp only [word, scratch_unchanged hf hd (d := 1024 + 8 * n) (by omega_arith),
        scratch_unchanged hf hd (d := 8 * n) (by omega_arith)]
    refine ⟨?_, ?_, hk.trans hk'⟩
    · rw [hm, ho', hv]
      exact written_step hn' ht
    · rw [hm, ho']
      exact hf.writeW (r := ⟨out, 1024⟩) (by simp) _ (Offset.contains_base out (by omega_arith) (by omega_arith))

theorem written_block {m : Mem} {out : Addr} {r : Block} (h : Written m out r 128) :
    blockAt m out = r := by
  apply Vector.ext
  intro i hi
  have he := h ⟨i, hi⟩ hi
  rw [← blockAt_get m out ⟨i, hi⟩] at he
  exact he

end VG.Proof.Argon2.RISCV64

end

end

/-! # Argon2 compression G on RISC-V: correctness and constant time

`vg_argon2_compress` is an internal function, which only the derivation
calls: its contract, `compressLocal`, states that its pointers are 8-byte
aligned. -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64

open VG VG.RISCV64 VG.Spec.Argon2
open VG.RISCV64.Wp (Upd wp_addi)

/-- The contract the proof is written against. -/
def compressLocal : Contract isa where
  pre s :=
    let x : Region := ⟨s.gpr .a0, 1024⟩
    let y : Region := ⟨s.gpr .a1, 1024⟩
    let out : Region := ⟨s.gpr .a2, 1024⟩
    let scratch : Region := ⟨s.gpr .a3, 4096⟩
    s.rd = [x, y] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ x.Disjoint scratch ∧ y.Disjoint scratch ∧
      (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a1).toNat % 8 = 0 ∧ (s.gpr .a2).toNat % 8 = 0 ∧
      (s.gpr .a3).toNat % 8 = 0
  post s t := blockAt t.mem (s.gpr .a2) =
    compress (blockAt s.mem (s.gpr .a0)) (blockAt s.mem (s.gpr .a1))
  pub s t := s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧
    s.gpr .a2 = t.gpr .a2 ∧ s.gpr .a3 = t.gpr .a3 ∧ s.sp = t.sp

theorem compress_ct : ConstantTime isa compressLocal.pre compressLocal.pub
    Impl.Argon2.RISCV64.compress := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A block unchanged by a frame disjoint from it. -/
theorem blockAt_frame {m m' : Mem} {rs : List Region} {x : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨x, 1024⟩ : Region).Disjoint r) : blockAt m' x = blockAt m x := by
  apply Vector.ext
  intro i hi
  show (blockAt m' x)[(⟨i, hi⟩ : Fin 128)] = (blockAt m x)[(⟨i, hi⟩ : Fin 128)]
  rw [blockAt_get, blockAt_get]
  exact hf.readW (r := ⟨x, 1024⟩) (Offset.contains_base x (by omega_using []) (by omega_using [])) hd (by decide)

/-- The base of the saves. -/
abbrev saveB (p : Addr) : Addr := p + BitVec.ofNat 64 2040

/-- The save area, past the two blocks. -/
abbrev saveR (p : Addr) : Region := ⟨p + BitVec.ofNat 64 2048, 48⟩

theorem saveB_off (p : Addr) (d : Nat) :
    saveB p + BitVec.ofNat 64 d = p + BitVec.ofNat 64 (2040 + d) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem saved_in : ∀ q ∈ Impl.Argon2.RISCV64.saved, 8 ≤ q.2 ∧ q.2 + 8 ≤ 8 + 48 := by decide

theorem saved_fits : ∀ q ∈ Impl.Argon2.RISCV64.saved, q.2 % 8 = 0 ∧ q.2 < 2048 := by decide

theorem saveR_eq (p : Addr) : (⟨saveB p + BitVec.ofNat 64 8, 48⟩ : Region) = saveR p := by
  rw [saveB_off]

theorem preserved_split : ∀ r ∈ .ra :: preserved, r ∈ Impl.Argon2.RISCV64.saved.map Prod.fst ∨
    (r ∉ roundRegs ∧ r ≠ .t0 ∧ r ≠ .t1 ∧ r ∉ Impl.Argon2.RISCV64.saved.map Prod.fst) := by decide

/-- `t0 := scratch + 2040`, the base of the saves and restores. -/
theorem base_ok (s : State) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' .t0 (saveB (s.gpr .a3)) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi .t0 .a3 2040 :: is)) s Q :=
  wp_addi (imm := 2040) (by decide) k

theorem compress_wp (s : State) (hs : compressLocal.pre s) :
    WP isa Impl.Argon2.RISCV64.compress s fun t => compressLocal.post s t ∧
      (∀ r ∈ .ra :: preserved, t.gpr r = s.gpr r) := by
  obtain ⟨hrd, hwr, hout, hx, hy, ax, ay, ao, ap⟩ := hs
  obtain ⟨p, hp⟩ : ∃ p, s.gpr .a3 = p := ⟨_, rfl⟩
  rw [hp] at hwr hout hx hy ap
  obtain scr : Scratch s p := ⟨hp, by simp [hwr], ap⟩
  unfold Impl.Argon2.RISCV64.compress
  apply WP.seq
  rw [show Impl.Argon2.RISCV64.save = .addi .t0 .a3 2040 :: Spill.saveCode .t0 Impl.Argon2.RISCV64.saved
    from rfl, List.cons_append]
  refine base_ok s fun s₀' u₀ => ?_
  obtain b0 : s₀'.gpr .t0 = saveB p := by rw [u₀.gpr, hp]
  refine Spill.save_ok (by rw [b0]; exact Spill.al8 ap (by decide)) saved_fits
    (fun q hq => by
      rw [b0, u₀.wr, saveB_off]
      exact scr.write (by have := saved_in q hq; omega_using [this])) ?_
  generalize e₀ : ({ s₀' with
    mem := Spill.saveMem s₀'.mem (s₀'.gpr .t0) s₀'.gpr Impl.Argon2.RISCV64.saved } : State) = s₀
  obtain m₀ : s₀.mem = Spill.saveMem s₀'.mem (s₀'.gpr .t0) s₀'.gpr Impl.Argon2.RISCV64.saved := by
    rw [← e₀]
  obtain gr₀ : s₀.gpr = s₀'.gpr := by rw [← e₀]
  obtain rd₀ : s₀.rd = s.rd := by rw [← e₀]; exact u₀.rd
  obtain wr₀ : s₀.wr = s.wr := by rw [← e₀]; exact u₀.wr
  obtain f₀ : Frame [saveR p] s.mem s₀.mem := by
    have := Spill.saveMem_frame saved_in (by decide) s₀'.mem (s₀'.gpr .t0) s₀'.gpr
    rw [b0, saveR_eq] at this
    rw [m₀, b0, ← u₀.mem]
    exact this
  obtain g₀ : ∀ r, r ≠ .t0 → s₀'.gpr r = s.gpr r := fun r hr => u₀.other r hr
  obtain sv₀ : Spill.Saved (saveB p) s.gpr Impl.Argon2.RISCV64.saved s₀.mem := by
    intro q hq
    have := Spill.saveMem_saved (by decide) s₀'.mem (s₀'.gpr .t0) s₀'.gpr q hq
    rw [b0] at this
    obtain hne : ∀ q ∈ Impl.Argon2.RISCV64.saved, q.1 ≠ .t0 := by decide
    rw [m₀, b0, this, g₀ _ (hne q hq)]
  obtain xs : (⟨s.gpr .a0, 1024⟩ : Region).Disjoint (saveR p) := hx.sub_right (Offset.sub_base _ (by omega_using []))
  obtain ys : (⟨s.gpr .a1, 1024⟩ : Region).Disjoint (saveR p) := hy.sub_right (Offset.sub_base _ (by omega_using []))
  obtain bx : blockAt s₀.mem (s.gpr .a0) = blockAt s.mem (s.gpr .a0) := blockAt_frame f₀ (by simpa using xs)
  obtain by' : blockAt s₀.mem (s.gpr .a1) = blockAt s.mem (s.gpr .a1) := blockAt_frame f₀ (by simpa using ys)
  obtain scr₀ : Scratch s₀ p := ⟨by rw [gr₀, g₀ .a3 (by decide), hp], by simp [wr₀, hwr], ap⟩
  obtain inputs : Inputs s₀ (s.gpr .a0) (s.gpr .a1) p :=
    ⟨by rw [gr₀, g₀ .a0 (by decide)], by rw [gr₀, g₀ .a1 (by decide)], by simp [rd₀, wr₀, hrd],
      by simp [rd₀, wr₀, hrd], hx, hy, ax, ay⟩
  refine (init_prefix 128 (by decide) s₀ scr₀ inputs).mono ?_
  rintro s₁ ⟨hinit, hf1, hk1⟩
  obtain ⟨horig, hwork⟩ := initialized_blocks hinit
  obtain scr1 := scr₀.of_copy hk1
  obtain sv₁ : Spill.Saved (saveB p) s.gpr Impl.Argon2.RISCV64.saved s₁.mem :=
    sv₀.frame_in saved_in hf1 (by rw [saveR_eq]; simpa using Offset.disjoint_base p (by omega_using []) (by omega_using []))
  apply WP.seq
  refine (rounds_ok rowIndex (List.finRange 8) s₁ scr1).mono ?_
  rintro s₂ ⟨hrow, hf2, hk2⟩
  apply WP.seq
  refine (rounds_ok colIndex (List.finRange 8) s₂ (scr1.of_keeps hk2)).mono ?_
  rintro s₃ ⟨hcol, hf3, hk3⟩
  obtain scr3 := (scr1.of_keeps hk2).of_keeps hk3
  obtain d1024 : ∀ r ∈ [(⟨off p 1024, 1024⟩ : Region)],
      Region.Disjoint ⟨saveB p + BitVec.ofNat 64 8, 48⟩ r := by
    rw [saveR_eq]; simpa using Offset.disjoint p (by omega_using []) (by omega_using []) (by omega_using [])
  obtain sv₃ : Spill.Saved (saveB p) s.gpr Impl.Argon2.RISCV64.saved s₃.mem :=
    (sv₁.frame_in saved_in hf2 d1024).frame_in saved_in hf3 d1024
  obtain hout3 : s₃.gpr .a2 = s.gpr .a2 := by
    rw [hk3.1 .a2 (by decide), hk2.1 .a2 (by decide), hk1.1 .a2 (by decide) (by decide), gr₀,
      g₀ .a2 (by decide)]
  obtain hw3 : s₃.wr = s.wr := hk3.2.2.1.trans (hk2.2.2.1.trans (hk1.2.2.1.trans wr₀))
  apply WP.block_append
  refine (finish_prefix 128 (by decide) s₃ scr3 hout3 (by rw [hw3, hwr]; simp) hout.symm ao).mono ?_
  rintro s₄ ⟨hfinish, hf4, hk4⟩
  obtain sv₄ : Spill.Saved (saveB p) s.gpr Impl.Argon2.RISCV64.saved s₄.mem :=
    sv₃.frame_in saved_in hf4 (by
      rw [saveR_eq]
      simpa using (hout.sub_right (Offset.sub_base p (d := 2048) (n := 48) (by omega_using []))).symm)
  obtain scr4 := scr3.of_copy hk4
  rw [show Impl.Argon2.RISCV64.restore = .addi .t0 .a3 2040 ::
    Spill.restoreCode .t0 Impl.Argon2.RISCV64.saved from rfl]
  refine base_ok s₄ fun s₅ u₅ => ?_
  obtain b5 : s₅.gpr .t0 = saveB p := by rw [u₅.gpr, scr4.reg]
  refine WP.mono (Spill.restore_wp (b := .t0) (B := saveB p) (Spill.al8 ap (by decide)) b5 saved_fits
    (by decide) (fun q hq => by
      rw [u₅.rd, u₅.wr, saveB_off]
      exact scr4.read (by have := saved_in q hq; omega_using [this])) (by rw [u₅.mem]; exact sv₄)) fun t ht => ⟨?_, ?_⟩
  · have ho : blockAt s₃.mem p = blockAt s₁.mem p :=
      blockAt_frame (hf2.trans hf3) (by simpa using Offset.base_disjoint p (by omega_using []) (by omega_using []))
    rw [horig] at ho
    obtain he := written_block hfinish
    rw [hcol, hrow, hwork, ho, bx, by'] at he
    show blockAt t.mem (s.gpr .a2) = _
    rw [ht.mem, u₅.mem, he]
    rfl
  · intro r hr
    rcases preserved_split r hr with h | ⟨h1, h2, h3, h4⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
      exact ht.gpr q hq
    · rw [ht.other r h4, u₅.other r h2, hk4.1 r h2 h3, hk3.1 r h1, hk2.1 r h1, hk1.1 r h2 h3, gr₀, g₀ r h2]

theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.RISCV64.compress s tr t ∧ abiPreserved s t ∧
      compressLocal.post s t := by
  obtain ⟨tr, t, he, hp, hk⟩ := compress_wp s hs
  exact ⟨tr, t, he, ⟨fun r hr => hk r (List.mem_cons_of_mem _ hr), Exec.sp he,
    hk .ra (List.mem_cons_self ..)⟩, hp⟩

end VG.Proof.Argon2.RISCV64
