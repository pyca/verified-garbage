module

import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Impl.Argon2.RISCV64.Compress
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Argon2.Spec
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Argon2.RISCV64.Ops

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
  ⟨_, h.wr, Offset.contains_base p hd (by omega)⟩

theorem Scratch.read {s : State} {p : Addr} (h : Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions (s.rd ++ s.wr) (off p d) n :=
  ⟨_, List.mem_append_right _ h.wr, Offset.contains_base p hd (by omega)⟩

theorem lane_injective : Function.Injective lane := by
  intro i j h
  revert i j
  decide

/-- The registers the rounds write. -/
abbrev roundRegs : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .a0, .a1, .a4, .a5, .a6, .a7, .s0, .s1, .s2, .s3, .s4, .t5, .t6, .s5]

theorem lane_mem (j : Fin 16) : lane j ∈ roundRegs := by revert j; decide

theorem t5_mem : Reg.t5 ∈ roundRegs := by decide
theorem t6_mem : Reg.t6 ∈ roundRegs := by decide

theorem lane_ne_r6 (j : Fin 16) : lane j ≠ .a3 := by revert j; decide
theorem lane_ne_t5 (j : Fin 16) : lane j ≠ .t5 := by revert j; decide
theorem lane_ne_t6 (j : Fin 16) : lane j ≠ .t6 := by revert j; decide

theorem word_offset (i : Nat) (hi : i < 128) : 1024 + 8 * i < 2048 := by
  omega

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
      (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- Load one word of the permuted block into its register. -/
theorem loadWord_ok (index : Fin 16 → Fin 128) (j : Fin 16) (s : State) {p : Addr}
    (hs : Scratch s p) :
    WP isa (.block [loadWord index j]) s fun t =>
      t = s.write (lane j) (word s.mem p (index j).val) := by
  have ld := hs.read (d := 1024 + 8 * (index j).val) (n := 8) (by omega)
  rw [← hs.reg] at ld
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d (word_offset _ (index j).isLt) (hs.al_off (by omega)) ld,
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
  have st := hs.write (d := 1024 + 8 * (index j).val) (n := 8) (by omega)
  rw [← hs.reg] at st
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d (word_offset _ (index j).isLt) (hs.al_off (by omega)) st,
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
          (by omega) (by omega) (by omega))).trans hf

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
  have na16 : a ≠ 16 := by omega
  have na17 : a ≠ 17 := by omega
  have na18 : a ≠ 18 := by omega
  have nb16 : b ≠ 16 := by omega
  have nb17 : b ≠ 17 := by omega
  have nb18 : b ≠ 18 := by omega
  have nd16 : d ≠ 16 := by omega
  have nd17 : d ≠ 17 := by omega
  have nd18 : d ≠ 18 := by omega
  have nm16 : m ≠ 16 := by omega
  have nm17 : m ≠ 17 := by omega
  have nm18 : m ≠ 18 := by omega
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
    rfl

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
  exact h'.holds j.1 (by omega)

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
