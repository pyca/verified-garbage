module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Blake2.Spec
public import VerifiedGarbage.Impl.Blake2.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-!
# BLAKE2 compression function on RISC-V: the rounds

The structure of the PPC64LE proof (`VG.Proof.Blake2.PPC64LE`), written once
for both word sizes, over the operand size `z` (`.d` for BLAKE2b, `.w` for
BLAKE2s, words of `z.bits` bits). The registers are 64 bits and `add` and
`xor` act on all of them, so a word of the work vector is the low `z.bits`
bits of its register (`Vars`): the word shifts and the stores of words read
only those. The code runs a round's four column `G`s side by side, then its
four diagonal ones: the round is proven on lines, half a `G` each, and then
on single operations, each reordered by a checker (see "Lines" below); each
kind of operation is symbolically executed once (`op_ok`). The message words
are read from the copy of the block in the scratch space (`Msg`).
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64

open VG VG.RISCV64
open VG.Impl.Blake2.RISCV64 (sz wd ws wreg T RT SB mOff)
open VG.Spec.Blake2 (Params Work Block)

/-! ## Words of `z.bits` bits -/

/-- The width of the loads and stores of words. -/
abbrev zW : Size → Width
  | .w => .w
  | .d => .d

/-- The size of a word in bytes. -/
abbrev zB (z : Size) : Nat := (zW z).bytes

theorem wd_bits (z : Size) : wd z.bits = zW z := by cases z <;> rfl

theorem ws_bits (z : Size) : ws z.bits = zB z := by cases z <;> rfl

theorem bits_div (z : Size) : z.bits / 8 = zB z := by cases z <;> rfl

theorem bits_le (z : Size) : z.bits ≤ 64 := by cases z <;> decide

theorem zB_le (z : Size) : zB z ≤ 8 := by cases z <;> decide

theorem zB_pos (z : Size) : 0 < zB z := by cases z <;> decide

theorem ext_trunc (z : Size) (v : BitVec z.bits) : (v.setWidth 64).setWidth z.bits = v := by
  cases z
  · rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  · simp only [Size.bits, BitVec.setWidth_eq]

theorem trunc_ofNat (z : Size) (n : Nat) : (BitVec.ofNat 64 n).setWidth z.bits = BitVec.ofNat z.bits n := by
  cases z
  · simp only [Size.bits]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  · exact BitVec.setWidth_eq _

theorem lo_add (z : Size) (x y : BitVec 64) :
    (x + y).setWidth z.bits = x.setWidth z.bits + y.setWidth z.bits :=
  BitVec.setWidth_add x y (bits_le z)

theorem lo_xor (z : Size) (x y : BitVec 64) :
    (x ^^^ y).setWidth z.bits = x.setWidth z.bits ^^^ y.setWidth z.bits := by
  ext i hi; simp

theorem lo_or (z : Size) (x y : BitVec 64) :
    (x ||| y).setWidth z.bits = x.setWidth z.bits ||| y.setWidth z.bits := by
  ext i hi; simp

/-- A right shift of words of `z.bits` bits: its low word is the shifted low word. -/
theorem exec_srl_z {z : Size} {s : State} {d n : Reg} {sh : Nat} (h : sh < z.bits) :
    ∃ v : BitVec 64, exec (.shift .srl (sz z.bits) d n sh) s = some (s.write d v) ∧
      v.setWidth z.bits = (s.gpr n).setWidth z.bits >>> sh := by
  cases z
  · exact ⟨_, exec_shift_w h, lo32_sext _⟩
  · exact ⟨_, exec_shift_d h, by simp only [Size.bits, BitVec.setWidth_eq]⟩

/-- A left shift of words of `z.bits` bits: its low word is the shifted low word. -/
theorem exec_sll_z {z : Size} {s : State} {d n : Reg} {sh : Nat} (h : sh < z.bits) :
    ∃ v : BitVec 64, exec (.shift .sll (sz z.bits) d n sh) s = some (s.write d v) ∧
      v.setWidth z.bits = (s.gpr n).setWidth z.bits <<< sh := by
  cases z
  · exact ⟨_, exec_shift_w h, lo32_sext _⟩
  · exact ⟨_, exec_shift_d h, by simp only [Size.bits, BitVec.setWidth_eq]⟩

/-- An offset `d` of an address that is a multiple of 8 is aligned for words
if `d` is. -/
theorem al (z : Size) {p : Addr} (hp : p.toNat % 8 = 0) {d : Nat} (hd : d % zB z = 0) :
    (p + BitVec.ofNat 64 d).toNat % zB z = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  cases z <;> simp only [zB, Width.bytes] at hd ⊢ <;> omega

theorem exec_ld {z : Size} {s : State} {t n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % zB z = 0)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) (zB z)) :
    exec (.load (wd z.bits) t n off) s =
      some (s.write t ((s.mem.readW (s.gpr n + BitVec.ofNat 64 off) z.bits).setWidth 64)) := by
  rw [wd_bits]
  cases z
  · exact exec_load_w ho ha h
  · rw [exec_load_d ho ha h, BitVec.setWidth_eq]

theorem exec_st {z : Size} {s : State} {t n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % zB z = 0)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) (zB z)) :
    exec (.store (wd z.bits) t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr t).setWidth z.bits) } := by
  rw [wd_bits]
  cases z
  · exact exec_store_w ho ha h
  · rw [exec_store_d ho ha h, BitVec.setWidth_eq]

theorem readW_writeW_self (z : Size) (m : Mem) (a : Addr) (v : BitVec z.bits) :
    (m.writeW a v).readW a z.bits = v := by
  cases z
  · exact Mem.readW_writeW_self32 m a v
  · exact Mem.readW_writeW_self64 m a v

/-! ## The pieces of `G` -/

section G
variable {z : Size} (P : Params z.bits)

/-- The rotations of `P` are encodable at the word size, and not zero. -/
def ROk : Prop :=
  0 < P.R1 ∧ P.R1 < z.bits ∧ 0 < P.R2 ∧ P.R2 < z.bits ∧ 0 < P.R3 ∧ P.R3 < z.bits ∧
    0 < P.R4 ∧ P.R4 < z.bits

/-- Rotation `k` of `P`: `R1`–`R4` for `k = 0 … 3`. -/
def rotOf : Nat → Nat
  | 0 => P.R1
  | 1 => P.R2
  | 2 => P.R3
  | _ => P.R4

theorem rotOf_ok (hR : ROk P) {k : Nat} (hk : k < 4) : 0 < rotOf P k ∧ rotOf P k < z.bits := by
  obtain ⟨p1, h1, p2, h2, p3, h3, p4, h4⟩ := hR
  match k, hk with
  | 0, _ => exact ⟨p1, h1⟩
  | 1, _ => exact ⟨p2, h2⟩
  | 2, _ => exact ⟨p3, h3⟩
  | 3, _ => exact ⟨p4, h4⟩

end G

/-! ## The work vector in registers -/

/-- The registers of the work vector. -/
def wregs : List Reg :=
  [.a3, .a4, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4, .s5]

theorem wreg_mem' : ∀ k < 16, wreg k ∈ wregs := by decide

theorem wreg_mem {k : Nat} (hk : k < 16) : wreg k ∈ wregs := wreg_mem' k hk

theorem wreg_inj' : ∀ i < 16, ∀ j < 16, wreg i = wreg j → i = j := by decide

theorem wreg_ne {i j : Nat} (hi : i < 16) (hj : j < 16) (h : i ≠ j) : wreg i ≠ wreg j :=
  fun e => h (wreg_inj' i hi j hj e)

theorem ne_wreg {q : Reg} (hq : q ∉ wregs) {k : Nat} (hk : k < 16) : q ≠ wreg k :=
  fun e => hq (by rw [e]; exact wreg_mem hk)

theorem wreg_ne_of {q : Reg} (hq : q ∉ wregs) {k : Nat} (hk : k < 16) : wreg k ≠ q :=
  fun e => hq (e ▸ wreg_mem hk)

theorem T_not_mem : T ∉ wregs := by decide
theorem SB_not_mem : SB ∉ wregs := by decide

section Rounds
variable {z : Size} (P : Params z.bits)

/-- The work vector `v` is in the low `z.bits` bits of its registers. -/
def Vars (s : State) (v : Work z.bits) : Prop :=
  ∀ k (hk : k < 16), (s.gpr (wreg k)).setWidth z.bits = (v[k]'(by omega))

/-- The rounds invariant, relative to the state `sB` at their start: the work
vector `v` is in its registers, and nothing else has changed but `T` and `RT`. -/
structure RI (sB : State) (v : Work z.bits) (s : State) : Prop where
  vars : Vars s v
  other : ∀ q, q ∉ wregs → q ≠ T → q ≠ RT → s.gpr q = sB.gpr q
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

/-- The message block `M` is at `mOff` of the scratch space at `p` (a multiple
of 8), in the permitted regions. -/
structure Msg (M : Block z.bits) (p : Addr) (s : State) : Prop where
  sb : s.gpr SB = p
  al : p.toNat % 8 = 0
  inr : ∀ j < 16, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (mOff + zB z * j)) (zB z)
  word : ∀ j (hj : j < 16), s.mem.readW (p + BitVec.ofNat 64 (mOff + zB z * j)) z.bits = M ⟨j, hj⟩

theorem Msg.of_RI {M : Block z.bits} {p : Addr} {sB s : State} {v : Work z.bits} (h : Msg M p sB)
    (hr : RI sB v s) : Msg M p s :=
  ⟨(hr.other _ SB_not_mem (by decide) (by decide)).trans h.sb, h.al,
    by rw [hr.rd, hr.wr]; exact h.inr, by rw [hr.mem]; exact h.word⟩

theorem mOff_al (z : Size) (j : Nat) : (mOff + zB z * j) % zB z = 0 := by
  cases z <;> simp only [mOff, zB, Width.bytes] <;> omega

/-! ## Lines: half of a `G` on the work vector

The code runs a round's four column `G`s side by side, then its four diagonal
ones (`Impl.Blake2.RISCV64.half`). The round is proven on *lines*, half of a
`G` each (`bline`): the spec's order of lines is the code's after moving lines
only past lines on other words (`LSame`, decided); then on single operations
(`Op`), each proven once (`op_ok`), whose order in the code is that of the
lines after moving operations only past operations on other registers
(`OSame`, decided). Both checkers see only the slots, the message selector
and the rotation number of each line or operation: the rotations of `P`, the
round's permutation of the message and the word size stay symbolic. -/

/-- An index `i < 16` as a `Fin 16`. -/
def fin16 (i : Nat) : Fin 16 := ⟨i % 16, Nat.mod_lt _ (by decide)⟩

/-- The message word of selector `n` of round `r`: none (`0`) for `n = 0`, else
word `s[n - 1]` of the round's permutation `s`. -/
def msgOf (r : Nat) (M : Block z.bits) (n : Nat) : BitVec z.bits :=
  if n = 0 then 0 else M (Spec.Blake2.sigmaAt r (n - 1))

theorem msgOf_zero (r : Nat) (M : Block z.bits) : msgOf r M 0 = 0 := rfl

theorem add_msgOf_zero (r : Nat) (M : Block z.bits) (y : BitVec z.bits) : y + msgOf r M 0 = y := by
  simp [msgOf]

theorem msgOf_succ (r : Nat) (M : Block z.bits) (n : Nat) :
    msgOf r M (n + 1) = M (Spec.Blake2.sigmaAt r n) := rfl

/-- Half of a `G`: `x[a] += x[b] + m; x[d] = (x[d] ^ x[a]) ⋙ R`, with the message
word `m` of selector `n` and the rotation `R` number `k`. -/
def bline (r : Nat) (M : Block z.bits) (x : Work z.bits) (a b d n k : Nat) : Work z.bits :=
  let y := x.set (fin16 a) (x[fin16 a] + x[fin16 b] + msgOf r M n)
  y.set (fin16 d) ((y[fin16 d] ^^^ y[fin16 a]).rotateRight (rotOf P k))

/-- A line: `(a, b, d, n, k)`. -/
abbrev Line := Nat × Nat × Nat × Nat × Nat

/-- The lines of a list in turn. -/
abbrev blines (r : Nat) (M : Block z.bits) (l : List Line) (v : Work z.bits) : Work z.bits :=
  l.foldl (fun x (a, b, d, n, k) => bline P r M x a b d n k) v

theorem bline_get (r : Nat) (M : Block z.bits) (x : Work z.bits) {a b d : Nat} (n k : Nat) (ha : a < 16)
    (hb : b < 16) (hd : d < 16) (had : a ≠ d) (m : Nat) (hm : m < 16) :
    (bline P r M x a b d n k)[m] =
      if d = m then (x[d] ^^^ (x[a] + x[b] + msgOf r M n)).rotateRight (rotOf P k)
      else if a = m then x[a] + x[b] + msgOf r M n else x[m] := by
  simp only [bline, fin16, Vector.getElem_set, Fin.getElem_fin, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hd, had, ite_false, ite_true]

/-- A `G`'s lines, with the message words of selectors `n₁` and `n₂`. -/
def gLines (a b c d n₁ n₂ : Nat) : List Line :=
  [(a, b, d, n₁, 0), (c, d, b, 0, 1), (a, b, d, n₂, 2), (c, d, b, 0, 3)]

/-- A `G` is its four lines. -/
theorem G_blines (r : Nat) (M : Block z.bits) (v : Work z.bits) (a b c d : Fin 16) (hab : a.1 ≠ b.1)
    (hac : a.1 ≠ c.1) (had : a.1 ≠ d.1) (hbc : b.1 ≠ c.1) (hbd : b.1 ≠ d.1) (hcd : c.1 ≠ d.1) (j k : Nat) :
    Spec.Blake2.G P v a b c d (M (Spec.Blake2.sigmaAt r j)) (M (Spec.Blake2.sigmaAt r k)) =
      blines P r M (gLines a.1 b.1 c.1 d.1 (j + 1) (k + 1)) v := by
  apply Vector.ext
  intro m hm
  have ha := a.2; have hb := b.2; have hc := c.2; have hd := d.2
  rw [G_get P v hab hac had hbc hbd hcd _ _ m hm]
  have ncb := Ne.symm hbc
  simp only [blines, gLines, List.foldl_cons, List.foldl_nil, bline_get, ha, hb, hc, hd, had, ncb, ne_eq,
    not_false_eq_true, msgOf_succ, msgOf_zero]
  have := Ne.symm hab; have := Ne.symm hac; have := Ne.symm had; have := Ne.symm hbd; have := Ne.symm hcd
  by_cases eb : b.1 = m
  · subst eb; simp [mix, rotOf, *]
  by_cases ec : c.1 = m
  · subst ec; simp [mix, rotOf, *]
  by_cases ed : d.1 = m
  · subst ed; simp [mix, rotOf, *]
  by_cases ea : a.1 = m
  · subst ea; simp [mix, rotOf, *]
  simp [*]

/-- A round's lines in the spec's order. -/
def specLines : List Line :=
  gLines 0 4 8 12 1 2 ++ gLines 1 5 9 13 3 4 ++ gLines 2 6 10 14 5 6 ++ gLines 3 7 11 15 7 8 ++
  gLines 0 5 10 15 9 10 ++ gLines 1 6 11 12 11 12 ++ gLines 2 7 8 13 13 14 ++ gLines 3 4 9 14 15 16

theorem round_spec (r : Nat) (M : Block z.bits) (v : Work z.bits) :
    Spec.Blake2.round P M v r = blines P r M specLines v := by
  simp only [Spec.Blake2.round, specLines, blines, List.foldl_append]
  rw [G_blines P r M _ 0 4 8 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 0 1,
    G_blines P r M _ 1 5 9 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 2 3,
    G_blines P r M _ 2 6 10 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 4 5,
    G_blines P r M _ 3 7 11 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 6 7,
    G_blines P r M _ 0 5 10 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 8 9,
    G_blines P r M _ 1 6 11 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 10 11,
    G_blines P r M _ 2 7 8 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 12 13,
    G_blines P r M _ 3 4 9 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 14 15]
  rfl

/-- Lines `l` and `l'` touch disjoint words. -/
def LIndep : Line → Line → Bool
  | (a, b, d, _, _), (a', b', d', _, _) =>
    decide (a < 16 ∧ b < 16 ∧ d < 16 ∧ a' < 16 ∧ b' < 16 ∧ d' < 16 ∧ a ≠ d ∧ a' ≠ d' ∧
      a ≠ a' ∧ a ≠ b' ∧ a ≠ d' ∧ b ≠ a' ∧ b ≠ d' ∧ d ≠ a' ∧ d ≠ b' ∧ d ≠ d')

theorem bline_comm {r : Nat} {M : Block z.bits} {x : Work z.bits} {a b d n k a' b' d' n' k' : Nat}
    (h : LIndep (a, b, d, n, k) (a', b', d', n', k') = true) :
    bline P r M (bline P r M x a b d n k) a' b' d' n' k' = bline P r M (bline P r M x a' b' d' n' k') a b d n k := by
  simp only [LIndep, decide_eq_true_eq] at h
  obtain ⟨ha, hb, hd, ha', hb', hd', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  apply Vector.ext
  intro m hm
  have := Ne.symm h3; have := Ne.symm h4; have := Ne.symm h5; have := Ne.symm h6; have := Ne.symm h7
  have := Ne.symm h8; have := Ne.symm h9; have := Ne.symm h10
  simp only [bline_get, ha, hb, hd, ha', hb', hd', h1, h2, ne_eq, not_false_eq_true]
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
def lpull (p : Line) : List Line → Option (List Line)
  | [] => none
  | q :: l => if q = p then some l else if LIndep q p then (lpull p l).map (q :: ·) else none

/-- `l'` runs the lines of `l`, each moved only past lines on other words. -/
def LSame : List Line → List Line → Bool
  | [], [] => true
  | p :: l', l => match lpull p l with
    | some r => LSame l' r
    | none => false
  | [], _ :: _ => false

theorem blines_cons (r : Nat) (M : Block z.bits) (p : Line) (l : List Line) (v : Work z.bits) :
    blines P r M (p :: l) v = blines P r M l (bline P r M v p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  obtain ⟨a, b, d, n, k⟩ := p; rfl

theorem lpull_ok {r : Nat} {M : Block z.bits} {p : Line} :
    ∀ {l l₁ : List Line}, lpull p l = some l₁ →
      ∀ v, blines P r M l v = blines P r M l₁ (bline P r M v p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  | [], _, h, _ => by simp [lpull] at h
  | q :: l, l₁, h, v => by
    unfold lpull at h
    by_cases e : q = p
    · subst e; simp only [ite_true, Option.some.injEq] at h; subst h; exact blines_cons _ _ _ _ _ _
    · simp only [e, ite_false] at h
      by_cases hq : LIndep q p = true
      · simp only [hq, ite_true] at h
        obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h
        rw [blines_cons, lpull_ok hl', blines_cons]
        obtain ⟨a, b, d, n, k⟩ := q; obtain ⟨a', b', d', n', k'⟩ := p
        exact congrArg _ (bline_comm P hq)
      · simp only [hq, Bool.false_eq_true, ite_false, reduceCtorEq] at h

theorem lsame_ok {r : Nat} {M : Block z.bits} : ∀ {l' l : List Line}, LSame l' l = true →
    ∀ v, blines P r M l' v = blines P r M l v
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [LSame] at h
  | p :: l', l, h, v => by
    unfold LSame at h
    split at h
    · rename_i l₁ hl
      rw [blines_cons, lpull_ok P hl, lsame_ok h]
    · simp at h

/-- Half `h` of the four `G`s `(i, x, y, c, d)` of `qs`, as lines in the code's order. -/
def halfLines (qs : List (Nat × Nat × Nat × Nat × Nat)) (h : Nat) : List Line :=
  qs.map (fun (i, x, y, _, d) => (x, y, d, 2 * i + h + 1, 2 * h)) ++
  qs.map (fun (_, _, y, c, d) => (c, d, y, 0, 2 * h + 1))

/-- A round's lines in the code's order. -/
def codeLines : List Line :=
  halfLines Impl.Blake2.RISCV64.columns 0 ++ halfLines Impl.Blake2.RISCV64.columns 1 ++
    halfLines Impl.Blake2.RISCV64.diagonals 0 ++ halfLines Impl.Blake2.RISCV64.diagonals 1

theorem round_lines (r : Nat) (M : Block z.bits) (v : Work z.bits) :
    Spec.Blake2.round P M v r = blines P r M codeLines v := by
  rw [round_spec, lsame_ok P (l' := specLines) (l := codeLines) (by decide)]

/-! ## The rounds as operations on eighteen slots

The sixteen words of the work vector (slots 0–15), `T` (16) and `RT` (17). -/

/-- The register of slot `i`. -/
def sreg (i : Nat) : Reg := if i < 16 then wreg i else if i = 16 then T else RT

theorem sreg_inj {i j : Nat} (hi : i < 18) (hj : j < 18) (h : sreg i = sreg j) : i = j := by
  have key : ∀ i < 18, ∀ j < 18, sreg i = sreg j → i = j := by decide
  exact key i hi j hj h

theorem sreg_word {k : Nat} (hk : k < 16) : sreg k = wreg k := by simp [sreg, hk]

/-- One instruction of a round, on slots: `ld n` loads the message word of selector
`n` into `T`; `shr d k` shifts slot `d` right by rotation `k` into `RT`, and
`shl d k` shifts it left by the rest of the word; `or d` puts `RT` back. -/
inductive Op
  | add (a b : Nat)
  | ld (n : Nat)
  | xor (d a : Nat)
  | shr (d k : Nat)
  | shl (d k : Nat)
  | or (d : Nat)
  deriving DecidableEq

def Op.code (r : Nat) : Op → Instr
  | .add a b => .add (sreg a) (sreg a) (sreg b)
  | .ld n => .load (wd z.bits) T SB (mOff + ws z.bits * Spec.Blake2.sigmaAt r (n - 1))
  | .xor d a => .logic .xor (sreg d) (sreg d) (sreg a)
  | .shr d k => .shift .srl (sz z.bits) RT (sreg d) (rotOf P k)
  | .shl d k => .shift .sll (sz z.bits) (sreg d) (sreg d) (z.bits - rotOf P k)
  | .or d => .logic .or (sreg d) (sreg d) RT

/-- The slot an operation writes, and those it reads. -/
def Op.dst : Op → Nat
  | .add a _ | .xor a _ | .shl a _ | .or a => a
  | .ld _ => 16
  | .shr _ _ => 17
def Op.srcs : Op → List Nat
  | .add a b | .xor a b => [a, b]
  | .ld _ => []
  | .shr d _ | .shl d _ => [d]
  | .or d => [d, 17]

/-- The value an operation writes. -/
def Op.val (r : Nat) (M : Block z.bits) (x : Nat → BitVec z.bits) : Op → BitVec z.bits
  | .add a b => x a + x b
  | .ld n => msgOf r M n
  | .xor d a => x d ^^^ x a
  | .shr d k => x d >>> rotOf P k
  | .shl d k => x d <<< (z.bits - rotOf P k)
  | .or d => x d ||| x 17

def Op.step (r : Nat) (M : Block z.bits) (x : Nat → BitVec z.bits) (op : Op) : Nat → BitVec z.bits :=
  fun j => if j = op.dst then op.val P r M x else x j

/-- The slots exist (the words are below 16), the message selectors are not `0`,
and the rotation numbers are below 4. -/
def Op.Valid : Op → Bool
  | .add a b => decide (a < 16 ∧ b < 17)
  | .ld n => decide (0 < n)
  | .xor d a => decide (d < 16 ∧ a < 16)
  | .shr d k | .shl d k => decide (d < 16 ∧ k < 4)
  | .or d => decide (d < 16)

theorem Op.val_congr {r : Nat} {M : Block z.bits} {x y : Nat → BitVec z.bits} (op : Op)
    (h : ∀ i ∈ op.srcs, x i = y i) : op.val P r M x = op.val P r M y := by
  cases op <;> simp only [Op.srcs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h <;>
    simp only [Op.val, h]

/-- The slots hold `x`. -/
def Holds18 (x : Nat → BitVec z.bits) (s : State) : Prop := ∀ i < 18, (s.gpr (sreg i)).setWidth z.bits = x i

/-- What an operation leaves. -/
structure OpPost (x : Nat → BitVec z.bits) (s s' : State) : Prop where
  holds : Holds18 x s'
  keep : ∀ q, (∀ i < 18, q ≠ sreg i) → s'.gpr q = s.gpr q
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem SB_ne_sreg : ∀ i < 18, SB ≠ sreg i := by decide

theorem ob (z : Size) {j : Nat} (hj : j < 16) : mOff + ws z.bits * j < 2048 := by
  rw [ws_bits]; have := zB_le z
  have := Nat.mul_le_mul this (Nat.le_of_lt_succ hj)
  simp only [mOff]; omega

theorem op_ok (hR : ROk P) (r : Nat) {M : Block z.bits} {p : Addr} (op : Op) (hv : op.Valid = true)
    {x : Nat → BitVec z.bits} {s : State} (hm : Msg M p s) (h : Holds18 x s) :
    WP isa (.block [op.code P r]) s (OpPost (op.step P r M x) s) := by
  have hd : op.dst < 18 := by cases op <;> simp_all [Op.Valid, Op.dst] <;> omega
  have hs : ∀ i ∈ op.srcs, i < 18 := by
    cases op <;> simp_all [Op.Valid, Op.srcs] <;> omega
  -- The instruction writes the value of `op` into its slot's register, and nothing else.
  have hw : ∃ v : BitVec 64, exec (op.code P r) s = some (s.write (sreg op.dst) v) ∧
      v.setWidth z.bits = op.val P r M x := by
    cases op with
    | add a b =>
      exact ⟨_, exec_add, by
        simp only [lo_add, h a (hs a (by simp [Op.srcs])), h b (hs b (by simp [Op.srcs])), Op.val]⟩
    | ld n =>
      have hn : n ≠ 0 := by simp only [Op.Valid, decide_eq_true_eq] at hv; omega
      have sj := (Spec.Blake2.sigmaAt r (n - 1)).isLt
      refine ⟨_, exec_ld (ob z sj) (by rw [hm.sb, ws_bits]; exact al z hm.al (mOff_al z _))
        (by rw [hm.sb, ws_bits]; exact hm.inr _ sj), ?_⟩
      rw [ext_trunc, hm.sb, ws_bits, hm.word _ sj]
      simp only [Op.val, msgOf, hn, ite_false]
    | xor d a =>
      exact ⟨_, exec_logic, by
        simp only [lo_xor, h d (hs d (by simp [Op.srcs])), h a (hs a (by simp [Op.srcs])), Op.val]⟩
    | shr d k =>
      have hk : k < 4 := by simp only [Op.Valid, decide_eq_true_eq] at hv; exact hv.2
      obtain ⟨v, he, hv'⟩ := exec_srl_z (z := z) (s := s) (d := RT) (n := sreg d) (rotOf_ok P hR hk).2
      exact ⟨v, he, by rw [hv', h d (hs d (by simp [Op.srcs]))]; rfl⟩
    | shl d k =>
      have hk : k < 4 := by simp only [Op.Valid, decide_eq_true_eq] at hv; exact hv.2
      have := rotOf_ok P hR hk
      obtain ⟨v, he, hv'⟩ := exec_sll_z (z := z) (s := s) (d := sreg d) (n := sreg d)
        (show z.bits - rotOf P k < z.bits by omega)
      exact ⟨v, he, by rw [hv', h d (hs d (by simp [Op.srcs]))]; rfl⟩
    | or d =>
      exact ⟨_, exec_logic, by
        simp only [lo_or, h d (hs d (by simp [Op.srcs])), Op.val]
        rw [show RT = sreg 17 from rfl, h 17 (by decide)]⟩
  obtain ⟨v, he, hv'⟩ := hw
  apply WP.of_runBlock
  refine ⟨s.write (sreg op.dst) v, by rw [runBlock_cons, he]; rfl, ⟨fun i hi => ?_, fun q hq => ?_, rfl, rfl, rfl⟩⟩
  · by_cases e : i = op.dst
    · subst e; rw [RegUpd.gpr_write_self, hv']; simp only [Op.step, ↓reduceIte]
    · rw [RegUpd.gpr_write_of_ne _ _ (show sreg i ≠ sreg op.dst from fun e' => e (sreg_inj hi hd e')), h i hi]
      simp only [Op.step, e, ↓reduceIte]
  · exact RegUpd.gpr_write_of_ne _ _ fun e => hq _ hd e

/-- The operations of `ops` in turn. -/
def stepAll (r : Nat) (M : Block z.bits) (x : Nat → BitVec z.bits) (ops : List Op) : Nat → BitVec z.bits :=
  ops.foldl (Op.step P r M) x

theorem ops_ok (hR : ROk P) (r : Nat) {M : Block z.bits} {p : Addr} :
    ∀ (ops : List Op), (ops.all Op.Valid) = true → ∀ {x : Nat → BitVec z.bits} {s : State}, Msg M p s →
      Holds18 x s → WP isa (.block (ops.map (Op.code P r))) s (OpPost (stepAll P r M x ops) s)
  | [], _, _, s, _, h => WP.block_nil ⟨h, fun _ _ => rfl, rfl, rfl, rfl⟩
  | op :: ops, hv, x, s, hm, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hv
    rw [List.map_cons, show op.code P r :: ops.map (Op.code P r) = [op.code P r] ++ ops.map (Op.code P r) from rfl,
      WP.block_append_iff]
    refine WP.mono (op_ok P hR r op hv.1 hm h) fun s₁ h₁ => ?_
    have hm₁ : Msg M p s₁ :=
      ⟨(h₁.keep SB SB_ne_sreg).trans hm.sb, hm.al, by rw [h₁.rd, h₁.wr]; exact hm.inr,
        by rw [h₁.mem]; exact hm.word⟩
    exact WP.mono (ops_ok hR r ops hv.2 hm₁ h₁.holds) fun s₂ h₂ =>
      ⟨h₂.holds, fun q hq => (h₂.keep q hq).trans (h₁.keep q hq), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
        h₂.wr.trans h₁.wr⟩

/-! ### Reordering operations -/

/-- Two operations on separate slots: neither writes what the other reads or writes. -/
def OIndep (o o' : Op) : Bool :=
  decide (o.dst ≠ o'.dst ∧ o.dst ∉ o'.srcs ∧ o'.dst ∉ o.srcs)

theorem op_comm {r : Nat} {M : Block z.bits} {x : Nat → BitVec z.bits} {o o' : Op} (h : OIndep o o' = true) :
    Op.step P r M (Op.step P r M x o) o' = Op.step P r M (Op.step P r M x o') o := by
  simp only [OIndep, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have v1 : o'.val P r M (Op.step P r M x o) = o'.val P r M x :=
    o'.val_congr P fun i hi => by
      have : i ≠ o.dst := fun e => h2 (e ▸ hi)
      simp only [Op.step, this, ↓reduceIte]
  have v2 : o.val P r M (Op.step P r M x o') = o.val P r M x :=
    o.val_congr P fun i hi => by
      have : i ≠ o'.dst := fun e => h3 (e ▸ hi)
      simp only [Op.step, this, ↓reduceIte]
  funext j
  show (if j = o'.dst then o'.val P r M (Op.step P r M x o) else Op.step P r M x o j) =
    (if j = o.dst then o.val P r M (Op.step P r M x o') else Op.step P r M x o' j)
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

theorem opull_ok {r : Nat} {M : Block z.bits} {o : Op} : ∀ {l l₁ : List Op}, opull o l = some l₁ →
    ∀ x, stepAll P r M x l = stepAll P r M (Op.step P r M x o) l₁
  | [], _, h, _ => by simp [opull] at h
  | p :: l, l₁, h, x => by
    unfold opull at h
    by_cases e : p = o
    · subst e; simp only [ite_true, Option.some.injEq] at h; subst h; rfl
    · simp only [e, ite_false] at h
      by_cases hp : OIndep p o = true
      · simp only [hp, ite_true] at h
        obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h
        show stepAll P r M (Op.step P r M x p) l = stepAll P r M (Op.step P r M (Op.step P r M x o) p) l'
        rw [opull_ok hl', op_comm P hp]
      · simp only [hp, Bool.false_eq_true, ite_false, reduceCtorEq] at h

theorem osame_ok {r : Nat} {M : Block z.bits} : ∀ {l' l : List Op}, OSame l' l = true →
    ∀ x, stepAll P r M x l' = stepAll P r M x l
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [OSame] at h
  | o :: l', l, h, x => by
    unfold OSame at h
    split at h
    · rename_i l₁ hl
      show stepAll P r M (Op.step P r M x o) l' = stepAll P r M x l
      rw [opull_ok P hl, osame_ok h]
    · simp at h

/-! ### Lines as operations -/

/-- A line's operations. -/
def lineOps : Line → List Op
  | (a, b, d, n, k) => ([.add a b] : List Op) ++ (if n = 0 then [] else ([.ld n, .add a 16] : List Op)) ++
    ([.xor d a, .shr d k, .shl d k, .or d] : List Op)

/-- The words of the slots. -/
def words (x : Nat → BitVec z.bits) : Work z.bits := Vector.ofFn fun i => x i.1

theorem rotr_shifts {y : BitVec z.bits} {R : Nat} (hr : R < z.bits) :
    y <<< (z.bits - R) ||| y >>> R = y.rotateRight R := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hr, BitVec.or_comm]

theorem lineOps_words (hR : ROk P) (r : Nat) (M : Block z.bits) (x : Nat → BitVec z.bits) {a b d n k : Nat}
    (ha : a < 16) (hb : b < 16) (hd : d < 16) (had : a ≠ d) (hk : k < 4) :
    words (stepAll P r M x (lineOps (a, b, d, n, k))) = bline P r M (words x) a b d n k := by
  have hrk := (rotOf_ok P hR hk).2
  apply Vector.ext
  intro m hm
  have hda : d ≠ a := Ne.symm had
  have h16a : (16 : Nat) ≠ a := by omega
  have h16d : (16 : Nat) ≠ d := by omega
  have h17d : (17 : Nat) ≠ d := by omega
  have h17a : (17 : Nat) ≠ a := by omega
  have hm16 : m ≠ 16 := by omega
  have hm17 : m ≠ 17 := by omega
  rw [bline_get P r M _ n k ha hb hd had m hm]
  by_cases hn : n = 0
  · subst hn
    simp only [words, stepAll, lineOps, List.foldl_cons, List.foldl_nil, List.nil_append, List.cons_append,
      ↓reduceIte, Op.step, Op.dst, Op.val, Vector.getElem_ofFn, add_msgOf_zero]
    by_cases e1 : m = d
    · subst e1; simp only [hda, h17d, ↓reduceIte, Ne.symm h17d]; rw [rotr_shifts hrk]
    · by_cases e2 : m = a
      · subst e2; simp only [e1, hm17, ↓reduceIte, Ne.symm e1]
      · simp only [e1, e2, hm17, ↓reduceIte, Ne.symm e1, Ne.symm e2]
  · simp only [words, stepAll, lineOps, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, hn,
      ↓reduceIte, Op.step, Op.dst, Op.val, Vector.getElem_ofFn]
    by_cases e1 : m = d
    · subst e1; simp only [hda, h17d, ↓reduceIte, Ne.symm h17d, Ne.symm h16a, Ne.symm h16d]
      rw [rotr_shifts hrk]
    · by_cases e2 : m = a
      · subst e2; simp only [e1, hm17, hm16, ↓reduceIte, Ne.symm e1]
      · simp only [e1, e2, hm17, hm16, ↓reduceIte, Ne.symm e1, Ne.symm e2]

/-- The lines in turn, as operations. -/
def linesOps (l : List Line) : List Op := l.flatMap lineOps

theorem linesOps_words (hR : ROk P) (r : Nat) (M : Block z.bits) : ∀ (l : List Line) (x : Nat → BitVec z.bits),
    (l.all fun (a, b, d, _, k) => decide (a < 16 ∧ b < 16 ∧ d < 16 ∧ a ≠ d ∧ k < 4)) = true →
    words (stepAll P r M x (linesOps l)) = blines P r M l (words x)
  | [], _, _ => rfl
  | (a, b, d, n, k) :: l, x, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ha, hb, hd, had, hk⟩, hl⟩ := h
    rw [linesOps, List.flatMap_cons, stepAll, List.foldl_append, ← stepAll, ← stepAll, ← linesOps,
      linesOps_words hR r M l _ hl, lineOps_words P hR r M _ ha hb hd had hk]
    simp only [blines, List.foldl_cons]

/-- Half `h` of the four `G`s `(i, x, y, c, d)` of `qs`, as the code's operations. -/
def halfOps (qs : List (Nat × Nat × Nat × Nat × Nat)) (h : Nat) : List Op :=
  qs.map (fun (_, x, y, _, _) => .add x y) ++
  qs.flatMap (fun (i, x, _, _, _) => [.ld (2 * i + h + 1), .add x 16]) ++
  qs.map (fun (_, x, _, _, d) => .xor d x) ++
  qs.flatMap (fun (_, _, _, _, d) => [.shr d (2 * h), .shl d (2 * h), .or d]) ++
  qs.map (fun (_, _, _, c, d) => .add c d) ++
  qs.map (fun (_, _, y, c, _) => .xor y c) ++
  qs.flatMap (fun (_, _, y, _, _) => [.shr y (2 * h + 1), .shl y (2 * h + 1), .or y])

/-- A round's operations as the code runs them. -/
def roundOps : List Op :=
  halfOps Impl.Blake2.RISCV64.columns 0 ++ halfOps Impl.Blake2.RISCV64.columns 1 ++
    halfOps Impl.Blake2.RISCV64.diagonals 0 ++ halfOps Impl.Blake2.RISCV64.diagonals 1

/-- The code of a round is its operations. -/
theorem round_code (r : Nat) : Impl.Blake2.RISCV64.round P r = .block (roundOps.map (Op.code P r)) := by
  have h1 : Impl.Blake2.RISCV64.half (w := z.bits) Impl.Blake2.RISCV64.columns r 0 P.R1 P.R2 =
      (halfOps Impl.Blake2.RISCV64.columns 0).map (Op.code P r) := rfl
  have h2 : Impl.Blake2.RISCV64.half (w := z.bits) Impl.Blake2.RISCV64.columns r 1 P.R3 P.R4 =
      (halfOps Impl.Blake2.RISCV64.columns 1).map (Op.code P r) := rfl
  have h3 : Impl.Blake2.RISCV64.half (w := z.bits) Impl.Blake2.RISCV64.diagonals r 0 P.R1 P.R2 =
      (halfOps Impl.Blake2.RISCV64.diagonals 0).map (Op.code P r) := rfl
  have h4 : Impl.Blake2.RISCV64.half (w := z.bits) Impl.Blake2.RISCV64.diagonals r 1 P.R3 P.R4 =
      (halfOps Impl.Blake2.RISCV64.diagonals 1).map (Op.code P r) := rfl
  rw [Impl.Blake2.RISCV64.round, roundOps, List.map_append, List.map_append, List.map_append, h1, h2, h3, h4]

theorem roundOps_fold (hR : ROk P) (r : Nat) (M : Block z.bits) (x : Nat → BitVec z.bits) :
    words (stepAll P r M x roundOps) = blines P r M codeLines (words x) := by
  rw [osame_ok P (l := linesOps codeLines) (by decide) x]
  exact linesOps_words P hR r M _ x (by decide)

/-- The slots of a state. -/
def slots (s : State) (i : Nat) : BitVec z.bits := (s.gpr (sreg i)).setWidth z.bits

theorem round_ok (hR : ROk P) (r : Nat) {M : Block z.bits} {p : Addr} {sB s : State}
    {v : Work z.bits} (hM : Msg M p sB) (h : RI sB v s) :
    WP isa (Impl.Blake2.RISCV64.round P r) s (RI sB (Spec.Blake2.round P M v r)) := by
  have hw : words (slots s) = v := by
    apply Vector.ext; intro k hk
    simp only [words, Vector.getElem_ofFn, slots, sreg_word hk]
    exact h.vars k hk
  rw [round_code]
  refine WP.mono (ops_ok P hR r _ (by decide) (hM.of_RI h) (x := slots s) fun i _ => rfl) fun s' h' =>
    ⟨fun k hk => ?_, fun q hq hT hRT => ?_, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr⟩
  · have e : stepAll P r M (slots s) roundOps k = (blines P r M codeLines (words (slots s)))[k] := by
      have := congrArg (·[k]'hk) (roundOps_fold P hR r M (slots s))
      simpa only [words, Vector.getElem_ofFn] using this
    rw [round_lines, ← hw, ← e, ← sreg_word hk]
    exact h'.holds k (by omega)
  · refine (h'.keep q fun i hi e => ?_).trans (h.other q hq hT hRT)
    by_cases hi16 : i < 16
    · exact ne_wreg hq hi16 (by rw [e, sreg_word hi16])
    · by_cases e16 : i = 16
      · exact hT (by rw [e, e16]; rfl)
      · exact hRT (by rw [e]; simp [sreg, hi16, e16])

theorem rounds_ok (hR : ROk P) {M : Block z.bits} {p : Addr} {sB : State} {v : Work z.bits}
    (hM : Msg M p sB) (h : RI sB v sB) (n : Nat) :
    WP isa (Impl.Blake2.RISCV64.rounds P n) sB
      (RI sB ((List.range n).foldl (Spec.Blake2.round P M) v)) := by
  induction n with
  | zero => exact WP.block_nil (M := isa) h
  | succ n ih =>
    refine WP.seq (WP.mono ih fun s hs => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact round_ok P hR n hM hs

end Rounds

end VG.Proof.Blake2.RISCV64
