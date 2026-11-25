module

public import VerifiedGarbage.Proof.Mont.AArch64.P521.Run
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Straight-line carry arithmetic on AArch64: a checker

What a sequence of `Op`s computes, checked by evaluation whatever the order
of its instructions. A *functional* (`Fn`) is a sum modulo `m` of
coefficients times registers and their bit fields, the carry, and the low
and high halves of products. Run backwards over the sequence, one
instruction at a time (`back`), it becomes the functional of the state
before that has the same value (`back_ok`): an addition replaces the
coefficient of its result by the same coefficient on each operand, provided
the coefficient of its carry is `2⁶⁴` times it (or the carry cannot be set);
a product's halves become a product once their coefficients match. So the
output of the code, as a functional of its final state, is compared with a
sum of products of its inputs. The side conditions (a sum that must not
carry) are read off upper bounds on the registers, run forwards (`fwd`).
-/

-- separate module: the checker, for every kernel
@[expose] public section

namespace VG.Proof.Mont.AArch64.P521

open VG VG.AArch64 VG.Impl.Mont.AArch64.P521

/-! ## Registers and places -/

/-- The number of a register. -/
def rn : Reg → Nat
  | .x0 => 0 | .x1 => 1 | .x2 => 2 | .x3 => 3 | .x4 => 4 | .x5 => 5 | .x6 => 6 | .x7 => 7
  | .x8 => 8 | .x9 => 9 | .x10 => 10 | .x11 => 11 | .x12 => 12 | .x13 => 13 | .x14 => 14 | .x15 => 15
  | .x16 => 16 | .x17 => 17 | .x19 => 18 | .x20 => 19 | .x21 => 20 | .x22 => 21 | .x23 => 22
  | .x24 => 23 | .x25 => 24 | .x26 => 25 | .x27 => 26 | .x28 => 27 | .x30 => 28

/-- The register of a number. -/
def nr : Nat → Option Reg
  | 0 => some .x0 | 1 => some .x1 | 2 => some .x2 | 3 => some .x3 | 4 => some .x4 | 5 => some .x5
  | 6 => some .x6 | 7 => some .x7 | 8 => some .x8 | 9 => some .x9 | 10 => some .x10 | 11 => some .x11
  | 12 => some .x12 | 13 => some .x13 | 14 => some .x14 | 15 => some .x15 | 16 => some .x16
  | 17 => some .x17 | 18 => some .x19 | 19 => some .x20 | 20 => some .x21 | 21 => some .x22
  | 22 => some .x23 | 23 => some .x24 | 24 => some .x25 | 25 => some .x26 | 26 => some .x27
  | 27 => some .x28 | 28 => some .x30 | _ => none

theorem nr_rn (r : Reg) : nr (rn r) = some r := by cases r <;> rfl

theorem rn_lt (r : Reg) : rn r < 29 := by cases r <;> decide

theorem nr_eq {l : Nat} {r : Reg} (h : nr l = some r) : l = rn r := by
  unfold nr at h
  split at h <;> first | (cases h; rfl) | exact absurd h (by simp)

theorem rn_inj {a b : Reg} (h : rn a = rn b) : a = b := by
  have := nr_rn a; rw [h, nr_rn b] at this; exact (Option.some.inj this).symm

/-- The place of word `i` of operand `k`. -/
def inpLoc (k i : Nat) : Nat := 32 + 16 * k + i

/-- The number at a place: a register, or a word of an operand. -/
def lv (inp : Nat → Nat → Nat) (s : St) (l : Nat) : Nat :=
  match nr l with
  | some r => s.g r
  | none => inp ((l - 32) / 16) ((l - 32) % 16)

theorem lv_reg (inp : Nat → Nat → Nat) (s : St) (r : Reg) : lv inp s (rn r) = s.g r := by
  simp only [lv, nr_rn]

theorem nr_none {l : Nat} (h : 29 ≤ l) : nr l = none := by
  unfold nr; split <;> first | (exfalso; omega_using [h]) | rfl

theorem lv_inp (inp : Nat → Nat → Nat) (s : St) {k i : Nat} (hi : i < 16) : lv inp s (inpLoc k i) = inp k i := by
  have h1 : (inpLoc k i - 32) / 16 = k := by unfold inpLoc; omega_using [hi]
  have h2 : (inpLoc k i - 32) % 16 = i := by unfold inpLoc; omega_using [hi]
  simp only [lv, nr_none (show 29 ≤ inpLoc k i by unfold inpLoc; omega_using []), h1, h2]

/-- States that agree but on register `d`. -/
def Agree (d : Reg) (s t : St) : Prop := ∀ r, r ≠ d → t.g r = s.g r

theorem lv_agree {inp : Nat → Nat → Nat} {d : Reg} {s t : St} (h : Agree d s t) {l : Nat} (hl : l ≠ rn d) :
    lv inp t l = lv inp s l := by
  unfold lv
  cases hn : nr l with
  | none => rfl
  | some r => exact h r fun e => hl (by rw [nr_eq hn, e])

/-! ## Functionals -/

/-- Bits `lo ≤ · < hi` of the number at `l`, with a coefficient. -/
structure Seg where
  l : Nat
  lo : Nat
  hi : Nat
  w : Nat

/-- The halves of the product of two factors, with coefficients. -/
structure Pr where
  a : Nat
  b : Nat
  cl : Nat
  ch : Nat

/-- A functional: a constant, the carry's coefficient, bit fields, products. -/
structure Fn where
  k : Nat
  f : Nat
  l : List Seg
  p : List Pr

/-- A factor of a product: a place `e` (below 1024), twice the number at a
place, modulo `2⁶⁴` (`1024 + l`), or the word of twice a number of several
words from two of its words (`2048 + 1024 l + l'`, the low one at `l'`). -/
def ev (inp : Nat → Nat → Nat) (s : St) (e : Nat) : Nat :=
  if e < 1024 then lv inp s e
  else if e < 2048 then lv inp s (e - 1024) * 2 ^ 1 % 2 ^ 64
  else (lv inp s ((e - 2048) / 1024) * 2 ^ 64 + lv inp s ((e - 2048) % 1024)) / 2 ^ 63 % 2 ^ 64

def Seg.ev (inp : Nat → Nat → Nat) (s : St) (g : Seg) : Nat := g.w * (lv inp s g.l % 2 ^ g.hi / 2 ^ g.lo)

def Pr.ev (inp : Nat → Nat → Nat) (s : St) (q : Pr) : Nat :=
  q.cl * (P521.ev inp s q.a * P521.ev inp s q.b % 2 ^ 64) + q.ch * (P521.ev inp s q.a * P521.ev inp s q.b / 2 ^ 64)

def sumL (inp : Nat → Nat → Nat) (s : St) : List Seg → Nat
  | [] => 0
  | g :: gs => g.ev inp s + sumL inp s gs

def sumP (inp : Nat → Nat → Nat) (s : St) : List Pr → Nat
  | [] => 0
  | q :: qs => q.ev inp s + sumP inp s qs

/-- The value of a functional. -/
def Fn.ev (inp : Nat → Nat → Nat) (s : St) (F : Fn) : Nat := F.k + F.f * s.c + sumL inp s F.l + sumP inp s F.p

/-! ## Congruence -/

/-- Equal modulo `m`. -/
def Cg (m a b : Nat) : Prop := a % m = b % m

theorem Cg.refl (m a : Nat) : Cg m a a := rfl
theorem Cg.of_eq {m a b : Nat} (h : a = b) : Cg m a b := h ▸ rfl
theorem Cg.symm {m a b : Nat} (h : Cg m a b) : Cg m b a := Eq.symm h
theorem Cg.trans {m a b c : Nat} (h : Cg m a b) (k : Cg m b c) : Cg m a c := Eq.trans h k
theorem Cg.add {m a b c d : Nat} (h : Cg m a b) (k : Cg m c d) : Cg m (a + c) (b + d) := by
  unfold Cg at *; rw [Nat.add_mod, h, k, ← Nat.add_mod]
theorem Cg.mul {m a b : Nat} (h : Cg m a b) (x : Nat) : Cg m (a * x) (b * x) := by
  unfold Cg at *; rw [Nat.mul_mod, h, ← Nat.mul_mod]
theorem Cg.mod (m a : Nat) : Cg m (a % m) a := Nat.mod_mod a m

/-! ## Bit fields -/

/-- A field added, to one of the same bits if there is one. -/
def putSeg (m : Nat) (g : Seg) : List Seg → List Seg
  | [] => [⟨g.l, g.lo, g.hi, g.w % m⟩]
  | q :: qs =>
    if Nat.beq q.l g.l && Nat.beq q.lo g.lo && Nat.beq q.hi g.hi then ⟨q.l, q.lo, q.hi, (q.w + g.w) % m⟩ :: qs
    else q :: putSeg m g qs

/-- A field added, unless its coefficient is zero. -/
def addSeg (m : Nat) (g : Seg) (l : List Seg) : List Seg := if Nat.beq (g.w % m) 0 then l else putSeg m g l

theorem putSeg_ok (m : Nat) (inp : Nat → Nat → Nat) (s : St) (g : Seg) : ∀ l,
    Cg m (sumL inp s (putSeg m g l)) (g.ev inp s + sumL inp s l)
  | [] => by
    simp only [putSeg, sumL, Seg.ev, Nat.add_zero]
    exact (Cg.mod m g.w).mul _
  | q :: qs => by
    rw [putSeg]
    split
    · rename_i h
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      simp only [sumL, Seg.ev, h.1.1, h.1.2, h.2]
      rw [← Nat.add_assoc]
      refine Cg.add (((Cg.mod m _).mul _).trans (Cg.of_eq ?_)) (Cg.refl _ _)
      rw [Nat.add_mul, Nat.add_comm]
    · simp only [sumL]
      exact ((Cg.refl m _).add (putSeg_ok m inp s g qs)).trans (Cg.of_eq (by omega_using []))

theorem addSeg_ok (m : Nat) (inp : Nat → Nat → Nat) (s : St) (g : Seg) (l : List Seg) :
    Cg m (sumL inp s (addSeg m g l)) (g.ev inp s + sumL inp s l) := by
  rw [addSeg]
  split
  · rename_i h
    have hz : Cg m (g.ev inp s) 0 := by
      have : Cg m g.w 0 := (Nat.eq_of_beq_eq_true h).trans (Nat.zero_mod m).symm
      exact (this.mul _).trans (Cg.of_eq (Nat.zero_mul _))
    exact ((hz.add (Cg.refl _ _)).trans (Cg.of_eq (Nat.zero_add _))).symm
  · exact putSeg_ok m inp s g l

/-- The fields of place `d`, and the others. -/
def part (d : Nat) : List Seg → List Seg × List Seg
  | [] => ([], [])
  | q :: qs =>
    let r := part d qs
    if Nat.beq q.l d then (q :: r.1, r.2) else (r.1, q :: r.2)

theorem part_ok (inp : Nat → Nat → Nat) (s : St) (d : Nat) : ∀ l,
    sumL inp s l = sumL inp s (part d l).1 + sumL inp s (part d l).2
  | [] => rfl
  | q :: qs => by
    rw [part, sumL, part_ok inp s d qs]
    split <;> simp only [sumL] <;> omega_using []

theorem part_fst (d : Nat) : ∀ l, ∀ q ∈ (part d l).1, q.l = d
  | [], q, h => absurd h (by simp [part])
  | q :: qs, q', h => by
    rw [part] at h
    split at h
    · rename_i hq
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.eq_of_beq_eq_true hq
      · exact part_fst d qs q' h
    · exact part_fst d qs q' h

theorem part_snd (d : Nat) : ∀ l, ∀ q ∈ (part d l).2, q.l ≠ d
  | [], q, h => absurd h (by simp [part])
  | q :: qs, q', h => by
    rw [part] at h
    split at h
    · exact part_snd d qs q' h
    · rename_i hq
      rcases List.mem_cons.mp h with rfl | h
      · exact fun e => hq (by rw [e]; exact Nat.beq_refl d)
      · exact part_snd d qs q' h

/-- The field from bit `pos`, removed. -/
def pick (pos : Nat) : List Seg → Option (Seg × List Seg)
  | [] => none
  | q :: qs =>
    if Nat.beq q.lo pos then some (q, qs) else
      match pick pos qs with
      | some (r, rs) => some (r, q :: rs)
      | none => none

theorem pick_ok (inp : Nat → Nat → Nat) (s : St) (pos : Nat) : ∀ {l : List Seg} {q : Seg} {r : List Seg},
    pick pos l = some (q, r) → q.lo = pos ∧ sumL inp s l = q.ev inp s + sumL inp s r ∧ (∀ x ∈ q :: r, x ∈ l)
  | [], _, _, h => absurd h (by simp [pick])
  | g :: gs, q, r, h => by
    rw [pick] at h
    split at h
    · rename_i hg
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Nat.eq_of_beq_eq_true hg, rfl, fun x hx => hx⟩
    · split at h
      · rename_i r' rs hp
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2, h3⟩ := pick_ok inp s pos hp
        refine ⟨h1, by simp only [sumL, h2]; omega_using [], fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_of_mem _ (h3 _ (List.mem_cons_self ..))
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (h3 _ (List.mem_cons_of_mem _ hx))
      · exact absurd h (by simp)

/-- The fields from bit `pos` on are all of them, up to bit 64 (or where
`w 2^pos` is zero), with coefficients that make `w` times the number. -/
def tile (m w : Nat) : Nat → Nat → List Seg → Bool
  | 0, _, _ => false
  | fuel + 1, pos, l =>
    match l with
    | [] => Nat.beq pos 64 || Nat.beq (w * 2 ^ pos % m) 0
    | _ :: _ =>
      match pick pos l with
      | none => false
      | some (q, r) => Nat.ble pos q.hi && Nat.beq (q.w % m) (w * 2 ^ pos % m) && tile m w fuel q.hi r

theorem field_split (x lo hi : Nat) (h : lo ≤ hi) :
    2 ^ lo * (x / 2 ^ lo) = 2 ^ lo * (x % 2 ^ hi / 2 ^ lo) + 2 ^ hi * (x / 2 ^ hi) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : x % 2 ^ (lo + e) / 2 ^ lo = x / 2 ^ lo % 2 ^ e := by
    rw [Nat.pow_add, Nat.mod_mul_right_div_self]
  have h2 : x / 2 ^ (lo + e) = x / 2 ^ lo / 2 ^ e := by rw [Nat.pow_add, Nat.div_div_eq_div_mul]
  rw [h1, h2, Nat.pow_add, Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div]

theorem tile_ok {m w : Nat} {inp : Nat → Nat → Nat} {s : St} {d : Nat} (hd : lv inp s d < 2 ^ 64) :
    ∀ (fuel pos : Nat) {l : List Seg}, tile m w fuel pos l = true → (∀ q ∈ l, q.l = d) →
      Cg m (sumL inp s l) (w * (2 ^ pos * (lv inp s d / 2 ^ pos)))
  | 0, _, _, h, _ => absurd h (by simp [tile])
  | fuel + 1, pos, [], h, _ => by
    simp only [tile, Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with h | h
    · subst h
      rw [Nat.div_eq_of_lt hd]
      exact Cg.refl _ _
    · rw [← Nat.mul_assoc]
      have hz : Cg m (w * 2 ^ pos) 0 := h.trans (Nat.zero_mod m).symm
      exact ((hz.mul _).trans (Cg.of_eq (Nat.zero_mul _))).symm
  | fuel + 1, pos, g :: gs, h, hl => by
    rw [tile] at h
    split at h
    · exact absurd h (by simp)
    · rename_i q r hp
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      obtain ⟨p1, p2, p3⟩ := pick_ok inp s pos hp
      have ih := tile_ok (m := m) (w := w) hd fuel q.hi h3 fun x hx => hl x (p3 x (List.mem_cons_of_mem _ hx))
      have hq : q.l = d := hl q (p3 q (List.mem_cons_self ..))
      rw [p2, field_split _ pos q.hi h1, Nat.mul_add]
      refine Cg.add ?_ ih
      rw [Seg.ev, p1, hq, ← Nat.mul_assoc]
      exact Cg.mul h2 _

/-- The coefficient of the register at place `d`, removed. -/
def take (m d : Nat) (l : List Seg) : Option (Nat × List Seg) :=
  let r := part d l
  match r.1 with
  | [] => some (0, r.2)
  | es@(_ :: _) =>
    match pick 0 es with
    | none => none
    | some (q, _) => if tile m q.w 8 0 es then some (q.w, r.2) else none

theorem take_ok {m d w : Nat} {l l' : List Seg} {inp : Nat → Nat → Nat} {s : St} (hd : lv inp s d < 2 ^ 64)
    (h : take m d l = some (w, l')) :
    Cg m (sumL inp s l) (w * lv inp s d + sumL inp s l') ∧ ∀ q ∈ l', q.l ≠ d := by
  rw [take] at h
  split at h
  · rename_i he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨Cg.of_eq ?_, part_snd d l⟩
    rw [part_ok inp s d l, he]
    simp only [sumL, Nat.zero_mul]
  · rename_i he
    split at h
    · exact absurd h (by simp)
    · rename_i q _ _
      split at h
      · rename_i ht
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, part_snd d l⟩
        rw [part_ok inp s d l]
        rw [he]
        refine Cg.add ((tile_ok hd 8 0 ht (he ▸ part_fst d l)).trans (Cg.of_eq ?_)) (Cg.refl _ _)
        rw [Nat.pow_zero, Nat.div_one, Nat.one_mul]
      · exact absurd h (by simp)

theorem sumL_agree {inp : Nat → Nat → Nat} {d : Reg} {s t : St} (h : Agree d s t) :
    ∀ {l : List Seg}, (∀ q ∈ l, q.l ≠ rn d) → sumL inp t l = sumL inp s l
  | [], _ => rfl
  | q :: qs, hl => by
    simp only [sumL, Seg.ev]
    rw [lv_agree h (hl q (List.mem_cons_self ..)), sumL_agree h fun x hx => hl x (List.mem_cons_of_mem _ hx)]

/-! ## Products -/

/-- The factor with the place `d` replaced by `l`. -/
def subE (d l e : Nat) : Nat :=
  if e < 1024 then (if e = d then l else e)
  else if e < 2048 then (if e - 1024 = d then 1024 + l else e)
  else 2048 + 1024 * (if (e - 2048) / 1024 = d then l else (e - 2048) / 1024) +
    (if (e - 2048) % 1024 = d then l else (e - 2048) % 1024)

/-- The place `d` is in the factor. -/
def inE (d e : Nat) : Bool :=
  if e < 1024 then Nat.beq e d
  else if e < 2048 then Nat.beq (e - 1024) d
  else Nat.beq ((e - 2048) / 1024) d || Nat.beq ((e - 2048) % 1024) d

theorem ev_agree {inp : Nat → Nat → Nat} {d : Reg} {s t : St} (h : Agree d s t) {e : Nat}
    (he : inE (rn d) e = false) : ev inp t e = ev inp s e := by
  unfold inE at he
  unfold ev
  split at he
  · rename_i h1
    rw [ite_eq_left h1, ite_eq_left h1, lv_agree h (Nat.ne_of_beq_eq_false he)]
  · rename_i h1
    rw [ite_eq_right h1, ite_eq_right h1]
    split at he
    · rename_i h2
      rw [ite_eq_left h2, ite_eq_left h2, lv_agree h (Nat.ne_of_beq_eq_false he)]
    · rename_i h2
      rw [ite_eq_right h2, ite_eq_right h2]
      simp only [Bool.or_eq_false_iff] at he
      rw [lv_agree h (Nat.ne_of_beq_eq_false he.1), lv_agree h (Nat.ne_of_beq_eq_false he.2)]

theorem ev_sub {inp : Nat → Nat → Nat} {d : Reg} {s t : St} (h : Agree d s t) {l : Nat} (hl : l < 1024)
    (hv : t.g d = lv inp s l) (e : Nat) : ev inp t e = ev inp s (subE (rn d) l e) := by
  have hd := rn_lt d
  have hv' : lv inp t (rn d) = lv inp s l := by rw [lv_reg, hv]
  have key : ∀ x, lv inp t x = lv inp s (if x = rn d then l else x) := fun x => by
    split
    · rename_i hx; rw [hx, hv']
    · rename_i hx; exact lv_agree h hx
  have kl : ∀ x, x < 1024 → (if x = rn d then l else x) < 1024 := fun x hx => by split <;> with_reducible assumption
  unfold ev subE
  by_cases h1 : e < 1024
  · rw [ite_eq_left h1, ite_eq_left h1, key e, ite_eq_left (kl e h1)]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : e < 2048
    · rw [ite_eq_left h2, ite_eq_left h2, key]
      by_cases hx : e - 1024 = rn d
      · rw [ite_eq_left hx, ite_eq_left hx, ite_eq_right (by omega_using []), ite_eq_left (by omega_using [hl])]
        rw [Nat.add_sub_cancel_left]
      · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right h1, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2, key, key ((e - 2048) % 1024)]
      have hb := kl ((e - 2048) % 1024) (Nat.mod_lt _ (by decide))
      generalize (if (e - 2048) / 1024 = rn d then l else (e - 2048) / 1024) = A
      generalize (if (e - 2048) % 1024 = rn d then l else (e - 2048) % 1024) = B at hb ⊢
      rw [ite_eq_right (by omega_using []), ite_eq_right (by omega_using [])]
      have e1 : (2048 + 1024 * A + B - 2048) / 1024 = A := by omega_using [hb]
      have e2 : (2048 + 1024 * A + B - 2048) % 1024 = B := by omega_using [hb]
      rw [e1, e2]

/-- The products with the factor `d` replaced by `e`, which no other factor is made of. -/
def renP (d e : Nat) : List Pr → Option (List Pr)
  | [] => some []
  | q :: qs =>
    if (!Nat.beq q.a d && inE d q.a) || (!Nat.beq q.b d && inE d q.b) then none else
      match renP d e qs with
      | none => none
      | some rs => some (⟨if Nat.beq q.a d then e else q.a, if Nat.beq q.b d then e else q.b, q.cl, q.ch⟩ :: rs)

theorem renP_ok {inp : Nat → Nat → Nat} {d : Reg} {s t : St} (h : Agree d s t) {e : Nat}
    (hv : t.g d = ev inp s e) : ∀ {p p' : List Pr}, renP (rn d) e p = some p' → sumP inp t p = sumP inp s p'
  | [], _, hp => by simp only [renP, Option.some.injEq] at hp; subst hp; rfl
  | q :: qs, p', hp => by
    have hd := rn_lt d
    rw [renP] at hp
    split at hp
    · exact absurd hp (by simp)
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', not_or, not_and, Bool.not_eq_true] at hc
      split at hp
      · exact absurd hp (by simp)
      · rename_i rs hr
        simp only [Option.some.injEq] at hp
        subst hp
        have key : ∀ x, (Nat.beq x (rn d) = false → inE (rn d) x = false) →
            ev inp t x = ev inp s (if Nat.beq x (rn d) then e else x) := fun x hx => by
          cases hb : Nat.beq x (rn d) with
          | true =>
            rw [Nat.eq_of_beq_eq_true hb, ite_eq_left rfl, ← hv, ev, ite_eq_left (by omega_using [hd]), lv_reg]
          | false => rw [ite_eq_right (by simp)]; exact ev_agree h (hx hb)
        simp only [sumP, Pr.ev]
        rw [key q.a hc.1, key q.b hc.2, renP_ok h hv hr]

/-- No product has the factor `d`. -/
def noP (d : Nat) : List Pr → Bool
  | [] => true
  | q :: qs => !inE d q.a && !inE d q.b && noP d qs

theorem noP_ok {inp : Nat → Nat → Nat} {d : Reg} {s t : St} (h : Agree d s t) :
    ∀ {p : List Pr}, noP (rn d) p = true → sumP inp t p = sumP inp s p
  | [], _ => rfl
  | q :: qs, hp => by
    simp only [noP, Bool.and_eq_true, Bool.not_eq_true'] at hp
    simp only [sumP, Pr.ev]
    rw [ev_agree h hp.1.1, ev_agree h hp.1.2, noP_ok h hp.2]

/-- The products with the place `d` replaced by `l`. -/
def subP (d l : Nat) : List Pr → List Pr
  | [] => []
  | q :: qs => ⟨subE d l q.a, subE d l q.b, q.cl, q.ch⟩ :: subP d l qs

theorem subP_ok {inp : Nat → Nat → Nat} {d : Reg} {s t : St} (h : Agree d s t) {l : Nat} (hl : l < 1024)
    (hv : t.g d = lv inp s l) : ∀ p : List Pr, sumP inp t p = sumP inp s (subP (rn d) l p)
  | [] => rfl
  | q :: qs => by
    simp only [subP, sumP, Pr.ev]
    rw [ev_sub h hl hv q.a, ev_sub h hl hv q.b, subP_ok h hl hv qs]

/-- The bit fields with the place `d` replaced by `l`. -/
def subL (d l : Nat) : List Seg → List Seg
  | [] => []
  | q :: qs => ⟨if Nat.beq q.l d then l else q.l, q.lo, q.hi, q.w⟩ :: subL d l qs

theorem subL_ok {inp : Nat → Nat → Nat} {d : Reg} {s t : St} (h : Agree d s t) {l : Nat}
    (hv : t.g d = lv inp s l) : ∀ p : List Seg, sumL inp t p = sumL inp s (subL (rn d) l p)
  | [] => rfl
  | q :: qs => by
    simp only [subL, sumL, Seg.ev]
    rw [subL_ok h hv qs]
    cases hb : Nat.beq q.l (rn d) with
    | true => rw [Nat.eq_of_beq_eq_true hb, ite_eq_left rfl, lv_reg, hv]
    | false => rw [ite_eq_right (by simp), lv_agree h (Nat.ne_of_beq_eq_false hb)]

/-- A product's half added, to the product of the same factors if there is one. -/
def addPr (m : Nat) (g : Pr) : List Pr → List Pr
  | [] => [⟨g.a, g.b, g.cl % m, g.ch % m⟩]
  | q :: qs =>
    if Nat.beq q.a g.a && Nat.beq q.b g.b then ⟨q.a, q.b, (q.cl + g.cl) % m, (q.ch + g.ch) % m⟩ :: qs
    else q :: addPr m g qs

theorem addPr_ok (m : Nat) (inp : Nat → Nat → Nat) (s : St) (g : Pr) : ∀ l,
    Cg m (sumP inp s (addPr m g l)) (g.ev inp s + sumP inp s l)
  | [] => by
    simp only [addPr, sumP, Pr.ev, Nat.add_zero]
    exact ((Cg.mod m g.cl).mul _).add ((Cg.mod m g.ch).mul _)
  | q :: qs => by
    rw [addPr]
    split
    · rename_i h
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      simp only [sumP, Pr.ev, h.1, h.2]
      rw [← Nat.add_assoc]
      refine Cg.add ((((Cg.mod m _).mul _).add ((Cg.mod m _).mul _)).trans (Cg.of_eq ?_)) (Cg.refl _ _)
      rw [Nat.add_mul, Nat.add_mul]
      omega_using []
    · simp only [sumP]
      exact ((Cg.refl m _).add (addPr_ok m inp s g qs)).trans (Cg.of_eq (by omega_using []))

/-! ## Bounds -/

/-- Lower and upper bounds on the registers, by number, and the carry's. -/
structure Bd where
  lb : List Nat
  ub : List Nat
  c : Nat

structure Bd.Ok (B : Bd) (s : St) : Prop where
  lb : ∀ r, B.lb.getD (rn r) 0 ≤ s.g r
  ub : ∀ r, s.g r ≤ B.ub.getD (rn r) (2 ^ 64 - 1)
  c : s.c ≤ B.c

def Bd.u (B : Bd) (r : Reg) : Nat := B.ub.getD (rn r) (2 ^ 64 - 1)

/-- The bounds with register `d` between `l` and `u`, and the carry at most `c`. -/
def Bd.set (B : Bd) (d : Reg) (l u c : Nat) : Bd := ⟨B.lb.set (rn d) l, B.ub.set (rn d) u, c⟩

theorem getD_set (xs : List Nat) (i j v d : Nat) :
    (xs.set i v).getD j d = if i = j ∧ j < xs.length then v else xs.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases h2 : i < xs.length
    · simp [h2]
    · simp [h2]
  · simp [h]

/-- The bounds are lists of all registers'. -/
def Bd.wf (B : Bd) : Bool := Nat.beq B.lb.length 29 && Nat.beq B.ub.length 29

theorem Bd.wf_set {B : Bd} (h : B.wf = true) (d : Reg) (l u c : Nat) : (B.set d l u c).wf = true := by
  simpa only [Bd.wf, Bd.set, List.length_set] using h

theorem Bd.Ok.set {B : Bd} {s t : St} (hw : B.wf = true) (h : B.Ok s) {d : Reg} (ha : Agree d s t) {l u c : Nat}
    (hl : l ≤ t.g d) (hu : t.g d ≤ u) (hc : t.c ≤ c) : (B.set d l u c).Ok t := by
  simp only [Bd.wf, Bool.and_eq_true, Nat.beq_eq] at hw
  refine ⟨fun r => ?_, fun r => ?_, hc⟩
  · simp only [Bd.set, getD_set]
    split
    · rename_i hr; rw [← rn_inj hr.1]; exact hl
    · rename_i hr
      have hne : r ≠ d := fun e => hr ⟨by rw [e], by rw [hw.1]; exact rn_lt r⟩
      rw [ha r hne]; exact h.lb r
  · simp only [Bd.set, getD_set]
    split
    · rename_i hr; rw [← rn_inj hr.1]; exact hu
    · rename_i hr
      have hne : r ≠ d := fun e => hr ⟨by rw [e], by rw [hw.2]; exact rn_lt r⟩
      rw [ha r hne]; exact h.ub r

/-- `u` if it is a word, else the greatest word. -/
def cap (u : Nat) : Nat := if Nat.ble u (2 ^ 64 - 1) then u else 2 ^ 64 - 1

theorem mod_le_cap {x u : Nat} (h : x ≤ u) : x % 2 ^ 64 ≤ cap u := by
  unfold cap
  split
  · exact Nat.le_trans (Nat.mod_le _ _) h
  · have := Nat.mod_lt x (show 0 < 2 ^ 64 by decide); omega_using [this]

/-- The bounds after an operation, `ib` bounding the operands' words. -/
def fwd (ib : Nat → Nat → Nat) : Op → Bd → Bd
  | .ld k i d, B => B.set d 0 (ib k i) B.c
  | .mul d n m, B => B.set d 0 (cap (B.u n * B.u m)) B.c
  | .umulh d n m, B => B.set d 0 (B.u n * B.u m / 2 ^ 64) B.c
  | .add d n m, B => B.set d 0 (cap (B.u n + B.u m)) B.c
  | .adds d n m, B => B.set d 0 (cap (B.u n + B.u m)) ((B.u n + B.u m) / 2 ^ 64)
  | .adcs d n m, B => B.set d 0 (cap (B.u n + B.u m + B.c)) ((B.u n + B.u m + B.c) / 2 ^ 64)
  | .adc d n m, B => B.set d 0 (cap (B.u n + B.u m + B.c)) B.c
  | .subs d _ _, B => B.set d 0 (2 ^ 64 - 1) 1
  | .sbcs d _ _, B => B.set d 0 (2 ^ 64 - 1) 1
  | .lsl d n k, B => B.set d 0 (cap (B.u n * 2 ^ k)) B.c
  | .lsr d n k, B => B.set d 0 (B.u n / 2 ^ k) B.c
  | .extr d n m k, B => B.set d 0 (cap ((B.u n * 2 ^ 64 + B.u m) / 2 ^ k)) B.c
  | .movz d v, B => B.set d (v % 2 ^ 16) (v % 2 ^ 16) B.c
  | .low d n m _, B => B.set d 0 (min (B.u n) (B.u m)) B.c

theorem agree_set (s : St) (d : Reg) (v : Nat) : Agree d s (s.set d v) := fun r hr => by simp only [St.set, hr, ite_false]
theorem agree_setc (s : St) (d : Reg) (v : Nat) : Agree d s (s.setc d v) := fun r hr => by simp only [St.setc, hr, ite_false]
theorem g_set (s : St) (d : Reg) (v : Nat) : (s.set d v).g d = v := by simp only [St.set, ite_true]
theorem g_setc (s : St) (d : Reg) (v : Nat) : (s.setc d v).g d = v % 2 ^ 64 := by simp only [St.setc, ite_true]

theorem step_agree (inp : Nat → Nat → Nat) (o : Op) (s : St) : Agree o.dst s (step inp o s) := by
  cases o <;> first | exact agree_set _ _ _ | exact agree_setc _ _ _

theorem step_Ok {inp : Nat → Nat → Nat} (hi : ∀ k i, inp k i < 2 ^ 64) {s : St} (h : Ok s) (o : Op) :
    Ok (step inp o s) := by
  have key : ∀ d v, v < 2 ^ 64 → Ok (s.set d v) := fun d v hv =>
    ⟨fun r => by simp only [St.set]; split <;> [exact hv; exact h.g r], h.c⟩
  have keyc : ∀ d v, v < 2 ^ 65 → Ok (s.setc d v) := fun d v hv =>
    ⟨fun r => by simp only [St.setc]; split <;> [exact Nat.mod_lt _ (by decide); exact h.g r],
      by simp only [St.setc]; omega_using [hv]⟩
  have md : ∀ x, x % 2 ^ 64 < 2 ^ 64 := fun x => Nat.mod_lt _ (by decide)
  cases o with
  | ld k i d => exact key _ _ (hi k i)
  | umulh d n m => exact key _ _ (Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' (h.g n) (h.g m)))
  | lsr d n k => exact key _ _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (h.g n))
  | movz d v => exact key _ _ (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  | low d n m k => exact key _ _ (Nat.and_lt_two_pow _ (h.g m))
  | adds d n m => exact keyc _ _ (by have := h.g n; have := h.g m; omega_arith)
  | adcs d n m => exact keyc _ _ (by have := h.g n; have := h.g m; have := h.c; omega_arith)
  | subs d n m => exact keyc _ _ (by have := h.g n; have := h.g m; omega_arith)
  | sbcs d n m => exact keyc _ _ (by have := h.g n; have := h.g m; have := h.c; omega_arith)
  | mul d n m => exact key _ _ (md _)
  | add d n m => exact key _ _ (md _)
  | adc d n m => exact key _ _ (md _)
  | lsl d n k => exact key _ _ (md _)
  | extr d n m k => exact key _ _ (md _)

theorem fwd_wf {ib : Nat → Nat → Nat} {B : Bd} (h : B.wf = true) (o : Op) : (fwd ib o B).wf = true := by
  cases o <;> exact Bd.wf_set h _ _ _ _

theorem fwd_ok {inp ib : Nat → Nat → Nat} (hi : ∀ k i, inp k i ≤ ib k i) {B : Bd} (hw : B.wf = true) {s : St}
    (hs : Ok s) (h : B.Ok s) (o : Op) : (fwd ib o B).Ok (step inp o s) := by
  have u : ∀ r, s.g r ≤ B.u r := h.ub
  have md : ∀ x, x % 2 ^ 64 ≤ 2 ^ 64 - 1 := fun x => by
    have := Nat.mod_lt x (show 0 < 2 ^ 64 by decide); omega_using [this]
  cases o with
  | ld k i d => exact h.set hw (agree_set _ _ _) (Nat.zero_le _) (Nat.le_trans (Nat.le_of_eq (g_set _ _ _)) (hi k i)) h.c
  | mul d n m =>
    exact h.set hw (agree_set _ _ _) (Nat.zero_le _) (Nat.le_trans (Nat.le_of_eq (g_set _ _ _)) (mod_le_cap (Nat.mul_le_mul (u n) (u m)))) h.c
  | umulh d n m =>
    exact h.set hw (agree_set _ _ _) (Nat.zero_le _)
      (Nat.le_trans (Nat.le_of_eq (g_set _ _ _)) (Nat.div_le_div_right (Nat.mul_le_mul (u n) (u m)))) h.c
  | add d n m =>
    exact h.set hw (agree_set _ _ _) (Nat.zero_le _) (Nat.le_trans (Nat.le_of_eq (g_set _ _ _)) (mod_le_cap (Nat.add_le_add (u n) (u m)))) h.c
  | adds d n m =>
    exact h.set hw (agree_setc _ _ _) (Nat.zero_le _) (Nat.le_trans (Nat.le_of_eq (g_setc _ _ _)) (mod_le_cap (Nat.add_le_add (u n) (u m))))
      (Nat.div_le_div_right (Nat.add_le_add (u n) (u m)))
  | adcs d n m =>
    exact h.set hw (agree_setc _ _ _) (Nat.zero_le _)
      (Nat.le_trans (Nat.le_of_eq (g_setc _ _ _)) (mod_le_cap (Nat.add_le_add (Nat.add_le_add (u n) (u m)) h.c)))
      (Nat.div_le_div_right (Nat.add_le_add (Nat.add_le_add (u n) (u m)) h.c))
  | adc d n m =>
    exact h.set hw (agree_set _ _ _) (Nat.zero_le _)
      (Nat.le_trans (Nat.le_of_eq (g_set _ _ _)) (mod_le_cap (Nat.add_le_add (Nat.add_le_add (u n) (u m)) h.c))) h.c
  | subs d n m =>
    exact h.set hw (agree_setc _ _ _) (Nat.zero_le _) (Nat.le_trans (Nat.le_of_eq (g_setc _ _ _)) (md _))
      (by have := hs.g n; have := hs.g m; show (_ : Nat) / _ ≤ _; omega_arith)
  | sbcs d n m =>
    exact h.set hw (agree_setc _ _ _) (Nat.zero_le _) (Nat.le_trans (Nat.le_of_eq (g_setc _ _ _)) (md _))
      (by have := hs.g n; have := hs.g m; have := hs.c; show (_ : Nat) / _ ≤ _; omega_arith)
  | lsl d n k =>
    exact h.set hw (agree_set _ _ _) (Nat.zero_le _) (Nat.le_trans (Nat.le_of_eq (g_set _ _ _)) (mod_le_cap (Nat.mul_le_mul_right _ (u n)))) h.c
  | lsr d n k =>
    exact h.set hw (agree_set _ _ _) (Nat.zero_le _) (Nat.le_trans (Nat.le_of_eq (g_set _ _ _)) (Nat.div_le_div_right (u n))) h.c
  | extr d n m k =>
    exact h.set hw (agree_set _ _ _) (Nat.zero_le _) (Nat.le_trans (Nat.le_of_eq (g_set _ _ _)) (mod_le_cap (Nat.div_le_div_right (Nat.add_le_add (Nat.mul_le_mul_right _ (u n)) (u m))))) h.c
  | movz d v =>
    exact h.set hw (agree_set _ _ _) (Nat.le_of_eq (g_set _ _ _).symm) (Nat.le_of_eq (g_set _ _ _)) h.c
  | low d n m k =>
    exact h.set hw (agree_set _ _ _) (Nat.zero_le _) (Nat.le_trans (Nat.le_of_eq (g_set _ _ _)) (Nat.le_min.mpr ⟨Nat.le_trans Nat.and_le_left (u n), Nat.le_trans Nat.and_le_right (u m)⟩)) h.c

/-- The bounds after a sequence. -/
def fwds (ib : Nat → Nat → Nat) : List Op → Bd → Bd
  | [], B => B
  | o :: os, B => fwds ib os (fwd ib o B)

theorem fwds_ok {inp ib : Nat → Nat → Nat} (hw : ∀ k i, inp k i < 2 ^ 64) (hi : ∀ k i, inp k i ≤ ib k i) :
    ∀ (os : List Op) {B : Bd} {s : St}, B.wf = true → Ok s → B.Ok s →
      (fwds ib os B).Ok (run inp os s) ∧ Ok (run inp os s)
  | [], _, _, _, hs, h => ⟨h, hs⟩
  | o :: os, _, _, hb, hs, h => fwds_ok hw hi os (fwd_wf hb o) (step_Ok hw hs o) (fwd_ok hi hb hs h o)

theorem run_Ok {inp : Nat → Nat → Nat} (hi : ∀ k i, inp k i < 2 ^ 64) : ∀ (os : List Op) {s : St}, Ok s → Ok (run inp os s)
  | [], _, hs => hs
  | o :: os, _, hs => run_Ok hi os (step_Ok hi hs o)

/-! ## Backwards -/

/-- The field of all bits of register `r`. -/
def full (r : Reg) (w : Nat) : Seg := ⟨rn r, 0, 64, w⟩

theorem full_ev {inp : Nat → Nat → Nat} {s : St} (h : Ok s) (r : Reg) (w : Nat) :
    (full r w).ev inp s = w * s.g r := by
  simp only [Seg.ev, full, lv_reg, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt (h.g r)]

/-- The fields of `d`, the number at `n` shifted left by `k`, as fields of `n`. -/
def pullShl (m d n k : Nat) : List Seg → Option (List Seg)
  | [] => some []
  | q :: qs =>
    match pullShl m d n k qs with
    | none => none
    | some r =>
      if Nat.beq q.l d then
        if Nat.ble k q.lo && Nat.ble q.lo q.hi && Nat.ble q.hi 64 then
          some (addSeg m ⟨n, q.lo - k, q.hi - k, q.w⟩ r)
        else if Nat.beq q.lo 0 && Nat.ble k q.hi && Nat.ble q.hi 64 then
          some (addSeg m ⟨n, 0, q.hi - k, q.w * 2 ^ k⟩ r)
        else none
      else some (addSeg m q r)

/-- The fields of `d`, the bits from `k` on of the number at `l` with the
number at `n` above it, as fields of `n` and `l`. -/
def pullExtr (m d n l k : Nat) : List Seg → Option (List Seg)
  | [] => some []
  | q :: qs =>
    match pullExtr m d n l k qs with
    | none => none
    | some r =>
      if Nat.beq q.l d then
        if Nat.beq q.lo 0 && Nat.ble (64 - k) q.hi && Nat.ble q.hi 64 then
          some (addSeg m ⟨l, k, 64, q.w⟩ (addSeg m ⟨n, 0, q.hi - (64 - k), q.w * 2 ^ (64 - k)⟩ r))
        else none
      else some (addSeg m q r)

theorem shl_field {x k l h : Nat} (h1 : k ≤ l) (h2 : l ≤ h) (h3 : h ≤ 64) :
    x * 2 ^ k % 2 ^ 64 % 2 ^ h / 2 ^ l = x % 2 ^ (h - k) / 2 ^ (l - k) := by
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h3), Nat.mul_comm x,
    show 2 ^ h = 2 ^ k * 2 ^ (h - k) by rw [← Nat.pow_add]; congr 1; omega_using [h1, h2], Nat.mul_mod_mul_left,
    show 2 ^ l = 2 ^ k * 2 ^ (l - k) by rw [← Nat.pow_add]; congr 1; omega_using [h1],
    Nat.mul_div_mul_left _ _ (Nat.two_pow_pos k)]

theorem shl_field0 {x k h : Nat} (h1 : k ≤ h) (h3 : h ≤ 64) :
    x * 2 ^ k % 2 ^ 64 % 2 ^ h = 2 ^ k * (x % 2 ^ (h - k)) := by
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h3), Nat.mul_comm x,
    show 2 ^ h = 2 ^ k * 2 ^ (h - k) by rw [← Nat.pow_add]; congr 1; omega_using [h1], Nat.mul_mod_mul_left]

theorem extr_field {x y k h : Nat} (hy : y < 2 ^ 64) (hk : k ≤ 64) (h1 : 64 - k ≤ h) (h3 : h ≤ 64) :
    (x * 2 ^ 64 + y) / 2 ^ k % 2 ^ 64 % 2 ^ h = y / 2 ^ k + 2 ^ (64 - k) * (x % 2 ^ (h - (64 - k))) := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ k * 2 ^ (64 - k) := by rw [← Nat.pow_add]; congr 1; omega_using [hk]
  have hlt : y / 2 ^ k < 2 ^ (64 - k) := Nat.div_lt_of_lt_mul (by rw [← e64]; exact hy)
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h3), e64, show x * (2 ^ k * 2 ^ (64 - k)) + y = y + 2 ^ k * (x * 2 ^ (64 - k)) by
    rw [Nat.mul_left_comm, Nat.add_comm], Nat.add_mul_div_left _ _ (Nat.two_pow_pos k),
    show 2 ^ h = 2 ^ (64 - k) * 2 ^ (h - (64 - k)) by rw [← Nat.pow_add]; congr 1; omega_using [h1],
    Nat.mod_mul, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add]

theorem pullShl_ok {m : Nat} {inp : Nat → Nat → Nat} {d n : Reg} {k : Nat} {s t : St} (hA : Agree d s t)
    (hv : t.g d = s.g n * 2 ^ k % 2 ^ 64) : ∀ {l l' : List Seg}, pullShl m (rn d) (rn n) k l = some l' →
      Cg m (sumL inp t l) (sumL inp s l')
  | [], _, h => by simp only [pullShl, Option.some.injEq] at h; subst h; exact Cg.refl _ _
  | q :: qs, l', h => by
    rw [pullShl] at h
    split at h
    · exact absurd h (by simp)
    · rename_i r hr
      have ih := pullShl_ok (inp := inp) hA hv hr
      rw [sumL]
      split at h
      · rename_i hd
        have hd := Nat.eq_of_beq_eq_true hd
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, Nat.ble_eq] at hc
          simp only [Option.some.injEq] at h
          subst h
          refine ((Cg.of_eq ?_).add ih).trans (addSeg_ok m inp s _ r).symm
          rw [Seg.ev, Seg.ev, hd, lv_reg, lv_reg, hv, shl_field hc.1.1 hc.1.2 hc.2]
        · split at h
          · rename_i hc
            simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hc
            simp only [Option.some.injEq] at h
            subst h
            refine ((Cg.of_eq ?_).add ih).trans (addSeg_ok m inp s _ r).symm
            rw [Seg.ev, Seg.ev, hd, lv_reg, lv_reg, hv, hc.1.1, shl_field0 hc.1.2 hc.2]
            simp only [Nat.pow_zero, Nat.div_one]
            rw [Nat.mul_assoc]
          · exact absurd h (by simp)
      · rename_i hd
        simp only [Option.some.injEq] at h
        subst h
        refine ((Cg.of_eq ?_).add ih).trans (addSeg_ok m inp s _ r).symm
        rw [Seg.ev, Seg.ev, lv_agree hA (Nat.ne_of_beq_eq_false (Bool.eq_false_iff.mpr hd))]

theorem pullExtr_ok {m : Nat} {inp : Nat → Nat → Nat} {d n q : Reg} {k : Nat} {s t : St} (hs : Ok s) (hA : Agree d s t)
    (hk : k ≤ 64) (hv : t.g d = (s.g n * 2 ^ 64 + s.g q) / 2 ^ k % 2 ^ 64) :
    ∀ {l l' : List Seg}, pullExtr m (rn d) (rn n) (rn q) k l = some l' → Cg m (sumL inp t l) (sumL inp s l')
  | [], _, h => by simp only [pullExtr, Option.some.injEq] at h; subst h; exact Cg.refl _ _
  | g :: gs, l', h => by
    rw [pullExtr] at h
    split at h
    · exact absurd h (by simp)
    · rename_i r hr
      have ih := pullExtr_ok (inp := inp) hs hA hk hv hr
      rw [sumL]
      split at h
      · rename_i hd
        have hd := Nat.eq_of_beq_eq_true hd
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hc
          simp only [Option.some.injEq] at h
          subst h
          refine Cg.trans ?_ ((addSeg_ok m inp s _ _).trans ((Cg.refl _ _).add (addSeg_ok m inp s _ r))).symm
          rw [← Nat.add_assoc]
          refine (Cg.of_eq ?_).add ih
          simp only [Seg.ev]
          rw [hd, lv_reg, lv_reg, lv_reg, hv, hc.1.1, extr_field (hs.g q) hk hc.1.2 hc.2, Nat.mod_eq_of_lt (hs.g q)]
          simp only [Nat.pow_zero, Nat.div_one]
          rw [Nat.mul_add, Nat.mul_assoc]
        · exact absurd h (by simp)
      · rename_i hd
        simp only [Option.some.injEq] at h
        subst h
        refine ((Cg.of_eq ?_).add ih).trans (addSeg_ok m inp s _ r).symm
        rw [Seg.ev, Seg.ev, lv_agree hA (Nat.ne_of_beq_eq_false (Bool.eq_false_iff.mpr hd))]

/-- The functional before an operation, from the one after it; `none` where
this is not enough to tell. -/
def back (m : Nat) (B : Bd) : Op → Fn → Option Fn
  | .ld k i d, F =>
    if Nat.ble i 15 && Nat.ble k 3 then some ⟨F.k, F.f, subL (rn d) (inpLoc k i) F.l, subP (rn d) (inpLoc k i) F.p⟩
    else none
  | .lsl d n k, F =>
    match pullShl m (rn d) (rn n) k F.l, (if Nat.beq k 1 then renP (rn d) (1024 + rn n) F.p else if noP (rn d) F.p then some F.p else none) with
    | some l, some p => if Nat.ble k 63 then some ⟨F.k, F.f, l, p⟩ else none
    | _, _ => none
  | .extr d n q k, F =>
    match pullExtr m (rn d) (rn n) (rn q) k F.l, (if Nat.beq k 63 then renP (rn d) (2048 + 1024 * rn n + rn q) F.p else if noP (rn d) F.p then some F.p else none) with
    | some l, some p => if Nat.ble k 63 then some ⟨F.k, F.f, l, p⟩ else none
    | _, _ => none
  | o, F =>
    if noP (rn o.dst) F.p then
      match take m (rn o.dst) F.l with
      | none => none
      | some (w, l) =>
        let both (f : Nat) (n q : Reg) (k : Nat) : Option Fn := some ⟨k, f, addSeg m (full n w) (addSeg m (full q w) l), F.p⟩
        let diff (f : Nat) (n q : Reg) (k : Nat) : Option Fn :=
          some ⟨k, f, addSeg m (full n w) (addSeg m (full q (m - w % m)) l), F.p⟩
        match o with
        | .mul _ n q => some ⟨F.k, F.f, l, addPr m ⟨rn n, rn q, w, 0⟩ F.p⟩
        | .umulh _ n q => some ⟨F.k, F.f, l, addPr m ⟨rn n, rn q, 0, w⟩ F.p⟩
        | .add _ n q => if Nat.ble (B.u n + B.u q) (2 ^ 64 - 1) then both F.f n q F.k else none
        | .adc _ n q => if Nat.ble (B.u n + B.u q + B.c) (2 ^ 64 - 1) then both ((F.f + w) % m) n q F.k else none
        | .adds _ n q =>
          if Nat.beq (F.f % m) (w * 2 ^ 64 % m) || Nat.ble (B.u n + B.u q) (2 ^ 64 - 1) then both 0 n q F.k else none
        | .adcs _ n q =>
          if Nat.beq (F.f % m) (w * 2 ^ 64 % m) || Nat.ble (B.u n + B.u q + B.c) (2 ^ 64 - 1) then both w n q F.k else none
        | .subs _ n q =>
          if Nat.beq (rn n) (rn q) then some ⟨(F.k + F.f) % m, 0, l, F.p⟩
          else if Nat.beq (F.f % m) (w * 2 ^ 64 % m) then diff 0 n q ((F.k + w * 2 ^ 64) % m) else none
        | .sbcs _ n q => if Nat.beq (F.f % m) (w * 2 ^ 64 % m) then diff w n q ((F.k + w * (2 ^ 64 - 1)) % m) else none
        | .lsr _ n k => if Nat.ble k 63 then some ⟨F.k, F.f, addSeg m ⟨rn n, k, 64, w⟩ l, F.p⟩ else none
        | .movz _ v => some ⟨(F.k + w * (v % 2 ^ 16)) % m, F.f, l, F.p⟩
        | .low _ n q k =>
          if Nat.beq (B.lb.getD (rn q) 0) (2 ^ k - 1) && Nat.beq (B.u q) (2 ^ k - 1) && Nat.ble k 64 then
            some ⟨F.k, F.f, addSeg m ⟨rn n, 0, k, w⟩ l, F.p⟩
          else none
        | _ => none
    else none

/-- A sum of words that is at most the greatest word is not reduced. -/
private theorem lt_of_ble {a b c x y z : Nat} (h : Nat.ble (a + b + c) (2 ^ 64 - 1) = true) (ha : x ≤ a) (hb : y ≤ b)
    (hc : z ≤ c) : x + y + z < 2 ^ 64 := by
  have := Nat.le_of_ble_eq_true h
  omega_using [this, ha, hb, hc]

private theorem lt_of_ble2 {a b x y : Nat} (h : Nat.ble (a + b) (2 ^ 64 - 1) = true) (ha : x ≤ a) (hb : y ≤ b) :
    x + y < 2 ^ 64 := by
  have := Nat.le_of_ble_eq_true h
  omega_using [this, ha, hb]

private theorem both_cg {m w w' L : Nat} {inp : Nat → Nat → Nat} {s : St} (hs : Ok s) (n q : Reg) {l : List Seg}
    (hL : L = sumL inp s l) :
    Cg m (sumL inp s (addSeg m (full n w) (addSeg m (full q w') l))) (w * s.g n + w' * s.g q + L) := by
  refine (addSeg_ok m inp s _ _).trans ?_
  rw [full_ev hs, Nat.add_assoc, hL]
  refine (Cg.refl _ _).add ((addSeg_ok m inp s _ _).trans ?_)
  rw [full_ev hs]; exact Cg.refl _ _

/-- `f c + w v`, for a sum `x = v + 2⁶⁴ c`. -/
private theorem carry_cg {m f w x : Nat} (h : Nat.beq (f % m) (w * 2 ^ 64 % m) = true ∨ x < 2 ^ 64) :
    Cg m (f * (x / 2 ^ 64) + w * (x % 2 ^ 64)) (w * x) := by
  rcases h with h | h
  · refine ((Cg.mul (m := m) (Nat.eq_of_beq_eq_true h) _).add (Cg.refl _ _)).trans (Cg.of_eq ?_)
    rw [Nat.mul_assoc, ← Nat.mul_add, Nat.div_add_mod]
  · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, Nat.mul_zero, Nat.zero_add]; exact Cg.refl _ _

/-- `w (n + (c - q))`, by the negation of `w` modulo `m`. -/
private theorem neg_cg {m w q c : Nat} (hm : 0 < m) (hq : q ≤ c) : Cg m (w * (c - q)) (w * c + (m - w % m) * q) := by
  have hl := Nat.mod_lt w hm
  have e : w * c + (m - w % m) * q = w * (c - q) + (w + (m - w % m)) * q := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hq
    rw [Nat.add_sub_cancel_left, Nat.mul_add, Nat.add_mul]
    omega_using []
  rw [e]
  have hz : (w + (m - w % m)) % m = 0 := by
    rw [show w + (m - w % m) = m * (w / m) + m by have := Nat.div_add_mod w m; omega_using [this, hl]]
    rw [Nat.mul_add_mod, Nat.mod_self]
  have : Cg m ((w + (m - w % m)) * q) 0 := by
    unfold Cg; rw [Nat.mul_mod, hz, Nat.zero_mul]
  exact ((Cg.refl m (w * (c - q))).add this).symm

theorem low_bits (x k : Nat) : x &&& (2 ^ k - 1) = x % 2 ^ k := Nat.and_two_pow_sub_one_eq_mod x k

/-- The value of a functional before and after an operation. -/
theorem back_ok {m : Nat} (hm : 0 < m) {inp : Nat → Nat → Nat} (hi : ∀ k i, inp k i < 2 ^ 64) {B : Bd} {s : St}
    (hs : Ok s) (hB : B.Ok s) {o : Op} {F F' : Fn} (h : back m B o F = some F') :
    Cg m (F.ev inp (step inp o s)) (F'.ev inp s) := by
  have hA := step_agree inp o s
  have hO : Ok (step inp o s) := step_Ok hi hs o
  have u : ∀ r, s.g r ≤ B.u r := hB.ub
  -- what is left once the result's coefficient is taken
  have main : ∀ {w : Nat} {l : List Seg} {p : List Pr}, take m (rn o.dst) F.l = some (w, l) →
      sumP inp (step inp o s) F.p = sumP inp s p →
      Cg m (F.ev inp (step inp o s))
        (F.k + (F.f * (step inp o s).c + w * (step inp o s).g o.dst) + sumL inp s l + sumP inp s p) := by
    intro w l p ht hp
    obtain ⟨t1, t2⟩ := take_ok (inp := inp) (s := step inp o s) (by rw [lv_reg]; exact hO.g _) ht
    rw [lv_reg, sumL_agree hA t2] at t1
    unfold Fn.ev
    rw [hp]
    refine Cg.add ?_ (Cg.refl _ _)
    refine (Cg.add (Cg.refl _ _) t1).trans (Cg.of_eq ?_)
    omega_using []
  cases o with
  | ld k i d =>
    rw [back] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Nat.ble_eq] at hc
      simp only [Option.some.injEq] at h
      subst h
      have hl : inpLoc k i < 1024 := by unfold inpLoc; omega_using [hc.1, hc.2]
      have hv : (step inp (.ld k i d) s).g d = lv inp s (inpLoc k i) := by
        rw [lv_inp inp s (by omega_using [hc.1])]; exact g_set _ _ _
      refine Cg.of_eq ?_
      unfold Fn.ev
      rw [subL_ok (d := d) hA hv, subP_ok (d := d) hA hl hv]
      rfl
    · exact absurd h (by simp)
  | lsl d n k =>
    rw [back] at h
    split at h
    · rename_i l p ht hp
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        have hg : (step inp (.lsl d n k) s).g d = s.g n * 2 ^ k % 2 ^ 64 := g_set _ _ _
        have hp' : sumP inp (step inp (.lsl d n k) s) F.p = sumP inp s p := by
          split at hp
          · rename_i h1
            have h1 := Nat.eq_of_beq_eq_true h1
            subst h1
            refine renP_ok (d := d) hA ?_ hp
            rw [ev, ite_eq_right (by omega_using []), ite_eq_left (by have := rn_lt n; omega_using [this]),
              Nat.add_sub_cancel_left, lv_reg]
            exact hg
          · split at hp
            · rename_i h2
              simp only [Option.some.injEq] at hp
              subst hp
              exact noP_ok (d := d) hA h2
            · exact absurd hp (by simp)
        unfold Fn.ev
        rw [hp']
        exact Cg.add (Cg.add (Cg.refl _ _) (pullShl_ok (d := d) hA hg ht)) (Cg.refl _ _)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  | extr d n q k =>
    rw [back] at h
    split at h
    · rename_i l p ht hp
      split at h
      · rename_i hk
        have hk := Nat.le_of_ble_eq_true hk
        simp only [Option.some.injEq] at h
        subst h
        have hg : (step inp (.extr d n q k) s).g d = (s.g n * 2 ^ 64 + s.g q) / 2 ^ k % 2 ^ 64 := g_set _ _ _
        have hp' : sumP inp (step inp (.extr d n q k) s) F.p = sumP inp s p := by
          split at hp
          · rename_i h1
            have h1 := Nat.eq_of_beq_eq_true h1
            subst h1
            refine renP_ok (d := d) hA ?_ hp
            have hn := rn_lt n
            have hq := rn_lt q
            have e1 : (2048 + 1024 * rn n + rn q - 2048) / 1024 = rn n := by omega_using [hq]
            have e2 : (2048 + 1024 * rn n + rn q - 2048) % 1024 = rn q := by omega_using [hq]
            rw [ev, ite_eq_right (by omega_using []), ite_eq_right (by omega_using []), e1, e2, lv_reg, lv_reg]
            exact hg
          · split at hp
            · rename_i h2
              simp only [Option.some.injEq] at hp
              subst hp
              exact noP_ok (d := d) hA h2
            · exact absurd hp (by simp)
        unfold Fn.ev
        rw [hp']
        exact Cg.add (Cg.add (Cg.refl _ _) (pullExtr_ok (d := d) hs hA (by omega_using [hk]) hg ht)) (Cg.refl _ _)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  | mul d n q =>
    simp only [back] at h
    split at h
    · rename_i hn
      split at h
      · exact absurd h (by simp)
      · rename_i w l ht
        simp only [Option.some.injEq] at h
        subst h
        refine (main ht (noP_ok (d := d) hA hn)).trans ?_
        unfold Fn.ev
        refine Cg.trans (Cg.of_eq ?_) ((Cg.refl _ _).add (addPr_ok m inp s _ _).symm)
        have hg : (step inp (.mul d n q) s).g (Op.mul d n q).dst = s.g n * s.g q % 2 ^ 64 := g_set _ _ _
        have hc : (step inp (.mul d n q) s).c = s.c := rfl
        rw [hg, hc]
        have hn := rn_lt n
        have hq := rn_lt q
        simp only [Pr.ev, ev, ite_eq_left (show rn n < 1024 by omega_using [hn]), ite_eq_left (show rn q < 1024 by omega_using [hq]), lv_reg,
          Nat.zero_mul]
        omega_using []
    · exact absurd h (by simp)
  | umulh d n q =>
    simp only [back] at h
    split at h
    · rename_i hn
      split at h
      · exact absurd h (by simp)
      · rename_i w l ht
        simp only [Option.some.injEq] at h
        subst h
        refine (main ht (noP_ok (d := d) hA hn)).trans ?_
        unfold Fn.ev
        refine Cg.trans (Cg.of_eq ?_) ((Cg.refl _ _).add (addPr_ok m inp s _ _).symm)
        have hg : (step inp (.umulh d n q) s).g (Op.umulh d n q).dst = s.g n * s.g q / 2 ^ 64 := g_set _ _ _
        have hc : (step inp (.umulh d n q) s).c = s.c := rfl
        rw [hg, hc]
        have hn := rn_lt n
        have hq := rn_lt q
        simp only [Pr.ev, ev, ite_eq_left (show rn n < 1024 by omega_using [hn]), ite_eq_left (show rn q < 1024 by omega_using [hq]), lv_reg,
          Nat.zero_mul]
        omega_using []
    · exact absurd h (by simp)
  | add d n q =>
    simp only [back] at h
    split at h
    · rename_i hn
      split at h
      · exact absurd h (by simp)
      · rename_i w l ht
        split at h
        · rename_i hb
          simp only [Option.some.injEq] at h
          subst h
          refine (main ht (noP_ok (d := d) hA hn)).trans ?_
          unfold Fn.ev
          dsimp only
          refine Cg.add ?_ (Cg.refl _ _)
          refine Cg.trans (Cg.of_eq ?_) ((Cg.refl _ _).add (both_cg hs n q rfl).symm)
          have hg : (step inp (.add d n q) s).g (Op.add d n q).dst = (s.g n + s.g q) % 2 ^ 64 := g_set _ _ _
          have hc : (step inp (.add d n q) s).c = s.c := rfl
          rw [hg, hc, Nat.mod_eq_of_lt (lt_of_ble2 hb (u n) (u q)), Nat.mul_add]
          omega_using []
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  | adc d n q =>
    simp only [back] at h
    split at h
    · rename_i hn
      split at h
      · exact absurd h (by simp)
      · rename_i w l ht
        split at h
        · rename_i hb
          simp only [Option.some.injEq] at h
          subst h
          refine (main ht (noP_ok (d := d) hA hn)).trans ?_
          unfold Fn.ev
          dsimp only
          refine Cg.add ?_ (Cg.refl _ _)
          refine Cg.trans ?_ (((Cg.refl _ _).add ((Cg.mod m _).mul _).symm).add (both_cg hs n q rfl).symm)
          have hg : (step inp (.adc d n q) s).g (Op.adc d n q).dst = (s.g n + s.g q + s.c) % 2 ^ 64 := g_set _ _ _
          have hc : (step inp (.adc d n q) s).c = s.c := rfl
          rw [hg, hc, Nat.mod_eq_of_lt (lt_of_ble hb (u n) (u q) hB.c), Nat.mul_add, Nat.mul_add, Nat.add_mul]
          exact Cg.of_eq (by omega_using [])
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  | adds d n q =>
    simp only [back] at h
    split at h
    · rename_i hn
      split at h
      · exact absurd h (by simp)
      · rename_i w l ht
        split at h
        · rename_i hb
          simp only [Option.some.injEq] at h
          subst h
          refine (main ht (noP_ok (d := d) hA hn)).trans ?_
          unfold Fn.ev
          dsimp only
          refine Cg.add ?_ (Cg.refl _ _)
          refine Cg.trans ?_ ((Cg.refl _ _).add (both_cg hs n q rfl).symm)
          have hg : (step inp (.adds d n q) s).g (Op.adds d n q).dst = (s.g n + s.g q) % 2 ^ 64 := g_setc _ _ _
          have hc : (step inp (.adds d n q) s).c = (s.g n + s.g q) / 2 ^ 64 := rfl
          rw [hg, hc, Nat.add_assoc F.k, Nat.zero_mul]
          refine ((Cg.refl _ _).add ((carry_cg ?_).add (Cg.refl _ _))).trans (Cg.of_eq ?_)
          · rw [Bool.or_eq_true] at hb
            exact hb.imp id fun hb => lt_of_ble2 hb (u n) (u q)
          · rw [Nat.mul_add]; omega_using []
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  | adcs d n q =>
    simp only [back] at h
    split at h
    · rename_i hn
      split at h
      · exact absurd h (by simp)
      · rename_i w l ht
        split at h
        · rename_i hb
          simp only [Option.some.injEq] at h
          subst h
          refine (main ht (noP_ok (d := d) hA hn)).trans ?_
          unfold Fn.ev
          dsimp only
          refine Cg.add ?_ (Cg.refl _ _)
          refine Cg.trans ?_ ((Cg.refl _ _).add (both_cg hs n q rfl).symm)
          have hg : (step inp (.adcs d n q) s).g (Op.adcs d n q).dst = (s.g n + s.g q + s.c) % 2 ^ 64 := g_setc _ _ _
          have hc : (step inp (.adcs d n q) s).c = (s.g n + s.g q + s.c) / 2 ^ 64 := rfl
          rw [hg, hc, Nat.add_assoc F.k]
          refine ((Cg.refl _ _).add ((carry_cg ?_).add (Cg.refl _ _))).trans (Cg.of_eq ?_)
          · rw [Bool.or_eq_true] at hb
            exact hb.imp id fun hb => lt_of_ble hb (u n) (u q) hB.c
          · rw [Nat.mul_add, Nat.mul_add]; omega_using []
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  | subs d n q =>
    simp only [back] at h
    split at h
    · rename_i hn
      split at h
      · exact absurd h (by simp)
      · rename_i w l ht
        split at h
        · rename_i hb
          obtain rfl := rn_inj (Nat.eq_of_beq_eq_true hb)
          simp only [Option.some.injEq] at h
          subst h
          refine (main ht (noP_ok (d := d) hA hn)).trans ?_
          unfold Fn.ev
          dsimp only
          refine Cg.add ?_ (Cg.refl _ _)
          refine Cg.trans (Cg.of_eq ?_) (((Cg.mod m _).symm.add (Cg.refl _ _)).add (Cg.refl _ _))
          have hg : (step inp (.subs d n n) s).g (Op.subs d n n).dst =
            (s.g n + (2 ^ 64 - 1 - s.g n) + 1) % 2 ^ 64 := g_setc _ _ _
          have hc : (step inp (.subs d n n) s).c = (s.g n + (2 ^ 64 - 1 - s.g n) + 1) / 2 ^ 64 := rfl
          have hq := hs.g n
          rw [hg, hc, show s.g n + (2 ^ 64 - 1 - s.g n) + 1 = 2 ^ 64 by omega_using [hq], Nat.mod_self,
            Nat.div_self (by decide)]
          omega_using []
        split at h
        · rename_i hb
          simp only [Option.some.injEq] at h
          subst h
          refine (main ht (noP_ok (d := d) hA hn)).trans ?_
          unfold Fn.ev
          dsimp only
          refine Cg.add ?_ (Cg.refl _ _)
          refine Cg.trans ?_ (((Cg.mod m _).symm.add (Cg.refl _ _)).add (both_cg hs n q rfl).symm)
          have hg : (step inp (.subs d n q) s).g (Op.subs d n q).dst =
            (s.g n + (2 ^ 64 - 1 - s.g q) + 1) % 2 ^ 64 := g_setc _ _ _
          have hc : (step inp (.subs d n q) s).c = (s.g n + (2 ^ 64 - 1 - s.g q) + 1) / 2 ^ 64 := rfl
          have hq := hs.g q
          rw [hg, hc, Nat.add_assoc F.k, Nat.zero_mul]
          refine ((Cg.refl _ _).add ((carry_cg (.inl hb)).add (Cg.refl _ _))).trans ?_
          rw [show s.g n + (2 ^ 64 - 1 - s.g q) + 1 = s.g n + (2 ^ 64 - s.g q) by omega_using [hq], Nat.mul_add]
          refine ((Cg.refl _ _).add (((Cg.refl _ _).add (neg_cg hm (Nat.le_of_lt hq))).add (Cg.refl _ _))).trans (Cg.of_eq ?_)
          omega_using []
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  | sbcs d n q =>
    simp only [back] at h
    split at h
    · rename_i hn
      split at h
      · exact absurd h (by simp)
      · rename_i w l ht
        split at h
        · rename_i hb
          simp only [Option.some.injEq] at h
          subst h
          refine (main ht (noP_ok (d := d) hA hn)).trans ?_
          unfold Fn.ev
          dsimp only
          refine Cg.add ?_ (Cg.refl _ _)
          refine Cg.trans ?_ (((Cg.mod m _).symm.add (Cg.refl _ _)).add (both_cg hs n q rfl).symm)
          have hg : (step inp (.sbcs d n q) s).g (Op.sbcs d n q).dst =
            (s.g n + (2 ^ 64 - 1 - s.g q) + s.c) % 2 ^ 64 := g_setc _ _ _
          have hc : (step inp (.sbcs d n q) s).c = (s.g n + (2 ^ 64 - 1 - s.g q) + s.c) / 2 ^ 64 := rfl
          have hq := hs.g q
          rw [hg, hc, Nat.add_assoc F.k]
          refine ((Cg.refl _ _).add ((carry_cg (.inl hb)).add (Cg.refl _ _))).trans ?_
          rw [Nat.mul_add, Nat.mul_add]
          refine ((Cg.refl _ _).add ((((Cg.refl _ _).add (neg_cg hm (show s.g q ≤ 2 ^ 64 - 1 by omega_using [hq]))).add
            (Cg.refl _ _)).add (Cg.refl _ _))).trans (Cg.of_eq ?_)
          omega_using []
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  | lsr d n k =>
    simp only [back] at h
    split at h
    · rename_i hn
      split at h
      · exact absurd h (by simp)
      · rename_i w l ht
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          refine (main ht (noP_ok (d := d) hA hn)).trans ?_
          unfold Fn.ev
          dsimp only
          refine Cg.add ?_ (Cg.refl _ _)
          refine Cg.trans (Cg.of_eq ?_) ((Cg.refl _ _).add (addSeg_ok m inp s _ _).symm)
          have hg : (step inp (.lsr d n k) s).g (Op.lsr d n k).dst = s.g n / 2 ^ k := g_set _ _ _
          have hc : (step inp (.lsr d n k) s).c = s.c := rfl
          rw [hg, hc]
          simp only [Seg.ev, lv_reg, Nat.mod_eq_of_lt (hs.g n)]
          omega_using []
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  | movz d v =>
    simp only [back] at h
    split at h
    · rename_i hn
      split at h
      · exact absurd h (by simp)
      · rename_i w l ht
        simp only [Option.some.injEq] at h
        subst h
        refine (main ht (noP_ok (d := d) hA hn)).trans ?_
        unfold Fn.ev
        dsimp only
        refine Cg.add ?_ (Cg.refl _ _)
        refine Cg.trans (Cg.of_eq ?_) (((Cg.mod m _).symm.add (Cg.refl _ _)).add (Cg.refl _ _))
        have hg : (step inp (.movz d v) s).g (Op.movz d v).dst = v % 2 ^ 16 := g_set _ _ _
        have hc : (step inp (.movz d v) s).c = s.c := rfl
        rw [hg, hc]
        omega_using []
    · exact absurd h (by simp)
  | low d n q k =>
    simp only [back] at h
    split at h
    · rename_i hn
      split at h
      · exact absurd h (by simp)
      · rename_i w l ht
        split at h
        · rename_i hb
          simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hb
          simp only [Option.some.injEq] at h
          subst h
          refine (main ht (noP_ok (d := d) hA hn)).trans ?_
          unfold Fn.ev
          dsimp only
          refine Cg.add ?_ (Cg.refl _ _)
          refine Cg.trans (Cg.of_eq ?_) ((Cg.refl _ _).add (addSeg_ok m inp s _ _).symm)
          have hl := hB.lb q
          have hu := u q
          have hq : s.g q = 2 ^ k - 1 := by omega_using [hl, hu, hb.1.1, hb.1.2]
          have hg : (step inp (.low d n q k) s).g (Op.low d n q k).dst = s.g n &&& s.g q := g_set _ _ _
          have hc : (step inp (.low d n q k) s).c = s.c := rfl
          rw [hg, hc, hq, low_bits]
          simp only [Seg.ev, lv_reg, Nat.pow_zero, Nat.div_one]
          omega_using []
        · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- The functional before a sequence. -/
def backs (m : Nat) (ib : Nat → Nat → Nat) : List Op → Bd → Fn → Option Fn
  | [], _, F => some F
  | o :: os, B, F =>
    match backs m ib os (fwd ib o B) F with
    | none => none
    | some G => back m B o G

/-- The value of a functional before and after a sequence. -/
theorem backs_ok {m : Nat} (hm : 0 < m) {inp ib : Nat → Nat → Nat} (hw : ∀ k i, inp k i < 2 ^ 64)
    (hi : ∀ k i, inp k i ≤ ib k i) : ∀ (os : List Op) {B : Bd} {s : St} {F F' : Fn}, B.wf = true → Ok s → B.Ok s →
      backs m ib os B F = some F' → Cg m (F.ev inp (run inp os s)) (F'.ev inp s)
  | [], _, _, _, _, _, _, _, h => by
    simp only [backs, Option.some.injEq] at h; subst h; exact Cg.refl _ _
  | o :: os, B, s, F, F', hb, hs, hB, h => by
    rw [backs] at h
    split at h
    · exact absurd h (by simp)
    · rename_i G hG
      exact (backs_ok hm hw hi os (fwd_wf hb o) (step_Ok hw hs o) (fwd_ok hi hb hs hB o) hG).trans
        (back_ok hm hw hs hB h)

end VG.Proof.Mont.AArch64.P521
