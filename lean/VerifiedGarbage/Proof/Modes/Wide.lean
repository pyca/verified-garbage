module
-- separate module: the batched modes' target-independent part, for every target

public import VerifiedGarbage.Proof.Modes.Steps
public import VerifiedGarbage.Impl.Modes.Wide

/-!
# Block cipher modes, a group of blocks at a time, for any target

A step of `Mode.widen G L M` takes a group of `G` blocks of `L` bytes. Its
step function is `group L G F`: `M`'s step function `F` on each block of
the group in turn (`split L G`), the outputs joined. Its block cipher
enciphers each of the buffer's `G` blocks (`blocksCipher L G ciph`). Each
mode here computes it (`ComputesB`):

* `cbcDecWide_computes`: CBC decryption, `Mode.cbcDecChained` widened.
* `cfbDecWide_computes`: CFB decryption, `Mode.cfbDecEarly` widened.

Both follow from what the widened operations leave in each byte of the
areas, which the operations on block `j` (`Op.shift`, `copyAt`, `xorAt`)
change only at block `j`.

`run_group`: running `group L G F` over groups of blocks is running `F`
over the blocks.
-/

@[expose] public section

namespace VG.Proof.Modes

open VG VG.Impl.Modes
open VG.Spec.Cbc (Cipher xor)

/-! ## Groups of blocks -/

/-- The `G` blocks of `L` bytes of `x`. -/
def split (L G : Nat) (x : List Byte) : List (List Byte) :=
  (List.range G).map fun j => (x.drop (L * j)).take L

/-- The block cipher `ciph` on each of `G` blocks of `L` bytes. -/
def blocksCipher (L G : Nat) (ciph : Cipher) : Cipher := fun x => ((split L G x).map ciph).flatten

/-- The step function `F` on a group of `G` blocks of `L` bytes. -/
def group (L G : Nat) (F : StepFn) : StepFn := fun c x =>
  let r := run F c (split L G x)
  (r.1.flatten, r.2)

theorem split_length (L G : Nat) (x : List Byte) : (split L G x).length = G := by simp [split]

theorem run_append (F : StepFn) : ∀ (c : List Byte) (xs ys : List (List Byte)),
    run F c (xs ++ ys) = ((run F c xs).1 ++ (run F (run F c xs).2 ys).1, (run F (run F c xs).2 ys).2)
  | _, [], _ => by simp [run]
  | c, x :: xs, ys => by
    simp only [List.cons_append, run, run_append F _ xs ys, List.cons_append]

/-- Running the groups is running their blocks. -/
theorem run_group (L G : Nat) (F : StepFn) : ∀ (c : List Byte) (gs : List (List Byte)),
    (run (group L G F) c gs).1.flatten = (run F c (gs.flatMap (split L G))).1.flatten ∧
      (run (group L G F) c gs).2 = (run F c (gs.flatMap (split L G))).2
  | _, [] => ⟨rfl, rfl⟩
  | c, g :: gs => by
    obtain ⟨h1, h2⟩ := run_group L G F (run F c (split L G g)).2 gs
    simp only [run, group, List.flatten_cons, List.flatMap_cons, run_append, List.flatten_append]
    exact ⟨by rw [h1], h2⟩

/-! ## Bytes of joined blocks -/

theorem length_flatten_of {L : Nat} : ∀ {ys : List (List Byte)}, (∀ y ∈ ys, y.length = L) →
    ys.flatten.length = ys.length * L
  | [], _ => by simp
  | y :: ys, h => by
    rw [List.flatten_cons, List.length_append, h y List.mem_cons_self,
      length_flatten_of (fun y hy => h y (List.mem_cons_of_mem _ hy)), List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem getD_flatten {L : Nat} : ∀ {ys : List (List Byte)}, (∀ y ∈ ys, y.length = L) → ∀ {i : Nat},
    i < L * ys.length → ys.flatten.getD i 0 = (ys.getD (i / L) []).getD (i % L) 0
  | [], _, _, hi => by simp at hi
  | y :: ys, h, i, hi => by
    have hy := h y List.mem_cons_self
    have hL : 0 < L := by
      rcases Nat.eq_zero_or_pos L with hL | hL
      · subst hL; simp at hi
      · exact hL
    rw [List.flatten_cons]
    by_cases hlt : i < L
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD,
        Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
      rfl
    · have hge : L ≤ i := Nat.le_of_not_lt hlt
      have hrec := getD_flatten (ys := ys) (fun y hy' => h y (List.mem_cons_of_mem _ hy')) (i := i - L)
        (by simp only [List.length_cons, Nat.mul_succ] at hi; omega)
      have e : i = (i - L) + L := by omega
      have hm : i % L = (i - L) % L := by rw [← Nat.add_mod_right (i - L) L, ← e]
      have hd : i / L = (i - L) / L + 1 := by rw [← Nat.add_div_right (i - L) hL, ← e]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hy, ← List.getD_eq_getElem?_getD, hrec,
        hm, hd]
      simp

/-! ## The operations on block `j` -/

/-- A copy of `bw` words from `src` at `sO` to `dst` at `dO`. -/
def copyAt (bw : Nat) (dst : Loc) (dO : Nat) (src : Loc) (sO : Nat) : List Op :=
  (List.range bw).map fun w => { wide := true, dst, dOff := 4 * w + dO, src, sOff := 4 * w + sO }

/-- `dst := x ⊕ y` on `bw` words, at `dO`, `xO` and `yO`. -/
def xorAt (bw : Nat) (dst : Loc) (dO : Nat) (x : Loc) (xO : Nat) (y : Loc) (yO : Nat) : List Op :=
  (List.range bw).map fun w =>
    { wide := true, dst, dOff := 4 * w + dO, src := x, sOff := 4 * w + xO, xr := some (y, 4 * w + yO) }

theorem copyBlk_shift (bw L st j : Nat) (dst src : Loc) :
    (copyBlk bw dst src).map (Op.shift L st j) = copyAt bw dst (shOff L st j dst) src (shOff L st j src) := by
  simp only [copyBlk, copyAt, List.map_map]; rfl

theorem xorBlk_shift (bw L st j : Nat) (dst x y : Loc) :
    (xorBlk bw dst x y).map (Op.shift L st j) =
      xorAt bw dst (shOff L st j dst) x (shOff L st j x) y (shOff L st j y) := by
  simp only [xorBlk, xorAt, List.map_map]; rfl

theorem copyAt_succ (bw : Nat) (dst : Loc) (dO : Nat) (src : Loc) (sO : Nat) :
    copyAt (bw + 1) dst dO src sO =
      copyAt bw dst dO src sO ++ [{ wide := true, dst, dOff := 4 * bw + dO, src, sOff := 4 * bw + sO }] := by
  simp [copyAt, List.range_succ]

theorem xorAt_succ (bw : Nat) (dst : Loc) (dO : Nat) (x : Loc) (xO : Nat) (y : Loc) (yO : Nat) :
    xorAt (bw + 1) dst dO x xO y yO = xorAt bw dst dO x xO y yO ++
      [{ wide := true, dst, dOff := 4 * bw + dO, src := x, sOff := 4 * bw + xO, xr := some (y, 4 * bw + yO) }] := by
  simp [xorAt, List.range_succ]

theorem byte_xor_zero' (x : Byte) : x ^^^ 0 = x := by simp

/-- Close a goal of nested `if`s on arithmetic conditions. -/
local macro "arith_ifs" : tactic =>
  `(tactic| ((repeat' split) <;> (try rw [byte_xor_zero']) <;>
    first | rfl | (exfalso; omega) | (congr 1; omega) | (congr 1 <;> (congr 1; omega))))

theorem copyAt_apply {dst src : Loc} (hne : dst ≠ src) (dO sO : Nat) (a : Areas) :
    ∀ bw l i, applyOps (copyAt bw dst dO src sO) a l i =
      if l = dst ∧ dO ≤ i ∧ i < dO + 4 * bw then a src (i - dO + sO) else a l i
  | 0, l, i => by
    simp only [copyAt, List.range_zero, List.map_nil, applyOps_nil]
    exact (ite_eq_right_iff.mpr fun h => absurd h.2.2 (by omega)).symm
  | bw + 1, l, i => by
    rw [copyAt_succ, applyOps_snoc]
    simp only [Op.apply, Op.val, Op.width, Bool.false_eq_true, ite_false, ite_true, copyAt_apply hne dO sO a bw]
    by_cases hl : l = dst
    · subst hl
      simp only [true_and, Ne.symm hne, false_and, ite_false]
      arith_ifs
    · simp only [hl, false_and, ite_false]

theorem xorAt_apply {dst x y : Loc} (hy : y ≠ dst) {dO xO yO : Nat} (hx : x = dst → xO = dO) (a : Areas) :
    ∀ bw l i, applyOps (xorAt bw dst dO x xO y yO) a l i =
      if l = dst ∧ dO ≤ i ∧ i < dO + 4 * bw then a x (i - dO + xO) ^^^ a y (i - dO + yO) else a l i
  | 0, l, i => by
    simp only [xorAt, List.range_zero, List.map_nil, applyOps_nil]
    exact (ite_eq_right_iff.mpr fun h => absurd h.2.2 (by omega)).symm
  | bw + 1, l, i => by
    rw [xorAt_succ, applyOps_snoc]
    simp only [Op.apply, Op.val, Op.width, Bool.false_eq_true, ite_false, ite_true, xorAt_apply hy hx a bw, hy,
      false_and]
    by_cases hl : l = dst
    · subst hl
      by_cases hxd : x = l
      · subst hxd
        obtain rfl := hx rfl
        simp only [true_and]
        arith_ifs
      · simp only [true_and, hxd, false_and, ite_false]
        arith_ifs
    · simp only [hl, false_and, ite_false]

theorem copyAt_inBounds {len : Loc → Nat} {bw : Nat} {dst src : Loc} {dO sO : Nat} (hd : dO + 4 * bw ≤ len dst)
    (hs : sO + 4 * bw ≤ len src) : ∀ o ∈ copyAt bw dst dO src sO, o.InBounds len := by
  intro o ho
  simp only [copyAt, List.mem_map, List.mem_range] at ho
  obtain ⟨w, hw, rfl⟩ := ho
  exact ⟨by simp [Op.width]; omega, by simp [Op.width]; omega, fun _ _ h => by cases h⟩

theorem xorAt_inBounds {len : Loc → Nat} {bw : Nat} {dst x y : Loc} {dO xO yO : Nat} (hd : dO + 4 * bw ≤ len dst)
    (hx : xO + 4 * bw ≤ len x) (hy : yO + 4 * bw ≤ len y) : ∀ o ∈ xorAt bw dst dO x xO y yO, o.InBounds len := by
  intro o ho
  simp only [xorAt, List.mem_map, List.mem_range] at ho
  obtain ⟨w, hw, rfl⟩ := ho
  exact ⟨by simp [Op.width]; omega, by simp [Op.width]; omega, fun l off h => by
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [Op.width]; omega⟩

theorem widen_pre_succ (G L : Nat) (M : Mode) :
    (Mode.widen (G + 1) L M).pre = (Mode.widen G L M).pre ++ M.pre.map (Op.shift L M.step G) := by
  simp [Mode.widen, List.range_succ, List.flatMap_append]

theorem widen_post_succ (G L : Nat) (M : Mode) :
    (Mode.widen (G + 1) L M).post = (Mode.widen G L M).post ++ M.post.map (Op.shift L M.step G) := by
  simp [Mode.widen, List.range_succ, List.flatMap_append]

theorem widen_pre_zero (L : Nat) (M : Mode) : (Mode.widen 0 L M).pre = [] := rfl
theorem widen_post_zero (L : Nat) (M : Mode) : (Mode.widen 0 L M).post = [] := rfl

/-! ## CBC decryption -/

section
variable (bw : Nat)

/-- The chaining value before block `i / 4 bw`'s byte `i`, in the areas `b`:
the chaining value's, or the previous block's. -/
def prevB (b : Areas) (i : Nat) : Byte := if i < 4 * bw then b .chn i else b .dat (i - 4 * bw)

theorem cbcDecWide_pre (a : Areas) : ∀ G l i, applyOps (Mode.cbcDecWide bw G).pre a l i =
    if l = .buf ∧ i < 4 * bw * G then a .dat i else a l i
  | 0, l, i => by
    simp only [Mode.cbcDecWide, widen_pre_zero, applyOps_nil, Nat.mul_zero, Nat.not_lt_zero, and_false, ite_false]
  | G + 1, l, i => by
    have ih : applyOps (Mode.widen G (4 * bw) (Mode.cbcDecChained bw)).pre a = _ :=
      funext fun l => funext fun i => cbcDecWide_pre a G l i
    simp only [Mode.cbcDecWide]
    rw [widen_pre_succ, applyOps_append, ih]
    simp only [Mode.cbcDecChained, Mode.cbcDec, copyBlk_shift, shOff]
    rw [copyAt_apply (by decide)]
    rw [Nat.mul_succ]
    generalize 4 * bw * G = m
    cases l <;> simp only [reduceCtorEq, false_and, ite_false, true_and] <;> arith_ifs

/-- After the posts of the first `j` blocks, from the areas `b`. -/
def cbcPost (b : Areas) (j : Nat) : Areas
  | .dat, i => if i < 4 * bw * j then b .buf i ^^^ prevB bw b i else b .dat i
  | .chn, i => if i < 4 * bw then (if j = 0 then b .chn i else b .dat (4 * bw * j - 4 * bw + i)) else b .chn i
  | .buf, i => if i < 4 * bw * j then b .buf i ^^^ prevB bw b i else b .buf i

theorem cbcDecWide_post (b : Areas) : ∀ G l i, applyOps (Mode.cbcDecWide bw G).post b l i = cbcPost bw b G l i
  | 0, l, i => by
    simp only [Mode.cbcDecWide, widen_post_zero, applyOps_nil]
    cases l <;> simp [cbcPost]
  | G + 1, l, i => by
    have ih : applyOps (Mode.widen G (4 * bw) (Mode.cbcDecChained bw)).post b = cbcPost bw b G :=
      funext fun l => funext fun i => cbcDecWide_post b G l i
    simp only [Mode.cbcDecWide]
    rw [widen_post_succ, applyOps_append, ih]
    simp only [Mode.cbcDecChained, Mode.cbcDec, List.map_append, copyBlk_shift, xorBlk_shift, shOff, applyOps_append]
    simp only [copyAt_apply (show Loc.dat ≠ .buf by decide), copyAt_apply (show Loc.chn ≠ .dat by decide),
      xorAt_apply (show Loc.chn ≠ .buf by decide) (fun _ => rfl), cbcPost, prevB]
    rw [Nat.mul_succ]
    have h0 : G = 0 → 4 * bw * G = 0 := fun h => by rw [h, Nat.mul_zero]
    have h1 : G ≠ 0 → 4 * bw ≤ 4 * bw * G := fun h => Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h)
    generalize 4 * bw * G = m at h0 h1
    cases l <;> simp only [reduceCtorEq, false_and, ite_false, true_and, Nat.add_one_ne_zero] <;> arith_ifs

end

/-! ## The blocks of a group -/

theorem split_block_length {L G : Nat} {x : List Byte} (hx : x.length = G * L) :
    ∀ y ∈ split L G x, y.length = L := by
  intro y hy
  simp only [split, List.mem_map, List.mem_range] at hy
  obtain ⟨j, hj, rfl⟩ := hy
  have : L * j + L ≤ G * L := by rw [← Nat.mul_succ, Nat.mul_comm G]; exact Nat.mul_le_mul_left _ hj
  simp only [List.length_take, List.length_drop, hx]; omega

theorem split_getD {L G : Nat} {x : List Byte} {k t : Nat} (hk : k < G) (ht : t < L) :
    ((split L G x).getD k []).getD t 0 = x.getD (L * k + t) 0 := by
  simp only [split, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some, List.getElem?_take, ht, ite_true, List.getElem?_drop]

theorem getD_blocksCipher {L G : Nat} {ciph : Cipher} (hc : ∀ b, (ciph b).length = L) {x : List Byte} {i : Nat}
    (hi : i < L * G) :
    (blocksCipher L G ciph x).getD i 0 = (ciph ((split L G x).getD (i / L) [])).getD (i % L) 0 := by
  have hL : 0 < L := Nat.pos_of_ne_zero fun h => by subst h; simp at hi
  have hk : i / L < G := (Nat.div_lt_iff_lt_mul hL).mpr (by rw [Nat.mul_comm]; exact hi)
  rw [blocksCipher, getD_flatten (fun y hy => by
      simp only [List.mem_map] at hy; obtain ⟨z, -, rfl⟩ := hy; exact hc z)
    (by rw [List.length_map, split_length]; exact hi)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, split, List.getElem?_range hk,
    Option.map_some, Option.getD_some]

theorem div_mod_eq {i L : Nat} : L * (i / L) + i % L = i := Nat.div_add_mod i L

/-- `f` at each index below `n`. -/
theorem getD_map_range {α : Type} (f : Nat → α) {n k : Nat} (d : α) (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]

theorem getD_mem {α : Type} {xs : List α} {k : Nat} (d : α) (hk : k < xs.length) : xs.getD k d ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk

/-- CBC decryption's steps: each block deciphered and XORed with the one
before (the chaining value before the first), the last block left. -/
theorem cbcDec_run (ciph : Cipher) : ∀ (c : List Byte) (xs : List (List Byte)),
    (run (cbcDecF ciph) c xs).1 =
      (List.range xs.length).map (fun k => xor (ciph (xs.getD k [])) ((c :: xs).getD k [])) ∧
      (run (cbcDecF ciph) c xs).2 = xs.getLastD c
  | _, [] => ⟨rfl, rfl⟩
  | c, x :: xs => by
    obtain ⟨h1, h2⟩ := cbcDec_run ciph x xs
    refine ⟨?_, by simp only [run, cbcDecF, h2, List.getLastD_cons]⟩
    simp only [run, cbcDecF, h1, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl

/-- Byte `t` of block `k` of the chaining values, `c` then the blocks `xs`
of `x`: `c`'s, or `x`'s byte `L k + t - L`. -/
theorem prev_getD {L G : Nat} {c x : List Byte} {k t : Nat} (hk : k < G) (ht : t < L) :
    ((c :: split L G x).getD k []).getD t 0 = if k = 0 then c.getD t 0 else x.getD (L * k + t - L) 0 := by
  rcases k with _ | k
  · rfl
  · simp only [List.getD_cons_succ, Nat.add_one_ne_zero, ite_false]
    rw [split_getD (by omega) ht, Nat.mul_succ]
    congr 1; omega

section
variable {bw : Nat} {ciph : Cipher} (hc : ∀ b, (ciph b).length = 4 * bw)
include hc

theorem cbcDecWide_computes (G : Nat) :
    ComputesB (Mode.cbcDecWide bw G) (4 * bw) (4 * bw * G) (blocksCipher (4 * bw) G ciph)
      (group (4 * bw) G (cbcDecF ciph)) := by
  intro a
  have hst : (Mode.cbcDecWide bw G).step = G * (4 * bw) := rfl
  rw [hst]
  have hLG : G * (4 * bw) = 4 * bw * G := Nat.mul_comm _ _
  -- The inputs, and the steps' closed form.
  generalize hx : rd a .dat (G * (4 * bw)) = x
  generalize hcv : rd a .chn (4 * bw) = c
  have hxl : x.length = G * (4 * bw) := by rw [← hx, rd_length]
  have hcl : c.length = 4 * bw := by rw [← hcv, rd_length]
  have hxs := split_block_length hxl
  have hxsl := split_length (4 * bw) G x
  obtain ⟨r1, r2⟩ := cbcDec_run ciph c (split (4 * bw) G x)
  rw [hxsl] at r1
  -- The areas after the block cipher.
  let b := cryptBuf (4 * bw * G) (blocksCipher (4 * bw) G ciph) (applyOps (Mode.cbcDecWide bw G).pre a)
  have bdat : ∀ i, b .dat i = a .dat i := fun i => by
    simp only [b, cryptBuf, reduceCtorEq, ite_false, cbcDecWide_pre, false_and]
  have bchn : ∀ i, b .chn i = a .chn i := fun i => by
    simp only [b, cryptBuf, reduceCtorEq, ite_false, cbcDecWide_pre, false_and]
  have rbuf : rd (applyOps (Mode.cbcDecWide bw G).pre a) .buf (4 * bw * G) = x := by
    rw [← hx, ← hLG]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    simp only [cbcDecWide_pre, true_and, ite_eq_left (show i < 4 * bw * G by rw [← hLG]; exact hi)]
  have bbuf : ∀ i, i < 4 * bw * G → b .buf i = (blocksCipher (4 * bw) G ciph x).getD i 0 := fun i _ => by
    simp only [b, cryptBuf, ite_true, rbuf]
  have hpost : stepA (Mode.cbcDecWide bw G) (4 * bw * G) (blocksCipher (4 * bw) G ciph) a = cbcPost bw b G :=
    funext fun l => funext fun i => cbcDecWide_post bw b G l i
  rw [hpost]
  simp only [group, r1, r2]
  -- Each step's output is a block.
  have hprevl : ∀ k < G, ((c :: split (4 * bw) G x).getD k []).length = 4 * bw := fun k hk => by
    rcases k with _ | k
    · exact hcl
    · rw [List.getD_cons_succ]; exact hxs _ (getD_mem _ (by rw [hxsl]; omega))
  have hout : ∀ y ∈ (List.range G).map (fun k => xor (ciph ((split (4 * bw) G x).getD k []))
      ((c :: split (4 * bw) G x).getD k [])), y.length = 4 * bw := by
    intro y hy
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    rw [xor_length, hc, hprevl k hk, Nat.min_self]
  refine ⟨rd_eq ?_ fun i hi => ?_, rd_eq ?_ fun i hi => ?_⟩
  · rw [length_flatten_of hout, List.length_map, List.length_range]
  · -- A byte of the data: block `k`'s byte `t`.
    have hL : 0 < 4 * bw := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hi; omega
    have hi' : i < 4 * bw * G := by rw [← hLG]; exact hi
    have hk : i / (4 * bw) < G := (Nat.div_lt_iff_lt_mul hL).mpr hi
    have ht : i % (4 * bw) < 4 * bw := Nat.mod_lt _ hL
    have hdm := div_mod_eq (i := i) (L := 4 * bw)
    rw [getD_flatten hout (by rw [List.length_map, List.length_range]; exact hi'), getD_map_range _ _ hk,
      getD_xor (by rw [hc]; exact ht) (by rw [hprevl _ hk]; exact ht), prev_getD hk ht]
    simp only [cbcPost, ite_eq_left hi', bbuf i hi', getD_blocksCipher hc hi', prevB, bchn, bdat]
    congr 1
    by_cases h0 : i / (4 * bw) = 0
    · have : i < 4 * bw := by
        have := Nat.div_add_mod i (4 * bw); rw [h0, Nat.mul_zero, Nat.zero_add] at this; omega
      rw [ite_eq_left this, ite_eq_left h0, ← hcv, getD_rd ht, Nat.mod_eq_of_lt this]
    · have : ¬ i < 4 * bw := fun h => h0 (Nat.div_eq_of_lt h)
      rw [ite_eq_right this, ite_eq_right h0, hdm, ← hx, getD_rd (by omega)]
  · rw [List.getLastD_eq_getLast?]
    rcases Nat.eq_zero_or_pos G with hG | hG
    · subst hG; simp [split, hcl]
    · rw [List.getLast?_eq_getElem?, hxsl, List.getElem?_eq_getElem (by rw [hxsl]; omega), Option.getD_some]
      exact hxs _ (List.getElem_mem _)
  · simp only [cbcPost, ite_eq_left hi, bchn, bdat]
    rw [List.getLastD_eq_getLast?]
    rcases Nat.eq_zero_or_pos G with hG | hG
    · subst hG
      simp only [ite_true, split, List.range_zero, List.map_nil, List.getLast?_nil, Option.getD_none, ← hcv,
        getD_rd hi]
    · have hk : G - 1 < G := by omega
      have e := split_getD (x := x) hk hi
      rw [show (split (4 * bw) G x).getD (G - 1) [] = (split (4 * bw) G x)[G - 1]'(by rw [hxsl]; exact hk) by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl] at e
      rw [ite_eq_right (by omega), List.getLast?_eq_getElem?, hxsl, List.getElem?_eq_getElem (by rw [hxsl]; exact hk),
        Option.getD_some, e, ← hx,
        getD_rd (by rw [hLG]; have := Nat.mul_le_mul_left (4 * bw) (show G - 1 + 1 ≤ G by omega)
                    rw [Nat.mul_succ] at this; omega)]
      congr 1
      rw [Nat.mul_sub_one]
end

/-! ## CFB decryption -/

section
variable (bw : Nat)

/-- After the pres of the first `j` blocks, from the areas `a`: the
chaining values before them in the buffer, the last of them in the chaining
value. -/
def cfbPre (a : Areas) (j : Nat) : Areas
  | .dat, i => a .dat i
  | .chn, i => if i < 4 * bw then (if j = 0 then a .chn i else a .dat (4 * bw * j - 4 * bw + i)) else a .chn i
  | .buf, i => if i < 4 * bw * j then prevB bw a i else a .buf i

theorem cfbDecWide_pre (a : Areas) : ∀ G l i, applyOps (Mode.cfbDecWide bw G).pre a l i = cfbPre bw a G l i
  | 0, l, i => by
    simp only [Mode.cfbDecWide, widen_pre_zero, applyOps_nil]
    cases l <;> simp [cfbPre]
  | G + 1, l, i => by
    have ih : applyOps (Mode.widen G (4 * bw) (Mode.cfbDecEarly bw)).pre a = cfbPre bw a G :=
      funext fun l => funext fun i => cfbDecWide_pre a G l i
    simp only [Mode.cfbDecWide]
    rw [widen_pre_succ, applyOps_append, ih]
    simp only [Mode.cfbDecEarly, List.map_append, copyBlk_shift, shOff, applyOps_append]
    simp only [copyAt_apply (show Loc.chn ≠ .dat by decide), copyAt_apply (show Loc.buf ≠ .chn by decide), cfbPre,
      prevB]
    rw [Nat.mul_succ]
    have h0 : G = 0 → 4 * bw * G = 0 := fun h => by rw [h, Nat.mul_zero]
    have h1 : G ≠ 0 → 4 * bw ≤ 4 * bw * G := fun h => Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h)
    generalize 4 * bw * G = m at h0 h1
    cases l <;> simp only [reduceCtorEq, false_and, ite_false, true_and, Nat.add_one_ne_zero] <;> arith_ifs

/-- After the posts of the first `j` blocks, from the areas `b`. -/
def cfbPost (b : Areas) (j : Nat) : Areas
  | .dat, i => if i < 4 * bw * j then b .dat i ^^^ b .buf i else b .dat i
  | .chn, i => b .chn i
  | .buf, i => b .buf i

theorem cfbDecWide_post (b : Areas) : ∀ G l i, applyOps (Mode.cfbDecWide bw G).post b l i = cfbPost bw b G l i
  | 0, l, i => by
    simp only [Mode.cfbDecWide, widen_post_zero, applyOps_nil]
    cases l <;> simp [cfbPost]
  | G + 1, l, i => by
    have ih : applyOps (Mode.widen G (4 * bw) (Mode.cfbDecEarly bw)).post b = cfbPost bw b G :=
      funext fun l => funext fun i => cfbDecWide_post b G l i
    simp only [Mode.cfbDecWide]
    rw [widen_post_succ, applyOps_append, ih]
    simp only [Mode.cfbDecEarly, xorBlk_shift, shOff]
    simp only [xorAt_apply (show Loc.buf ≠ .dat by decide) (fun _ => rfl), cfbPost]
    rw [Nat.mul_succ]
    generalize 4 * bw * G = m
    cases l <;> simp only [reduceCtorEq, false_and, ite_false, true_and] <;> arith_ifs

end

/-- CFB decryption's steps: each block XORed with the cipher of the one
before (the chaining value before the first), the last block left. -/
theorem cfbDec_run' (ciph : Cipher) : ∀ (c : List Byte) (xs : List (List Byte)),
    (run (cfbDecF ciph) c xs).1 =
      (List.range xs.length).map (fun k => xor (xs.getD k []) (ciph ((c :: xs).getD k []))) ∧
      (run (cfbDecF ciph) c xs).2 = xs.getLastD c
  | _, [] => ⟨rfl, rfl⟩
  | c, x :: xs => by
    obtain ⟨h1, h2⟩ := cfbDec_run' ciph x xs
    refine ⟨?_, by simp only [run, cfbDecF, h2, List.getLastD_cons]⟩
    simp only [run, cfbDecF, h1, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl

section
variable {bw : Nat} {ciph : Cipher} (hc : ∀ b, (ciph b).length = 4 * bw)
include hc

theorem cfbDecWide_computes (G : Nat) :
    ComputesB (Mode.cfbDecWide bw G) (4 * bw) (4 * bw * G) (blocksCipher (4 * bw) G ciph)
      (group (4 * bw) G (cfbDecF ciph)) := by
  intro a
  have hst : (Mode.cfbDecWide bw G).step = G * (4 * bw) := rfl
  rw [hst]
  have hLG : G * (4 * bw) = 4 * bw * G := Nat.mul_comm _ _
  generalize hx : rd a .dat (G * (4 * bw)) = x
  generalize hcv : rd a .chn (4 * bw) = c
  have hxl : x.length = G * (4 * bw) := by rw [← hx, rd_length]
  have hcl : c.length = 4 * bw := by rw [← hcv, rd_length]
  have hxs := split_block_length hxl
  have hxsl := split_length (4 * bw) G x
  obtain ⟨r1, r2⟩ := cfbDec_run' ciph c (split (4 * bw) G x)
  rw [hxsl] at r1
  have hprevl : ∀ k < G, ((c :: split (4 * bw) G x).getD k []).length = 4 * bw := fun k hk => by
    rcases k with _ | k
    · exact hcl
    · rw [List.getD_cons_succ]; exact hxs _ (getD_mem _ (by rw [hxsl]; omega))
  -- The buffer before the block cipher: the chaining values.
  have hP : ∀ k < G, (split (4 * bw) G (rd (applyOps (Mode.cfbDecWide bw G).pre a) .buf (4 * bw * G))).getD k [] =
      (c :: split (4 * bw) G x).getD k [] := fun k hk => by
    have hl1 := split_block_length (x := rd (applyOps (Mode.cfbDecWide bw G).pre a) .buf (4 * bw * G))
      (by rw [rd_length, hLG]) _ (getD_mem (xs := split (4 * bw) G
        (rd (applyOps (Mode.cfbDecWide bw G).pre a) .buf (4 * bw * G))) [] (by rw [split_length]; exact hk))
    apply List.ext_getElem (by rw [hl1, hprevl k hk])
    intro t h1 _
    have ht : t < 4 * bw := by rw [hl1] at h1; exact h1
    have hkt : 4 * bw * k + t < 4 * bw * G := by
      have := Nat.mul_le_mul_left (4 * bw) (show k + 1 ≤ G by omega); rw [Nat.mul_succ] at this; omega
    rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0, split_getD hk ht, prev_getD hk ht, getD_rd hkt,
      cfbDecWide_pre, cfbPre, ite_eq_left hkt, prevB]
    rcases k with _ | k
    · rw [Nat.mul_zero, Nat.zero_add, ite_eq_left ht, ite_eq_left rfl, ← hcv, getD_rd ht]
    · rw [ite_eq_right (by rw [Nat.mul_succ]; omega), ite_eq_right (Nat.add_one_ne_zero _), ← hx,
        getD_rd (by rw [hLG]; omega)]
  let b := cryptBuf (4 * bw * G) (blocksCipher (4 * bw) G ciph) (applyOps (Mode.cfbDecWide bw G).pre a)
  have bdat : ∀ i, b .dat i = a .dat i := fun i => by
    simp only [b, cryptBuf, reduceCtorEq, ite_false, cfbDecWide_pre, cfbPre]
  have bchn : ∀ i, b .chn i = cfbPre bw a G .chn i := fun i => by
    simp only [b, cryptBuf, reduceCtorEq, ite_false, cfbDecWide_pre]
  have hpost : stepA (Mode.cfbDecWide bw G) (4 * bw * G) (blocksCipher (4 * bw) G ciph) a = cfbPost bw b G :=
    funext fun l => funext fun i => cfbDecWide_post bw b G l i
  rw [hpost]
  simp only [group, r1, r2]
  have hout : ∀ y ∈ (List.range G).map (fun k => xor ((split (4 * bw) G x).getD k [])
      (ciph ((c :: split (4 * bw) G x).getD k []))), y.length = 4 * bw := by
    intro y hy
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    rw [xor_length, hc, hxs _ (getD_mem _ (by rw [hxsl]; exact hk)), Nat.min_self]
  refine ⟨rd_eq ?_ fun i hi => ?_, rd_eq ?_ fun i hi => ?_⟩
  · rw [length_flatten_of hout, List.length_map, List.length_range]
  · have hL : 0 < 4 * bw := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hi; omega
    have hi' : i < 4 * bw * G := by rw [← hLG]; exact hi
    have hk : i / (4 * bw) < G := (Nat.div_lt_iff_lt_mul hL).mpr hi
    have ht : i % (4 * bw) < 4 * bw := Nat.mod_lt _ hL
    have hdm := div_mod_eq (i := i) (L := 4 * bw)
    rw [getD_flatten hout (by rw [List.length_map, List.length_range]; exact hi'), getD_map_range _ _ hk,
      getD_xor (by rw [hxs _ (getD_mem _ (by rw [hxsl]; exact hk))]; exact ht) (by rw [hc]; exact ht),
      split_getD hk ht, hdm, ← hP _ hk]
    simp only [cfbPost, ite_eq_left hi', bdat, b, cryptBuf, ite_true, ← hx, getD_rd hi]
    rw [getD_blocksCipher hc hi']
  · rw [List.getLastD_eq_getLast?]
    rcases Nat.eq_zero_or_pos G with hG | hG
    · subst hG; simp [split, hcl]
    · rw [List.getLast?_eq_getElem?, hxsl, List.getElem?_eq_getElem (by rw [hxsl]; omega), Option.getD_some]
      exact hxs _ (List.getElem_mem _)
  · simp only [cfbPost, bchn, cfbPre, ite_eq_left hi]
    rw [List.getLastD_eq_getLast?]
    rcases Nat.eq_zero_or_pos G with hG | hG
    · subst hG
      simp only [ite_true, split, List.range_zero, List.map_nil, List.getLast?_nil, Option.getD_none, ← hcv,
        getD_rd hi]
    · have hk : G - 1 < G := by omega
      have e := split_getD (x := x) hk hi
      rw [show (split (4 * bw) G x).getD (G - 1) [] = (split (4 * bw) G x)[G - 1]'(by rw [hxsl]; exact hk) by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl] at e
      rw [ite_eq_right (by omega), List.getLast?_eq_getElem?, hxsl, List.getElem?_eq_getElem (by rw [hxsl]; exact hk),
        Option.getD_some, e, ← hx,
        getD_rd (by rw [hLG]; have := Nat.mul_le_mul_left (4 * bw) (show G - 1 + 1 ≤ G by omega)
                    rw [Nat.mul_succ] at this; omega)]
      congr 1
      rw [Nat.mul_sub_one]

/-- CFB decryption with the chaining value updated before the block cipher,
one block a step. -/
theorem cfbDecEarly_computes : Computes (Mode.cfbDecEarly bw) (4 * bw) ciph (cfbDecF ciph) := by
  intro a
  have hb : rd (applyOps (Mode.cfbDecEarly bw).pre a) .buf (4 * bw) = rd a .chn (4 * bw) :=
    rd_eq (by simp [rd_length]) fun i hi => by
      simp only [Mode.cfbDecEarly, applyOps_append, copyBlk_apply (show Loc.chn ≠ .dat by decide),
        copyBlk_apply (show Loc.buf ≠ .chn by decide), reduceCtorEq, false_and, ite_false, true_and, hi, ite_true]
      rw [getD_rd hi]
  simp only [stepA, Mode.cfbDecEarly, cfbDecF, applyOps_append] at hb ⊢
  refine ⟨rd_eq (by simp [xor_length, hc, rd_length]) fun i hi => ?_, rd_eq (rd_length _ _ _) fun i hi => ?_⟩
  · rw [xorBlk_apply, ite_eq_left ⟨rfl, hi⟩]
    simp only [cryptBuf, ite_true, hb, reduceCtorEq, ite_false,
      copyBlk_apply (show Loc.chn ≠ .dat by decide), copyBlk_apply (show Loc.buf ≠ .chn by decide), false_and]
    rw [getD_xor (by rw [rd_length]; exact hi) (by rw [hc]; exact hi), getD_rd hi]
  · rw [xorBlk_apply, ite_eq_right (by simp)]
    simp only [cryptBuf, reduceCtorEq, ite_false, copyBlk_apply (show Loc.chn ≠ .dat by decide),
      copyBlk_apply (show Loc.buf ≠ .chn by decide), false_and, true_and, hi, ite_true]
    rw [getD_rd hi]

end

/-! ## Groups of blocks in memory -/

theorem drop_take_flatten {L : Nat} : ∀ {ys : List (List Byte)}, (∀ y ∈ ys, y.length = L) → ∀ {j : Nat}
    (hj : j < ys.length), (ys.flatten.drop (L * j)).take L = ys[j]
  | [], _, _, hj => by simp at hj
  | y :: ys, h, j, hj => by
    have hy := h y List.mem_cons_self
    rcases j with _ | j
    · rw [Nat.mul_zero, List.drop_zero, List.flatten_cons, List.take_left' hy]; rfl
    · rw [List.flatten_cons, List.drop_append, List.drop_eq_nil_of_le (by rw [hy, Nat.mul_succ]; omega),
        List.nil_append, hy, show L * (j + 1) - L = L * j by rw [Nat.mul_succ]; omega,
        drop_take_flatten (fun y hy' => h y (List.mem_cons_of_mem _ hy')) (by simp at hj; omega)]
      rfl

/-- Splitting `G` joined blocks gives them back. -/
theorem split_flatten {L G : Nat} {ys : List (List Byte)} (hl : ys.length = G) (h : ∀ y ∈ ys, y.length = L) :
    split L G ys.flatten = ys := by
  apply List.ext_getElem (by rw [split_length, hl])
  intro j h1 _
  simp only [split, List.getElem_map, List.getElem_range]
  exact drop_take_flatten h (by rw [split_length] at h1; omega)

/-- Each step's output is a block of `L` bytes, and its chaining value of
`Lc`, from a chaining value of `Lc` and a block of `L`. -/
def Blockwise (F : StepFn) (L Lc : Nat) : Prop :=
  ∀ c x, c.length = Lc → x.length = L → (F c x).1.length = L ∧ (F c x).2.length = Lc

theorem run_blockwise {F : StepFn} {L Lc : Nat} (hF : Blockwise F L Lc) : ∀ (c : List Byte) (xs : List (List Byte)),
    c.length = Lc → (∀ x ∈ xs, x.length = L) → (∀ y ∈ (run F c xs).1, y.length = L) ∧ (run F c xs).2.length = Lc
  | _, [], hc, _ => ⟨fun _ h => by simp [run] at h, hc⟩
  | c, x :: xs, hc, hx => by
    obtain ⟨h1, h2⟩ := hF c x hc (hx x List.mem_cons_self)
    obtain ⟨r1, r2⟩ := run_blockwise hF _ xs h2 (fun x' hx' => hx x' (List.mem_cons_of_mem _ hx'))
    refine ⟨fun y hy => ?_, r2⟩
    simp only [run, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact h1
    · exact r1 y hy

/-- Running the groups is running their blocks. -/
theorem run_group_blocks {L Lc G : Nat} {F : StepFn} (hF : Blockwise F L Lc) :
    ∀ (c : List Byte) (gs : List (List Byte)), c.length = Lc → (∀ g ∈ gs, g.length = G * L) →
    ((run (group L G F) c gs).1.flatMap (split L G) = (run F c (gs.flatMap (split L G))).1) ∧
      (run (group L G F) c gs).2 = (run F c (gs.flatMap (split L G))).2
  | _, [], _, _ => ⟨rfl, rfl⟩
  | c, g :: gs, hc, h => by
    have hg := split_block_length (h g List.mem_cons_self)
    obtain ⟨o1, o2⟩ := run_blockwise hF c (split L G g) hc hg
    obtain ⟨h1, h2⟩ := run_group_blocks hF (run F c (split L G g)).2 gs o2
      (fun g hg => h g (List.mem_cons_of_mem _ hg))
    simp only [run, group, List.flatMap_cons, run_append]
    refine ⟨?_, h2⟩
    rw [split_flatten (by rw [run_length, split_length]) o1, h1]

theorem bytesAt_split (L G : Nat) (m : Mem) (p : Addr) :
    split L G (Spec.Aes.bytesAt m p (G * L)) = chunksAt L m p G := by
  apply List.ext_getElem (by rw [split_length, chunksAt_length])
  intro j h1 _
  have hj : j < G := by rw [split_length] at h1; exact h1
  have hjL : L * j + L ≤ G * L := by rw [← Nat.mul_succ, Nat.mul_comm G]; exact Nat.mul_le_mul_left _ hj
  simp only [split, List.getElem_map, List.getElem_range, chunksAt]
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt]; omega)
  intro t h2 _
  simp only [List.length_take, List.length_drop, Spec.Aes.bytesAt, List.length_map, List.length_range] at h2
  simp only [Spec.Aes.bytesAt, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
    BitVec.ofNat_add, BitVec.add_assoc]

theorem chunksAt_add (L : Nat) (m : Mem) (p : Addr) (a b : Nat) :
    chunksAt L m p (a + b) = chunksAt L m p a ++ chunksAt L m (p + BitVec.ofNat 64 (L * a)) b := by
  simp only [chunksAt, List.range_add, List.map_append, List.map_map, Function.comp_def, Nat.mul_add,
    BitVec.ofNat_add, BitVec.add_assoc]

/-- The data in blocks, as groups of blocks. -/
theorem chunksAt_group (L G : Nat) (m : Mem) : ∀ (p : Addr) (q : Nat),
    chunksAt L m p (G * q) = (chunksAt (G * L) m p q).flatMap (split L G)
  | _, 0 => by simp [chunksAt]
  | p, q + 1 => by
    rw [Nat.mul_succ, chunksAt_add, chunksAt_group L G m p q, chunksAt_add (G * L) m p q 1, List.flatMap_append]
    congr 1
    have h1 : ∀ p', chunksAt (G * L) m p' 1 = [Spec.Aes.bytesAt m p' (G * L)] := fun p' => by
      simp [chunksAt]
    rw [h1, List.flatMap_cons, List.flatMap_nil, List.append_nil, bytesAt_split, Nat.mul_left_comm, Nat.mul_comm L,
      Nat.mul_assoc, Nat.mul_comm q L]

theorem flatten_split (L : Nat) : ∀ (G : Nat) (x : List Byte), x.length = G * L → (split L G x).flatten = x
  | 0, x, h => by simp at h; simp [split, h]
  | G + 1, x, h => by
    have e : split L (G + 1) x = x.take L :: split L G (x.drop L) := by
      simp only [split, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero, List.drop_zero]
      congr 1
      apply List.map_congr_left; intro j _
      simp only [Function.comp, List.drop_drop, Nat.mul_succ, Nat.add_comm]
    rw [e, List.flatten_cons, flatten_split L G (x.drop L) (by rw [List.length_drop, h, Nat.succ_mul]; omega),
      List.take_append_drop]

/-- Bytes, as joined chunks. -/
theorem bytesAt_flatten (L G : Nat) (m : Mem) (p : Addr) :
    Spec.Aes.bytesAt m p (G * L) = (chunksAt L m p G).flatten := by
  rw [← bytesAt_split, flatten_split _ _ _ (by simp [Spec.Aes.bytesAt])]

/-- The operations on blocks `j < G`, each within bounds. -/
theorem flatMap_inBounds {len : Loc → Nat} {G : Nat} {ops : Nat → List Op}
    (h : ∀ j < G, ∀ o ∈ ops j, o.InBounds len) : ∀ o ∈ (List.range G).flatMap ops, o.InBounds len := by
  intro o ho
  simp only [List.mem_flatMap, List.mem_range] at ho
  obtain ⟨j, hj, ho⟩ := ho
  exact h j hj o ho

theorem blk_le {L G j : Nat} (hj : j < G) : L * j + L ≤ L * G := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj

section
variable {bw : Nat} {len : Loc → Nat}

theorem cbcDecWide_inBounds (G : Nat) (hd : 4 * bw * G ≤ len .dat) (hb : 4 * bw * G ≤ len .buf)
    (hc : 4 * bw ≤ len .chn) :
    (∀ o ∈ (Mode.cbcDecWide bw G).pre, o.InBounds len) ∧ (∀ o ∈ (Mode.cbcDecWide bw G).post, o.InBounds len) := by
  refine ⟨flatMap_inBounds fun j hj => ?_, flatMap_inBounds fun j hj => ?_⟩
  · simp only [Mode.cbcDecChained, Mode.cbcDec, copyBlk_shift, shOff]
    exact copyAt_inBounds (by have := blk_le (L := 4 * bw) hj; omega) (by have := blk_le (L := 4 * bw) hj; omega)
  · simp only [Mode.cbcDecChained, Mode.cbcDec, List.map_append, copyBlk_shift, xorBlk_shift, shOff]
    have := blk_le (L := 4 * bw) hj
    intro o ho
    simp only [List.mem_append] at ho
    rcases ho with (ho | ho) | ho
    · exact xorAt_inBounds (by omega) (by omega) (by omega) o ho
    · exact copyAt_inBounds (by omega) (by omega) o ho
    · exact copyAt_inBounds (by omega) (by omega) o ho

theorem cfbDecWide_inBounds (G : Nat) (hd : 4 * bw * G ≤ len .dat) (hb : 4 * bw * G ≤ len .buf)
    (hc : 4 * bw ≤ len .chn) :
    (∀ o ∈ (Mode.cfbDecWide bw G).pre, o.InBounds len) ∧ (∀ o ∈ (Mode.cfbDecWide bw G).post, o.InBounds len) := by
  refine ⟨flatMap_inBounds fun j hj => ?_, flatMap_inBounds fun j hj => ?_⟩
  · simp only [Mode.cfbDecEarly, List.map_append, copyBlk_shift, shOff]
    have := blk_le (L := 4 * bw) hj
    intro o ho
    simp only [List.mem_append] at ho
    rcases ho with ho | ho
    · exact copyAt_inBounds (by omega) (by omega) o ho
    · exact copyAt_inBounds (by omega) (by omega) o ho
  · simp only [Mode.cfbDecEarly, xorBlk_shift, shOff]
    have := blk_le (L := 4 * bw) hj
    exact xorAt_inBounds (by omega) (by omega) (by omega)

end

theorem cbcDecF_blockwise {L : Nat} {ciph : Cipher} (hc : ∀ b, (ciph b).length = L) :
    Blockwise (cbcDecF ciph) L L := fun c x h1 h2 => ⟨by simp [cbcDecF, xor_length, hc, h1], h2⟩

theorem cfbDecF_blockwise {L : Nat} {ciph : Cipher} (hc : ∀ b, (ciph b).length = L) :
    Blockwise (cfbDecF ciph) L L := fun c x _ h2 => ⟨by simp [cfbDecF, xor_length, hc, h2], h2⟩

end VG.Proof.Modes
