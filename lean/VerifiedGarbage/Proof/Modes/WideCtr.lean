module
-- separate module: batched counter mode's target-independent part, for every target, apart from the decryptions'

public import VerifiedGarbage.Proof.Modes.Wide
public import VerifiedGarbage.Proof.Modes.CtrStep
public import VerifiedGarbage.Proof.Modes.Ctr32Step
import VerifiedGarbage.Proof.AesCtr.Ctr32

/-!
# Counter mode, a group of blocks at a time, for any target

`ctrEarly_computes`: counter mode with the counter block stepped before the
block cipher (`Mode.ctrEarlyWith o`) computes `ctrStep ciph g`, the data
block XORed with the enciphered counter block and the counter block stepped
by `g`, for an operation `o` that writes `g` of the counter block over it
(`IncOp o g`): `inc` (`incOp_ctr`), and GCM's `inc₃₂` (`incOp_ctr32`). The
steps are `ctrF` and `ctr32F` (`CtrStep.lean`, `Ctr32Step.lean`).

`ctrWide_computes`: `G` of them at a time (`Mode.widen G 16`) compute
`group 16 G (ctrStep ciph g)`. Each block's `pre` copies the counter block
`gʲ(T)` to its block of the buffer and steps it, and `post` is CFB
decryption's (`cfbDecWide_post`).
-/

@[expose] public section

namespace VG.Proof.Modes

open VG VG.Impl.Modes VG.Spec.Cbc

/-- `o` writes `g` of the 16-byte counter block over it, and nothing else. -/
def IncOp (o : Op) (g : List Byte → List Byte) : Prop :=
  ∀ a l i, o.apply a l i = if l = .chn ∧ i < 16 then (g (rd a .chn 16)).getD i 0 else a l i

/-- A step of counter mode: the data block XORed with the enciphered counter
block, and the counter block stepped by `g`. -/
def ctrStep (ciph : Cipher) (g : List Byte → List Byte) : StepFn := fun c x => (xor x (ciph c), g c)

/-- GCM's `inc₃₂` on a counter block, as `ctr32F` steps it. -/
def inc32B (c : List Byte) : List Byte := Spec.Ctr.ofNat (ctr32Val (Spec.Ctr.toNat c) 1) 16

theorem ctrF_eq (ciph : Cipher) : ctrF ciph = ctrStep ciph Spec.Ctr.inc := rfl
theorem ctr32F_eq (ciph : Cipher) : ctr32F ciph = ctrStep ciph inc32B := rfl

theorem incOp_ctr : IncOp Mode.ctrInc Spec.Ctr.inc := by
  intro a l i
  simp only [Op.apply, Op.width, Op.val, Mode.ctrInc, ite_true, Nat.zero_le, true_and, Nat.zero_add,
    Nat.sub_zero, rd]

theorem incOp_ctr32 : IncOp Mode.ctr32Inc inc32B := by
  intro a l i
  have ht : (rd a .chn 16).length = 16 := rd_length _ _ _
  have hnext := ofNat_ctr32Val_one (Spec.Ctr.toNat (rd a .chn 16))
  rw [AesCtr.ofNat_toNat ht] at hnext
  have hlo : (List.range 4).map (fun j => a .chn (12 + j)) = (rd a .chn 16).drop 12 := by
    apply List.ext_getElem (by simp [rd])
    intro j h1 _
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop, rd]
  simp only [Op.apply, Op.width, Op.val, Mode.ctr32Inc, Bool.false_eq_true, ite_true, ite_false, inc32B, hnext,
    hlo]
  by_cases hl : l = .chn
  · subst hl
    simp only [true_and]
    by_cases h12 : 12 ≤ i
    · by_cases h16 : i < 16
      · rw [ite_eq_left ⟨h12, by omega⟩, ite_eq_left h16, List.getD_eq_getElem?_getD,
          List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
        simp only [List.length_take, ht, show min 12 16 = 12 from rfl]
      · rw [ite_eq_right (fun h => h16 (by omega)), ite_eq_right h16]
    · rw [ite_eq_right (fun h => h12 h.1), ite_eq_left (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simp [ht]; omega), List.getElem?_take_of_lt (by omega),
        ← List.getD_eq_getElem?_getD, getD_rd (by omega)]
  · simp only [hl, false_and, ite_false]

/-- An operation on the chaining value alone is the same on every block. -/
theorem shift_chn {o : Op} (hd : o.dst = .chn) (hs : o.src = .chn) (hx : o.xr = none) (L st j : Nat) :
    Op.shift L st j o = o := by
  cases o; simp_all [Op.shift, shOff]

theorem repeat_succ {α : Type} (f : α → α) (k : Nat) (x : α) : Nat.repeat f (k + 1) x = f (Nat.repeat f k x) := rfl

theorem repeat_succ' {α : Type} (f : α → α) : ∀ (k : Nat) (x : α), Nat.repeat f (k + 1) x = Nat.repeat f k (f x)
  | 0, _ => rfl
  | k + 1, x => by rw [repeat_succ, repeat_succ' f k x, repeat_succ]

section
variable {o : Op} {g : List Byte → List Byte} (hg : IncOp o g) (hsh : ∀ L st j, Op.shift L st j o = o)
  (hgl : ∀ c, c.length = 16 → (g c).length = 16)

theorem iterate_length (hgl : ∀ c, c.length = 16 → (g c).length = 16) {c : List Byte} (hc : c.length = 16) :
    ∀ k, (Nat.repeat g k c).length = 16
  | 0 => hc
  | k + 1 => by rw [repeat_succ]; exact hgl _ (iterate_length hgl hc k)

/-- After the pres of the first `j` blocks, from the areas `a`: the counter
blocks `gᵏ(T)` in the buffer, `gʲ(T)` in the chaining value. -/
def ctrPre (g : List Byte → List Byte) (a : Areas) (j : Nat) : Areas
  | .dat, i => a .dat i
  | .chn, i => if i < 16 then (Nat.repeat g j (rd a .chn 16)).getD i 0 else a .chn i
  | .buf, i => if i < 16 * j then (Nat.repeat g (i / 16) (rd a .chn 16)).getD (i % 16) 0 else a .buf i

include hgl in
theorem rd_ctrPre_chn (a : Areas) (j : Nat) : rd (ctrPre g a j) .chn 16 = Nat.repeat g j (rd a .chn 16) :=
  rd_eq (iterate_length hgl (rd_length _ _ _) j) fun i hi => by simp only [ctrPre, ite_eq_left hi]

include hg hsh hgl in
theorem ctrWide_pre (a : Areas) : ∀ G l i,
    applyOps (Mode.widen G 16 (Mode.ctrEarlyWith o)).pre a l i = ctrPre g a G l i
  | 0, l, i => by
    simp only [widen_pre_zero, applyOps_nil]
    cases l
    · rfl
    · simp only [ctrPre]
      split
      · rw [show Nat.repeat g 0 (rd a .chn 16) = rd a .chn 16 from rfl, getD_rd ‹_›]
      · rfl
    · simp [ctrPre]
  | G + 1, l, i => by
    have ih : applyOps (Mode.widen G 16 (Mode.ctrEarlyWith o)).pre a = ctrPre g a G :=
      funext fun l => funext fun i => ctrWide_pre a G l i
    rw [widen_pre_succ, applyOps_append, ih]
    simp only [Mode.ctrEarlyWith, List.map_append, copyBlk_shift, shOff, List.map_cons, List.map_nil, hsh,
      applyOps_append, applyOps_cons, applyOps_nil]
    rw [hg]
    have hc : rd (applyOps (copyAt 4 .buf (16 * G) .chn 0) (ctrPre g a G)) .chn 16 = Nat.repeat g G (rd a .chn 16) := by
      rw [← rd_ctrPre_chn hgl a G]
      exact List.map_congr_left fun i _ => by
        rw [copyAt_apply (show Loc.buf ≠ .chn by decide), ite_eq_right (by simp)]
    rw [hc, copyAt_apply (show Loc.buf ≠ .chn by decide)]
    cases l
    · simp [ctrPre]
    · simp only [ctrPre, true_and, reduceCtorEq, false_and, ite_false]
      by_cases hi : i < 16
      · rw [ite_eq_left hi, ite_eq_left hi, repeat_succ]
      · simp only [hi, ite_false]
    · simp only [ctrPre, reduceCtorEq, false_and, ite_false, true_and]
      by_cases h1 : 16 * G ≤ i ∧ i < 16 * G + 16
      · rw [ite_eq_left h1, ite_eq_left (by omega), ite_eq_left (by omega),
          show i / 16 = G by omega, show i % 16 = i - 16 * G + 0 by omega]
      · rw [ite_eq_right h1]
        by_cases h2 : i < 16 * G
        · rw [ite_eq_left h2, ite_eq_left (by omega)]
        · rw [ite_eq_right h2, ite_eq_right (by omega)]

end

/-- Counter mode's steps: block `k` XORed with the enciphered `gᵏ(T)`, and
`gⁿ(T)` left. -/
theorem ctrStep_run (ciph : Cipher) (g : List Byte → List Byte) : ∀ (c : List Byte) (xs : List (List Byte)),
    (run (ctrStep ciph g) c xs).1 = (List.range xs.length).map (fun k => xor (xs.getD k []) (ciph (Nat.repeat g k c))) ∧
      (run (ctrStep ciph g) c xs).2 = Nat.repeat g xs.length c
  | _, [] => ⟨rfl, rfl⟩
  | c, x :: xs => by
    obtain ⟨h1, h2⟩ := ctrStep_run ciph g (g c) xs
    refine ⟨?_, by simp only [run, ctrStep, h2, List.length_cons, repeat_succ']⟩
    simp only [run, ctrStep, h1, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp, repeat_succ', List.getD_cons_succ]

section
variable {o : Op} {g : List Byte → List Byte} {ciph : Cipher} (hc : ∀ b, (ciph b).length = 16)
  (hg : IncOp o g) (hsh : ∀ L st j, Op.shift L st j o = o) (hgl : ∀ c, c.length = 16 → (g c).length = 16)
include hc hg

include hgl in
/-- One block a step. -/
theorem ctrEarly_computes : Computes (Mode.ctrEarlyWith o) 16 ciph (ctrStep ciph g) := by
  intro a
  have hb : rd (applyOps (Mode.ctrEarlyWith o).pre a) .buf 16 = rd a .chn 16 :=
    rd_eq (rd_length _ _ _) fun i hi => by
      simp only [Mode.ctrEarlyWith, applyOps_append, applyOps_cons, applyOps_nil]
      rw [hg, ite_eq_right (by simp), copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩, getD_rd hi]
  have hchn : rd (applyOps (Mode.ctrEarlyWith o).pre a) .chn 16 = g (rd a .chn 16) := by
    have hc' : rd (applyOps (copyBlk 4 .buf .chn) a) .chn 16 = rd a .chn 16 :=
      List.map_congr_left fun i _ => by rw [copyBlk_apply (by decide), ite_eq_right (by simp)]
    apply List.ext_getElem (by rw [rd_length, hgl _ (rd_length _ _ _)])
    intro i h1 _
    have hi : i < 16 := by simpa [rd] using h1
    rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0, getD_rd hi]
    simp only [Mode.ctrEarlyWith, applyOps_append, applyOps_cons, applyOps_nil]
    rw [hg, ite_eq_left ⟨rfl, hi⟩, hc']
  simp only [stepA, ctrStep]
  refine ⟨rd_eq (by simp [xor_length, rd_length, hc, Mode.ctrEarlyWith]) fun i hi => ?_, ?_⟩
  · simp only [Mode.ctrEarlyWith] at hi
    simp only [Mode.ctrEarlyWith]
    rw [xorBlk_apply, ite_eq_left ⟨rfl, hi⟩]
    simp only [cryptBuf, reduceCtorEq, ite_false, ite_true]
    rw [show (Mode.ctrEarlyWith o).pre = copyBlk 4 .buf .chn ++ [o] from rfl] at hb
    rw [hb, getD_xor (by rw [rd_length]; exact hi) (by rw [hc]; exact hi), getD_rd hi]
    simp only [applyOps_append, applyOps_cons, applyOps_nil]
    rw [hg, ite_eq_right (by simp), copyBlk_apply (by decide), ite_eq_right (by simp)]
  · rw [← hchn]
    exact List.map_congr_left fun i _ => by
      simp only [Mode.ctrEarlyWith]
      rw [xorBlk_apply, ite_eq_right (by simp)]
      simp only [cryptBuf, reduceCtorEq, ite_false]

include hsh hgl in
/-- `G` blocks a step. -/
theorem ctrWide_computes (G : Nat) :
    ComputesB (Mode.widen G 16 (Mode.ctrEarlyWith o)) 16 (16 * G) (blocksCipher 16 G ciph)
      (group 16 G (ctrStep ciph g)) := by
  intro a
  have hst : (Mode.widen G 16 (Mode.ctrEarlyWith o)).step = G * 16 := rfl
  rw [hst]
  have hLG : G * 16 = 16 * G := Nat.mul_comm _ _
  generalize hx : rd a .dat (G * 16) = x
  generalize hcv : rd a .chn 16 = c
  have hxl : x.length = G * 16 := by rw [← hx, rd_length]
  have hcl : c.length = 16 := by rw [← hcv, rd_length]
  have hxs := split_block_length hxl
  have hxsl := split_length 16 G x
  obtain ⟨r1, r2⟩ := ctrStep_run ciph g c (split 16 G x)
  rw [hxsl] at r1 r2
  have hpre := ctrWide_pre hg hsh hgl a G
  -- The buffer before the block cipher: the counter blocks.
  have hP : ∀ k < G, (split 16 G (rd (applyOps (Mode.widen G 16 (Mode.ctrEarlyWith o)).pre a) .buf (16 * G))).getD k [] =
      Nat.repeat g k c := fun k hk => by
    have hl1 := split_block_length (x := rd (applyOps (Mode.widen G 16 (Mode.ctrEarlyWith o)).pre a) .buf (16 * G))
      (by rw [rd_length, hLG]) _ (getD_mem (xs := split 16 G
        (rd (applyOps (Mode.widen G 16 (Mode.ctrEarlyWith o)).pre a) .buf (16 * G))) [] (by rw [split_length]; exact hk))
    apply List.ext_getElem (by rw [hl1, iterate_length hgl hcl])
    intro t h1 _
    have ht : t < 16 := by rw [hl1] at h1; exact h1
    have hkt : 16 * k + t < 16 * G := by omega
    rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0, split_getD hk ht, getD_rd hkt, hpre, ctrPre,
      ite_eq_left hkt, show (16 * k + t) / 16 = k by omega, show (16 * k + t) % 16 = t by omega, hcv]
  let b := cryptBuf (16 * G) (blocksCipher 16 G ciph) (applyOps (Mode.widen G 16 (Mode.ctrEarlyWith o)).pre a)
  have bdat : ∀ i, b .dat i = a .dat i := fun i => by
    simp only [b, cryptBuf, reduceCtorEq, ite_false, hpre, ctrPre]
  have bchn : ∀ i, b .chn i = ctrPre g a G .chn i := fun i => by
    simp only [b, cryptBuf, reduceCtorEq, ite_false, hpre]
  have hpost : stepA (Mode.widen G 16 (Mode.ctrEarlyWith o)) (16 * G) (blocksCipher 16 G ciph) a =
      cfbPost 4 b G :=
    funext fun l => funext fun i => cfbDecWide_post 4 b G l i
  rw [hpost]
  simp only [group, r1, r2]
  have hout : ∀ y ∈ (List.range G).map (fun k => xor ((split 16 G x).getD k []) (ciph (Nat.repeat g k c))),
      y.length = 16 := by
    intro y hy
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    rw [xor_length, hc, hxs _ (getD_mem _ (by rw [hxsl]; exact hk)), Nat.min_self]
  refine ⟨rd_eq ?_ fun i hi => ?_, rd_eq (iterate_length hgl hcl G) fun i hi => ?_⟩
  · rw [length_flatten_of hout, List.length_map, List.length_range]
  · have hi' : i < 16 * G := by rw [← hLG]; exact hi
    have hk : i / 16 < G := by omega
    have ht : i % 16 < 16 := Nat.mod_lt _ (by decide)
    have hdm := div_mod_eq (i := i) (L := 16)
    rw [getD_flatten hout (by rw [List.length_map, List.length_range]; exact hi'), getD_map_range _ _ hk,
      getD_xor (by rw [hxs _ (getD_mem _ (by rw [hxsl]; exact hk))]; exact ht) (by rw [hc]; exact ht),
      split_getD hk ht, hdm, ← hP _ hk]
    simp only [cfbPost, show 4 * 4 * G = 16 * G from rfl, ite_eq_left hi', bdat, b, cryptBuf, ite_true, ← hx,
      getD_rd hi]
    rw [getD_blocksCipher hc hi']
  · simp only [cfbPost, bchn, ctrPre, ite_eq_left hi, hcv]

end

/-! ## Bounds and lengths -/

theorem ctrEarly_inBounds {len : Loc → Nat} {o : Op} (ho : o.InBounds len) (hd : 16 ≤ len .dat)
    (hb : 16 ≤ len .buf) (hc : 16 ≤ len .chn) :
    (∀ o' ∈ (Mode.ctrEarlyWith o).pre, o'.InBounds len) ∧ (∀ o' ∈ (Mode.ctrEarlyWith o).post, o'.InBounds len) := by
  refine ⟨fun o' h => ?_, xorBlk_inBounds hd hd hb⟩
  simp only [Mode.ctrEarlyWith, List.mem_append, List.mem_singleton] at h
  rcases h with h | rfl
  · exact copyBlk_inBounds hb hc o' h
  · exact ho

theorem ctrWide_inBounds {len : Loc → Nat} {o : Op} (hsh : ∀ L st j, Op.shift L st j o = o)
    (ho : o.InBounds len) (G : Nat) (hd : 16 * G ≤ len .dat) (hb : 16 * G ≤ len .buf) (hc : 16 ≤ len .chn) :
    (∀ o' ∈ (Mode.widen G 16 (Mode.ctrEarlyWith o)).pre, o'.InBounds len) ∧
      (∀ o' ∈ (Mode.widen G 16 (Mode.ctrEarlyWith o)).post, o'.InBounds len) := by
  refine ⟨flatMap_inBounds fun j hj => ?_, (cfbDecWide_inBounds (bw := 4) G hd hb hc).2⟩
  simp only [Mode.ctrEarlyWith, List.map_append, copyBlk_shift, shOff, List.map_cons, List.map_nil, hsh]
  have := blk_le (L := 16) hj
  intro o' h
  simp only [List.mem_append, List.mem_singleton] at h
  rcases h with h | rfl
  · exact copyAt_inBounds (by omega) (by omega) o' h
  · exact ho

theorem ctrStep_blockwise {ciph : Cipher} (hc : ∀ b, (ciph b).length = 16) {g : List Byte → List Byte}
    (hgl : ∀ c, c.length = 16 → (g c).length = 16) : Blockwise (ctrStep ciph g) 16 16 :=
  fun c x h1 h2 => ⟨by simp [ctrStep, xor_length, hc, h2], hgl c h1⟩

theorem inc_length (c : List Byte) (_ : c.length = 16) : (Spec.Ctr.inc c).length = 16 := by
  simp [Spec.Ctr.inc, Spec.Ctr.ofNat]

theorem inc32B_length (c : List Byte) (_ : c.length = 16) : (inc32B c).length = 16 := by
  simp [inc32B, Spec.Ctr.ofNat]

end VG.Proof.Modes
