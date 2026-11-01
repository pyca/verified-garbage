module

import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillBlock
public import VerifiedGarbage.Proof.Argon2.SegmentStart
import VerifiedGarbage.Proof.Argon2.Slices
public import VerifiedGarbage.Proof.Argon2.Iterations
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillState
public import VerifiedGarbage.Proof.Argon2.Lanes
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillRef
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.MemoryInit
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Initial
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Scratch
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Locals
public import VerifiedGarbage.Proof.Argon2.Contract

/-!
# Argon2 on PPC64LE: the filling loops

`FB s₀ st`: the body with the memory matrix holding `st`'s. `segment_ok`:
a segment, from its first index (`Proof.Argon2.segmentStart`), through
`fillBlock_ok`; `lanes_ok`, `slices_ok` and `passes_ok` the loops around
it, and `passes_ok` all passes, from the initialized memory. Each loop
counts up in the frame and runs while the count differs from its bound.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd wp_addi wp_subi wp_sub wp_li)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Impl.Argon2.PPC64LE.Derive (sliceOff segLenOff indexOff laneOff passOff counterOff ld st)

/-- The body, the memory matrix holding `st`'s. -/
structure FB (s₀ : State) (st : FillState) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  mem : Represents s.mem (memP s₀) (prm s₀).blocks st.memory

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A store to the frame keeps the cached address block and the matrix. -/
theorem loc_keep {m : Mem} {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 336) (v : BitVec 64) :
    blockAt (m.writeW (E s₀ + BitVec.ofNat 64 d) v) (scrP s₀ + BitVec.ofNat 64 6144) =
      blockAt m (scrP s₀ + BitVec.ofNat 64 6144) ∧
    ∀ k < (prm s₀).blocks, blockAt (m.writeW (E s₀ + BitVec.ofNat 64 d) v) (matrixCell (memP s₀) k) =
      blockAt m (matrixCell (memP s₀) k) := by
  have f := frame_loc (s₀ := s₀) (m := m) (d := d) v
  refine ⟨blockAt_keep f fun r hr => ?_, fun k hk => blockAt_keep f fun r hr => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact (loc_disj hp h₁ h₂ (scrR s₀) (by simp)).symm.sub_left (scr_sub (by decide))
  · simp only [List.mem_singleton] at hr; subst hr
    have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    exact (loc_disj hp h₁ h₂ (memR s₀) (by simp)).symm.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk')

/-- A store to a loop variable keeps `FB`. -/
theorem FB.store {st : FillState} {s t : State} (h : FB s₀ st s) (it : Inv s₀ t) {d : Nat} (hd : 32 ≤ d)
    (hd' : d + 8 ≤ 248) {v : BitVec 64} (hm : t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) v)
    (ho : ∀ e, e + 8 ≤ 336 → (d + 8 ≤ e ∨ e + 8 ≤ d) → lw s₀ t e = lw s₀ s e) : FB s₀ st t :=
  ⟨it, Prm.of_lw h.pr fun e h₁ h₂ => ho e (by omega_arith) (.inl (by omega_arith)),
    Represents.keep h.mem fun k hk => by rw [hm]; exact (loc_keep hp hd (by omega_arith) v).2 k hk⟩

omit hp in
theorem FB.of_only {st : FillState} {s t : State} {ds : List Reg} (h : FB s₀ st s) (o : Only ds s t)
    (hd : ∀ r ∈ ds, Free r := by decide) : FB s₀ st t :=
  ⟨h.inv.only o hd, h.pr.of_mem o.mem, by rw [o.mem]; exact h.mem⟩

omit hp in
/-- `[r30 + d] += 1`, and `r4 :=` its difference with `B`, by `tail`. -/
theorem advanceTail_ok {s : State} (h : Inv s₀ s) {d n : Nat} (hd : VarOff d) (hl : LocOff d)
    (hn : lw s₀ s d = BitVec.ofNat 64 n) (hn' : n + 1 < 2 ^ 64) {B : Nat} (hB : B < 2 ^ 64)
    {tail : List Instr}
    (ht : ∀ t : State, Inv s₀ t → t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) (BitVec.ofNat 64 (n + 1)) →
      t.gpr .r3 = BitVec.ofNat 64 (n + 1) →
      WP isa (.block tail) t fun u => Only [.r4] t u ∧ u.gpr .r4 = BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 B) :
    WP isa (.block (ld .r3 d :: .addi .r3 .r3 1 :: st d .r3 :: tail)) s fun t => Inv s₀ t ∧
      t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) (BitVec.ofNat 64 (n + 1)) ∧
      (∀ e, e + 8 ≤ 336 → (d + 8 ≤ e ∨ e + 8 ≤ d) → lw s₀ t e = lw s₀ s e) ∧
      VG.PPC64LE.eval (.nonzero .d .r4) t = some (!decide (n + 1 = B)) := by
  refine wp_ldloc h (d := d) hl fun s₁ u₁ => wp_addi (by decide) fun s₂ u₂ => ?_
  have i₂ := (h.upd u₁).upd u₂
  have a₂ : s₂.gpr .r3 = BitVec.ofNat 64 (n + 1) := by rw [u₂.gpr, u₁.gpr, hn, BitVec.ofNat_add_ofNat]
  refine wp_stloc i₂ (d := d) hd fun s₃ i₃ _ o₃ g₃ m₃ => ?_
  have m₃' : s₃.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) (BitVec.ofNat 64 (n + 1)) := by
    rw [m₃, a₂, u₂.mem, u₁.mem]
  refine (ht s₃ i₃ m₃' (by rw [g₃, a₂])).mono fun t ⟨o, z⟩ =>
    ⟨i₃.only o, by rw [o.mem, m₃'], fun e he hde => by
      rw [lw_mem o.mem, o₃ e he hde, lw_mem u₂.mem, lw_mem u₁.mem], ?_⟩
  rw [MdStream.PPC64LE.eval_nonzero, z, ofNat_sub_beq hn' hB]

end

/-- The body at a lane of the filling loops. -/
structure LS (s₀ : State) (st : FillState) (pass slice lane : Nat) (s : State) : Prop where
  fb : FB s₀ st s
  pass : lw s₀ s passOff = BitVec.ofNat 64 pass
  slice : lw s₀ s sliceOff = BitVec.ofNat 64 slice
  lane : lw s₀ s laneOff = BitVec.ofNat 64 lane

theorem FS.ls {s₀ s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) : LS s₀ st pass slice lane s :=
  ⟨⟨h.inv, h.pr, h.mem⟩, h.pos.pass, h.pos.slice, h.pos.lane⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The index advanced. -/
theorem FS.next {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t)
    (hm : t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 indexOff) (BitVec.ofNat 64 (index + 1)))
    (ho : ∀ e, e + 8 ≤ 336 → (indexOff + 8 ≤ e ∨ e + 8 ≤ indexOff) → lw s₀ t e = lw s₀ s e) :
    FS s₀ pass slice lane (index + 1) ctr st t := by
  have k := loc_keep hp (m := s.mem) (d := indexOff) (by decide) (by decide) (BitVec.ofNat 64 (index + 1))
  rw [← hm] at k
  refine ⟨it, Prm.of_lw h.pr fun e h₁ h₂ => ho e (by omega_arith) (.inl (by simp only [indexOff]; omega_arith)),
    ⟨by rw [ho _ (by decide) (by decide)]; exact h.pos.pass, by rw [ho _ (by decide) (by decide)]; exact h.pos.slice,
      by rw [ho _ (by decide) (by decide)]; exact h.pos.lane, by rw [lw, hm, Mem.readW_writeW_self64]⟩, ?_,
    Represents.keep h.mem k.2⟩
  obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h.cache
  · exact ⟨c0, by rw [ho _ (by decide) (by decide)]; exact c1, .inl c2⟩
  · exact ⟨c0, by rw [ho _ (by decide) (by decide)]; exact c1, .inr ⟨c3, by rw [k.1]; exact c4⟩⟩

/-- `setLocal d v`. -/
theorem setLocal_ok {s : State} {st : FillState} (h : FB s₀ st s) {d : Nat} (hd : VarOff d) (hd₁ : 32 ≤ d)
    (hd₂ : d + 8 ≤ 248) {v : Nat} (hv : v < 2 ^ 15) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, FB s₀ st t → lw s₀ t d = BitVec.ofNat 64 v →
      (∀ e, e + 8 ≤ 336 → (d + 8 ≤ e ∨ e + 8 ≤ d) → lw s₀ t e = lw s₀ s e) →
      (∀ r ∉ [Reg.r3], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.PPC64LE.Derive.setLocal d v ++ is)) s Q := by
  unfold Impl.Argon2.PPC64LE.Derive.setLocal
  simp only [List.cons_append, List.nil_append]
  refine wp_li hv fun s₁ u₁ => ?_
  have f₁ := h.of_only (Only.of_upd u₁)
  refine wp_stloc f₁.inv (d := d) hd fun t it vt ot gt mt =>
    k t (f₁.store hp it hd₁ hd₂ mt ot) (by rw [vt, u₁.gpr]) (fun e he hde => by rw [ot e he hde, lw_mem u₁.mem])
      fun r hr => by rw [gt, u₁.other _ (fun e => hr (by simp [e]))]

/-- The block of `segmentStart`: the counter cleared, and `r3` zero in the
first slice of the first pass. -/
theorem segStartBlk_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block (Impl.Argon2.PPC64LE.Derive.setLocal counterOff 0 ++
      ([ld .r3 passOff, ld .r4 sliceOff, .logic .or .r3 .r3 .r4] : List Instr))) s
      fun t => LS s₀ st pass slice lane t ∧ lw s₀ t counterOff = BitVec.ofNat 64 0 ∧
        isa.eval (.zero .d .r3) t = some (decide (pass = 0 ∧ slice = 0)) := by
  refine setLocal_ok hp h.fb (d := counterOff) (by decide) (by decide) (by decide) (by decide)
    fun s₂ f₂ v₂ o₂ _ => ?_
  have L₂ : ∀ d ∈ [passOff, sliceOff, laneOff], lw s₀ s₂ d = lw s₀ s d := fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    exact o₂ d (by rcases hd with rfl | rfl | rfl <;> decide) (by rcases hd with rfl | rfl | rfl <;> decide)
  refine wp_ldloc f₂.inv (d := passOff) (by decide) fun s₃ u₃ =>
    wp_ldloc (f₂.inv.upd u₃) (d := sliceOff) (by decide) fun s₄ u₄ =>
    wp_or fun t u₅ => WP.block_nil ?_
  have o := ((Only.of_upd u₃).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)
  have ft := f₂.of_only o
  have m : t.mem = s₂.mem := o.mem
  refine ⟨⟨ft, by rw [lw_mem m, L₂ _ (by simp)]; exact h.pass, by rw [lw_mem m, L₂ _ (by simp)]; exact h.slice,
    by rw [lw_mem m, L₂ _ (by simp)]; exact h.lane⟩, by rw [lw_mem m, v₂], ?_⟩
  rw [show isa.eval _ t = VG.PPC64LE.eval _ t from rfl, MdStream.PPC64LE.eval_zero, u₅.gpr,
    u₄.other _ (by decide), u₄.gpr, u₃.gpr, lw_mem u₃.mem, L₂ _ (by simp), L₂ _ (by simp), h.pass, h.slice,
    or_zero (by omega_arith) (by omega_arith)]

/-- `segmentStart`: the counter cleared, and the segment's first index. -/
theorem segmentStart_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.PPC64LE.Derive.segmentStart s
      (FS s₀ pass slice lane (Proof.Argon2.segmentStart pass slice) 0 st) := by
  unfold Impl.Argon2.PPC64LE.Derive.segmentStart
  refine WP.seq ((segStartBlk_ok hp h hpass hs).mono fun s₄ ⟨f₄, c₄, z₄⟩ => ?_)
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) z₄ (fun hb => ?_) fun hb => ?_
  all_goals
    rw [← List.append_nil (Impl.Argon2.PPC64LE.Derive.setLocal _ _)]
    refine setLocal_ok hp f₄.fb (d := indexOff) (by decide) (by decide) (by decide) (by decide)
      fun t ft vt ot _ => WP.block_nil ?_
    have Lt : ∀ d ∈ [passOff, sliceOff, laneOff, counterOff], lw s₀ t d = lw s₀ s₄ d := fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      exact ot d (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
    refine ⟨ft.inv, ft.pr, ⟨by rw [Lt _ (by simp)]; exact f₄.pass, by rw [Lt _ (by simp)]; exact f₄.slice,
      by rw [Lt _ (by simp)]; exact f₄.lane, ?_⟩, ⟨by decide, by rw [Lt _ (by simp), c₄], .inl rfl⟩, ft.mem⟩
    rw [vt, Proof.Argon2.segmentStart]
  · rw [ite_eq_left (of_decide_eq_true hb)]
  · rw [ite_eq_right (of_decide_eq_false hb)]

end

theorem segment_snoc (p : Spec.Argon2.Params) (pass lane slice start k : Nat) (st : FillState) :
    Proof.Argon2.segment p pass lane slice start (k + 1) st =
      Spec.Argon2.fillBlock p pass slice lane (start + k) (Proof.Argon2.segment p pass lane slice start k st) := by
  rw [Proof.Argon2.segment_append, Proof.Argon2.segment_succ, Proof.Argon2.segment_zero]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The comparison of the segment's first index with its length. -/
theorem segCmp_ok {s : State} {pass slice lane S ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane S ctr st s) (hS : S ≤ 2) :
    WP isa (.block [ld .r3 indexOff, ld .r4 segLenOff, .sub .r4 .r3 .r4]) s
      fun t => FS s₀ pass slice lane S ctr st t ∧
        isa.eval (.zero .d .r4) t = some (decide (S = (prm s₀).segmentLen)) := by
  have sl := segLen_lt hp
  refine wp_ldloc h.inv (d := indexOff) (by decide) fun t₁ u₁ =>
    wp_ldloc (h.inv.upd u₁) (d := segLenOff) (by decide) fun t₂ u₂ =>
    wp_sub fun t u => WP.block_nil ?_
  refine ⟨h.of_only (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u)), ?_⟩
  rw [show isa.eval _ t = VG.PPC64LE.eval _ t from rfl, MdStream.PPC64LE.eval_zero, u.gpr,
    u₂.other _ (by decide), u₁.gpr, u₂.gpr, lw_mem u₁.mem, h.pr.segLen, h.pos.index,
    MdStream.PPC64LE.sub_beq (by omega_arith) (by omega_arith)]

/-- One block of a segment, and the index advanced. -/
theorem segStep_ok {t : State} {pass slice lane i c : Nat} {X : FillState}
    (ht : FS s₀ pass slice lane i c X t) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : i < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i) :
    WP isa (.seq Impl.Argon2.PPC64LE.Derive.fillBlock
      (.block (Impl.Argon2.PPC64LE.Derive.advanceBy indexOff (ld .r4 segLenOff)))) t
      fun v => FS s₀ pass slice lane (i + 1) (ctrNext (prm s₀) pass slice i c)
        (Spec.Argon2.fillBlock (prm s₀) pass slice lane i X) v ∧
        VG.PPC64LE.eval (.nonzero .d .r4) v = some (!decide (i + 1 = (prm s₀).segmentLen)) := by
  have sl := segLen_lt hp
  refine WP.seq ((fillBlock_ok hp ht hpass hl hs hi active).mono fun u hu => ?_)
  unfold Impl.Argon2.PPC64LE.Derive.advanceBy
  refine (advanceTail_ok hu.inv (d := indexOff) (n := i) (by decide) (by decide) hu.pos.index (by omega_arith)
    (B := (prm s₀).segmentLen) (by omega_arith) fun v iv mv av => ?_).mono
    fun v ⟨iv, mv, ov, cv⟩ => ⟨hu.next hp iv mv ov, cv⟩
  have sv : lw s₀ v segLenOff = BitVec.ofNat 64 (prm s₀).segmentLen := by
    rw [lw, mv, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact hu.pr.segLen
  refine wp_ldloc iv (d := segLenOff) (by decide) fun v₁ u₁ => wp_sub fun w u => WP.block_nil
    ⟨((Only.of_upd u₁).trans (Only.of_upd u)).mono (by simp), ?_⟩
  rw [u.gpr, u₁.other _ (by decide), av, u₁.gpr, sv]

/-- `segment`: a segment of the filling loops. -/
theorem segment_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) (hl : lane < lanesN s₀) :
    WP isa Impl.Argon2.PPC64LE.Derive.segment s
      (LS s₀ (Proof.Argon2.segment (prm s₀) pass lane slice 0 (prm s₀).segmentLen st) pass slice lane) := by
  have s2 := hp.segLen_two
  have sl := segLen_lt hp
  have hS : Proof.Argon2.segmentStart pass slice ≤ 2 := by unfold Proof.Argon2.segmentStart; split <;> omega_arith
  have hS2 : pass = 0 → slice = 0 → Proof.Argon2.segmentStart pass slice = 2 := fun a b => by
    unfold Proof.Argon2.segmentStart; rw [ite_eq_left ⟨a, b⟩]
  generalize hSd : Proof.Argon2.segmentStart pass slice = S at hS hS2
  rw [Proof.Argon2.segment_start _ _ _ _ _ s2, hSd]
  unfold Impl.Argon2.PPC64LE.Derive.segment
  refine WP.seq ((segmentStart_ok hp h hpass hs).mono fun t₁ h₁ => ?_)
  rw [hSd] at h₁
  refine WP.seq ((segCmp_ok hp h₁ hS).mono fun t₃ ⟨h₃, c₃⟩ => ?_)
  refine WP.ite (decide (S = (prm s₀).segmentLen)) c₃ (fun hb => ?_) fun hb => ?_
  · have hb' : S = (prm s₀).segmentLen := of_decide_eq_true hb
    refine WP.block_nil ?_
    rw [show (prm s₀).segmentLen - S = 0 by omega_arith, Proof.Argon2.segment_zero]
    exact h₃.ls
  · have hb' : S < (prm s₀).segmentLen := by have := of_decide_eq_false hb; omega_arith
    refine WP.loop (M := isa) (fun n t => ∃ i, n = (prm s₀).segmentLen - i ∧ S ≤ i ∧ i < (prm s₀).segmentLen ∧
      ∃ c, FS s₀ pass slice lane i c (Proof.Argon2.segment (prm s₀) pass lane slice S (i - S) st) t) ?_
      ((prm s₀).segmentLen - S) t₃ ⟨S, rfl, Nat.le_refl _, hb', 0, by rw [Nat.sub_self]; exact h₃⟩
    rintro n t ⟨i, rfl, hSi, hi, c, ht⟩
    refine (segStep_ok hp ht hpass hl hs hi (by
        by_cases a : pass = 0
        · by_cases b : slice = 0
          · have := hS2 a b; omega_arith
          · exact .inr (.inl b)
        · exact .inl a)).mono fun v ⟨hv, cv⟩ => ?_
    have eq : Proof.Argon2.segment (prm s₀) pass lane slice S (i + 1 - S) st =
        Spec.Argon2.fillBlock (prm s₀) pass slice lane i
          (Proof.Argon2.segment (prm s₀) pass lane slice S (i - S) st) := by
      rw [show i + 1 - S = (i - S) + 1 by omega_arith, segment_snoc, show S + (i - S) = i by omega_arith]
    rw [← eq] at hv
    by_cases e : i + 1 = (prm s₀).segmentLen
    · refine .inl ⟨cv.trans (by rw [e]; simp), ?_⟩
      rw [show (prm s₀).segmentLen - S = i + 1 - S by omega_arith]
      exact hv.ls
    · exact .inr ⟨cv.trans (by rw [decide_eq_false e]; rfl), _, by omega_arith, i + 1, rfl, by omega_arith, by omega_arith, _, hv⟩

end

theorem foldl_range'_snoc {α : Type} (f : α → Nat → α) (start k : Nat) (x : α) :
    (List.range' start (k + 1)).foldl f x = f ((List.range' start k).foldl f x) (start + k) := by
  rw [List.range'_concat, List.foldl_append]
  simp

/-- The body at a slice of the filling loops. -/
structure SS (s₀ : State) (st : FillState) (pass slice : Nat) (s : State) : Prop where
  fb : FB s₀ st s
  pass : lw s₀ s passOff = BitVec.ofNat 64 pass
  slice : lw s₀ s sliceOff = BitVec.ofNat 64 slice

/-- The body at a pass of the filling loops. -/
structure PS (s₀ : State) (st : FillState) (pass : Nat) (s : State) : Prop where
  fb : FB s₀ st s
  pass : lw s₀ s passOff = BitVec.ofNat 64 pass

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `r4 :=` the difference of `r3` with argument `i`, a `u32`. -/
theorem argTail_ok {t : State} (it : Inv s₀ t) {i : Nat} (hi : i < 18) {n : Nat}
    (at' : t.gpr .r3 = BitVec.ofNat 64 n) :
    WP isa (.block [Impl.Argon2.PPC64LE.Derive.ldw .r4 i, .sub .r4 .r3 .r4]) t fun u =>
      Only [.r4] t u ∧ u.gpr .r4 = BitVec.ofNat 64 n - BitVec.ofNat 64 (arg32 s₀ i).toNat := by
  refine wp_ldw hp it hi fun t₁ u₁ => wp_sub fun u v => WP.block_nil
    ⟨((Only.of_upd u₁).trans (Only.of_upd v)).mono (by simp), ?_⟩
  rw [v.gpr, u₁.other _ (by decide), at', u₁.gpr, ofNat_toNat (toNat_ext32 _)]

/-- A lane's segment of a slice, and the lane advanced. -/
theorem laneStep_ok {t : State} {pass slice l : Nat} {X : FillState} (ht : LS s₀ X pass slice l t)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) (hl : l < lanesN s₀) :
    WP isa (.seq Impl.Argon2.PPC64LE.Derive.segment
      (.block (Impl.Argon2.PPC64LE.Derive.advanceBy laneOff
        (Impl.Argon2.PPC64LE.Derive.ldw .r4 Impl.Argon2.PPC64LE.Derive.lanesArg)))) t fun v =>
      LS s₀ (Proof.Argon2.segment (prm s₀) pass l slice 0 (prm s₀).segmentLen X) pass slice (l + 1) v ∧
      VG.PPC64LE.eval (.nonzero .d .r4) v = some (!decide (l + 1 = lanesN s₀)) := by
  have hlt := hp.lanes_lt
  refine WP.seq ((segment_ok hp ht hpass hs hl).mono fun u hu => ?_)
  unfold Impl.Argon2.PPC64LE.Derive.advanceBy
  refine (advanceTail_ok hu.fb.inv (d := laneOff) (n := l) (by decide) (by decide) hu.lane (by omega_arith)
    (B := lanesN s₀) (by omega_arith) fun v iv _ av => argTail_ok hp iv (i := 7) (by decide) av).mono
    fun v ⟨iv, mv, ov, cv⟩ => ⟨?_, cv⟩
  refine ⟨hu.fb.store hp iv (d := laneOff) (by decide) (by decide) mv ov, ?_, ?_, ?_⟩
  · rw [ov _ (by decide) (by decide)]; exact hu.pass
  · rw [ov _ (by decide) (by decide)]; exact hu.slice
  · rw [lw, mv, Mem.readW_writeW_self64]

/-- `lanesLoop`: every lane's segment of a slice. -/
theorem lanes_ok {s : State} {pass slice : Nat} {st : FillState} (h : SS s₀ st pass slice s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.PPC64LE.Derive.lanesLoop s
      (SS s₀ (Proof.Argon2.lanes (prm s₀) pass slice 0 (lanesN s₀) st) pass slice) := by
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.PPC64LE.Derive.lanesLoop
  rw [← List.append_nil (Impl.Argon2.PPC64LE.Derive.setLocal _ _)]
  refine WP.seq (setLocal_ok hp h.fb (d := laneOff) (by decide) (by decide) (by decide) (by decide)
    fun t₁ f₁ v₁ o₁ _ => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧
    LS s₀ (Proof.Argon2.lanes (prm s₀) pass slice 0 l st) pass slice l t) ?_ (lanesN s₀) t₁
    ⟨0, by omega_arith, hl1, f₁, by rw [o₁ _ (by decide) (by decide)]; exact h.pass,
      by rw [o₁ _ (by decide) (by decide)]; exact h.slice, v₁⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (laneStep_ok hp ht hpass hs hl).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Proof.Argon2.segment (prm s₀) pass l slice 0 (prm s₀).segmentLen
      (Proof.Argon2.lanes (prm s₀) pass slice 0 l st) = Proof.Argon2.lanes (prm s₀) pass slice 0 (l + 1) st from by
    unfold Proof.Argon2.lanes; rw [foldl_range'_snoc, Nat.zero_add]] at hv
  by_cases e : l + 1 = lanesN s₀
  · refine .inl ⟨cv.trans (by rw [e]; simp), ?_⟩
    rw [← e]
    exact ⟨hv.fb, hv.pass, hv.slice⟩
  · exact .inr ⟨cv.trans (by rw [decide_eq_false e]; rfl), _, by omega_arith, l + 1, rfl, by omega_arith, hv⟩

/-- A slice of a pass, and the slice advanced. -/
theorem sliceStep_ok {t : State} {pass j : Nat} {X : FillState} (ht : SS s₀ X pass j t)
    (hpass : pass < 2 ^ 32) (hj : j < 4) :
    WP isa (.seq Impl.Argon2.PPC64LE.Derive.lanesLoop
      (.block (Impl.Argon2.PPC64LE.Derive.advanceImm sliceOff 4))) t fun v =>
      SS s₀ (Proof.Argon2.lanes (prm s₀) pass j 0 (lanesN s₀) X) pass (j + 1) v ∧
      VG.PPC64LE.eval (.nonzero .d .r4) v = some (!decide (j + 1 = 4)) := by
  refine WP.seq ((lanes_ok hp ht hpass hj).mono fun u hu => ?_)
  unfold Impl.Argon2.PPC64LE.Derive.advanceImm
  refine (advanceTail_ok hu.fb.inv (d := sliceOff) (n := j) (by decide) (by decide) hu.slice (by omega_arith)
    (B := 4) (by decide) fun t it _ at' => wp_subi (by decide) fun u v =>
      WP.block_nil ⟨Only.of_upd v, by rw [v.gpr, at']⟩).mono
    fun v ⟨iv, mv, ov, cv⟩ => ⟨?_, cv⟩
  refine ⟨hu.fb.store hp iv (d := sliceOff) (by decide) (by decide) mv ov, ?_, ?_⟩
  · rw [ov _ (by decide) (by decide)]; exact hu.pass
  · rw [lw, mv, Mem.readW_writeW_self64]

/-- `slicesLoop`: one pass. -/
theorem slices_ok {s : State} {pass : Nat} {st : FillState} (h : PS s₀ st pass s) (hpass : pass < 2 ^ 32) :
    WP isa Impl.Argon2.PPC64LE.Derive.slicesLoop s (PS s₀ (Spec.Argon2.fillPass (prm s₀) st pass) pass) := by
  unfold Impl.Argon2.PPC64LE.Derive.slicesLoop
  rw [← Proof.Argon2.slices_pass, ← List.append_nil (Impl.Argon2.PPC64LE.Derive.setLocal _ _)]
  refine WP.seq (setLocal_ok hp h.fb (d := sliceOff) (by decide) (by decide) (by decide) (by decide)
    fun t₁ f₁ v₁ o₁ _ => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun n t => ∃ j, n = 4 - j ∧ j < 4 ∧
    SS s₀ (Proof.Argon2.slices (prm s₀) pass 0 j st) pass j t) ?_ 4 t₁
    ⟨0, rfl, by decide, f₁, by rw [o₁ _ (by decide) (by decide)]; exact h.pass, v₁⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine (sliceStep_ok hp ht hpass hj).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Proof.Argon2.lanes (prm s₀) pass j 0 (lanesN s₀) (Proof.Argon2.slices (prm s₀) pass 0 j st) =
      Proof.Argon2.slices (prm s₀) pass 0 (j + 1) st from by
    unfold Proof.Argon2.slices; rw [foldl_range'_snoc, Nat.zero_add]; rfl] at hv
  by_cases e : j + 1 = 4
  · refine .inl ⟨cv.trans (by rw [e]; simp), ?_⟩
    rw [show (4 : Nat) = j + 1 by omega_arith]
    exact ⟨hv.fb, hv.pass⟩
  · exact .inr ⟨cv.trans (by rw [decide_eq_false e]; rfl), _, by omega_arith, j + 1, rfl, by omega_arith, hv⟩

/-- A pass, and the pass advanced. -/
theorem passStep_ok {t : State} {k : Nat} {X : FillState} (ht : PS s₀ X k t) (hk : k < itersN s₀) :
    WP isa (.seq Impl.Argon2.PPC64LE.Derive.slicesLoop
      (.block (Impl.Argon2.PPC64LE.Derive.advanceBy passOff
        (Impl.Argon2.PPC64LE.Derive.ldw .r4 Impl.Argon2.PPC64LE.Derive.iterationsArg)))) t fun v =>
      PS s₀ (Spec.Argon2.fillPass (prm s₀) X k) (k + 1) v ∧
        VG.PPC64LE.eval (.nonzero .d .r4) v = some (!decide (k + 1 = itersN s₀)) := by
  have hpl : itersN s₀ < 2 ^ 32 := (arg32 s₀ 5).isLt
  refine WP.seq ((slices_ok hp ht (by omega_arith)).mono fun u hu => ?_)
  unfold Impl.Argon2.PPC64LE.Derive.advanceBy
  refine (advanceTail_ok hu.fb.inv (d := passOff) (n := k) (by decide) (by decide) hu.pass (by omega_arith)
    (B := itersN s₀) (by omega_arith) fun v iv _ av => argTail_ok hp iv (i := 5) (by decide) av).mono
    fun v ⟨iv, mv, ov, cv⟩ => ⟨?_, cv⟩
  refine ⟨hu.fb.store hp iv (d := passOff) (by decide) (by decide) mv ov, ?_⟩
  rw [lw, mv, Mem.readW_writeW_self64]

/-- `passesLoop`: every pass. -/
theorem passes_ok {s : State} {st : FillState} (h : FB s₀ st s) :
    WP isa Impl.Argon2.PPC64LE.Derive.passesLoop s (FB s₀ (Proof.Argon2.iterations (prm s₀) 0 (itersN s₀) st)) := by
  have hp1 := hp.passes_pos
  unfold Impl.Argon2.PPC64LE.Derive.passesLoop
  rw [← List.append_nil (Impl.Argon2.PPC64LE.Derive.setLocal _ _)]
  refine WP.seq (setLocal_ok hp h (d := passOff) (by decide) (by decide) (by decide) (by decide)
    fun t₁ f₁ v₁ _ _ => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun n t => ∃ k, n = itersN s₀ - k ∧ k < itersN s₀ ∧
    PS s₀ (Proof.Argon2.iterations (prm s₀) 0 k st) k t) ?_ (itersN s₀) t₁ ⟨0, by omega_arith, by omega_arith, f₁, v₁⟩
  rintro n t ⟨k, rfl, hk, ht⟩
  refine (passStep_ok hp ht hk).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Spec.Argon2.fillPass (prm s₀) (Proof.Argon2.iterations (prm s₀) 0 k st) k =
      Proof.Argon2.iterations (prm s₀) 0 (k + 1) st from by
    unfold Proof.Argon2.iterations; rw [foldl_range'_snoc, Nat.zero_add]] at hv
  by_cases e : k + 1 = itersN s₀
  · refine .inl ⟨cv.trans (by rw [e]; simp), ?_⟩
    rw [← e]
    exact hv.fb
  · exact .inr ⟨cv.trans (by rw [decide_eq_false e]; rfl), _, by omega_arith, k + 1, rfl, by omega_arith, hv⟩

end

end VG.Proof.Argon2.PPC64LE.Derive
