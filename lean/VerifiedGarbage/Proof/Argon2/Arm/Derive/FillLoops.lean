import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillBlock
import VerifiedGarbage.Proof.Argon2.SegmentStart
import VerifiedGarbage.Proof.Argon2.Slices
import VerifiedGarbage.Proof.Argon2.Iterations

/-!
# Argon2 on ARMv7: the filling loops

`FB s₀ st`: the body with the memory matrix holding `st`'s. `segment_ok`:
a segment, from its first index (`Proof.Argon2.segmentStart`), through
`fillBlock_ok`; `lanes_ok`, `slices_ok` and `passes_ok` the loops around
it, and `passes_ok` all passes, from the initialized memory. Each loop
counts up in the locals and runs while the count differs from its bound.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_orr wp_cmp wp_ldr op2_imm op2_reg)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.Arm (blk)
open VG.Proof.Sha512.Arm (Only)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff)

/-- The body, the memory matrix holding `st`'s. -/
structure FB (s₀ : State) (st : FillState) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  mem : Represents s.mem (memB s₀) (prm s₀).blocks st.memory

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A store to the locals keeps their other words, the cached address block and the matrix. -/
theorem loc_store {s t : State} {d : Nat} (hd : d + 4 ≤ 144) {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v) :
    (∀ e, e + 4 ≤ 256 → (e + 4 ≤ d ∨ d + 4 ≤ e) → lw s₀ t e = lw s₀ s e) ∧
    blk t.mem (scrP s₀) 6144 = blk s.mem (scrP s₀) 6144 ∧
    ∀ k < (prm s₀).blocks, blockAt t.mem (matrixCell (memB s₀) k) = blockAt s.mem (matrixCell (memB s₀) k) := by
  have f : Frame [⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)
  refine ⟨fun e he hde => ?_, ?_, fun k hk => ?_⟩
  · show t.mem.readW _ 32 = _
    rw [hm, lw_store hp (by omega) he hde.symm]
  · rw [scr_blk hp t.mem (by decide), scr_blk hp s.mem (by decide)]
    refine blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (loc_disj hp hd (scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ (by decide))
  · refine blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    exact (loc_disj hp hd (memR s₀) (by simp)).symm.sub_left (cell_in_mem hk')

/-- A store to a word of the locals other than the parameters keeps `FB`. -/
theorem FB.store {st : FillState} {s t : State} (h : FB s₀ st s) (it : Inv s₀ t) {d : Nat} (hd : d + 4 ≤ 144)
    (hd' : ∀ e ∈ [divisorOff, segLenOff, laneLenOff, strideOff], e + 4 ≤ d ∨ d + 4 ≤ e) {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v) : FB s₀ st t := by
  obtain ⟨l, _, c⟩ := loc_store hp hd hm
  exact ⟨it, Prm.of_lw h.pr fun e he => l e (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl | rfl | rfl <;> decide)
    (hd' e he), Represents.keep h.mem c⟩

omit hp in
theorem FB.of_only {st : FillState} {s t : State} {ds : List Reg} (h : FB s₀ st s) (o : Only ds s t)
    (h11 : Reg.r11 ∉ ds) : FB s₀ st t :=
  ⟨h.inv.only o h11, h.pr.of_mem o.mem, by rw [o.mem]; exact h.mem⟩

/-- `[r11, #d] += 1`, compared with `r1`, loaded by `ld`. -/
theorem advanceTail_ok {s : State} (h : Inv s₀ s) {d n : Nat} (hd : d + 4 ≤ 144)
    (hn : lw s₀ s d = BitVec.ofNat 32 n) (hn' : n + 1 < 2 ^ 32) {B : Nat} (hB : B < 2 ^ 32)
    {tail : List Instr}
    (ht : ∀ t : State, Inv s₀ t → t.mem = s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 d))
      (BitVec.ofNat 32 (n + 1)) → t.gpr .r0 = BitVec.ofNat 32 (n + 1) →
      WP isa (.block tail) t fun u => Only [.r1] t u ∧ u.z = (BitVec.ofNat 32 (n + 1) - BitVec.ofNat 32 B == 0)) :
    WP isa (.block (Impl.Argon2.Arm.Derive.ld .r0 d :: .dp .add .r0 .r0 (.imm 1) ::
      Impl.Argon2.Arm.Derive.st d .r0 :: tail)) s fun t => Inv s₀ t ∧
      t.mem = s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) (BitVec.ofNat 32 (n + 1)) ∧
      VG.Arm.eval .ne t = some (!decide (n + 1 = B)) ∧ ∀ r ∉ [Reg.r0, .r1], t.gpr r = s.gpr r := by
  refine wp_ldloc hp h (d := d) hd fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ => ?_
  have i₂ := (h.upd u₁ (by decide)).upd u₂ (by decide)
  have a₂ : s₂.gpr .r0 = BitVec.ofNat 32 (n + 1) := by
    rw [u₂.gpr, u₁.gpr, hn, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
  refine wp_stloc hp i₂ (d := d) hd fun s₃ i₃ _ _ g₃ m₃ => ?_
  have m₃' : s₃.mem = s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) (BitVec.ofNat 32 (n + 1)) := by
    rw [m₃, a₂, u₂.mem, u₁.mem]
  refine (ht s₃ i₃ m₃' (by rw [g₃, a₂])).mono fun t ⟨o, z⟩ =>
    ⟨i₃.only o (by decide), by rw [o.mem, m₃'], ?_, fun r hr => ?_⟩
  · rw [MdStream.Arm.eval_ne, z, MdStream.Arm.sub_beq hn' hB]
  · rw [o.gpr r (fun e => hr (by simp at e; simp [e])), g₃, u₂.other _ (fun e => hr (by simp [e])),
      u₁.other _ (fun e => hr (by simp [e]))]

/-- `advance d o`: `[r11, #d] += 1`, compared with `[r11, #o]`. -/
theorem advance_ok {s : State} (h : Inv s₀ s) {d n : Nat} (hd : d + 4 ≤ 144) (hn : lw s₀ s d = BitVec.ofNat 32 n)
    (hn' : n + 1 < 2 ^ 32) {o B : Nat} (ho : o < 4096) (hB : B < 2 ^ 32)
    (hin : ∀ t : State, Inv s₀ t → InRegions (t.rd ++ t.wr) (State.addr (E s₀ + BitVec.ofNat 32 o)) 4)
    (hsrc : ∀ t : State, Inv s₀ t → t.mem = s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 d))
      (BitVec.ofNat 32 (n + 1)) → lw s₀ t o = BitVec.ofNat 32 B) :
    WP isa (.block (Impl.Argon2.Arm.Derive.advance d o)) s fun t => Inv s₀ t ∧
      t.mem = s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) (BitVec.ofNat 32 (n + 1)) ∧
      VG.Arm.eval .ne t = some (!decide (n + 1 = B)) ∧ ∀ r ∉ [Reg.r0, .r1], t.gpr r = s.gpr r := by
  unfold Impl.Argon2.Arm.Derive.advance
  refine advanceTail_ok hp h hd hn hn' hB fun t it mt at' => ?_
  refine wp_ldr ho (by rw [it.r11]) (hin t it) fun t₁ u₁ => wp_cmp (op2_reg _ _) fun u f z => WP.block_nil
    ⟨((Only.of_upd u₁).trans (Only.of_fupd f)).mono (by simp), ?_⟩
  rw [z, u₁.other _ (by decide), at', u₁.gpr,
    show t.mem.readW (State.addr (E s₀ + BitVec.ofNat 32 o)) 32 = lw s₀ t o from rfl, hsrc t it mt]

end

/-- The body at a lane of the filling loops. -/
structure LS (s₀ : State) (st : FillState) (pass slice lane : Nat) (s : State) : Prop where
  fb : FB s₀ st s
  pass : lw s₀ s passOff = BitVec.ofNat 32 pass
  slice : lw s₀ s sliceOff = BitVec.ofNat 32 slice
  lane : lw s₀ s laneOff = BitVec.ofNat 32 lane

theorem FS.ls {s₀ s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) : LS s₀ st pass slice lane s :=
  ⟨⟨h.inv, h.pr, h.mem⟩, h.pos.pass, h.pos.slice, h.pos.lane⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The index advanced. -/
theorem FS.next {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t)
    (hm : t.mem = s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 indexOff)) (BitVec.ofNat 32 (index + 1))) :
    FS s₀ pass slice lane (index + 1) ctr st t := by
  obtain ⟨l, b, c⟩ := loc_store hp (d := indexOff) (by decide) hm
  refine ⟨it, Prm.of_lw h.pr fun e he => l e (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl | rfl | rfl <;> decide),
    ⟨by rw [l _ (by decide) (by decide)]; exact h.pos.pass, by rw [l _ (by decide) (by decide)]; exact h.pos.slice,
      by rw [l _ (by decide) (by decide)]; exact h.pos.lane, ?_⟩, ?_, Represents.keep h.mem c⟩
  · show t.mem.readW _ 32 = _
    rw [hm, Mem.readW_writeW_self32]
  · obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h.cache
    · exact ⟨c0, by rw [l _ (by decide) (by decide)]; exact c1, .inl c2⟩
    · exact ⟨c0, by rw [l _ (by decide) (by decide)]; exact c1, .inr ⟨c3, by rw [b]; exact c4⟩⟩

/-- `setLocal d v`. -/
theorem setLocal_ok {s : State} {st : FillState} (h : FB s₀ st s) {d : Nat} (hd : d + 4 ≤ 144)
    (hd' : ∀ e ∈ [divisorOff, segLenOff, laneLenOff, strideOff], e + 4 ≤ d ∨ d + 4 ≤ e) {v : BitVec 32}
    (hv : encodable v = true) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, FB s₀ st t → lw s₀ t d = v →
      (∀ e, e + 4 ≤ 256 → (d + 4 ≤ e ∨ e + 4 ≤ d) → lw s₀ t e = lw s₀ s e) → (∀ r ∉ [Reg.r0], t.gpr r = s.gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.setLocal d v ++ is)) s Q := by
  unfold Impl.Argon2.Arm.Derive.setLocal
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm hv) fun s₁ u₁ => ?_
  have f₁ := h.of_only (Only.of_upd u₁) (by decide)
  refine wp_stloc hp f₁.inv (d := d) hd fun t it vt ot gt mt =>
    k t (f₁.store hp it hd hd' mt) (by rw [vt, u₁.gpr]) (fun e he hde => by rw [ot e he hde, lw_mem u₁.mem])
      fun r hr => by rw [gt, u₁.other _ (fun e => hr (by simp [e]))]

/-- The block of `segmentStart`: the counter cleared, and Z in the first slice of the first pass. -/
theorem segStartBlk_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block (Impl.Argon2.Arm.Derive.setLocal counterOff 0 ++
      ([Impl.Argon2.Arm.Derive.ld .r0 passOff, Impl.Argon2.Arm.Derive.ld .r1 sliceOff, .dp .orr .r0 .r0 (.reg .r1),
        .cmp .r0 (.imm 0)] : List Instr))) s
      fun t => LS s₀ st pass slice lane t ∧ lw s₀ t counterOff = 0 ∧
        VG.Arm.eval .eq t = some (decide (pass = 0 ∧ slice = 0)) := by
  refine setLocal_ok hp h.fb (d := counterOff) (by decide) (by decide) (by decide) fun s₂ f₂ v₂ o₂ _ => ?_
  have L₂ : ∀ d ∈ [passOff, sliceOff, laneOff], lw s₀ s₂ d = lw s₀ s d := fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    exact o₂ d (by rcases hd with rfl | rfl | rfl <;> decide) (by rcases hd with rfl | rfl | rfl <;> decide)
  refine wp_ldloc hp f₂.inv (d := passOff) (by decide) fun s₃ u₃ =>
    wp_ldloc hp (f₂.inv.upd u₃ (by decide)) (d := sliceOff) (by decide) fun s₄ u₄ =>
    wp_orr (op2_reg _ _) fun s₅ u₅ => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ?_
  have o := (((Only.of_upd u₃).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans (Only.of_fupd f)
  have ft := f₂.of_only o (by decide)
  have m : t.mem = s₂.mem := o.mem
  refine ⟨⟨ft, by rw [lw_mem m, L₂ _ (by simp)]; exact h.pass, by rw [lw_mem m, L₂ _ (by simp)]; exact h.slice,
    by rw [lw_mem m, L₂ _ (by simp)]; exact h.lane⟩, by rw [lw_mem m, v₂], ?_⟩
  rw [MdStream.Arm.eval_eq, z, u₅.gpr, u₄.other _ (by decide), u₄.gpr, u₃.gpr, lw_mem u₃.mem, L₂ _ (by simp),
    L₂ _ (by simp), h.pass, h.slice, sub_zero32, or_zero hpass (by omega)]

/-- `segmentStart`: the counter cleared, and the segment's first index. -/
theorem segmentStart_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.Arm.Derive.segmentStart s
      (FS s₀ pass slice lane (Proof.Argon2.segmentStart pass slice) 0 st) := by
  unfold Impl.Argon2.Arm.Derive.segmentStart
  refine WP.seq ((segStartBlk_ok hp h hpass hs).mono fun s₄ ⟨f₄, c₄, z₄⟩ => ?_)
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) z₄ (fun hb => ?_) fun hb => ?_
  all_goals
    rw [← List.append_nil (Impl.Argon2.Arm.Derive.setLocal _ _)]
    refine setLocal_ok hp f₄.fb (d := indexOff) (by decide) (by decide) (by decide) fun t ft vt ot _ => WP.block_nil ?_
    have Lt : ∀ d ∈ [passOff, sliceOff, laneOff, counterOff], lw s₀ t d = lw s₀ s₄ d := fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      exact ot d (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
    refine ⟨ft.inv, ft.pr, ⟨by rw [Lt _ (by simp)]; exact f₄.pass, by rw [Lt _ (by simp)]; exact f₄.slice,
      by rw [Lt _ (by simp)]; exact f₄.lane, ?_⟩, ⟨by decide, by rw [Lt _ (by simp), c₄]; rfl, .inl rfl⟩, ft.mem⟩
    rw [vt, Proof.Argon2.segmentStart]
  · rw [ite_eq_left (of_decide_eq_true hb)]; rfl
  · rw [ite_eq_right (of_decide_eq_false hb)]; rfl

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
    WP isa (.block [Impl.Argon2.Arm.Derive.ld .r0 indexOff, Impl.Argon2.Arm.Derive.ld .r1 segLenOff,
      .cmp .r0 (.reg .r1)]) s
      fun t => FS s₀ pass slice lane S ctr st t ∧ VG.Arm.eval .eq t = some (decide (S = (prm s₀).segmentLen)) := by
  have sl := segLen_lt hp
  refine wp_ldloc hp h.inv (d := indexOff) (by decide) fun t₁ u₁ =>
    wp_ldloc hp (h.inv.upd u₁ (by decide)) (d := segLenOff) (by decide) fun t₂ u₂ =>
    wp_cmp (op2_reg _ _) fun t f z => WP.block_nil ?_
  refine ⟨h.of_only (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_fupd f)) (by decide), ?_⟩
  rw [MdStream.Arm.eval_eq, z, u₂.other _ (by decide), u₁.gpr, u₂.gpr, lw_mem u₁.mem, h.pr.segLen, h.pos.index,
    MdStream.Arm.sub_beq (by omega) (by omega)]

/-- One block of a segment, and the index advanced. -/
theorem segStep_ok {t : State} {pass slice lane i c : Nat} {X : FillState}
    (ht : FS s₀ pass slice lane i c X t) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : i < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i) :
    WP isa (.seq Impl.Argon2.Arm.Derive.fillBlock
      (.block (Impl.Argon2.Arm.Derive.advance indexOff segLenOff))) t
      fun v => FS s₀ pass slice lane (i + 1) (ctrNext (prm s₀) pass slice i c)
        (Spec.Argon2.fillBlock (prm s₀) pass slice lane i X) v ∧
        VG.Arm.eval .ne v = some (!decide (i + 1 = (prm s₀).segmentLen)) := by
  have sl := segLen_lt hp
  refine WP.seq ((fillBlock_ok hp ht hpass hl hs hi active).mono fun u hu => ?_)
  refine (advance_ok hp hu.inv (d := indexOff) (n := i) (by decide) hu.pos.index (by omega)
    (o := segLenOff) (B := (prm s₀).segmentLen) (by decide) (by omega)
    (fun v iv => loc_in' hp iv (d := segLenOff) (by decide)) fun v iv mv => ?_).mono
    fun v ⟨iv, mv, cv, _⟩ => ⟨hu.next hp iv mv, cv⟩
  rw [(loc_store hp (d := indexOff) (by decide) mv).1 _ (by decide) (by decide), hu.pr.segLen]

/-- `segment`: a segment of the filling loops. -/
theorem segment_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) (hl : lane < lanesN s₀) :
    WP isa Impl.Argon2.Arm.Derive.segment s
      (LS s₀ (Proof.Argon2.segment (prm s₀) pass lane slice 0 (prm s₀).segmentLen st) pass slice lane) := by
  have s2 := hp.segLen_two
  have sl := segLen_lt hp
  have hS : Proof.Argon2.segmentStart pass slice ≤ 2 := by unfold Proof.Argon2.segmentStart; split <;> omega
  have hS2 : pass = 0 → slice = 0 → Proof.Argon2.segmentStart pass slice = 2 := fun a b => by
    unfold Proof.Argon2.segmentStart; rw [ite_eq_left ⟨a, b⟩]
  generalize hSd : Proof.Argon2.segmentStart pass slice = S at hS hS2
  rw [Proof.Argon2.segment_start _ _ _ _ _ s2, hSd]
  unfold Impl.Argon2.Arm.Derive.segment
  refine WP.seq ((segmentStart_ok hp h hpass hs).mono fun t₁ h₁ => ?_)
  rw [hSd] at h₁
  refine WP.seq ((segCmp_ok hp h₁ hS).mono fun t₃ ⟨h₃, c₃⟩ => ?_)
  refine WP.ite (decide (S = (prm s₀).segmentLen)) c₃ (fun hb => ?_) fun hb => ?_
  · have hb' : S = (prm s₀).segmentLen := of_decide_eq_true hb
    refine WP.block_nil ?_
    rw [show (prm s₀).segmentLen - S = 0 by omega, Proof.Argon2.segment_zero]
    exact h₃.ls
  · have hb' : S < (prm s₀).segmentLen := by have := of_decide_eq_false hb; omega
    refine WP.loop (M := isa) (fun n t => ∃ i, n = (prm s₀).segmentLen - i ∧ S ≤ i ∧ i < (prm s₀).segmentLen ∧
      ∃ c, FS s₀ pass slice lane i c (Proof.Argon2.segment (prm s₀) pass lane slice S (i - S) st) t) ?_
      ((prm s₀).segmentLen - S) t₃ ⟨S, rfl, Nat.le_refl _, hb', 0, by rw [Nat.sub_self]; exact h₃⟩
    rintro n t ⟨i, rfl, hSi, hi, c, ht⟩
    refine (segStep_ok hp ht hpass hl hs hi (by
        by_cases a : pass = 0
        · by_cases b : slice = 0
          · have := hS2 a b; omega
          · exact .inr (.inl b)
        · exact .inl a)).mono fun v ⟨hv, cv⟩ => ?_
    have eq : Proof.Argon2.segment (prm s₀) pass lane slice S (i + 1 - S) st =
        Spec.Argon2.fillBlock (prm s₀) pass slice lane i (Proof.Argon2.segment (prm s₀) pass lane slice S (i - S) st) := by
      rw [show i + 1 - S = (i - S) + 1 by omega, segment_snoc, show S + (i - S) = i by omega]
    rw [← eq] at hv
    by_cases e : i + 1 = (prm s₀).segmentLen
    · refine .inl ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], ?_⟩
      rw [show (prm s₀).segmentLen - S = i + 1 - S by omega]
      exact hv.ls
    · exact .inr ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], _, by omega, i + 1, rfl, by omega, by omega, _, hv⟩

end

theorem foldl_range'_snoc {α : Type} (f : α → Nat → α) (start k : Nat) (x : α) :
    (List.range' start (k + 1)).foldl f x = f ((List.range' start k).foldl f x) (start + k) := by
  rw [List.range'_concat, List.foldl_append]
  simp

/-- The body at a slice of the filling loops. -/
structure SS (s₀ : State) (st : FillState) (pass slice : Nat) (s : State) : Prop where
  fb : FB s₀ st s
  pass : lw s₀ s passOff = BitVec.ofNat 32 pass
  slice : lw s₀ s sliceOff = BitVec.ofNat 32 slice

/-- The body at a pass of the filling loops. -/
structure PS (s₀ : State) (st : FillState) (pass : Nat) (s : State) : Prop where
  fb : FB s₀ st s
  pass : lw s₀ s passOff = BitVec.ofNat 32 pass

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A lane's segment of a slice, and the lane advanced. -/
theorem laneStep_ok {t : State} {pass slice l : Nat} {X : FillState} (ht : LS s₀ X pass slice l t)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) (hl : l < lanesN s₀) :
    WP isa (.seq Impl.Argon2.Arm.Derive.segment
      (.block (Impl.Argon2.Arm.Derive.advance laneOff (argOff 7)))) t fun v =>
      LS s₀ (Proof.Argon2.segment (prm s₀) pass l slice 0 (prm s₀).segmentLen X) pass slice (l + 1) v ∧
      VG.Arm.eval .ne v = some (!decide (l + 1 = lanesN s₀)) := by
  have hlt := hp.lanes_lt
  refine WP.seq ((segment_ok hp ht hpass hs hl).mono fun u hu => ?_)
  refine (advance_ok hp hu.fb.inv (d := laneOff) (n := l) (by decide) hu.lane (by omega) (o := argOff 7)
    (B := lanesN s₀) (by decide) (by omega) (fun v iv => iv.arg_in hp (by decide))
    fun v iv _ => iv.arg hp (by decide) |>.trans (by simp)).mono fun v ⟨iv, mv, cv, _⟩ => ⟨?_, cv⟩
  obtain ⟨lv, _, _⟩ := loc_store hp (d := laneOff) (by decide) mv
  refine ⟨hu.fb.store hp iv (d := laneOff) (by decide) (by decide) mv, ?_, ?_, ?_⟩
  · rw [lv _ (by decide) (by decide)]; exact hu.pass
  · rw [lv _ (by decide) (by decide)]; exact hu.slice
  · show v.mem.readW _ 32 = _
    rw [mv, Mem.readW_writeW_self32]

/-- `lanesLoop`: every lane's segment of a slice. -/
theorem lanes_ok {s : State} {pass slice : Nat} {st : FillState} (h : SS s₀ st pass slice s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.Arm.Derive.lanesLoop s
      (SS s₀ (Proof.Argon2.lanes (prm s₀) pass slice 0 (lanesN s₀) st) pass slice) := by
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.Arm.Derive.lanesLoop
  rw [← List.append_nil (Impl.Argon2.Arm.Derive.setLocal _ _)]
  refine WP.seq (setLocal_ok hp h.fb (d := laneOff) (by decide) (by decide) (by decide)
    fun t₁ f₁ v₁ o₁ _ => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧
    LS s₀ (Proof.Argon2.lanes (prm s₀) pass slice 0 l st) pass slice l t) ?_ (lanesN s₀) t₁
    ⟨0, by omega, hl1, f₁, by rw [o₁ _ (by decide) (by decide)]; exact h.pass,
      by rw [o₁ _ (by decide) (by decide)]; exact h.slice, v₁⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (laneStep_ok hp ht hpass hs hl).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Proof.Argon2.segment (prm s₀) pass l slice 0 (prm s₀).segmentLen
      (Proof.Argon2.lanes (prm s₀) pass slice 0 l st) = Proof.Argon2.lanes (prm s₀) pass slice 0 (l + 1) st from by
    unfold Proof.Argon2.lanes; rw [foldl_range'_snoc, Nat.zero_add]] at hv
  by_cases e : l + 1 = lanesN s₀
  · refine .inl ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], ?_⟩
    rw [← e]
    exact ⟨hv.fb, hv.pass, hv.slice⟩
  · exact .inr ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], _, by omega, l + 1, rfl, by omega, hv⟩

/-- A slice of a pass, and the slice advanced. -/
theorem sliceStep_ok {t : State} {pass j : Nat} {X : FillState} (ht : SS s₀ X pass j t)
    (hpass : pass < 2 ^ 32) (hj : j < 4) :
    WP isa (.seq Impl.Argon2.Arm.Derive.lanesLoop
      (.block (Impl.Argon2.Arm.Derive.advanceImm sliceOff 4))) t fun v =>
      SS s₀ (Proof.Argon2.lanes (prm s₀) pass j 0 (lanesN s₀) X) pass (j + 1) v ∧
      VG.Arm.eval .ne v = some (!decide (j + 1 = 4)) := by
  refine WP.seq ((lanes_ok hp ht hpass hj).mono fun u hu => ?_)
  unfold Impl.Argon2.Arm.Derive.advanceImm
  refine (advanceTail_ok hp hu.fb.inv (d := sliceOff) (n := j) (by decide) hu.slice (by omega) (B := 4)
    (by decide) fun t it _ _ => wp_cmp (op2_imm (by decide)) fun u f z =>
      WP.block_nil ⟨(Only.of_fupd f).mono (by simp), by rw [z, ‹t.gpr .r0 = _›]; rfl⟩).mono
    fun v ⟨iv, mv, cv, _⟩ => ⟨?_, cv⟩
  obtain ⟨lv, _, _⟩ := loc_store hp (d := sliceOff) (by decide) mv
  refine ⟨hu.fb.store hp iv (d := sliceOff) (by decide) (by decide) mv, ?_, ?_⟩
  · rw [lv _ (by decide) (by decide)]; exact hu.pass
  · show v.mem.readW _ 32 = _
    rw [mv, Mem.readW_writeW_self32]

/-- `slicesLoop`: one pass. -/
theorem slices_ok {s : State} {pass : Nat} {st : FillState} (h : PS s₀ st pass s) (hpass : pass < 2 ^ 32) :
    WP isa Impl.Argon2.Arm.Derive.slicesLoop s (PS s₀ (Spec.Argon2.fillPass (prm s₀) st pass) pass) := by
  unfold Impl.Argon2.Arm.Derive.slicesLoop
  rw [← Proof.Argon2.slices_pass, ← List.append_nil (Impl.Argon2.Arm.Derive.setLocal _ _)]
  refine WP.seq (setLocal_ok hp h.fb (d := sliceOff) (by decide) (by decide) (by decide)
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
  · refine .inl ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], ?_⟩
    rw [show (4 : Nat) = j + 1 by omega]
    exact ⟨hv.fb, hv.pass⟩
  · exact .inr ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], _, by omega, j + 1, rfl, by omega, hv⟩

/-- A pass, and the pass advanced. -/
theorem passStep_ok {t : State} {k : Nat} {X : FillState} (ht : PS s₀ X k t) (hk : k < itersN s₀) :
    WP isa (.seq Impl.Argon2.Arm.Derive.slicesLoop
      (.block (Impl.Argon2.Arm.Derive.advance passOff (argOff 5)))) t fun v =>
      PS s₀ (Spec.Argon2.fillPass (prm s₀) X k) (k + 1) v ∧
        VG.Arm.eval .ne v = some (!decide (k + 1 = itersN s₀)) := by
  have hpl : itersN s₀ < 2 ^ 32 := (arg s₀ 5).isLt
  refine WP.seq ((slices_ok hp ht (by omega)).mono fun u hu => ?_)
  refine (advance_ok hp hu.fb.inv (d := passOff) (n := k) (by decide) hu.pass (by omega) (o := argOff 5)
    (B := itersN s₀) (by decide) hpl (fun v iv => iv.arg_in hp (by decide))
    fun v iv _ => iv.arg hp (by decide) |>.trans (by simp)).mono fun v ⟨iv, mv, cv, _⟩ => ⟨?_, cv⟩
  refine ⟨hu.fb.store hp iv (d := passOff) (by decide) (by decide) mv, ?_⟩
  show v.mem.readW _ 32 = _
  rw [mv, Mem.readW_writeW_self32]

/-- `passesLoop`: every pass. -/
theorem passes_ok {s : State} {st : FillState} (h : FB s₀ st s) :
    WP isa Impl.Argon2.Arm.Derive.passesLoop s (FB s₀ (Proof.Argon2.iterations (prm s₀) 0 (itersN s₀) st)) := by
  have hp1 := hp.passes_pos
  unfold Impl.Argon2.Arm.Derive.passesLoop
  rw [← List.append_nil (Impl.Argon2.Arm.Derive.setLocal _ _)]
  refine WP.seq (setLocal_ok hp h (d := passOff) (by decide) (by decide) (by decide)
    fun t₁ f₁ v₁ _ _ => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun n t => ∃ k, n = itersN s₀ - k ∧ k < itersN s₀ ∧
    PS s₀ (Proof.Argon2.iterations (prm s₀) 0 k st) k t) ?_ (itersN s₀) t₁ ⟨0, by omega, by omega, f₁, v₁⟩
  rintro n t ⟨k, rfl, hk, ht⟩
  refine (passStep_ok hp ht hk).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Spec.Argon2.fillPass (prm s₀) (Proof.Argon2.iterations (prm s₀) 0 k st) k =
      Proof.Argon2.iterations (prm s₀) 0 (k + 1) st from by
    unfold Proof.Argon2.iterations; rw [foldl_range'_snoc, Nat.zero_add]] at hv
  by_cases e : k + 1 = itersN s₀
  · refine .inl ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], ?_⟩
    rw [← e]
    exact hv.fb
  · exact .inr ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], _, by omega, k + 1, rfl, by omega, hv⟩

end

end VG.Proof.Argon2.Arm.Derive
