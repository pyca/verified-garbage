import VerifiedGarbage.Proof.AesCbc.AArch64.Block

/-!
# AES-CBC on AArch64: the loop, for any mode on whole blocks

The invariant after `k` blocks (`LInv`): the registers hold the arguments
(`x22` the next block, `x23` the blocks left), the other callee-saved
registers and the stack pointer are unchanged, only the chaining value, the
data and the first 2064 bytes of the scratch buffer have changed since the
registers were saved, the first `k` blocks are the mode's (`Mode.out`) of
the first `k` blocks on entry and the rest are unchanged, and the chaining
value is the mode's after them (`Mode.chain`). CBC is `cbcMode`; other
modes' functions with the same arguments reuse the loop.

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
blocks (`BodyOk`), `whole body` meets the contract.
-/

namespace VG.Proof.AesCbc.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCbc.AArch64
open VG.Spec.Aes (bytesAt)

section
variable (s₀ : State)

abbrev W : Addr := s₀.gpr .x0
abbrev R : Nat := (s₀.gpr .x1).toNat
abbrev Iv : Addr := s₀.gpr .x2
abbrev Dp : Addr := s₀.gpr .x3
abbrev N : Nat := (s₀.gpr .x4).toNat
abbrev S : Addr := s₀.gpr .x5

abbrev schR : Region := ⟨W s₀, 240⟩
abbrev ivR : Region := ⟨Iv s₀, 16⟩
abbrev dataR : Region := ⟨Dp s₀, 16 * N s₀⟩
abbrev scrR : Region := ⟨S s₀, 2176⟩

/-- The cipher of the direction. -/
abbrev ciph (enc : Bool) : Spec.Cbc.Cipher :=
  ciphOf enc (R s₀) (bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)))

/-- The blocks on entry. -/
abbrev blks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀)

/-- The chaining value on entry. -/
abbrev iv0 : List Byte := bytesAt s₀.mem (Iv s₀) 16

/-- The address of block `k`. -/
abbrev blk (k : Nat) : Addr := Dp s₀ + BitVec.ofNat 64 (16 * k)

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀]
  wr : s₀.wr = [ivR s₀, dataR s₀, scrR s₀]
  sch_iv : (schR s₀).Disjoint (ivR s₀)
  sch_data : (schR s₀).Disjoint (dataR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  iv_data : (ivR s₀).Disjoint (dataR s₀)
  iv_scr : (ivR s₀).Disjoint (scrR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  iv_wrap : (Iv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {M : Mode} {s₀ : State} (h : (modeAArch64 M).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩

/-- The key schedule as the mode uses it. -/
abbrev wK (s₀ : State) : List Byte := bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1))

/-- The first `k` blocks after the mode. -/
abbrev outK (M : Mode) (s₀ : State) (k : Nat) : List (List Byte) :=
  M.out (R s₀) (wK s₀) (iv0 s₀) ((blks s₀).take k)

/-- The chaining value after the first `k` blocks. -/
abbrev chainK (M : Mode) (s₀ : State) (k : Nat) : List Byte :=
  M.chain (R s₀) (wK s₀) (iv0 s₀) ((blks s₀).take k)

/-- The loop invariant, after `k` blocks. -/
structure LInv (M : Mode) (s₀ : State) (k : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W s₀
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = Iv s₀
  x22 : s.gpr .x22 = blk s₀ k
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)
  x24 : s.gpr .x24 = S s₀
  other : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 →
    r ≠ .x30 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) s.mem
  data : Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) = outK M s₀ k ++ (blks s₀).drop k
  iv : bytesAt s.mem (Iv s₀) 16 = chainK M s₀ k

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < N s₀) : Region.Sub ⟨blk s₀ k, 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem UPre.blk_disjoint (hp : UPre s₀) {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨blk s₀ j, 16⟩ : Region).Disjoint ⟨blk s₀ k, 16⟩ := by
  have := hp.data_wrap
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

end

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

/-- The regions the function writes. -/
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m := by
  have f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)

/-- The blocks after a step that changed only block `k`, the chaining
value and the first 2064 bytes of the scratch buffer. -/
theorem UPre.blocksAt_step {m m' : Mem} {k : Nat} (hk : k < N s₀)
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩] m m') :
    Spec.Cbc.blocksAt m' (Dp s₀) (N s₀) =
      (Spec.Cbc.blocksAt m (Dp s₀) (N s₀)).set k (bytesAt m' (blk s₀ k) 16) := by
  refine blocksAt_set fun j hj hjk => Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.blk_disjoint hj hk hjk
  · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Region.sub_prefix (by decide))

omit hp in
/-- Block `k` before the step, from the invariant. -/
theorem LInv.block {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) (hk : k < N s₀) :
    bytesAt s.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
  have hl : (outK M s₀ k).length = k := by
    rw [outK, M.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_eq_getElem (show k < (Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀)).length by
      rw [length_blocksAt]; exact hk),
    List.getElem?_append_right (show (outK M s₀ k).length ≤ k by omega), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero,
    List.getElem?_eq_getElem (show k < (blks s₀).length by simp [Spec.Cbc.blocksAt]; exact hk)] at this
  show bytesAt s.mem (Dp s₀ + BitVec.ofNat 64 (16 * k)) 16 = _
  rw [← getElem_blocksAt _ _ hk]
  exact Option.some.inj this

end

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) = (blks s₀).take k ++ [(blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cbc.blocksAt]; exact hk)]
  rfl

theorem x1_ofNat (s₀ : State) : s₀.gpr .x1 = BitVec.ofNat 64 (R s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [R]

theorem x4_ofNat (s₀ : State) : s₀.gpr .x4 = BitVec.ofNat 64 (N s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [N]

theorem ofNat_ne_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x != 0) = !decide (x = 0) := by
  have : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
      simpa using this
    · intro he; rw [he]; rfl
  rw [bne, this]

theorem eval_x23 {s : State} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr .x23 = BitVec.ofNat 64 x) :
    isa.eval (.nonzero .x .x23) s = some !decide (x = 0) := by
  show some (s.read .x .x23 != 0) = _
  rw [State.read, h, BitVec.setWidth_eq, ofNat_ne_zero hx]

theorem eval_zero_x23 {s : State} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr .x23 = BitVec.ofNat 64 x) :
    isa.eval (.zero .x .x23) s = some (decide (x = 0)) := by
  show some (s.read .x .x23 == 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  have := ofNat_ne_zero hx
  rw [bne] at this
  cases hb : (BitVec.ofNat 64 x == 0) <;> rw [hb] at this <;> cases hd : decide (x = 0) <;> simp_all

/-- What `advance` leaves after block `k`: the registers of block `k + 1`. -/
theorem advance_regs {s₀ : State} {k : Nat} (hk : k < N s₀) {s : State}
    (h22 : s.gpr .x22 = blk s₀ k) (h23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)) :
    ∃ s', runBlock isa advance s = some s' ∧ s'.gpr .x22 = blk s₀ (k + 1) ∧
      s'.gpr .x23 = BitVec.ofNat 64 (N s₀ - (k + 1)) ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', run, x22', x23', keep, sp', mem', rd', wr'⟩ := advance_ok s
  have hN := (s₀.gpr .x4).isLt
  have dec : BitVec.ofNat 64 (N s₀ - k) - 1 = BitVec.ofNat 64 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  refine ⟨s', run, ?_, ?_, keep, sp', mem', rd', wr'⟩
  · rw [x22', h22, Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega)]
  · rw [x23', h23, dec]

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` blocks to `k + 1`. -/
def BodyOk (M : Mode) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv M s₀ k s →
    WP isa body s (LInv M s₀ (k + 1))

theorem loop_ok {M : Mode} {body : Prog isa} (hb : BodyOk M body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv M s₀ k s) :
    WP isa (.loop body (.nonzero .x .x23)) s (LInv M s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .nonzero .x .x23) (Q := LInv M s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv M s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' h' => ?_
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have ev := eval_x23 (x := N s₀ - (k + 1)) (by omega) h'.x23
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## Saving and restoring the registers -/

theorem prologue_wp {M : Mode} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ (LInv M s₀ 0) := by
  obtain ⟨s₁, run₁, x19₁, x20₁, x21₁, x22₁, x23₁, x24₁, keep₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    prologue_ok s₀ fun d _ h₂ => by
      rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  have f₀ := savedMem_frame s₀
  have disj : ∀ (r : Region), r ∈ [ivR s₀, dataR s₀] → ∀ r' ∈ [⟨s₀.gpr .x5 + BitVec.ofNat 64 2064, 56⟩],
      r.Disjoint r' := by
    intro r hr r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
    subst hr'
    rcases hr with rfl | rfl
    · exact hp.iv_scr.sub_right (UPre.scr_sub (by decide))
    · exact hp.data_scr.sub_right (UPre.scr_sub (by decide))
  have ivS : bytesAt (savedMem s₀) (Iv s₀) 16 = iv0 s₀ :=
    Proof.Cmac.bytesAt_frame f₀ (disj _ (by simp)) (by decide)
  have dataS : Spec.Cbc.blocksAt (savedMem s₀) (Dp s₀) (N s₀) = blks s₀ := by
    simp only [Spec.Cbc.blocksAt]
    refine List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame f₀ (fun r hr => ?_) (by decide)
    have := List.mem_range.mp hj
    exact (disj _ (by simp) r hr).sub_left (UPre.data_sub this)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  exact { x19 := x19₁, x20 := x20₁, x21 := x21₁
          x22 := by rw [x22₁]; simp
          x23 := by rw [x23₁, x4_ofNat]; rfl
          x24 := x24₁
          other := fun r _ h19 h20 h21 h22 h23 h24 _ => keep₁ r h19 h20 h21 h22 h23 h24
          sp := sp₁, rd := rd₁, wr := wr₁
          frame := by rw [mem₁]; exact Frame.refl _ _
          data := by
            rw [mem₁, dataS]
            rw [outK, List.take_zero, M.out_nil, List.drop_zero, List.nil_append]
          iv := by
            rw [mem₁, ivS]
            rw [chainK, List.take_zero, M.chain_nil] }

theorem mid_wp {M : Mode} {body : Prog isa} (hb : BodyOk M body) {s₀ : State} (hp : UPre s₀) {s₁ : State}
    (h : LInv M s₀ 0 s₁) :
    WP isa (.ite (.zero .x .x23) (.block []) (.loop body (.nonzero .x .x23))) s₁ (LInv M s₀ (N s₀)) := by
  have hN := (s₀.gpr .x4).isLt
  have ev := eval_zero_x23 (x := N s₀) hN (by rw [h.x23]; rfl)
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hb hp (by omega) h

theorem slots_disj {s₀ : State} (hp : UPre s₀) :
    ∀ r ∈ [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩], (⟨S s₀ + BitVec.ofNat 64 2064, 56⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] (savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d)
    (h₂ : d + 8 ≤ 2120) :
    m.readW (S s₀ + BitVec.ofNat 64 d) 64 = (savedMem s₀).readW (S s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 2064, 56⟩) (slot_contains _ h₁ h₂) (slots_disj hp) (by decide)

theorem epilogue_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv M s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => GprAbi s₀ s' ∧ (modeAArch64 M).post s₀ s' := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  obtain ⟨s₃, run₃, slot₃, keep₃, sp₃, mem₃⟩ :=
    restore_ok s₂ h₂.x24 fun d _ h₂' => by
      rw [rdwr, hp.rd, hp.wr]
      exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by have := hp.scr_wrap; omega))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have sl {r : Reg} {d : Nat} (h : (r, d) ∈ saved) : s₃.gpr r = s₀.gpr r := by
    have hd : 2064 ≤ d ∧ d + 8 ≤ 2120 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      omega
    rw [slot₃ r d h, slot_read hp h₂.frame hd.1 hd.2, savedMem_slot s₀ h]
  have hall : (blks s₀).take (N s₀) = blks s₀ := List.take_of_length_le (by simp [Spec.Cbc.blocksAt])
  have hnil : (blks s₀).drop (N s₀) = [] := List.drop_of_length_le (by simp [Spec.Cbc.blocksAt])
  refine ⟨⟨fun r hr => ?_, by rw [sp₃, h₂.sp]⟩, ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sl (d := 2064) (by simp [saved])
    · exact sl (d := 2072) (by simp [saved])
    · exact sl (d := 2080) (by simp [saved])
    · exact sl (d := 2088) (by simp [saved])
    · exact sl (d := 2096) (by simp [saved])
    · exact sl (d := 2112) (by simp [saved])
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · rw [keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact h₂.other _ (by simp [preserved]) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · exact sl (d := 2104) (by simp [saved])
  · show Spec.Cbc.blocksAt s₃.mem (Dp s₀) (N s₀) = _
    rw [mem₃, h₂.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₃.mem (Iv s₀) 16 = _
    rw [mem₃, h₂.iv]; simp only [chainK, hall]

theorem whole_wp {M : Mode} {body : Prog isa} (hb : BodyOk M body) {s₀ : State}
    (h0 : (modeAArch64 M).pre s₀) :
    WP isa (whole body) s₀ fun s' => GprAbi s₀ s' ∧ (modeAArch64 M).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ h₁ =>
    WP.seq (WP.mono (mid_wp hb hp h₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.AesCbc.AArch64
