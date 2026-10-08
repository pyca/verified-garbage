import VerifiedGarbage.Proof.AesCbc.X86_64.Block

/-!
# AES-CBC on x86-64: the loop, for either direction

The invariant after `k` blocks (`LInv`): the registers hold the arguments
(`r13` the next block, `r14` the blocks left), only the chaining value, the
data, the first 2064 bytes of the scratch buffer and the stack below the
return address have changed since the registers were saved, the first `k`
blocks are CBC of the first `k` blocks on entry and the rest are unchanged,
and the chaining value is the one to continue from after the first `k`.

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
blocks and sets ZF when none are left (`BodyOk`), `whole body` meets the
contract.
-/

namespace VG.Proof.AesCbc.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCbc.X86_64
open VG.Spec.Aes (bytesAt)

section
variable (s₀ : State)

abbrev W : Addr := s₀.gpr .rdi
abbrev R : Nat := (s₀.gpr .rsi).toNat
abbrev Iv : Addr := s₀.gpr .rdx
abbrev Dp : Addr := s₀.gpr .rcx
abbrev N : Nat := (s₀.gpr .r8).toNat
abbrev S : Addr := s₀.gpr .r9

abbrev schR : Region := ⟨W s₀, 240⟩
abbrev ivR : Region := ⟨Iv s₀, 16⟩
abbrev dataR : Region := ⟨Dp s₀, 16 * N s₀⟩
abbrev scrR : Region := ⟨S s₀, 2176⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 8

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
  ret_iv : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (ivR s₀)
  ret_data : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (dataR s₀)
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (scrR s₀)
  stk_sch : (stkR s₀).Disjoint (schR s₀)
  stk_iv : (stkR s₀).Disjoint (ivR s₀)
  stk_data : (stkR s₀).Disjoint (dataR s₀)
  stk_scr : (stkR s₀).Disjoint (scrR s₀)
  iv_wrap : (Iv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {enc : Bool} {s₀ : State} (h : (cbcX86_64 enc).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t⟩

/-- The memory after saving the registers. -/
abbrev savedMem (s : State) : Mem := Spill.saveMem s.mem (s.gpr .r9) s.gpr saved

/-- CBC of the first `k` blocks. -/
abbrev outK (enc : Bool) (s₀ : State) (k : Nat) : List (List Byte) :=
  cbc enc (ciph s₀ enc) (iv0 s₀) ((blks s₀).take k)

/-- The loop invariant, after `k` blocks. -/
structure LInv (enc : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = W s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = Iv s₀
  r13 : s.gpr .r13 = blk s₀ k
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  r15 : s.gpr .r15 = S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  data : Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) = outK enc s₀ k ++ (blks s₀).drop k
  iv : bytesAt s.mem (Iv s₀) 16 = Spec.Cbc.next (iv0 s₀) (cts enc ((blks s₀).take k) (outK enc s₀ k))

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

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 2064 ≤ d) (h₂ : d + 8 ≤ 2112) :
    (⟨b + BitVec.ofNat 64 2064, 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 2064) + BitVec.ofNat 64 (d - 2064) from
    (Offset.add_add_eq b (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

theorem saved_bound : ∀ p ∈ saved, 2064 ≤ p.2 ∧ p.2 + 8 ≤ 2112 := by decide

/-- Saving the registers changes only their slots. -/
theorem savedMem_frame (s : State) : Frame [⟨s.gpr .r9 + BitVec.ofNat 64 2064, 48⟩] s.mem (savedMem s) :=
  Spill.saveMem_frame _ _ _ _ fun p hp => slot_contains _ (saved_bound p hp).1 (saved_bound p hp).2

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

/-- The regions the function writes. -/
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀, stkR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hR)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m := by
  have f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

/-- The blocks after a step that changed only block `k`, the chaining
value, the first 2064 bytes of the scratch buffer and the stack. -/
theorem UPre.blocksAt_step {m m' : Mem} {k : Nat} (hk : k < N s₀)
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] m m') :
    Spec.Cbc.blocksAt m' (Dp s₀) (N s₀) =
      (Spec.Cbc.blocksAt m (Dp s₀) (N s₀)).set k (bytesAt m' (blk s₀ k) 16) := by
  refine blocksAt_set fun j hj hjk => bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.blk_disjoint hj hk hjk
  · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Region.sub_prefix (by decide))
  · exact hp.stk_data.symm.sub_left (UPre.data_sub hj)

omit hp in
/-- Block `k` before the step, from the invariant. -/
theorem LInv.block {enc : Bool} {k : Nat} {s : State} (h : LInv enc s₀ k s) (hk : k < N s₀) :
    bytesAt s.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
  have hl : (outK enc s₀ k).length = k := by
    cases enc <;> simp [cbc, length_encrypt, length_decrypt, Spec.Cbc.blocksAt] <;> omega
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_eq_getElem (show k < (Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀)).length by
      rw [length_blocksAt]; exact hk),
    List.getElem?_append_right (show (outK enc s₀ k).length ≤ k by omega), hl, Nat.sub_self,
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

theorem rsi_ofNat (s₀ : State) : s₀.gpr .rsi = BitVec.ofNat 64 (R s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [R]

theorem r8_ofNat (s₀ : State) : s₀.gpr .r8 = BitVec.ofNat 64 (N s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [N]

theorem beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
    simpa using this
  · intro he; rw [he]; rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa advance s = some s' ∧
      s'.gpr .r13 = s.gpr .r13 + BitVec.ofNat 64 16 ∧ s'.gpr .r14 = s.gpr .r14 - 1 ∧
      s'.zf = some ((s.gpr .r14 - 1) == 0) ∧ (∀ r, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, advance, runBlock_cons,
      runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · exact gpr_setReg_self _ _ _
  · rw [zf_setReg, zf_arithFlags]; simp
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

/-- What `advance` leaves after block `k`: the registers of block `k + 1`,
and ZF set if it was the last. -/
theorem advance_regs {s₀ : State} {k : Nat} (hk : k < N s₀) {s : State}
    (h13 : s.gpr .r13 = blk s₀ k) (h14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)) :
    ∃ s', runBlock isa advance s = some s' ∧ s'.gpr .r13 = blk s₀ (k + 1) ∧
      s'.gpr .r14 = BitVec.ofNat 64 (N s₀ - (k + 1)) ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)) ∧
      (∀ r, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', run, r13', r14', zf', keep, mem', rd', wr'⟩ := advance_ok s
  have hN := (s₀.gpr .r8).isLt
  have dec : BitVec.ofNat 64 (N s₀ - k) - 1 = BitVec.ofNat 64 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  refine ⟨s', run, ?_, ?_, ?_, keep, mem', rd', wr'⟩
  · rw [r13', h13, Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega)]
  · rw [r14', h14, dec]
  · rw [zf', h14, dec, beq_zero (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN)]

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` blocks to `k + 1`, and sets
ZF if no blocks are left. -/
def BodyOk (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
    WP isa body s fun s' => LInv enc s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0))

theorem loop_ok {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv enc s₀ k s) : WP isa (.loop body .ne) s (LInv enc s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := LInv enc s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv enc s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' ⟨h', zf'⟩ => ?_
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by simp [eval, zf', hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by simp [eval, zf', hz], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## Saving and restoring the registers -/

theorem prologue_ok (s : State)
    (hw : ∀ d, 2064 ≤ d → d + 8 ≤ 2112 → InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (save ++ setup) s = some s' ∧
      s'.gpr .rbx = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rsi ∧ s'.gpr .r12 = s.gpr .rdx ∧
      s'.gpr .r13 = s.gpr .rcx ∧ s'.gpr .r14 = s.gpr .r8 ∧ s'.gpr .r15 = s.gpr .r9 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.zf = some (s.gpr .r8 == 0) ∧
      s'.mem = savedMem s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [save, setup, saved, List.map, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, at_, exec, readSrc, State.store64, State.ea, offset_nat,
      hw 2064 (by decide) (by decide), hw 2072 (by decide) (by decide), hw 2080 (by decide) (by decide),
      hw 2088 (by decide) (by decide), hw 2096 (by decide) (by decide), hw 2104 (by decide) (by decide),
      ite_true, Option.map_some, execAlu, Option.bind_some]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, BitVec.and_self]
  trivial

theorem prologue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s₁ => LInv enc s₀ 0 s₁ ∧ s₁.zf = some (decide (N s₀ = 0)) := by
  have hN := (s₀.gpr .r8).isLt
  obtain ⟨s₁, run₁, rbx₁, rbp₁, r12₁, r13₁, r14₁, r15₁, rsp₁, zf₁, mem₁, rd₁, wr₁⟩ :=
    prologue_ok s₀ fun d _ h₂ => by
      rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  have f₀ := savedMem_frame s₀
  have disj : ∀ (r : Region), r ∈ [ivR s₀, dataR s₀] → ∀ r' ∈ [⟨s₀.gpr .r9 + BitVec.ofNat 64 2064, 48⟩],
      r.Disjoint r' := by
    intro r hr r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
    subst hr'
    rcases hr with rfl | rfl
    · exact hp.iv_scr.sub_right (UPre.scr_sub (by decide))
    · exact hp.data_scr.sub_right (UPre.scr_sub (by decide))
  have ivS : bytesAt (savedMem s₀) (Iv s₀) 16 = iv0 s₀ :=
    bytesAt_frame f₀ (disj _ (by simp)) (by decide)
  have dataS : Spec.Cbc.blocksAt (savedMem s₀) (Dp s₀) (N s₀) = blks s₀ := by
    simp only [Spec.Cbc.blocksAt]
    refine List.map_congr_left fun j hj => bytesAt_frame f₀ (fun r hr => ?_) (by decide)
    have := List.mem_range.mp hj
    exact (disj _ (by simp) r hr).sub_left (UPre.data_sub this)
  refine WP.of_runBlock ⟨s₁, run₁, ?_, ?_⟩
  · exact { rbx := rbx₁, rbp := rbp₁, r12 := r12₁
            r13 := by rw [r13₁]; simp
            r14 := by rw [r14₁, r8_ofNat]; rfl
            r15 := r15₁, rsp := rsp₁, rd := rd₁, wr := wr₁
            frame := by rw [mem₁]; exact Frame.refl _ _
            data := by
              rw [mem₁, dataS]
              cases enc <;> simp [cbc, Spec.Cbc.encrypt, Spec.Cbc.decrypt]
            iv := by
              rw [mem₁, ivS]
              cases enc <;> simp [cbc, cts, Spec.Cbc.encrypt, Spec.Cbc.next] }
  · rw [zf₁, r8_ofNat, beq_zero hN]

theorem mid_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {s₁ : State}
    (h : LInv enc s₀ 0 s₁) (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop body .ne)) s₁ (LInv enc s₀ (N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := hz
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hb hp (by omega) h

theorem slots_disj {s₀ : State} (hp : UPre s₀) :
    ∀ r ∈ [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀], (⟨S s₀ + BitVec.ofNat 64 2064, 48⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))
  · exact Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)
  · exact hp.stk_scr.symm.sub_left (UPre.scr_sub (by decide))

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] (savedMem s₀) m) {d : Nat} (h₁ : 2064 ≤ d)
    (h₂ : d + 8 ≤ 2112) :
    m.readW (S s₀ + BitVec.ofNat 64 d) 64 = (savedMem s₀).readW (S s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 2064, 48⟩) (slot_contains _ h₁ h₂) (slots_disj hp) (by decide)

theorem epilogue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv enc s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => gprPreserved s₀ s' ∧ (cbcX86_64 enc).post s₀ s' := by
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  have hsv : Spill.Saved s₂.mem (s₂.gpr .r15) s₀.gpr saved := fun p hp' => by
    have := saved_bound p hp'
    rw [h₂.r15, slot_read hp h₂.frame this.1 this.2]
    exact Spill.saveMem_saved _ _ _ _ (by decide) p hp'
  have hall : (blks s₀).take (N s₀) = blks s₀ := List.take_of_length_le (by simp [Spec.Cbc.blocksAt])
  have hnil : (blks s₀).drop (N s₀) = [] := List.drop_of_length_le (by simp [Spec.Cbc.blocksAt])
  refine WP.mono (Spill.restore_ok .r15 saved s₀.gpr s₂ (by decide) (fun p hp' => ?_) hsv)
    fun s₃ ⟨g₁, g₂, mem₃, _⟩ => ⟨⟨Spill.calleeSaved_ok g₁ g₂ (by decide) h₂.rsp, ?_⟩, ?_, ?_⟩
  · have := saved_bound p hp'
    rw [rdwr, hp.rd, hp.wr, h₂.r15]
    exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by have := hp.scr_wrap; omega))
  · rw [mem₃]
    refine (UPre.big_of h₂.frame).readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)
  · show Spec.Cbc.blocksAt s₃.mem (Dp s₀) (N s₀) = _
    rw [mem₃, h₂.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₃.mem (Iv s₀) 16 = _
    rw [mem₃, h₂.iv]; simp only [outK, hall]

theorem whole_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (h0 : (cbcX86_64 enc).pre s₀) :
    WP isa (whole body) s₀ fun s' => gprPreserved s₀ s' ∧ (cbcX86_64 enc).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (mid_wp hb hp h₁ z₁) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.AesCbc.X86_64
