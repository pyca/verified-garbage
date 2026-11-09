module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.CT
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.Block

/-! # DSA parameter generation on ARMv7: the frame's words in a state of the search

`SS.stF`: a store into a variable word of the frame keeps the claims, arrays
and header words. `SS.ldF`: a load of a word whose value the stage keeps.
`cmpF_vp`, `st_vp`, `stImm_vp`: those as pieces. `less_vp`: an unsigned
comparison of `r0` with `r1`; `wp_cst`: a 32-bit constant.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_cmp op2_imm op2_reg eval_eq)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {G : GP} {σ : State} {c : Cfg} {s : State}

/-- `c` with the frame word `o` := `v`. -/
abbrev Cfg.setV (c : Cfg) (o : Nat) (v : BitVec 32) : Cfg := { c with V := upd c.V o v, LS := o :: c.LS }

/-- The frame is apart from the claims and the key working space. -/
theorem SS.of_frame {t : State} (h : SS G σ c s) {V : Nat → BitVec 32} {LS : List Nat} (gi : GI G σ V LS t)
    (r : Rest [.r12] s t) (f : Frame [G.rFrame] s.mem t.mem) : SS G σ { c with V := V, LS := LS } t := by
  have gi₀ := h.gi
  have big := gi₀.scrBig
  have fit := gi₀.scrFit
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega
  have kd : ∀ r' ∈ [G.rFrame], G.rK.Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    show Region.Disjoint ⟨State.addr G.KB, _⟩ _
    rw [gi₀.kaddr]; exact gi₀.scr_frame big
  refine ⟨gi, (r.gpr _ (by decide)).trans h.r7, (r.gpr _ (by decide)).trans h.r8,
    (r.gpr _ (by decide)).trans h.r9, h.sb.frame f (fun x hx r' hr' => ?_) (fun x hx => ?_), h.clOk,
    fun j hj => ?_, h.liveOk, fun d hd => ?_, h.kslOk⟩
  · simp only [List.mem_singleton] at hr'; subst hr'
    have := h.clOk x hx; exact gi₀.scr_frame (by omega)
  · have := h.clOk x hx; omega
  · rw [num_frame h.lens f kd (h.liveOk j hj)]; exact h.arrs j hj
  · rw [slot_frame h.lens f kd (h.kslOk d hd)]; exact h.ksl d hd

/-- `str r, [sp, #o]` (through `r12`) of a variable frame word. -/
theorem SS.stF (h : SS G σ c s) {o : Nat} (hv : VarOk G o) {r : Reg} (hr : r ≠ .r12)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, SS G σ (c.setV o (s.gpr r)) t → Rest [.r12] s t → WP isa (.block rest) t Q) :
    WP isa (.block (st r o ++ rest)) s Q :=
  h.gi.stF hv hr fun t gi r f => k t (h.of_frame gi r f) r

/-! ## As pieces -/

/-- A load of a frame word whose value both runs know. -/
theorem ld_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G σ (c σ) s)
    {r : Reg} {o : Nat} (ho : o + 4 ≤ F + 16) (h4 : o % 4 = 0) {x : BitVec 32}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → Upd s t r x → Q σ t) : VP P (.block [ld r o]) Q :=
  VP.ld (SS.spOk hF) fun σ s hs => (hF σ s hs).gi.ldV ho h4 (hx σ s hs) fun t u => WP.block_nil (k σ s t hs u)

theorem beq_sub_zero (x y : BitVec 32) : (x - y == 0) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have : x - y ≠ 0 := fun e => h (by rw [← BitVec.sub_add_cancel x y, e]; exact BitVec.zero_add y)
    rw [beq_false_of_ne this, beq_false_of_ne h]

/-- `cmpF o v`: Z iff the frame word `o`, which both runs know, is `v`. -/
theorem cmpF_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G σ (c σ) s)
    {o v : Nat} (ho : o + 4 ≤ F + 16) (h4 : o % 4 = 0) (hv : v < 256) {x : BitVec 32}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → Rest [.r0] s t → t.mem = s.mem → isa.eval .eq t = some (x == BitVec.ofNat 32 v) →
      Q σ t) : VP P (.block (cmpF o v)) Q := by
  rw [show cmpF o v = [ld .r0 o] ++ [.cmp .r0 (.imm (BitVec.ofNat 32 v))] from rfl]
  refine VP.block_append (G := fun σ t => ∃ s, P σ s ∧ Upd s t .r0 x)
    (ld_vp hF ho h4 hx fun σ s t hs u => ⟨s, hs, u⟩) ?_
  refine VP.taint [.r0] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0])
      (.block [.cmp .r0 (.imm (BitVec.ofNat 32 0))]), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ ⟨_, _, u₁⟩ ⟨_, _, u₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [u₁.gpr, u₂.gpr]) fun σ s ⟨s₀, hs₀, u⟩ => ?_
  refine wp_cmp (op2_imm (encodable_lt hv)) fun t f z => WP.block_nil ?_
  refine k σ s₀ t hs₀ ((u.rest (by simp)).trans (f.rest _)) (by rw [f.mem, u.mem]) ?_
  rw [eval_eq, z, u.gpr, beq_sub_zero]

/-- A store into a variable word of the frame. -/
theorem st_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G σ (c σ) s)
    {r : Reg} (hr : r ≠ .r12) {o : Nat} (hv : VarOk G o)
    (k : ∀ σ s t, P σ s → SS G σ ((c σ).setV o (s.gpr r)) t → Rest [.r12] s t → Q σ t) :
    VP P (.block (st r o)) Q :=
  VP.st (SS.spOk hF) fun σ s hs => by
    rw [← List.append_nil (st r o)]
    exact (hF σ s hs).stF hv hr fun t h R => WP.block_nil (k σ s t hs h R)

/-- `stImm o v`: the frame word `o` := `v`. -/
theorem stImm_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G σ (c σ) s)
    {o v : Nat} (hv : v < 256) (ho : VarOk G o)
    (k : ∀ σ s t, P σ s → SS G σ ((c σ).setV o (BitVec.ofNat 32 v)) t → Rest [.r1, .r12] s t → Q σ t) :
    VP P (.block (stImm o v)) Q := by
  refine VP.block_append (G := fun σ t => ∃ s, P σ s ∧ Upd s t .r1 (BitVec.ofNat 32 v) ∧ SS G σ (c σ) t)
    (VP.taint [] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [])
      (.block [.mov .r1 (.imm (BitVec.ofNat 32 0))]), rfl⟩ (fun _ _ _ _ _ _ r hr => absurd hr (by simp))
      fun σ s hs => wp_mov (op2_imm (encodable_lt hv)) fun t u => WP.block_nil
        ⟨s, hs, u, (hF σ s hs).of_rest (u.rest (ws := [.r1]) (by simp)) u.mem⟩) ?_
  refine st_vp (fun σ t ⟨_, _, _, h⟩ => h) (by decide) ho fun σ s t ⟨s₀, hs₀, u, _⟩ h R => ?_
  rw [u.gpr] at h
  exact k σ s₀ t hs₀ h ((u.rest (by simp)).trans (R.mono (by simp)))

end

/-! ## Unsigned comparisons and constants -/

theorem less_ok (s : State) :
    WP isa (.block less) s fun t =>
      (t.z = decide ((s.gpr .r0).toNat < (s.gpr .r1).toNat) ∧ t.mem = s.mem) ∧ Rest [.r12] s t := by
  refine VG.Proof.Ffdh.Arm.withRest_all [.r12] ?_ (by rfl) (by rfl)
  unfold less
  by_cases ge : (s.gpr .r1).toNat ≤ (s.gpr .r0).toNat
  · have lt : ¬ (s.gpr .r0).toNat < (s.gpr .r1).toNat := by omega
    ffrun [ge, lt, show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_add]
  · have lt : (s.gpr .r0).toNat < (s.gpr .r1).toNat := by omega
    ffrun [ge, lt, show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_add]

/-- `less` as a piece: `Z` iff `r0 < r1`, which both runs know. -/
theorem less_vp {P Q : State → State → Prop} {x y : BitVec 32} (hx : ∀ σ s, P σ s → s.gpr .r0 = x)
    (hy : ∀ σ s, P σ s → s.gpr .r1 = y)
    (k : ∀ σ s t, P σ s → Rest [.r12] s t → t.mem = s.mem → isa.eval .eq t = some (decide (x.toNat < y.toNat)) →
      Q σ t) : VP P (.block less) Q := by
  refine VP.taint [.r0, .r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1]) (.block less), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => WP.mono (less_ok s) fun t ⟨⟨z, m⟩, R⟩ =>
      k σ s t hs R m (by rw [eval_eq, z, hx σ s hs, hy σ s hs])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hx _ _ h₁, hx _ _ h₂]
  · rw [hy _ _ h₁, hy _ _ h₂]

theorem setWidth_ofNat16 {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

section
variable {G : GP}

/-- `ld r0 o; movw r1 v; less`: `Z` iff the frame word `o`, which both runs
know, is below `v`. -/
theorem ltF_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G σ (c σ) s)
    {o v : Nat} (ho : o + 4 ≤ F + 16) (h4 : o % 4 = 0) (hv : v < 2 ^ 16) {x : BitVec 32}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → Rest [.r0, .r1, .r12] s t → t.mem = s.mem →
      isa.eval .eq t = some (decide (x.toNat < v)) → Q σ t) :
    VP P (.seq (.block [ld .r0 o]) (.block (([.movw .r1 (BitVec.ofNat 16 v)] : List Instr) ++ less))) Q := by
  refine VP.seq (G := fun σ t => ∃ s, P σ s ∧ Upd s t .r0 x) (ld_vp hF ho h4 hx fun σ s t hs u => ⟨s, hs, u⟩) ?_
  refine VP.block_append (G := fun σ t => ∃ s, P σ s ∧ Rest [.r0, .r1] s t ∧ t.mem = s.mem ∧ t.gpr .r0 = x ∧
      t.gpr .r1 = BitVec.ofNat 32 v)
    (VP.taint [] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [])
      (.block [.movw .r1 (BitVec.ofNat 16 0)]), rfl⟩ (fun _ _ _ _ _ _ r hr => absurd hr (by simp))
      fun σ s ⟨s₀, hs₀, u⟩ => VG.Proof.X25519.Arm.wp_movw fun t u' => WP.block_nil ⟨s₀, hs₀,
        (u.rest (by simp)).trans (u'.rest (by simp)), by rw [u'.mem, u.mem], by rw [u'.other _ (by decide), u.gpr],
        by rw [u'.gpr, setWidth_ofNat16 hv]⟩) ?_
  refine less_vp (x := x) (y := BitVec.ofNat 32 v) (fun σ s ⟨_, _, _, _, h0, _⟩ => h0)
    (fun σ s ⟨_, _, _, _, _, h1⟩ => h1) fun σ s t ⟨s₀, hs₀, R, m, _, _⟩ R' m' e => k σ s₀ t hs₀
      ((R.mono (by simp)).trans (R'.mono (by simp))) (m'.trans m) ?_
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

end

/-- `movw` and `movt` of the halves of `v`. -/
theorem cst_val {v : Nat} (hv : v < 2 ^ 32) :
    (BitVec.ofNat 16 (v / 2 ^ 16) ++ ((BitVec.ofNat 16 (v % 2 ^ 16)).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

/-- `cst d v`: `d` := `v`. -/
theorem wp_cst {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {v : Nat} (hv : v < 2 ^ 32)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 32 v) → WP isa (.block is) s' Q) :
    WP isa (.block (cst d v ++ is)) s Q := by
  simp only [cst, List.cons_append, List.nil_append]
  refine VG.Proof.X25519.Arm.wp_movw fun s₁ u₁ => VG.Proof.X25519.Arm.WP.cons rfl (k _ ?_)
  have hval : (BitVec.ofNat 16 (v / 2 ^ 16) ++ (s₁.gpr d).extractLsb' 0 16 : BitVec 32) = BitVec.ofNat 32 v := by
    rw [u₁.gpr]; exact cst_val hv
  have e := Upd.setReg s₁ d (BitVec.ofNat 16 (v / 2 ^ 16) ++ (s₁.gpr d).extractLsb' 0 16 : BitVec 32)
  exact ⟨e.gpr.trans hval, fun r hr => (e.other r hr).trans (u₁.other r hr), e.mem.trans u₁.mem,
    e.rd.trans u₁.rd, e.wr.trans u₁.wr, e.sp.trans u₁.sp⟩

end VG.Proof.Dsa.Arm.Gen
