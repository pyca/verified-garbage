module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.CT
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: the frame's words in a state of the search

`SS.stF`: a store into a variable word of the frame keeps the claims, arrays
and header words. `SS.ldF`: a load of a word whose value the stage keeps.
`cmpF_vp`, `st_vp`, `stImm_vp`: those as pieces.
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
    {r : Reg} {o : Nat} (ho : o + 4 ≤ F + 32) (h4 : o % 4 = 0) {x : BitVec 32}
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
    {o v : Nat} (ho : o + 4 ≤ F + 32) (h4 : o % 4 = 0) (hv : v < 256) {x : BitVec 32}
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

end VG.Proof.Dsa.Arm.Gen
