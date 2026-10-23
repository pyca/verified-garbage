module

public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Body
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Argon2 on PPC64LE: the derivation's locals

`lw s₀ s d`: the doubleword at `r30 + d` in the body. A store to the frame's
variables keeps the invariant and every other doubleword (`wp_stloc`);
writes to the memory matrix, `scratch`, the output or the calls' frames keep
all of them (`lw_keep`). `wp_lda` and `wp_ldw` load an argument, of 64 or 32
bits.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_ld wp_std wp_lwz wp_mov)
open VG.Impl.Argon2.PPC64LE.Derive (ld st lda ldw argOff locals savedSlots argSlots)

/-- An offset of a doubleword in the frame's local variable space. -/
abbrev LocOff (d : Nat) : Prop := 32 ≤ d ∧ d + 8 ≤ 336 ∧ d % 8 = 0

/-- An offset of a doubleword the body may write: H′'s input or the loop
variables. -/
abbrev VarOff (d : Nat) : Prop := (32 ≤ d ∧ d + 8 ≤ 104 ∨ 208 ≤ d ∧ d + 8 ≤ 336) ∧ d % 8 = 0

section
variable {s₀ : State}

theorem loc_in {s : State} (h : Inv s₀ s) {d n : Nat} (h₁ : 32 ≤ d) (h₂ : d + n ≤ 336) :
    InRegions s.wr (E s₀ + BitVec.ofNat 64 d) n := by
  rw [h.wr, entry_wr, E_add]
  exact ⟨_, List.mem_cons_self .., Offset.contains _ (by omega) (by omega) (by omega)⟩

theorem loc_in' {s : State} (h : Inv s₀ s) {d n : Nat} (h₁ : 32 ≤ d) (h₂ : d + n ≤ 336) :
    InRegions (s.rd ++ s.wr) (E s₀ + BitVec.ofNat 64 d) n :=
  let ⟨r, hr, hc⟩ := loc_in h h₁ h₂
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- A store's doubleword is within the body's regions. -/
theorem var_in {d : Nat} (hd : VarOff d) :
    ∃ r ∈ bodyW s₀, r.Contains (E s₀ + BitVec.ofNat 64 d) 8 := by
  rw [E_add]
  rcases hd.1 with h | h
  · exact ⟨inR s₀, by simp, Offset.contains _ (by omega) (by omega) (by omega)⟩
  · exact ⟨varR s₀, by simp, Offset.contains _ (by omega) (by omega) (by omega)⟩

/-- `std r, d(r30)` -/
theorem wp_stloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : VarOff d) {r : Reg} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → lw s₀ t d = s.gpr r →
      (∀ e, e + 8 ≤ 336 → d + 8 ≤ e ∨ e + 8 ≤ d → lw s₀ t e = lw s₀ s e) → t.gpr = s.gpr →
      t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) (s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (st d r :: is)) s Q := by
  obtain ⟨R, hR, hc⟩ := var_in hd
  refine wp_std (a := E s₀ + BitVec.ofNat 64 d) ⟨by omega, by omega⟩ (by rw [h.r30])
    (loc_in h (by omega) (by omega)) fun t u => k t (h.mupd u ((Frame.refl _ _).writeW hR _ hc))
    (by rw [lw, u.mem, Mem.readW_writeW_self64]) (fun e he he' => ?_) u.gpr u.mem
  rw [lw, lw, u.mem, Mem.readW_writeW_sep (by
    rw [E_add, E_add]
    exact Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]

/-- `ld r, d(r30)` -/
theorem wp_ldloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : LocOff d) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (lw s₀ s d) → WP isa (.block is) t Q) :
    WP isa (.block (ld r d :: is)) s Q :=
  wp_ld ⟨by omega, by omega⟩ (by rw [h.r30]) (loc_in' h hd.1 (by omega)) k

theorem argOff_lt {i : Nat} (hi : i < 18) : argOff i < 2 ^ 15 ∧ argOff i % 4 = 0 := by
  revert hi; revert i; decide

variable (hp : DPre s₀)
include hp

/-- Argument `i` is readable. -/
theorem Inv.arg_in {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {n : Nat} (hn : n ≤ 8) :
    InRegions (s.rd ++ s.wr) (E s₀ + BitVec.ofNat 64 (argOff i)) n := by
  by_cases h8 : i < 8
  · refine loc_in' h ?_ ?_ <;> simp only [argOff, locals, h8, ite_true] <;> first | omega | skip
  · have e : argOff i = 368 + 8 * i := by
      simp only [argOff, locals]; rw [ite_eq_right_iff.mpr (by omega)]
    rw [h.rd, e, E_add, hp.rd]
    refine ⟨argR s₀, List.mem_append_left _ (by simp), ?_⟩
    rw [argR_eq]
    exact Offset.contains _ (by omega) (by omega) (by omega)

/-- `ld r, (argOff i)(r30)`: a 64-bit argument. -/
theorem wp_lda {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (lda r i :: is)) s Q :=
  wp_ld (argOff_lt hi) (by rw [h.r30]) (h.arg_in hp hi (by decide)) fun t u =>
    k t (by rw [h.arg hp hi] at u; exact u)

/-- `lwz r, (argOff i)(r30)`: a 32-bit argument, zero-extended. -/
theorem wp_ldw {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r ((arg32 s₀ i).setWidth 64) → WP isa (.block is) t Q) :
    WP isa (.block (ldw r i :: is)) s Q :=
  wp_lwz (argOff_lt hi).1 (by rw [h.r30]) (h.arg_in hp hi (by decide)) fun t u =>
    k t (by rw [h.arg32 hp hi] at u; exact u)

/-- The frame's doublewords are outside the buffers and the calls' frames. -/
theorem loc_disj {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 336) :
    ∀ r ∈ [memR s₀, scrR s₀, outR s₀, callR s₀],
      Region.Disjoint ⟨E s₀ + BitVec.ofNat 64 d, 8⟩ r := by
  rw [E_add]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact stk_disj hp (by omega) _ (by simp)
  · exact stk_disj hp (by omega) _ (by simp)
  · exact stk_disj hp (by omega) _ (by simp)
  · have e : B s₀ = B s₀ + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
    show Region.Disjoint _ ⟨B s₀, 48⟩
    rw [e]
    exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- The frame is kept by writes outside it. -/
theorem lw_keep {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r') {d : Nat}
    (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 336) : lw s₀ t d = lw s₀ s d :=
  (f.sub hs).readW (Region.contains_self _ _) (loc_disj hp h₁ h₂) (by decide)

end

theorem saveMem_congr {m : Mem} {b : Addr} {g g' : Reg → BitVec 64} :
    ∀ {l : List (Reg × Nat)}, (∀ p ∈ l, g p.1 = g' p.1) →
      Spill.saveMem m b g l = Spill.saveMem m b g' l
  | [], _ => rfl
  | (r, d) :: l, h => by
    simp only [Spill.saveMem]
    rw [h (r, d) List.mem_cons_self]
    exact saveMem_congr fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- `scratch`, from the Parameter Save Area, after the setup. -/
theorem setupMem_arg (s₀ : State) {i : Nat} (h₁ : 8 ≤ i) (h₂ : i < 18) :
    (setupMem s₀).readW (E s₀ + BitVec.ofNat 64 (argOff i)) 64 = arg s₀ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = 8 + k := ⟨i - 8, by omega⟩
  have e : argOff (8 + k) = 368 + 8 * (8 + k) := by
    simp only [argOff, locals]; rw [ite_eq_right_iff.mpr (by omega)]
  rw [E_add, e, show 48 + (368 + 8 * (8 + k)) = 416 + 8 * (8 + k) by omega,
    (setupMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide),
    ← stackArg_eq, show 8 + k = k + 8 by omega]
  rfl

/-- The body's first instructions: the return address, the caller's
registers and the register arguments to the frame, `r30` to the frame and
`r31` to `scratch`. -/
theorem setup_ok {s₀ : State} (hp : DPre s₀) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = setupMem s₀ → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.PPC64LE.Derive.setup ++ is)) (entry s₀) Q := by
  have h0 : E s₀ + BitVec.ofNat 64 0 = E s₀ := BitVec.add_zero _
  have hl : ∀ p ∈ savedSlots ++ argSlots, p.1 ≠ .r0 ∧ p.1 ≠ .r12 := by decide
  simp only [Impl.Argon2.PPC64LE.Derive.setup, List.cons_append, List.append_assoc]
  refine MdStream.PPC64LE.WP.cons (s' := (entry s₀).write .r12 (E s₀))
    (by simp only [exec, show (0 : Nat) < 2 ^ 15 by decide, ite_true, entry_sp, h0]) ?_
  have u₁ := Upd.write (entry s₀) .r12 (E s₀)
  refine MdStream.PPC64LE.WP.cons exec_mflr ?_
  have u₂ := Upd.write ((entry s₀).write .r12 (E s₀)) .r0 ((entry s₀).write .r12 (E s₀)).lr
  have lr : ((entry s₀).write .r12 (E s₀)).lr = s₀.lr := rfl
  generalize ((entry s₀).write .r12 (E s₀)).write .r0 ((entry s₀).write .r12 (E s₀)).lr = c at u₂
  rw [lr] at u₂
  have c12 : c.gpr .r12 = E s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  have cg : ∀ r, r ≠ .r0 → r ≠ .r12 → c.gpr r = s₀.gpr r := fun r h₁ h₂ => by
    rw [u₂.other _ h₁, u₁.other _ h₂]; rfl
  have cwr : c.wr = (entry s₀).wr := by rw [u₂.wr, u₁.wr]
  have inE : ∀ d n, 32 ≤ d → d + n ≤ 336 → InRegions c.wr (E s₀ + BitVec.ofNat 64 d) n :=
    fun d n h₁ h₂ => by
      rw [cwr, entry_wr, E_add]
      exact ⟨_, List.mem_cons_self .., Offset.contains _ (by omega) (by omega) (by omega)⟩
  refine wp_std (a := E s₀ + BitVec.ofNat 64 104) (by decide) (by rw [c12]; rfl)
    (inE 104 8 (by decide) (by decide)) fun d ud => ?_
  rw [show (savedSlots ++ argSlots).map (fun (r, d) => Instr.store .d r .r12 d) =
    Spill.saveCode .r12 (savedSlots ++ argSlots) from rfl]
  refine Spill.save_ok (by decide) (fun p hp => slots_fits.1 p hp) (fun p hp => by
    rw [ud.wr, ud.gpr, c12]
    have := slots_in p hp
    exact inE _ _ (by omega) (by omega)) ?_
  refine wp_mov fun f uf => ?_
  have f30 : f.gpr .r30 = E s₀ := by rw [uf.gpr]; show d.gpr .r12 = _; rw [ud.gpr, c12]
  have fmem : f.mem = setupMem s₀ := by
    rw [uf.mem]
    show Spill.saveMem d.mem (d.gpr .r12) d.gpr _ = _
    rw [ud.mem, ud.gpr, c12, u₂.mem, u₁.mem, u₂.gpr]
    exact saveMem_congr fun p hp => by
      rw [cg _ (hl p hp).1 (hl p hp).2]
  have frd : f.rd = s₀.rd := by
    rw [uf.rd]; show d.rd = _; rw [ud.rd, u₂.rd, u₁.rd]; rfl
  have fin : InRegions (f.rd ++ f.wr) (E s₀ + BitVec.ofNat 64 (argOff 15)) 8 := by
    refine ⟨argR s₀, List.mem_append_left _ (by rw [frd, hp.rd]; simp), ?_⟩
    rw [argR_eq, show argOff 15 = 488 by decide, E_add]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  refine wp_ld (a := E s₀ + BitVec.ofNat 64 (argOff 15)) (by decide) (by rw [f30]; rfl) fin
    fun t ut => ?_
  rw [fmem, setupMem_arg s₀ (by decide) (by decide)] at ut
  refine k t ⟨?_, ?_, ut.gpr, fun r hr => ?_, ?_, ?_, ?_⟩ (by rw [ut.mem, fmem])
  · rw [ut.sp, uf.sp]; show d.sp = _; rw [ud.sp, u₂.sp, u₁.sp]; rfl
  · rw [ut.other _ (by decide), f30]
  · have h0 : r ≠ .r0 := fun e => by subst e; exact absurd hr (by decide)
    have h12 : r ≠ .r12 := fun e => by subst e; exact absurd hr (by decide)
    have h30 : r ≠ .r30 := fun e => by subst e; exact absurd hr (by decide)
    have h31 : r ≠ .r31 := fun e => by subst e; exact absurd hr (by decide)
    rw [ut.other _ h31, uf.other _ h30]; show d.gpr r = _; rw [ud.gpr, cg r h0 h12]
  · rw [ut.rd, frd]
  · rw [ut.wr, uf.wr]; show d.wr = _; rw [ud.wr, cwr]
  · rw [ut.mem, fmem]; exact Frame.refl _ _

end VG.Proof.Argon2.PPC64LE.Derive
