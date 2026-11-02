module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Body
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Argon2.RISCV64.Ops

/-!
# Argon2 on RISC-V: the derivation's locals

`lw s₀ s d`: the doubleword at `s3 + d` in the body. A store to the frame's
variables keeps the invariant and every other doubleword (`wp_stloc`);
writes to the memory matrix, `scratch` or the output keep all of them
(`lw_keep`). `wp_lda` and `wp_ldw` load an argument, of 64 or 32 bits.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_ld wp_sd wp_mv wp_addSp wp_addi)
open VG.Proof.Argon2.RISCV64 (wp_lwu)
open VG.Impl.Argon2.RISCV64.Derive (ld st lda ldw argOff locals savedSlots argSlots)

/-- An offset of a doubleword in the frame. -/
abbrev LocOff (d : Nat) : Prop := d + 8 ≤ 320 ∧ d % 8 = 0

/-- An offset of a doubleword the body may write: H′'s input or the loop
variables. -/
abbrev VarOff (d : Nat) : Prop := (d + 8 ≤ 72 ∨ 184 ≤ d ∧ d + 8 ≤ 312) ∧ d % 8 = 0

section
variable {s₀ : State}

theorem loc_in {s : State} (h : Inv s₀ s) {d n : Nat} (h₂ : d + n ≤ 320) :
    InRegions s.wr (E s₀ + BitVec.ofNat 64 d) n := by
  rw [h.wr, entry_wr]
  exact ⟨_, List.mem_cons_self .., Offset.contains _ (by omega) (by omega) (by omega)⟩

theorem loc_in' {s : State} (h : Inv s₀ s) {d n : Nat} (h₂ : d + n ≤ 320) :
    InRegions (s.rd ++ s.wr) (E s₀ + BitVec.ofNat 64 d) n :=
  let ⟨r, hr, hc⟩ := loc_in h h₂
  ⟨r, List.mem_append_right _ hr, hc⟩

theorem Inv.loc_al {s : State} (h : Inv s₀ s) {d k : Nat} (hk : k ∣ 16) (hd : d % k = 0) :
    (E s₀ + BitVec.ofNat 64 d).toNat % k = 0 := by
  have := h.eal
  have hE := (E s₀).isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h64 : k ∣ 2 ^ 64 := Nat.dvd_trans hk (by decide)
  rw [Nat.mod_mod_of_dvd _ h64, Nat.add_mod, Nat.mod_mod_of_dvd _ h64, hd,
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hk (Nat.dvd_of_mod_eq_zero this)), Nat.add_zero,
    Nat.zero_mod]

/-- A store's doubleword is within the body's regions. -/
theorem var_in {d : Nat} (hd : VarOff d) :
    ∃ r ∈ bodyW s₀, r.Contains (E s₀ + BitVec.ofNat 64 d) 8 := by
  rcases hd.1 with h | h
  · exact ⟨inR s₀, by simp, Offset.contains _ (by omega) (by omega) (by omega)⟩
  · exact ⟨varR s₀, by simp, Offset.contains _ (by omega) (by omega) (by omega)⟩

/-- `sd r, d(s3)` -/
theorem wp_stloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : VarOff d) {r : Reg} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → lw s₀ t d = s.gpr r →
      (∀ e, e + 8 ≤ 320 → d + 8 ≤ e ∨ e + 8 ≤ d → lw s₀ t e = lw s₀ s e) → t.gpr = s.gpr →
      t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) (s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (st d r :: is)) s Q := by
  obtain ⟨R, hR, hc⟩ := var_in hd
  refine wp_sd (a := E s₀ + BitVec.ofNat 64 d) (by omega) (by rw [h.s3])
    (h.loc_al (by decide) hd.2) (loc_in h (by omega))
    fun t u => k t (h.mupd u ((Frame.refl _ _).writeW hR _ hc))
    (by rw [lw, u.mem, Mem.readW_writeW_self64]) (fun e he he' => ?_) u.gpr u.mem
  rw [lw, lw, u.mem, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]

/-- `ld r, d(s3)` -/
theorem wp_ldloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : LocOff d) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (lw s₀ s d) → WP isa (.block is) t Q) :
    WP isa (.block (ld r d :: is)) s Q :=
  wp_ld (by omega) (by rw [h.s3]) (h.loc_al (by decide) hd.2) (loc_in' h hd.1) k

theorem argOff_lt {i : Nat} (hi : i < 18) : argOff i < 2048 ∧ argOff i % 8 = 0 := by
  revert hi; revert i; decide

variable (hp : DPre s₀)
include hp

/-- Argument `i` is readable. -/
theorem Inv.arg_in {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {n : Nat} (hn : n ≤ 8) :
    InRegions (s.rd ++ s.wr) (E s₀ + BitVec.ofNat 64 (argOff i)) n := by
  by_cases h8 : i < 8
  · refine loc_in' h ?_; simp only [argOff, locals, h8, ite_true]; omega
  · have e : argOff i = 320 + 8 * (i - 8) := by
      simp only [argOff, locals]; rw [ite_eq_right_iff.mpr (by omega)]
    have hE := E_hi hp
    rw [h.rd, e, hp.rd]
    refine ⟨argR s₀, List.mem_append_left _ (by simp), ?_⟩
    rw [argR_eq]
    exact Offset.contains _ (by omega) (by omega) (by omega)

/-- `ld r, (argOff i)(s3)`: a 64-bit argument. -/
theorem wp_lda {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (lda r i :: is)) s Q :=
  wp_ld (argOff_lt hi).1 (by rw [h.s3]) (h.loc_al (by decide) (argOff_lt hi).2)
    (h.arg_in hp hi (by decide)) fun t u => k t (by rw [h.arg hp hi] at u; exact u)

/-- `lwu r, (argOff i)(s3)`: a 32-bit argument, zero-extended. -/
theorem wp_ldw {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r ((arg32 s₀ i).setWidth 64) → WP isa (.block is) t Q) :
    WP isa (.block (ldw r i :: is)) s Q :=
  wp_lwu (argOff_lt hi).1 (by rw [h.s3])
    (h.loc_al (by decide) (by have := (argOff_lt hi).2; omega)) (h.arg_in hp hi (by decide))
    fun t u => k t (by rw [h.arg32 hp hi] at u; exact u)

/-- The frame's doublewords are outside the buffers. -/
theorem loc_disj {d : Nat} (h₂ : d + 8 ≤ 320) :
    ∀ r ∈ [memR s₀, scrR s₀, outR s₀], Region.Disjoint ⟨E s₀ + BitVec.ofNat 64 d, 8⟩ r :=
  stk_disj hp h₂

/-- The frame is kept by writes outside it. -/
theorem lw_keep {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [memR s₀, scrR s₀, outR s₀], Region.Sub r r') {d : Nat}
    (h₂ : d + 8 ≤ 320) : lw s₀ t d = lw s₀ s d :=
  (f.sub hs).readW (Region.contains_self _ _) (loc_disj hp h₂) (by decide)

end

theorem saveMem_congr {m : Mem} {b : Addr} {g g' : Reg → BitVec 64} :
    ∀ {l : List (Reg × Nat)}, (∀ p ∈ l, g p.1 = g' p.1) →
      Spill.saveMem m b g l = Spill.saveMem m b g' l
  | [], _ => rfl
  | (r, d) :: l, h => by
    simp only [Spill.saveMem]
    rw [h (r, d) List.mem_cons_self]
    exact saveMem_congr fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- `scratch`, from the stack, after the setup. -/
theorem setupMem_arg (s₀ : State) {i : Nat} (h₁ : 8 ≤ i) (h₂ : i < 18) :
    (setupMem s₀).readW (E s₀ + BitVec.ofNat 64 (argOff i)) 64 = arg s₀ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = 8 + k := ⟨i - 8, by omega⟩
  have e : argOff (8 + k) = 320 + 8 * k := by
    simp only [argOff, locals]; rw [ite_eq_right_iff.mpr (by omega)]; omega
  rw [e, (setupMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide),
    show E s₀ + BitVec.ofNat 64 (320 + 8 * k) = stackArgAddr s₀ k from (stackArg_eq s₀ k).symm,
    show 8 + k = k + 8 by omega]
  rfl

/-- The body's first instructions: the return address, the caller's
registers and the register arguments to the frame, `s3` to the frame, `s4`
to `scratch` and `s0` 2048 bytes above it. -/
theorem setup_ok {s₀ : State} (hp : DPre s₀) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = setupMem s₀ → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.setup ++ is)) (entry s₀) Q := by
  have hl : ∀ p ∈ savedSlots ++ argSlots, p.1 ≠ .t0 := by decide
  have eal := E_al hp
  simp only [Impl.Argon2.RISCV64.Derive.setup, List.cons_append, List.append_assoc]
  refine wp_addSp (imm := 0) (by decide) fun c u₁ => ?_
  have c0 : c.gpr .t0 = E s₀ := by rw [u₁.gpr, entry_sp, BitVec.add_zero]
  have cg : ∀ r, r ≠ .t0 → c.gpr r = s₀.gpr r := fun r h₁ => by rw [u₁.other _ h₁]; rfl
  have cwr : c.wr = (entry s₀).wr := u₁.wr
  have inE : ∀ d n, d + n ≤ 320 → InRegions c.wr (E s₀ + BitVec.ofNat 64 d) n :=
    fun d n h₂ => by
      rw [cwr, entry_wr]
      exact ⟨_, List.mem_cons_self .., Offset.contains _ (by omega) (by omega) (by omega)⟩
  rw [show (savedSlots ++ argSlots).map (fun (r, d) => Instr.store .d r .t0 d) =
    Spill.saveCode .t0 (savedSlots ++ argSlots) from rfl]
  refine Spill.save_ok (by rw [c0]; omega) (fun p hp => slots_fits.1 p hp) (fun p hp => by
    rw [c0]
    have := slots_in p hp
    exact inE _ _ (by omega)) ?_
  refine wp_mv fun f uf => ?_
  have f3 : f.gpr .s3 = E s₀ := by rw [uf.gpr]; exact c0
  have fmem : f.mem = setupMem s₀ := by
    rw [uf.mem]
    show Spill.saveMem c.mem (c.gpr .t0) c.gpr _ = _
    rw [u₁.mem, c0]
    exact saveMem_congr fun p hp => by rw [cg _ (hl p hp)]
  have frd : f.rd = s₀.rd := by rw [uf.rd]; show c.rd = _; rw [u₁.rd]; rfl
  have fin : InRegions (f.rd ++ f.wr) (E s₀ + BitVec.ofNat 64 (argOff 15)) 8 := by
    have hE := E_hi hp
    refine ⟨argR s₀, List.mem_append_left _ (by rw [frd, hp.rd]; simp), ?_⟩
    rw [argR_eq, show argOff 15 = 376 by decide]
    exact Offset.contains _ (by decide) (by decide) (by omega)
  refine wp_ld (a := E s₀ + BitVec.ofNat 64 (argOff 15)) (by decide) (by rw [f3]; rfl)
    (by rw [show argOff 15 = 376 by decide]; exact Spill.al8 (by omega) (by decide)) fin
    fun g ug => ?_
  rw [fmem, setupMem_arg s₀ (by decide) (by decide)] at ug
  refine wp_addi (imm := 1024) (by decide) fun h₁ uh => wp_addi (imm := 1024) (by decide) fun t ut => ?_
  have nt : ∀ r, r ≠ .s0 → r ≠ .s4 → r ≠ .s3 → r ≠ .t0 → t.gpr r = s₀.gpr r := fun r a b c' d => by
    rw [ut.other _ a, uh.other _ a, ug.other _ b, uf.other _ c']; exact cg r d
  have gs4 : g.gpr .s4 = scrP s₀ := ug.gpr
  refine k t ⟨?_, ?_, ?_, ?_, eal, hp.scr_al, fun r hr => ?_, ?_, ?_, ?_⟩ ?_
  · rw [ut.sp, uh.sp, ug.sp, uf.sp]; show c.sp = _; rw [u₁.sp]; rfl
  · rw [ut.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide), f3]
  · rw [ut.other _ (by decide), uh.other _ (by decide), gs4]
  · rw [ut.gpr, uh.gpr, gs4, BitVec.add_assoc, ← BitVec.ofNat_add]
  · exact nt r (fun e => by subst e; exact absurd hr (by decide))
      (fun e => by subst e; exact absurd hr (by decide))
      (fun e => by subst e; exact absurd hr (by decide))
      (fun e => by subst e; exact absurd hr (by decide))
  · rw [ut.rd, uh.rd, ug.rd, frd]
  · rw [ut.wr, uh.wr, ug.wr, uf.wr]; show c.wr = _; exact cwr
  · rw [ut.mem, uh.mem, ug.mem, fmem]; exact Frame.refl _ _
  · rw [ut.mem, uh.mem, ug.mem, fmem]

end VG.Proof.Argon2.RISCV64.Derive
