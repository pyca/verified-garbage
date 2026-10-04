import VerifiedGarbage.Proof.Argon2.Arm.Derive.Body

/-!
# Argon2 on ARMv7: the derivation's locals

`lw s₀ s d`: the word at `[r11, #d]` in the body. A store to the locals keeps
the invariant and every other word (`Inv.store_loc`); writes to the memory
matrix, `scratch`, the output or the stack below the locals keep all of them
(`lw_keep`).
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Argon2.Arm (stkR addr_toNat)
open VG.Proof.MdStream.Arm (Upd Mupd wp_ldr wp_str)
open VG.Impl.Argon2.Arm.Derive (ld st)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem loc_addr {d : Nat} (hd : d < 256) :
    State.addr (E s₀ + BitVec.ofNat 32 d) = State.addr (E s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := E_hi hp; omega)

/-- Another word of the frame, after a store to the locals. -/
theorem lw_store {m : Mem} {d e : Nat} (hd : d + 4 ≤ 256) (he : e + 4 ≤ 256) (hde : d + 4 ≤ e ∨ e + 4 ≤ d)
    (v : BitVec 32) :
    (m.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v).readW (State.addr (E s₀ + BitVec.ofNat 32 e)) 32 =
      m.readW (State.addr (E s₀ + BitVec.ofNat 32 e)) 32 := by
  rw [loc_addr hp (by omega), loc_addr hp (by omega)]
  exact MdStream.Arm.readW_writeW_save m _ v (by omega) (by omega) (by omega)

theorem Inv.store_loc {s t : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {v : BitVec 32}
    (u : Mupd s t (s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v)) :
    Inv s₀ t ∧ lw s₀ t d = v ∧ ∀ e, e + 4 ≤ 256 → (d + 4 ≤ e ∨ e + 4 ≤ d) → lw s₀ t e = lw s₀ s e := by
  refine ⟨h.step u.sp (by rw [u.gpr]) u.rd u.wr ?_, ?_, fun e he hde => ?_⟩
  · rw [u.mem]
    exact (Frame.refl _ _).writeW (r := locR s₀) (by simp) v
      (contains32 (by rw [loc_nat hp (d := d) (by omega)]; omega) (by rw [loc_nat hp (d := d) (by omega)]; omega))
  · show t.mem.readW _ 32 = v
    rw [u.mem, Mem.readW_writeW_self32]
  · show t.mem.readW _ 32 = _
    rw [u.mem, lw_store hp (by omega) he hde]

/-- `str r, [r11, #d]` -/
theorem wp_stloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → lw s₀ t d = s.gpr r → (∀ e, e + 4 ≤ 256 → (d + 4 ≤ e ∨ e + 4 ≤ d) →
      lw s₀ t e = lw s₀ s e) → t.gpr = s.gpr → t.mem = s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 d))
      (s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (st d r :: is)) s Q :=
  wp_str (by omega) (by rw [h.r11]) (loc_in hp h hd) fun t u =>
    let ⟨i, v, o⟩ := h.store_loc hp hd u
    k t i v o u.gpr u.mem

/-- `ldr r, [r11, #d]` -/
theorem wp_ldloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (lw s₀ s d) → WP isa (.block is) t Q) :
    WP isa (.block (ld r d :: is)) s Q :=
  wp_ldr (by omega) (by rw [h.r11]) (loc_in' hp h hd) k

/-- `ldr r, [r11, #argOff i]` -/
theorem wp_ldarg {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (ld r (Impl.Argon2.Arm.Derive.argOff i) :: is)) s Q :=
  wp_ldr (by simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]; omega) (by rw [h.r11])
    (h.arg_in hp hi) fun t u => k t (by have := h.arg hp hi; simp only [lw] at this; rw [this] at u; exact u)

/-- The locals are outside the memory matrix, `scratch`, the output and the stack below them. -/
theorem loc_disj {d : Nat} (hd : d + 4 ≤ 144) :
    ∀ r ∈ [memR s₀, scrR s₀, outR s₀, callR s₀],
      Region.Disjoint ⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩ r := by
  have := hp.sp_lo
  have hE := E_nat hp
  have sub := frame_stk hp (d := d) (n := 4) (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · show Region.Disjoint _ ⟨State.addr (E s₀) - BitVec.ofNat 64 40, 40⟩
    rw [← addr_sub' (by omega)]
    exact disj32 (.inr (by rw [sub_toNat' (by omega), loc_nat hp (d := d) (by omega)]; omega))
      (by rw [loc_nat hp (d := d) (by omega)]; have := E_hi hp; omega) (by rw [sub_toNat' (by omega)]; omega)

/-- The locals are kept by writes outside them. -/
theorem lw_keep {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r') {d : Nat}
    (hd : d + 4 ≤ 144) : lw s₀ t d = lw s₀ s d :=
  (f.sub hs).readW (Region.contains_self _ _) (loc_disj hp hd) (by decide)

end

/-- The body's first instruction points `r11` to the locals. -/
theorem inv_start {s₀ : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = (entry s₀).mem → (∀ r, r ≠ .r11 → t.gpr r = (entry s₀).gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (.addSp .r11 0 :: is)) (entry s₀) Q := by
  refine MdStream.Arm.WP.cons (s' := (entry s₀).setReg .r11 ((entry s₀).sp + BitVec.ofNat 32 0)) (by
    simp [exec]) ?_
  have u := MdStream.Arm.Upd.setReg (entry s₀) .r11 ((entry s₀).sp + BitVec.ofNat 32 0)
  have esp : (entry s₀).sp = E s₀ := entry_sp' s₀
  refine k _ ⟨by rw [u.sp, esp], by rw [u.gpr, esp]; simp, by rw [u.rd, entry_rd], by rw [u.wr],
    by rw [u.mem]; exact Frame.refl _ _⟩ u.mem u.other

end VG.Proof.Argon2.Arm.Derive
