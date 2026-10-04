import VerifiedGarbage.Proof.Argon2.Arm.Derive.HCall

/-!
# Argon2 on ARMv7: clearing the memory matrix

`clear_ok`: `clear` zeroes the `blocks · 1024` bytes of the memory matrix,
one word per iteration, and writes nothing else. Its loop counts the words
left in `r6` (`blocks · 256`), with `r5` the next word's address and `r7`
zero.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_subs wp_str op2_imm op2_lsl)
open VG.Spec.Blake2 (bytesAt)

/-- The memory matrix, as an address. -/
abbrev memB (s₀ : State) : Addr := State.addr (memP s₀)

/-- A byte after a zero word is stored at `a`. -/
theorem writeW_zero (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 32)) x = if (x - a).toNat < 4 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- `[x + d + k]`, at a 32-bit address that does not wrap. -/
theorem addr32 {x : BitVec 32} {d k : Nat} (h : x.toNat + d + k < 2 ^ 32) :
    State.addr (x + BitVec.ofNat 32 d + BitVec.ofNat 32 k) = State.addr x + BitVec.ofNat 64 (d + k) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact addr_add (by omega)

/-- A store to a region the body may write keeps the invariant. -/
theorem Inv.store {s₀ s t : State} (h : Inv s₀ s) {R : Region} (hR : R ∈ bodyW s₀) {a : Addr}
    {v : BitVec 32} (hc : R.Contains a 4) (u : Mupd s t (s.mem.writeW a v)) : Inv s₀ t :=
  h.step u.sp (by rw [u.gpr]) u.rd u.wr (by rw [u.mem]; exact (Frame.refl _ _).writeW hR v hc)

/-- The loop's state after `j` words. -/
structure CI (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  r5 : s.gpr .r5 = memP s₀ + BitVec.ofNat 32 (4 * j)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (blocksN s₀ * 256 - j)
  r7 : s.gpr .r7 = 0
  zero : ∀ i < 4 * j, s.mem (memB s₀ + BitVec.ofNat 64 i) = 0
  frame : Frame [memR s₀] s₁.mem s.mem

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem blocks_pos : 1 ≤ blocksN s₀ := by
  rw [hp.blocks_eq, hp.laneLen_eq]
  have := Nat.mul_le_mul hp.lanes_pos (show 1 ≤ 4 * (prm s₀).segmentLen by have := hp.segLen_two; omega)
  omega

theorem clearLoop_ok {s₁ : State} (h : CI s₀ s₁ 0 s₁) :
    WP isa (.loop (.block Impl.Argon2.Arm.Derive.clearWord) .ne) s₁ (CI s₀ s₁ (blocksN s₀ * 256)) := by
  have hm := hp.mem_fits
  have hb := hp.blocks_lt
  have b1 := blocks_pos hp
  refine WP.loop (M := isa) (fun n s => ∃ j, n = blocksN s₀ * 256 - j ∧ j < blocksN s₀ * 256 ∧ CI s₀ s₁ j s)
    ?_ (blocksN s₀ * 256) s₁ ⟨0, by omega, by omega, h⟩
  rintro n s ⟨j, rfl, hj, c⟩
  have ea : State.addr (s.gpr .r5 + BitVec.ofNat 32 0) = memB s₀ + BitVec.ofNat 64 (4 * j) := by
    rw [c.r5, addr32 (by omega), Nat.add_zero]
  have hc : (memR s₀).Contains (memB s₀ + BitVec.ofNat 64 (4 * j)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  simp only [Impl.Argon2.Arm.Derive.clearWord]
  refine wp_str (by decide) ea (by rw [c.inv.wr]; exact ⟨_, mem_mem hp, hc⟩) fun t₁ u₁ => ?_
  have i₁ := c.inv.store (R := memR s₀) (by simp) hc u₁
  refine wp_add (op2_imm (by decide)) fun t₂ u₂ => wp_subs (op2_imm (by decide)) fun t u zf => WP.block_nil ?_
  have i₃ := (i₁.upd u₂ (by decide)).upd u (by decide)
  have e₁ : t.gpr .r6 = BitVec.ofNat 32 (blocksN s₀ * 256 - (j + 1)) := by
    rw [u.gpr, u₂.other _ (by decide), u₁.gpr, c.r6, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.Arm.sub_ofNat (by omega), Nat.sub_sub]
  have next : CI s₀ s₁ (j + 1) t := by
    refine ⟨i₃, ?_, e₁, ?_, fun i hi => ?_, ?_⟩
    · rw [u.other _ (by decide), u₂.gpr, u₁.gpr, c.r5, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl
    · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.gpr, c.r7]
    · rw [u.mem, u₂.mem, u₁.mem, c.r7, writeW_zero]
      by_cases hi' : i < 4 * j
      · split
        · rfl
        · exact c.zero i hi'
      · rw [show memB s₀ + BitVec.ofNat 64 i = memB s₀ + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 (i - 4 * j) by
          rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' (by omega)],
          Offset.add_sub_cancel_left]
        split
        · rfl
        · rename_i hn; rw [BitVec.toNat_ofNat] at hn; omega
    · rw [u.mem, u₂.mem, u₁.mem]
      exact c.frame.writeW (List.mem_singleton_self _) _ hc
  have z : VG.Arm.eval .ne t = some (!decide (blocksN s₀ * 256 - (j + 1) = 0)) := by
    rw [MdStream.Arm.eval_ne, zf, ← u.gpr, e₁, MdStream.Arm.ofNat_beq_zero (by omega)]
  by_cases done : j + 1 = blocksN s₀ * 256
  · refine .inl ⟨by rw [z]; simp; omega, done ▸ next⟩
  · refine .inr ⟨by rw [z]; simp; omega, blocksN s₀ * 256 - (j + 1), by omega, j + 1, rfl, by omega, next⟩

theorem clear_ok {s : State} (h : Inv s₀ s) :
    WP isa Impl.Argon2.Arm.Derive.clear s fun t => Inv s₀ t ∧ Frame [memR s₀] s.mem t.mem ∧
      ∀ i < blocksN s₀ * 1024, t.mem (memB s₀ + BitVec.ofNat 64 i) = 0 := by
  have hb := hp.blocks_lt
  have eb : blocksN s₀ = (arg s₀ 14).toNat := rfl
  unfold Impl.Argon2.Arm.Derive.clear Impl.Argon2.Arm.Derive.clearSetup
  refine WP.seq (wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ =>
    wp_ldarg hp (h.upd u₁ (by decide)) (i := 14) (by decide) fun s₂ u₂ => ?_)
  have i₂ := (h.upd u₁ (by decide)).upd u₂ (by decide)
  refine wp_mov (op2_lsl (by decide)) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have i₄ := (i₂.upd u₃ (by decide)).upd u₄ (by decide)
  refine (clearLoop_ok hp ⟨i₄, ?_, ?_, u₄.gpr, fun i hi => absurd hi (by omega), Frame.refl _ _⟩).mono
    fun t c => ⟨c.inv, ?_, fun i hi => c.zero i (by omega)⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    simp
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [shl_nat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show s.mem = s₄.mem by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]]
    exact c.frame

end

end VG.Proof.Argon2.Arm.Derive
