import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Calls

/-!
# Argon2 H′ on ARMv7: hashing in `scratch`

What the hash macros keep (`Keeps`: `r4`–`r8`, `r11`, the stack pointer, the
permissions, and the memory outside `scratch[0, 832)` and the 32 bytes below
the stack pointer), and the hash of a fixed `scratch` buffer
(`absorbFixed_ok`) and of the 64-byte digest (`next_ok`).
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (init update finalize absorbFixed next)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_reg op2_imm)

/-- The registers the hash macros keep, that callers keep their values in. -/
abbrev kept : List Reg := [.r4, .r5, .r6, .r7, .r8, .r11]

/-- The registers the macros write are not kept. -/
theorem kept_ne : ∀ q ∈ kept, q ≠ .r0 ∧ q ≠ .r1 ∧ q ≠ .r2 ∧ q ≠ .r3 ∧ q ≠ .r9 ∧ q ≠ .r10 ∧ q ≠ .r12 ∧
    q ≠ .lr := by decide

/-- What the hash macros keep. -/
structure Keeps (B SP : BitVec 32) (s t : State) : Prop where
  gpr : ∀ r ∈ kept, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨State.addr B, 832⟩, stkR SP 32] s.mem t.mem

theorem Keeps.refl {B SP : BitVec 32} (s : State) : Keeps B SP s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Keeps.trans {B SP : BitVec 32} {s t u : State} (h : Keeps B SP s t) (h' : Keeps B SP t u) :
    Keeps B SP s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.sp.trans h.sp, h'.rd.trans h.rd, h'.wr.trans h.wr,
    h.frame.trans h'.frame⟩

theorem Keeps.r4 {B SP : BitVec 32} {s t : State} (h : Keeps B SP s t) : t.gpr .r4 = s.gpr .r4 :=
  h.gpr _ (by decide)

theorem Keeps.ctx {B SP : BitVec 32} {s t : State} (h : Keeps B SP s t) (c : Ctx B SP s) : Ctx B SP t :=
  c.of_regs h.r4 h.sp h.wr

/-- Steps that keep memory, the permissions, the stack pointer and `kept`. -/
theorem Keeps.same {B SP : BitVec 32} {s t : State} (hg : ∀ r ∈ kept, t.gpr r = s.gpr r)
    (hs : t.sp = s.sp) (hm : t.mem = s.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Keeps B SP s t :=
  ⟨hg, hs, hrd, hwr, hm ▸ Frame.refl _ _⟩

/-- Calls keep the callee-saved registers and write within the regions. -/
theorem Keeps.of_call {B SP : BitVec 32} {s t : State} (hr : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r)
    (hsp : t.sp = s.sp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [(⟨State.addr B, 832⟩ : Region), stkR SP 32], Region.Sub r r') :
    Keeps B SP s t :=
  ⟨fun r h => by
    have hk : r ∈ preserved ∧ r ≠ .lr := by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hr r hk.1 hk.2,
    hsp, hrd, hwr, hf.sub hs⟩

/-- Bytes outside `scratch[0, 832)` and the stack are kept. -/
theorem Keeps.bytes {B SP : BitVec 32} {s t : State} (h : Keeps B SP s t) {R : Region}
    (hR : R.len ≤ 2 ^ 64) (h₁ : R.Disjoint ⟨State.addr B, 832⟩) (h₂ : R.Disjoint (stkR SP 32)) :
    bytesAt t.mem R.base R.len = bytesAt s.mem R.base R.len :=
  Proof.Blake2.bytesAt_congr fun i hi => h.frame.bytes (R := R) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂) hR hi

/-! ## Fixed buffers -/

/-- Absorb `size` bytes at `scratch + offset` into an empty state. -/
theorem absorbFixed_ok {B SP : BitVec 32} {s : State} (c : Ctx B SP s) {offset size : Nat}
    (heo : encodable (BitVec.ofNat 32 offset) = true) (hes : encodable (BitVec.ofNat 32 size) = true)
    (ho : B.toNat + offset + size ≤ 2 ^ 32) (hlo : 768 ≤ offset) (hs : size < 2 ^ 32) (hpos : 0 < size)
    (hcov : Covers [⟨State.addr B + BitVec.ofNat 64 offset, size⟩] s.wr)
    (hstk : (stkR SP 32).Disjoint ⟨State.addr B + BitVec.ofNat 64 offset, size⟩) {h0 : HashValue 64}
    (repr : Repr b h0 s.mem (State.addr B) []) :
    WP isa (absorbFixed offset size) s fun t =>
      Repr b h0 t.mem (State.addr B) (bytesAt s.mem (State.addr B + BitVec.ofNat 64 offset) size) ∧
      Keeps B SP s t := by
  unfold absorbFixed
  have hfit := c.fits
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm heo) fun s₃ u₃ => wp_mov (op2_imm hes) fun s₄ u₄ => WP.block_nil ?_)
  have o : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have m : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have c₄ : Ctx B SP s₄ := c.of_regs (o _ (by decide) (by decide) (by decide) (by decide))
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  have eD : s₄.gpr .r9 = B + BitVec.ofNat 32 offset := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.r4]
  have eDw : State.addr (B + BitVec.ofNat 32 offset) = State.addr B + BitVec.ofNat 64 offset :=
    addr_add (by omega)
  have dTo : (B + BitVec.ofNat 32 offset).toNat = B.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega)]; omega
  have hL : (s₄.gpr .r10).toNat = size := by
    rw [u₄.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]
  have hDc : Covers [⟨State.addr (B + BitVec.ofNat 32 offset), size⟩] (s₄.rd ++ s₄.wr) := by
    rw [eDw, show s₄.wr = s.wr by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]]; exact Covers.right hcov
  have hDs : Region.Disjoint ⟨State.addr (B + BitVec.ofNat 32 offset), size⟩ ⟨State.addr B, 768⟩ := by
    rw [eDw]; exact Offset.disjoint_base _ hlo (by omega)
  have hDk : (stkR SP 32).Disjoint ⟨State.addr (B + BitVec.ofNat 32 offset), size⟩ := by
    rw [eDw]; exact hstk
  have hcount : s₄.gpr .r3 ++ s₄.gpr .r2 = BitVec.ofNat 64 ([] : List Byte).length := by
    have e1 : s₄.gpr .r3 = 0 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    have e2 : s₄.gpr .r2 = 0 := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    rw [e1, e2]; rfl
  refine (update_ok c₄ eD hL (by rw [dTo]; omega) hDc hDs hDk (by rw [m]; exact repr) hcount
    (by simp only [List.length_nil]; omega)).mono ?_
  rintro t ⟨r, cs, rd, wr, sp, f⟩
  refine ⟨by rw [m, eDw, List.nil_append] at r; exact r, ?_⟩
  refine (Keeps.same (B := B) (SP := SP) (fun q hq => o q (kept_ne q hq).2.2.1
      (kept_ne q hq).2.2.2.1 (kept_ne q hq).2.2.2.2.1 (kept_ne q hq).2.2.2.2.2.1) (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) m
      (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])).trans
    (Keeps.of_call cs sp rd wr f ?_)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

/-! ## The hash of the digest -/

theorem next_ok {B SP : BitVec 32} {s : State} (c : Ctx B SP s) {n : Nat}
    (hn : s.gpr .r1 = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa next s fun t =>
      bytesAt t.mem (State.addr B + 768) 64 =
        finalHash b (Spec.Blake2.init b n 0) (bytesAt s.mem (State.addr B + 768) 64) ∧
      Keeps B SP s t := by
  unfold next
  have hfit := c.fits
  refine WP.seq ((init_ok c hn hn₁ hn₂).mono fun s₁ ⟨r₁, cs₁, rd₁, wr₁, sp₁, f₁⟩ => ?_)
  have k₁ : Keeps B SP s s₁ := Keeps.of_call cs₁ sp₁ rd₁ wr₁ f₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  have dg : bytesAt s₁.mem (State.addr B + 768) 64 = bytesAt s.mem (State.addr B + 768) 64 := by
    refine Proof.Blake2.bytesAt_congr fun i hi => f₁.bytes (R := ⟨State.addr B + 768, 64⟩) ?_ (by simp) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by decide) (by decide)
  refine WP.seq ((absorbFixed_ok (k₁.ctx c) (offset := 768) (size := 64) (by decide) (by decide) (by omega)
    (by decide) (by decide) (by decide) ((k₁.ctx c).cov (by decide)) (c.stk_sub (by decide)) r₁).mono
    fun s₂ ⟨r₂, k₂⟩ => ?_)
  rw [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, dg] at r₂
  have c₂ := (k₁.trans k₂).ctx c
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ =>
    WP.block_nil ?_)
  have c₄ : Ctx B SP s₄ := c₂.of_regs (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
    (by rw [u₄.sp, u₃.sp]) (by rw [u₄.wr, u₃.wr])
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  refine (finalize_ok c₄ (d := bytesAt s.mem (State.addr B + 768) 64) (by rw [m₄]; exact r₂)
    (by
      have len : (bytesAt s.mem (State.addr B + 768) 64).length = 64 := by simp [bytesAt]
      rw [u₄.gpr, u₄.other _ (by decide), u₃.gpr, len]; rfl) (by simp [bytesAt])).mono ?_
  rintro t ⟨d, cs, rd, wr, sp, f⟩
  refine ⟨d, (k₁.trans k₂).trans ?_⟩
  refine Keeps.of_call (fun q hq hl => (cs q hq hl).trans ?_) (sp.trans (by rw [u₄.sp, u₃.sp]))
    (rd.trans (by rw [u₄.rd, u₃.rd])) (wr.trans (by rw [u₄.wr, u₃.wr])) (m₄ ▸ f) ?_
  · have : q ≠ .r2 ∧ q ≠ .r3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₄.other _ this.2, u₃.other _ this.1]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

end VG.Proof.Argon2.Arm.HPrime
