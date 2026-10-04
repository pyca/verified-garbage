import VerifiedGarbage.Proof.Argon2.Arm.Derive.Contract

/-!
# Argon2 on ARMv7: the derivation's frames

`vg_argon2` pushes its register arguments, then the caller's `r4`–`r11` and
its return address (with `r3`), then allocates 144 bytes for the locals
(`Impl.Argon2.Arm.Derive.derive`). `entry s₀` is the state its body starts
in; `frames_ok` gives the callee-saved registers and the stack pointer back,
from a body that leaves the stack pointer at the locals and the saved words
alone (`BodyDone`).
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Argon2.Arm (stkR pushed_sp_toNat addr_toNat)
open VG.Impl.Argon2.Arm.Derive (body derive locals restoreRegs)

/-- The registers of the first frame: the register arguments. -/
abbrev argRegs : List Reg := [.r0, .r1, .r2, .r3]

/-- The registers of the second frame: `r3` (for alignment), the caller's
`r4`–`r11` and the return address. -/
abbrev savedRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

/-- The state the body starts in. -/
def entry (s₀ : State) : State := allocated 144 (pushed savedRegs (pushed argRegs s₀))

/-- The stack pointer of the body: below the frames and the locals. -/
abbrev E (s₀ : State) : BitVec 32 := E0 s₀ - BitVec.ofNat 32 200

/-- What the body must keep for the frames to restore the caller's state. -/
structure BodyDone (s₀ t : State) : Prop where
  sp : t.sp = E s₀
  saved : ∀ j < 9, t.mem.readW (State.addr (E s₀ + BitVec.ofNat 32 (148 + 4 * j))) 32 =
    s₀.gpr (savedRegs[j + 1]?.getD .r0)

section
variable {s₀ : State} (hlo : 200 ≤ (E0 s₀).toNat)
include hlo

theorem sp1 : (pushed argRegs s₀).sp.toNat = (E0 s₀).toNat - 16 := by
  have h : 200 ≤ s₀.sp.toNat := hlo
  rw [pushed_sp_toNat (by simp only [List.length_cons, List.length_nil]; omega)]; rfl

theorem sp2 : (pushed savedRegs (pushed argRegs s₀)).sp.toNat = (E0 s₀).toNat - 56 := by
  rw [pushed_sp_toNat (by rw [sp1 hlo]; simp only [List.length_cons, List.length_nil]; omega), sp1 hlo]; rfl

theorem E_toNat : (E s₀).toNat = (E0 s₀).toNat - 200 := sub_toNat' hlo

theorem entry_sp : (entry s₀).sp = E s₀ := by
  apply BitVec.eq_of_toNat_eq
  simp only [entry, allocated]
  rw [sub_toNat' (by rw [sp2 hlo]; omega), sp2 hlo, E_toNat hlo]
  omega

end

/-- Loading the registers of `l` from offsets of `sp`, then running `rest`. -/
theorem restoreSp_ok {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.2 < 4096 ∧ InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 p.2)) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 p.2)) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldrSp p.1 p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h1, h2⟩ := hl p List.mem_cons_self
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine MdStream.Arm.wp_ldrSp h1 rfl h2 fun s₁ u₁ => ?_
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr hsp => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp)
    · rw [u₁.sp, u₁.rd, u₁.wr]; exact (hl q (List.mem_cons_of_mem _ hq))
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, u₁.sp]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other _ hr.1]

theorem frames_ok {s₀ : State} (hlo : 240 ≤ (E0 s₀).toNat) {Q : State → Prop}
    (hb : WP isa body (entry s₀) fun t => BodyDone s₀ t ∧ t.wr = (entry s₀).wr ∧ Q t)
    (hQ : ∀ t u, Q t → u.mem = t.mem → Q u) :
    WP isa derive s₀ fun u => abiPreserved s₀ u ∧ Q u := by
  have hE := (E0 s₀).isLt
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  have h1 := sp1 (s₀ := s₀) (by omega)
  have h2 := sp2 (s₀ := s₀) (by omega)
  unfold derive
  refine WP.frame (rs := argRegs) (r := .r0) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
    (by decide) ?_
  refine WP.frame (rs := savedRegs) (r := .r3) (by decide)
    (by rw [h1]; simp only [List.length_cons, List.length_nil]; omega) (by decide) ?_
  refine WP.seq (WP.alloc (by decide) (by rw [h2]; show 144 ≤ _; omega) (hb.mono fun t ⟨d, w, q⟩ => ?_))
  -- The restores.
  set S2 := pushed savedRegs (pushed argRegs s₀) with hS2
  have spS2 : (freed 144 t).sp = S2.sp := by
    simp only [freed, d.sp]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, E_toNat (by omega), h2, BitVec.toNat_ofNat]
    omega
  have wS2 : (freed 144 t).wr = S2.wr := by simp only [freed, w, entry, allocated, List.tail_cons, hS2]
  have S2sp : S2.sp.toNat = (E0 s₀).toNat - 56 := h2
  have hS2v : ∀ i (hi : i < 10), S2.mem.readW (State.addr (S2.sp + BitVec.ofNat 32 (4 * i))) 32 =
      s₀.gpr savedRegs[i] := fun i hi => by
    have := VG.Proof.Argon2.Arm.storeWords_readW (pushed argRegs s₀).mem
      ((pushed argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length))
      (savedRegs.map (pushed argRegs s₀).gpr) (by
        simp only [List.length_map, List.length_cons, List.length_nil]
        rw [sub_toNat' (by rw [h1]; omega), h1]; omega) (i := i) (by simpa using hi)
    rw [List.getElem_map] at this
    exact this
  have inS2 : ∀ d, d + 4 ≤ 40 → InRegions ((freed 144 t).rd ++ (freed 144 t).wr)
      (State.addr ((freed 144 t).sp + BitVec.ofNat 32 d)) 4 := fun d hd => by
    have hw : ⟨State.addr S2.sp, 40⟩ ∈ S2.wr := by simp [hS2, pushed]
    rw [wS2, spS2, addr_add (by rw [S2sp]; omega)]
    exact ⟨⟨State.addr S2.sp, 40⟩, List.mem_append_right _ hw, Offset.contains_base _ hd (by omega)⟩
  show WP isa (.block (Impl.Argon2.Arm.Derive.savedSlots.map fun p => Instr.ldrSp p.1 p.2)) (freed 144 t) _
  rw [← List.append_nil (List.map _ _)]
  refine restoreSp_ok _ _ _ (by decide) (fun p hpm => ⟨?_, inS2 p.2 ?_⟩) fun u hu ho hm hrd hwr hsp => WP.block_nil ?_
  · simp only [Impl.Argon2.Arm.Derive.savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [Impl.Argon2.Arm.Derive.savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  -- The values restored.
  have key : ∀ j < 9, State.addr (S2.sp + BitVec.ofNat 32 (4 * (j + 1))) =
      State.addr (E s₀ + BitVec.ofNat 32 (148 + 4 * j)) := fun j hj => by
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, S2sp, E_toNat (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 4 * (j + 1)) (by omega), Nat.mod_eq_of_lt (a := 148 + 4 * j) (by omega)]
    omega
  have tv : ∀ j (hj : j < 9), t.mem.readW (State.addr (S2.sp + BitVec.ofNat 32 (4 * (j + 1)))) 32 =
      s₀.gpr (savedRegs[j + 1]?.getD .r0) := fun j hj => by
    rw [key j hj]; exact d.saved j hj
  have hv : ∀ p ∈ Impl.Argon2.Arm.Derive.savedSlots, u.gpr p.1 = s₀.gpr p.1 := by
    intro p hpm
    rw [hu p hpm, spS2]
    have hm' : (freed 144 t).mem = t.mem := rfl
    rw [hm']
    simp only [Impl.Argon2.Arm.Derive.savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tv 0 (by decide)
    · exact tv 1 (by decide)
    · exact tv 2 (by decide)
    · exact tv 3 (by decide)
    · exact tv 4 (by decide)
    · exact tv 5 (by decide)
    · exact tv 6 (by decide)
    · exact tv 7 (by decide)
    · exact tv 8 (by decide)
  refine ⟨⟨fun r hr => ?_, ?_⟩, hQ t _ q (by rw [popped_mem, popped_mem, hm]; rfl)⟩
  · have hr0 : r ≠ .r0 := by rintro rfl; simp [preserved] at hr
    have hr3 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr0, popped_gpr hr3]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hv (.r4, 4) (by decide), hv (.r5, 8) (by decide), hv (.r6, 12) (by decide), hv (.r7, 16) (by decide),
      hv (.r8, 20) (by decide), hv (.r9, 24) (by decide), hv (.r10, 28) (by decide), hv (.r11, 32) (by decide),
      hv (.lr, 36) (by decide)]
  · simp only [popped_sp, hsp, spS2, hS2, pushed_sp, List.length_cons, List.length_nil]
    rw [BitVec.sub_add_cancel, BitVec.sub_add_cancel]

end VG.Proof.Argon2.Arm.Derive
