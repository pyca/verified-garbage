import VerifiedGarbage.Proof.Sm4.Arm.KeyInit

/-!
# The loop of the SM4 key schedule on ARMv7

Each iteration runs four rounds of the key schedule (`rounds4_ok .key`),
puts the state's words in the tail buffer as a block (`fromBs_step`), and
stores them to the schedule as little-endian words (`extract_ok`): the
first block's words, last first, byte-reversed (`rev`). The schedule's
pointer waits in slot `nSlot` (the rounds use every register).
-/

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS)
open VG.Proof.Sm4 (quads ofBlock outBlock keyInit rkOf getLsbD_outBlock' writeW32_byte writeW32_other)

/-! ## The extraction -/

/-- The extraction, after its first `k` words: the schedule's bytes at `A`
before `4 k` hold the tail buffer's first block, last byte first. -/
structure ExtInv (s₀ : State) (b P : BitVec 32) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  ptr : s.gpr u7 = P
  bytes : ∀ t < 4 * k, ∀ j < 8, (s.mem (State.addr P + BitVec.ofNat 64 t)).getLsbD j =
    ((tailBlock s₀ 0).getD (15 - t) 0).getLsbD j
  frame : Frame [⟨State.addr P, 4 * k⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The extraction's word `k`. -/
theorem extStep_ok {s₀ s : State} {b P : BitVec 32} {k : Nat} (hk : k < 4)
    (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) (hP : P.toNat + 16 ≤ 2 ^ 32)
    (hw : ScrIn s₀.wr b) (hS : ∀ t < 4, InRegions s₀.wr (State.addr P + BitVec.ofNat 64 (4 * t)) 4)
    (hsep : Region.Disjoint ⟨State.addr P, 16⟩ ⟨State.addr b, 4 * slots⟩) (hb₀ : s₀.gpr sb = b)
    (hi : ExtInv s₀ b P k s) :
    ∃ s', runBlock isa [ldS t0 (tailAt 0 (3 - k)), .rev t0 t0, .str t0 u7 (4 * k)] s = some s' ∧
      ExtInv s₀ b P (k + 1) s' := by
  have hb := addr_toNat b
  have hPn := addr_toNat P
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s t0 sb (k := tailAt 0 (3 - k)) hi.base
    (tailAt_lt (by decide) (by omega)) (by rw [hi.wr]; exact hw)
  let s₂ := s₁.setReg t0 (rev (s₁.gpr t0))
  have e₂ : runBlock isa [.rev t0 t0] s₁ = some s₂ := by
    rw [runBlock_cons, show exec (.rev t0 t0) s₁ = some s₂ from rfl, runStep_some, runBlock_nil]
  have u7₂ : s₂.gpr u7 = P := by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide), hi.ptr]
  have eA : State.addr (s₂.gpr u7 + BitVec.ofNat 32 (4 * k)) = State.addr P + BitVec.ofNat 64 (4 * k) := by
    rw [u7₂, addr_add (by omega)]
  have wr₂ : s₂.wr = s₀.wr := by show s₁.wr = _; rw [wr₁, hi.wr]
  have hin : InRegions s₂.wr (State.addr (s₂.gpr u7 + BitVec.ofNat 32 (4 * k))) 4 :=
    by rw [wr₂, eA]; exact hS k hk
  -- The slot read is the one on entry.
  have hslot : s.mem.readW (wordAddr b (tailAt 0 (3 - k))) 32 = s₀.mem.readW (wordAddr b (tailAt 0 (3 - k))) 32 := by
    have hk' := tailAt_lt (c := 0) (w := 3 - k) (by decide) (by omega)
    rw [slot_addr (by omega)]
    refine hi.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hsep.sub_left (Region.sub_prefix (by omega))).sub_right
      (VG.Offset.sub_base _ (by omega))).symm
  have v₂ : s₂.gpr t0 = rev (s₀.mem.readW (wordAddr b (tailAt 0 (3 - k))) 32) := by
    rw [RegUpd.gpr_setReg_self, v₁, hslot]
  let s₃ : State := { s₂ with mem := s₂.mem.writeW (State.addr P + BitVec.ofNat 64 (4 * k)) (s₂.gpr t0) }
  have e₃ : runBlock isa [.str t0 u7 (4 * k)] s₂ = some s₃ := by
    rw [runBlock_cons, exec_str (by omega) hin, eA, runStep_some, runBlock_nil]
  have mem₂ : s₂.mem = s.mem := m₁
  refine ⟨s₃, ?_, ⟨by show s₂.gpr sb = b; rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide), hi.base],
    u7₂, fun t ht j hj => ?_, ?_, fun r hr => ?_, by show s₁.rd = _; rw [rd₁, hi.rd], wr₂,
    by show s₁.sp = _; rw [sp₁, hi.sp]⟩⟩
  · rw [show ([ldS t0 (tailAt 0 (3 - k)), .rev t0 t0, .str t0 u7 (4 * k)] : List Instr) =
      [.ldr t0 sb (4 * tailAt 0 (3 - k))] ++ ([.rev t0 t0] ++ [.str t0 u7 (4 * k)]) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · show (s₂.mem.writeW _ _ _).getLsbD j = _
    by_cases hlt : t < 4 * k
    · rw [writeW32_other _ _ _ _ (VG.Proof.Sm4.off_sub_not _ (Or.inl hlt) (by omega) (by decide) (by omega)),
        mem₂]
      exact hi.bytes t hlt j hj
    · have hc : t - 4 * k < 4 := by omega
      rw [show State.addr P + BitVec.ofNat 64 t =
          State.addr P + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 (t - 4 * k) by
        rw [VG.Offset.add_add, show 4 * k + (t - 4 * k) = t by omega],
        writeW32_byte _ _ _ hc hj, v₂, rev_bit _ hc hj,
        tailBlock_bit s₀ (c := 0) (i := 15 - t) hb₀ hfit (by decide) (by omega) hj,
        show (15 - t) / 4 = 3 - k by omega, show (15 - t) % 4 = 3 - (t - 4 * k) by omega]
  · refine (hi.frame.sub fun r hr => ⟨⟨State.addr P, 4 * (k + 1)⟩, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩).trans ?_
    show Frame _ s.mem (s₂.mem.writeW _ _)
    rw [mem₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Offset.contains_base _ (by omega) (by omega))
  · show (s₁.setReg t0 _).gpr r = _
    rw [RegUpd.gpr_setReg_of_ne _ _ hr, o₁ r hr, hi.regs r hr]

/-- The schedule's bytes `16 m … 16 m + 15`: the words of the tail buffer's
first block, the last first, each little-endian; the schedule's pointer
stepped. -/
theorem extract_ok {s : State} {b S : BitVec 32} {m : Nat} (hm : m < 8) (hb : s.gpr sb = b) (hw : ScrIn s.wr b)
    (hSfit : S.toNat + 128 ≤ 2 ^ 32) (hS : (⟨State.addr S, 128⟩ : Region) ∈ s.wr)
    (hsep : Region.Disjoint ⟨State.addr S, 128⟩ ⟨State.addr b, 4 * slots⟩)
    (hn : s.mem.readW (wordAddr b nSlot) 32 = S + BitVec.ofNat 32 (16 * m)) :
    ∃ s', runBlock isa extract s = some s' ∧
      (∀ t < 16, ∀ j < 8, (s'.mem (State.addr S + BitVec.ofNat 64 (16 * m + t))).getLsbD j =
        ((tailBlock s 0).getD (15 - t) 0).getLsbD j) ∧
      s'.mem.readW (wordAddr b nSlot) 32 = S + BitVec.ofNat 32 (16 * (m + 1)) ∧
      Frame [⟨State.addr S + BitVec.ofNat 64 (16 * m), 16⟩, ⟨wordAddr b nSlot, 4⟩] s.mem s'.mem ∧
      (∀ r, r ≠ t0 → r ≠ u7 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hfit := hw.fit
  have hSn := addr_toNat S
  let P := S + BitVec.ofNat 32 (16 * m)
  have hPa : State.addr P = State.addr S + BitVec.ofNat 64 (16 * m) := addr_add (by omega)
  have hPn : P.toNat + 16 ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega)]; omega
  have subP : Region.Sub ⟨State.addr P, 16⟩ ⟨State.addr S, 128⟩ := by rw [hPa]; exact VG.Offset.sub_base _ (by omega)
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s u7 sb (k := nSlot) hb (by decide) hw
  rw [hn] at v₁
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hb]
  have hw₁ : ScrIn s₁.wr b := by rw [wr₁]; exact hw
  have hS₁ : ∀ t < 4, InRegions s₁.wr (State.addr P + BitVec.ofNat 64 (4 * t)) 4 := fun t ht =>
    ⟨_, by rw [wr₁]; exact hS, by rw [hPa, VG.Offset.add_add]; exact VG.Offset.contains_base _ (by omega) (by omega)⟩
  have hsepP : Region.Disjoint ⟨State.addr P, 16⟩ ⟨State.addr b, 4 * slots⟩ := hsep.sub_left subP
  have i0 : ExtInv s₁ b P 0 s₁ := ⟨hb₁, v₁, fun t ht => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨s₂, e₂, i₂⟩ := extStep_ok (k := 0) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i0
  obtain ⟨s₃, e₃, i₃⟩ := extStep_ok (k := 1) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i₂
  obtain ⟨s₄, e₄, i₄⟩ := extStep_ok (k := 2) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i₃
  obtain ⟨s₅, e₅, i₅⟩ := extStep_ok (k := 3) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i₄
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := addImm_ok s₅ u7 u7 16 (by decide)
  obtain ⟨s₇, e₇, m₇, g₇, rd₇, wr₇, sp₇, -, f₇⟩ := stSlot_ok s₆ u7 sb (k := nSlot)
    (by rw [o₆ _ (by decide), i₅.base]) (by decide) (by rw [wr₆, i₅.wr, wr₁]; exact hw)
  have hmem₇ : s₇.mem = s₅.mem.writeW (wordAddr b nSlot) (P + BitVec.ofNat 32 16) := by
    rw [m₇, m₆, r₆, i₅.ptr]; rfl
  have hblk : tailBlock s₁ 0 = tailBlock s 0 := by simp only [tailBlock, m₁, hb₁, hb]
  have dN : Region.Disjoint ⟨State.addr P, 16⟩ ⟨wordAddr b nSlot, 4⟩ :=
    hsepP.sub_right (slot_sub hfit (by decide))
  refine ⟨s₇, ?_, fun t ht j hj => ?_, ?_, ?_, fun r h0 h7 => ?_, by rw [rd₇, rd₆, i₅.rd, rd₁],
    by rw [wr₇, wr₆, i₅.wr, wr₁], by rw [sp₇, sp₆, i₅.sp, sp₁]⟩
  · rw [extract, show (List.range 4).flatMap (fun k => ([ldS t0 (tailAt 0 (3 - k)), .rev t0 t0,
        .str t0 u7 (4 * k)] : List Instr)) = [ldS t0 (tailAt 0 (3 - 0)), .rev t0 t0, .str t0 u7 (4 * 0)] ++
        ([ldS t0 (tailAt 0 (3 - 1)), .rev t0 t0, .str t0 u7 (4 * 1)] ++
        ([ldS t0 (tailAt 0 (3 - 2)), .rev t0 t0, .str t0 u7 (4 * 2)] ++
        [ldS t0 (tailAt 0 (3 - 3)), .rev t0 t0, .str t0 u7 (4 * 3)])) from rfl,
      show ([.dp .add u7 u7 (.imm 16), stS nSlot u7] : List Instr) =
        [.dp .add u7 u7 (.imm 16)] ++ [.str u7 sb (4 * nSlot)] from rfl,
      runBlock_app, runBlock_app,
      show ([ldS u7 nSlot] : List Instr) = [.ldr u7 sb (4 * nSlot)] from rfl, e₁, Option.bind_some,
      runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, runBlock_app, e₄, Option.bind_some,
      e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, e₇]
  · have hx : (⟨State.addr P, 16⟩ : Region).Contains (State.addr P + BitVec.ofNat 64 t) 1 :=
      VG.Offset.contains_base _ (by omega) (by omega)
    rw [show State.addr S + BitVec.ofNat 64 (16 * m + t) = State.addr P + BitVec.ofNat 64 t by
        rw [hPa, VG.Offset.add_add],
      hmem₇, writeW32_other _ _ _ _ (out_of_disj dN hx (Region.contains_self _ _)), i₅.bytes t (by omega) j hj,
      hblk]
  · rw [hmem₇, Mem.readW_writeW_self32]
    simp only [P]
    rw [VG.Offset.add_add, show 16 * m + 16 = 16 * (m + 1) by omega]
  · rw [← m₁]
    refine (i₅.frame.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; rw [hPa]; exact fun _ h => h⟩).trans ?_
    rw [← m₆]
    exact f₇.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [g₇, o₆ r h7, i₅.regs r h0, o₁ r h7]

end VG.Proof.Sm4.Arm
