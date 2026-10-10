import VerifiedGarbage.Proof.Seed.Arm.KeyRound

/-!
# SEED key expansion on ARMv7: the whole function

`expandKey_wp`: with the working space as an argument (`expandKeyArm`),
`expandKey` saves the callee-saved registers and the schedule's pointer,
loads the key's words (`keyLoad_ok`), computes the 32 inputs of `G`
(`keyRounds_ok`), and `G` of eight at a time to the schedule
(`keyChunk_ok`); RFC 4269 §2.3's schedule is `G` of these inputs
(`expandKey_eq`).
-/

namespace VG.Proof.Seed

open VG VG.Arm VG.Impl.Seed.Arm

/-- Key expansion on ARMv7 with its working space at `r2`. -/
def expandKeyArm : Contract Arm.isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 16⟩
    let sched : Region := ⟨State.addr (s.gpr .r1), 128⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 4 * slots⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧
      (s.gpr .r0).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 128 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 4 * slots ≤ 2 ^ 32
  post s s' :=
    Spec.Seed.scheduleAt s'.mem (State.addr (s.gpr .r1)) =
      Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (State.addr (s.gpr .r0)))
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.sp = s₂.sp

end VG.Proof.Seed

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Seed.Arm VG.Proof.Seed
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS)
open VG.Arm.Straight (wordAddr add_ofNat_ofNat in_off)

/-! ## Copies between slots -/

/-- `ldr t0, [sb, #4 a]; str t0, [sb, #4 d]` for each `(a, d)`. -/
def copiesCode (L : List (Nat × Nat)) : List Instr := L.flatMap fun p => [ldS t0 p.1, stS p.2 t0]

theorem copies_ok {s : State} (h : Room s) {n : Nat} (hn : n ≤ slots) :
    ∀ (L : List (Nat × Nat)), (∀ p ∈ L, p.1 < slots ∧ p.2 < n) → (∀ p ∈ L, ∀ q ∈ L, p.1 ≠ q.2) →
      (L.map (·.2)).Nodup →
      ∃ s', runBlock isa (copiesCode L) s = some s' ∧
        (∀ p ∈ L, slotW s' p.2 = slotW s p.1) ∧
        (∀ j < slots, j ∉ L.map (·.2) → slotW s' j = slotW s j) ∧
        (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        Frame [⟨State.addr (s.gpr sb), 4 * n⟩] s.mem s'.mem
  | [], _, _, _ => ⟨s, runBlock_nil, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | p :: L, hL, hd, hnd => by
    have hp := hL p List.mem_cons_self
    have hpd : p.2 < slots := by omega
    let s₁ := setMem (s.setReg t0 (slotW s p.1)) (s.mem.writeW (slotA s p.2) (slotW s p.1))
    have e₁ : runBlock isa [ldS t0 p.1, stS p.2 t0] s = some s₁ := by
      rw [runBlock_cons, exec_ldS h hp.1, runStep_some, runBlock_cons,
        exec_stS (room_setReg h (by decide) _) hpd, runStep_some, runBlock_nil]
      simp only [s₁, slotA_setReg _ (show t0 ≠ sb by decide), gpr_setReg_self, mem_setReg]
    have h₁ : Room s₁ := room_setMem (room_setReg h (by decide) _) _
    have sb₁ : s₁.gpr sb = s.gpr sb := by
      simp only [s₁, gpr_setMem, gpr_setReg_of_ne _ _ (show sb ≠ t0 by decide)]
    have sl₁ : ∀ j < slots, slotW s₁ j = if j = p.2 then slotW s p.1 else slotW s j := by
      intro j hj
      rw [show s₁ = setMem _ _ from rfl, slotW_setMem, slotA_setReg _ (by decide)]
      exact slotW_setMem_write h hpd hj _
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', o', g', rd', wr', sp', f'⟩ := copies_ok h₁ hn L (fun q hq => hL q (List.mem_cons_of_mem _ hq))
      (fun q hq q' hq' => hd q (List.mem_cons_of_mem _ hq) q' (List.mem_cons_of_mem _ hq')) hnd.2
    have hfit := h.fit
    refine ⟨s', ?_, fun q hq => ?_, fun j hj hjL => ?_, fun r hr => ?_, by rw [rd']; rfl, by rw [wr']; rfl,
      by rw [sp']; rfl, ?_⟩
    · rw [copiesCode, List.flatMap_cons, runBlock_append, e₁, Option.bind_some]; exact e'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [o' _ (by have := (hL q List.mem_cons_self).2; omega) hnd.1, sl₁ _ hpd, ite_eq_left rfl]
      · rw [v' q hq, sl₁ _ (hL q (List.mem_cons_of_mem _ hq)).1,
          ite_eq_right (hd q (List.mem_cons_of_mem _ hq) p List.mem_cons_self)]
    · simp only [List.map_cons, List.mem_cons, not_or] at hjL
      rw [o' j hj hjL.2, sl₁ j hj, ite_eq_right hjL.1]
    · rw [g' r hr]
      simp only [s₁, gpr_setMem, gpr_setReg_of_ne _ _ hr]
    · refine Frame.trans ?_ (by rw [sb₁] at f'; exact f')
      show Frame _ s.mem (s.mem.writeW (slotA s p.2) (slotW s p.1))
      refine (Frame.refl _ _).writeW List.mem_cons_self _ ?_
      rw [slots_eq] at hfit hn
      exact Straight.slot_contains _ hp.2 (by omega)

/-! ## Stores to the schedule -/

/-- `ldr t0, [sb, #4 a]; str t0, [kp, #4 o]` for each `(a, o)`. -/
def storesCode (L : List (Nat × Nat)) : List Instr := L.flatMap fun p => [ldS t0 p.1, .str t0 kp (4 * p.2)]

/-- The schedule at `P` (in `kp`), writable and apart from the scratch buffer. -/
structure OutPre (s : State) (P : BitVec 32) : Prop where
  room : Room s
  kp : s.gpr kp = P
  mem : (⟨State.addr P, 128⟩ : Region) ∈ s.wr
  fit : P.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr P, 128⟩ (scratchR s)

theorem stores_ok {P : BitVec 32} :
    ∀ (L : List (Nat × Nat)) (s : State), OutPre s P → (∀ p ∈ L, p.1 < slots ∧ p.2 < 32) →
      (L.map (·.2)).Nodup →
      ∃ s', runBlock isa (storesCode L) s = some s' ∧
        (∀ p ∈ L, s'.mem.readW (State.addr P + BitVec.ofNat 64 (4 * p.2)) 32 = slotW s p.1) ∧
        (∀ o < 32, o ∉ L.map (·.2) → s'.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32 =
          s.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32) ∧
        (∀ j < slots, slotW s' j = slotW s j) ∧
        (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        Frame [⟨State.addr P, 128⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, runBlock_nil, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | p :: L, s, hs, hL, hnd => by
    have hp := hL p List.mem_cons_self
    have hP := hs.fit
    have hA : State.addr (P + BitVec.ofNat 32 (4 * p.2)) = State.addr P + BitVec.ofNat 64 (4 * p.2) :=
      addr_add (by omega)
    let s₁ := s.setReg t0 (slotW s p.1)
    let s₂ := setMem s₁ (s.mem.writeW (State.addr P + BitVec.ofNat 64 (4 * p.2)) (slotW s p.1))
    have e₁ : runBlock isa [ldS t0 p.1, .str t0 kp (4 * p.2)] s = some s₂ := by
      rw [runBlock_cons, exec_ldS hs.room hp.1, runStep_some, runBlock_cons,
        exec_str (by omega) (by
          rw [show s₁.gpr kp = P by simp only [s₁, gpr_setReg_of_ne _ _ (show kp ≠ t0 by decide), hs.kp]]
          exact in_off hs.mem hP (by omega) (by omega)),
        runStep_some, runBlock_nil]
      simp only [s₂, s₁, gpr_setReg_of_ne _ _ (show kp ≠ t0 by decide), hs.kp, gpr_setReg_self, mem_setReg, hA]
      rfl
    have hsep : ∀ j < slots, Region.Disjoint ⟨State.addr P + BitVec.ofNat 64 (4 * p.2), 4⟩ ⟨slotA s j, 4⟩ := by
      intro j hj
      refine (hs.sep.sub_left (Offset.sub_base _ (by omega))).sub_right ?_
      have := hs.room.fit
      rw [slots_eq] at hj this
      rw [slotA, slot_addr (by omega)]
      exact Offset.sub_base _ (by rw [slots_eq]; omega)
    have sl₂ : ∀ j < slots, slotW s₂ j = slotW s j := by
      intro j hj
      show (s.mem.writeW _ _).readW (wordAddr (s₁.gpr sb) j) 32 = _
      rw [show s₁.gpr sb = s.gpr sb from gpr_setReg_of_ne _ _ (by decide)]
      exact Mem.readW_writeW_sep (fun x h1 h2 => hsep j hj x h2 h1) (by decide)
    have sb₂ : s₂.gpr sb = s.gpr sb := by
      show (s.setReg t0 (slotW s p.1)).gpr sb = _; exact gpr_setReg_of_ne _ _ (by decide)
    have hs₂ : OutPre s₂ P := ⟨hs.room.congr sb₂ rfl,
      by simp only [s₂, gpr_setMem, s₁, gpr_setReg_of_ne _ _ (show kp ≠ t0 by decide), hs.kp], hs.mem, hP,
      by unfold scratchR; rw [sb₂]; exact hs.sep⟩
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', o', sl', g', rd', wr', sp', f'⟩ := stores_ok L s₂ hs₂
      (fun q hq => hL q (List.mem_cons_of_mem _ hq)) hnd.2
    have hw : ∀ o < 32, s₂.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32 =
        if o = p.2 then slotW s p.1 else s.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32 := by
      intro o ho
      show (s.mem.writeW _ _).readW _ 32 = _
      split
      · rename_i e; subst e; exact Mem.readW_writeW_self32 _ _ _
      · rename_i e
        exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)
    refine ⟨s', ?_, fun q hq => ?_, fun o ho hoL => ?_, fun j hj => by rw [sl' j hj, sl₂ j hj],
      fun r hr => ?_, by rw [rd']; rfl, by rw [wr']; rfl, by rw [sp']; rfl, ?_⟩
    · rw [storesCode, List.flatMap_cons, runBlock_append, e₁, Option.bind_some]; exact e'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [o' _ hp.2 hnd.1, hw _ hp.2, ite_eq_left rfl]
      · rw [v' q hq, sl₂ _ (hL q (List.mem_cons_of_mem _ hq)).1]
    · simp only [List.map_cons, List.mem_cons, not_or] at hoL
      rw [o' o ho hoL.2, hw o ho, ite_eq_right hoL.1]
    · rw [g' r hr]; exact gpr_setReg_of_ne _ _ hr
    · refine Frame.trans ?_ f'
      show Frame _ s.mem (s.mem.writeW _ (slotW s p.1))
      exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

/-! ## `G` of eight inputs, to the schedule -/

theorem nodup_map_range {f : Nat → Nat} (hf : ∀ a b, f a = f b → a = b) (n : Nat) :
    ((List.range n).map f).Nodup :=
  List.Pairwise.map f (fun a b hab h => hab (hf a b h)) List.nodup_range

def chunkIn (c : Nat) : List (Nat × Nat) := (List.range 8).map fun w => (uSlot (8 * c + w), tSlot w)
def chunkOut (c : Nat) : List (Nat × Nat) := (List.range 8).map fun w => (tSlot w, 8 * c + w)

theorem keyChunk_eq (c : Nat) :
    keyChunk c = copiesCode (chunkIn c) ++ g8 ++ storesCode (chunkOut c) := by
  simp only [keyChunk, copiesCode, storesCode, chunkIn, chunkOut, List.flatMap_map]

theorem keyChunk_ok {c : Nat} (hc : c < 4) {s : State} (h : Room s) {P : BitVec 32}
    (hp : s.gpr kp = P) (hm : (⟨State.addr P, 128⟩ : Region) ∈ s.wr) (hf : P.toNat + 128 ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨State.addr P, 128⟩ (scratchR s)) :
    ∃ s', runBlock isa (keyChunk c) s = some s' ∧
      (∀ w < 8, s'.mem.readW (State.addr P + BitVec.ofNat 64 (4 * (8 * c + w))) 32 =
        Spec.Seed.g (slotW s (uSlot (8 * c + w)))) ∧
      (∀ o < 32, (o < 8 * c ∨ 8 * c + 8 ≤ o) → s'.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32 =
        s.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32) ∧
      (∀ j, 56 ≤ j → j < slots → slotW s' j = slotW s j) ∧ Room s' ∧ s'.gpr sb = s.gpr sb ∧ s'.gpr kp = P ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [workR s, ⟨State.addr P, 128⟩] s.mem s'.mem := by
  have hS := slots_eq
  -- The inputs to `G`'s words.
  obtain ⟨s₁, e₁, v₁, o₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := copies_ok h (n := tailSlot) (by decide) (chunkIn c)
    (by intro p hp; simp only [chunkIn, List.mem_map, List.mem_range] at hp; obtain ⟨w, hw, rfl⟩ := hp
        simp [uSlot, aSlot, tSlot, tailSlot, slots_eq]; omega)
    (by intro p hp q hq; simp only [chunkIn, List.mem_map, List.mem_range] at hp hq
        obtain ⟨w, hw, rfl⟩ := hp; obtain ⟨w', hw', rfl⟩ := hq; simp [uSlot, aSlot, tSlot]; omega)
    (by simp only [chunkIn, List.map_map]
        exact nodup_map_range (fun a b hab => by simpa [tSlot] using hab) 8)
  have sb₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide)
  have h₁ : Room s₁ := h.congr sb₁ wr₁
  have k₁ : ∀ j, 56 ≤ j → j < slots → slotW s₁ j = slotW s j := fun j h1 h2 => o₁ j h2 (by
    simp only [chunkIn, List.map_map, List.mem_map, List.mem_range, Function.comp, not_exists, not_and]
    intro w hw he; simp [tSlot] at he; omega)
  -- `G`.
  obtain ⟨s₂, e₂, gv₂, k₂, h₂, rd₂, wr₂, sp₂, g₂, f₂⟩ := g8_lanes h₁
  have sb₂ : s₂.gpr sb = s.gpr sb := by rw [g₂ _ (by decide), sb₁]
  have hO : OutPre s₂ P :=
    ⟨h₂, by rw [g₂ _ (by decide), g₁ _ (by decide), hp], by rw [wr₂, wr₁]; exact hm, hf,
      by unfold scratchR; rw [sb₂]; exact hsep⟩
  -- The stores.
  obtain ⟨s', e', v', o', sl', g', rd', wr', sp', f'⟩ := stores_ok (chunkOut c) s₂ hO
    (by intro p hp; simp only [chunkOut, List.mem_map, List.mem_range] at hp; obtain ⟨w, hw, rfl⟩ := hp
        simp [tSlot, slots_eq]; omega)
    (by simp only [chunkOut, List.map_map]
        exact nodup_map_range (fun a b hab => by simpa using hab) 8)
  have sb' : s'.gpr sb = s.gpr sb := by rw [g' _ (by decide), sb₂]
  -- `s`'s memory outside the scratch buffer through the first three steps.
  have fr₃ : Frame [workR s] s.mem s₂.mem := by
    exact (by simpa [workR] using f₁ : Frame [workR s] s.mem s₁.mem).trans (by simpa [workR, sb₁] using f₂)
  refine ⟨s', ?_, fun w hw => ?_, fun o ho ho' => ?_, fun j h1 h2 => ?_, h.congr sb' (by rw [wr', wr₂, wr₁]), sb',
    by rw [g' _ (by decide)]; exact hO.kp, by rw [rd', rd₂, rd₁], by rw [wr', wr₂, wr₁], by rw [sp', sp₂, sp₁], ?_⟩
  · rw [keyChunk_eq, runBlock_append, runBlock_append, e₁, Option.bind_some, e₂, Option.bind_some, e']
  · rw [v' (tSlot w, 8 * c + w) (by simp only [chunkOut, List.mem_map, List.mem_range]; exact ⟨w, hw, rfl⟩),
      tSlot_lane, show slotW s₂ (tSlot 0 + w) = lv s₂ (tSlot 0) w from rfl, gv₂ w hw, lv, ← tSlot_lane,
      v₁ (uSlot (8 * c + w), tSlot w) (by simp only [chunkIn, List.mem_map, List.mem_range]; exact ⟨w, hw, rfl⟩)]
  · rw [o' o ho (by
      simp only [chunkOut, List.map_map, List.mem_map, List.mem_range, Function.comp, not_exists, not_and]
      intro w hw he; omega)]
    refine fr₃.readW (r := ⟨State.addr P + BitVec.ofNat 64 (4 * o), 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hsep.sub_left (Offset.sub_base _ (by omega))).sub_right (workR_sub_scratch s)
  · rw [sl' j h2, k₂ j h1 h2, k₁ j h1 h2]
  · refine (fr₃.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (f'.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)

/-- The four chunks of `G`. -/
theorem keyChunks_ok {s : State} (h : Room s) {P : BitVec 32}
    (hp : s.gpr kp = P) (hm : (⟨State.addr P, 128⟩ : Region) ∈ s.wr) (hf : P.toNat + 128 ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨State.addr P, 128⟩ (scratchR s)) :
    ∀ n ≤ 4, ∃ s', runBlock isa ((List.range n).flatMap keyChunk) s = some s' ∧
      (∀ o < 8 * n, s'.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32 =
        Spec.Seed.g (slotW s (uSlot o))) ∧
      (∀ j, 56 ≤ j → j < slots → slotW s' j = slotW s j) ∧ Room s' ∧ s'.gpr sb = s.gpr sb ∧ s'.gpr kp = P ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [workR s, ⟨State.addr P, 128⟩] s.mem s'.mem := by
  intro n hn
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun o ho => by omega, fun _ _ _ => rfl, h, rfl, hp, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, e₁, v₁, k₁, h₁, sb₁, kp₁, rd₁, wr₁, sp₁, f₁⟩ := ih (by omega)
    obtain ⟨s₂, e₂, v₂, o₂, k₂, h₂, sb₂, kp₂, rd₂, wr₂, sp₂, f₂⟩ := keyChunk_ok (c := n) (by omega) h₁
      kp₁ (by rw [wr₁]; exact hm) hf (by unfold scratchR; rw [sb₁]; exact hsep)
    refine ⟨s₂, ?_, fun o ho => ?_, fun j h1 h2 => by rw [k₂ j h1 h2, k₁ j h1 h2], h₂, by rw [sb₂, sb₁], kp₂,
      by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁], f₁.trans (by simpa [workR, sb₁] using f₂)⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_append, e₁, Option.bind_some, List.flatMap_singleton, e₂]
    · by_cases hlo : o < 8 * n
      · rw [o₂ o (by omega) (.inl hlo), v₁ o hlo]
      · rw [show o = 8 * n + (o - 8 * n) by omega, v₂ _ (by omega),
          k₁ _ (by simp [uSlot, aSlot]) (uSlot_lt (by omega))]

/-! ## The key's words -/

theorem keyLoad_eq : keyLoad = [.ldr .r4 .r0 0, .rev .r4 .r4, .ldr .r5 .r0 4, .rev .r5 .r5,
    .ldr .r6 .r0 8, .rev .r6 .r6, .ldr .r7 .r0 12, .rev .r7 .r7] := rfl

theorem exec_rev (s : State) (d m : Reg) : exec (.rev d m) s = some (s.setReg d (rev (s.gpr m))) := rfl

theorem ldRev_ok {t : State} {K : BitVec 32} (d : Reg) (h0 : t.gpr .r0 = K)
    (hK : (⟨State.addr K, 16⟩ : Region) ∈ t.rd ++ t.wr) (hfit : K.toNat + 16 ≤ 2 ^ 32) {o : Nat} (ho : o ≤ 12) :
    ∃ t', runBlock isa [.ldr d .r0 o, .rev d d] t = some t' ∧
      t'.gpr d = byteRev32 (t.mem.readW (State.addr K + BitVec.ofNat 64 o) 32) ∧
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  have hin : InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r0 + BitVec.ofNat 32 o)) 4 := by
    rw [h0]; exact in_off hK hfit (by omega) (by omega)
  rw [runBlock_cons, exec_ldr (by omega) hin, runStep_some, runBlock_cons, exec_rev, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [gpr_setReg_self, gpr_setReg_self, h0, addr_add (by omega)]; rfl
  · rw [gpr_setReg_of_ne _ _ hr, gpr_setReg_of_ne _ _ hr]

theorem keyLoad_ok {s : State} {K : BitVec 32} (hr0 : s.gpr .r0 = K)
    (hK : (⟨State.addr K, 16⟩ : Region) ∈ s.rd ++ s.wr) (hfit : K.toNat + 16 ≤ 2 ^ 32) :
    ∃ s', runBlock isa keyLoad s = some s' ∧ kw s' = keyWords (Spec.Seed.blockAt s.mem (State.addr K)) 0 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldRev_ok .r4 hr0 hK hfit (o := 0) (by decide)
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := ldRev_ok .r5 (by rw [o₁ _ (by decide), hr0])
    (by rw [rd₁, wr₁]; exact hK) hfit (o := 4) (by decide)
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := ldRev_ok .r6 (by rw [o₂ _ (by decide), o₁ _ (by decide), hr0])
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact hK) hfit (o := 8) (by decide)
  obtain ⟨s₄, e₄, v₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := ldRev_ok .r7
    (by rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hr0])
    (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hK) hfit (o := 12) (by decide)
  refine ⟨s₄, ?_, ?_, fun r h4 h5 h6 h7 => by rw [o₄ r h7, o₃ r h6, o₂ r h5, o₁ r h4],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁], by rw [sp₄, sp₃, sp₂, sp₁]⟩
  · rw [keyLoad_eq, show ([.ldr .r4 .r0 0, .rev .r4 .r4, .ldr .r5 .r0 4, .rev .r5 .r5,
      .ldr .r6 .r0 8, .rev .r6 .r6, .ldr .r7 .r0 12, .rev .r7 .r7] : List Instr) =
      [.ldr .r4 .r0 0, .rev .r4 .r4] ++ ([.ldr .r5 .r0 4, .rev .r5 .r5] ++ ([.ldr .r6 .r0 8, .rev .r6 .r6] ++
      [.ldr .r7 .r0 12, .rev .r7 .r7])) from rfl, runBlock_append, e₁, Option.bind_some, runBlock_append, e₂,
      Option.bind_some, runBlock_append, e₃, Option.bind_some, e₄]
  · simp only [kw, keyWords]
    rw [Proof.Seed.wordAt_blockAt _ _ (by decide), Proof.Seed.wordAt_blockAt _ _ (by decide),
      Proof.Seed.wordAt_blockAt _ _ (by decide), Proof.Seed.wordAt_blockAt _ _ (by decide),
      o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), v₁, o₄ _ (by decide), o₃ _ (by decide), v₂,
      o₄ _ (by decide), v₃, v₄, m₃, m₂, m₁]

/-! ## The whole function -/

theorem expandKey_wp {s₀ : State} (hp : expandKeyArm.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ expandKeyArm.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB⟩ := hp
  let b := s₀.gpr .r2
  let K := s₀.gpr .r0
  let P := s₀.gpr .r1
  have fitB' : b.toNat + 4 * slots ≤ 2 ^ 32 := fitB
  have fitK' : K.toNat + 16 ≤ 2 ^ 32 := fitK
  have fitS' : P.toNat + 128 ≤ 2 ^ 32 := fitS
  have hwS : ScrIn s₀.wr b := ⟨by rw [hwr]; simp [b], fitB⟩
  have hwP : (⟨State.addr P, 128⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [P]
  have hrK : (⟨State.addr K, 16⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [K]
  -- The prologue.
  obtain ⟨s₁, e₁, sv₁, g₁, rd₁, wr₁, sp₁, f₁, -⟩ := save_ok (base := .r2) hwS rfl
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movR_ok s₁ sb .r2
  have sb₂ : s₂.gpr sb = b := by rw [r₂, g₁]
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := movR_ok s₂ kp .r1
  have sb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), sb₂]
  have g₀₃ : ∀ r, r ≠ sb → r ≠ kp → s₃.gpr r = s₀.gpr r := fun r h1 h2 => by rw [o₃ r h2, o₂ r h1, g₁]
  have f₀₃ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₃.mem := by rw [m₃, m₂]; exact f₁
  have h₃ : Room s₃ := ⟨by unfold scratchR; rw [sb₃, wr₃, wr₂, wr₁]; exact hwS.mem, by rw [sb₃]; exact fitB'⟩
  have ptr₃ : s₃.gpr kp = P := by rw [r₃, o₂ _ (by decide), g₁]
  -- The key, as on entry.
  have key₃ : Spec.Seed.blockAt s₃.mem (State.addr K) = Spec.Seed.blockAt s₀.mem (State.addr K) := by
    apply Vector.ext; intro i hi
    simp only [Spec.Seed.blockAt, Vector.getElem_ofFn]
    exact f₀₃.bytes (R := ⟨State.addr K, 16⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by simp only; omega) hi
  -- The key's words.
  obtain ⟨s₄, e₄, k₄, g₄, m₄, rd₄, wr₄, sp₄⟩ := keyLoad_ok (s := s₃) (K := K) (g₀₃ _ (by decide) (by decide))
    (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact List.mem_append_left _ hrK) fitK'
  have sb₄ : s₄.gpr sb = b := by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), sb₃]
  have h₄ : Room s₄ := h₃.congr (by rw [sb₄, sb₃]) wr₄
  have sl₄ : ∀ j, slotW s₄ j = slotW s₃ j := fun j => by simp only [slotW, m₄, sb₄, sb₃]
  -- The inputs of `G`.
  let key := Spec.Seed.blockAt s₀.mem (State.addr K)
  obtain ⟨s₅, e₅, h₅, -, v₅, o₅, g₅, rd₅, wr₅, sp₅, f₅⟩ := keyRounds_ok key h₄ (by rw [k₄, key₃]) 16 (Nat.le_refl _)
  have sb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide), sb₄]
  have keep₅ : ∀ j < slots, uSlot 32 ≤ j → slotW s₅ j = slotW s₃ j := fun j h1 h2 => by
    rw [o₅ j h1 (.inr h2), sl₄]
  -- `G`, to the schedule.
  obtain ⟨s₆, e₆, v₆, k₆, h₆, sb₆, -, rd₆, wr₆, sp₆, f₆⟩ := keyChunks_ok h₅ (P := P)
    (by rw [g₅ _ (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide), ptr₃])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwP) fitS'
    (by unfold scratchR; rw [sb₅]; exact dSB) 4 (Nat.le_refl _)
  -- The epilogue.
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇, sp₇⟩ := movR_ok s₆ .r12 sb
  have sv₆ : Saved s₀ b s₆.mem := by
    intro i hi
    have hs : savedSlot + i < slots := by rw [savedSlot_eq, slots_eq]; omega
    have := k₆ (savedSlot + i) (by rw [savedSlot_eq]; omega) hs
    simp only [slotW, sb₆, sb₅] at this
    rw [this, show s₅.mem.readW (wordAddr b (savedSlot + i)) 32 = slotW s₅ (savedSlot + i) by
      simp only [slotW, sb₅], keep₅ _ hs (by simp [uSlot, aSlot, savedSlot_eq]; omega), slotW, sb₃, m₃, m₂]
    exact sv₁ i hi
  obtain ⟨s₈, e₈, rg₈, -, m₈, -, -, -⟩ := restore_ok (s₀ := s₀) (b := b)
    (by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwS) (by rw [r₇, sb₆, sb₅]) (by rw [m₇]; exact sv₆)
  refine WP.of_runBlock ⟨s₈, ?_, rg₈, ?_⟩
  · rw [runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append,
      runBlock_append, e₁, Option.bind_some,
      show ([movR sb .r2, movR kp .r1] : List Instr) = [movR sb .r2] ++ [movR kp .r1] from rfl,
      runBlock_append, e₂, Option.bind_some, e₃, Option.bind_some, e₄, Option.bind_some, e₅, Option.bind_some,
      e₆, Option.bind_some, e₇, Option.bind_some, e₈]
  · show Spec.Seed.scheduleAt s₈.mem (State.addr P) = Spec.Seed.expandKey key
    rw [Proof.Seed.expandKey_eq]
    apply Vector.ext; intro i hi
    rw [Proof.Seed.scheduleAt_readW _ _ i hi, Vector.getElem_ofFn, m₈, m₇, v₆ i (by omega), v₅ i (by omega)]

end VG.Proof.Seed.Arm
