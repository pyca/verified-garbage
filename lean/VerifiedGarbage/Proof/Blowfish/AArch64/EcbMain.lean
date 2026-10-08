import VerifiedGarbage.Proof.Blowfish.AArch64.Tail

/-!
# The ECB function

`q8`–`q15` are saved in the second half of the working space, the constants
set, the batches and the blocks left run, and `q8`–`q15` restored
(`ecb_correct`).
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-- The callee-saved vector registers, in the order they are saved. -/
def savedReg (k : Nat) : VReg := [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15].getD k .v8

theorem savedReg_inj : ∀ a < 8, ∀ b < 8, a ≠ b → savedReg a ≠ savedReg b := by decide

theorem saveRegs_eq : saveRegs = (List.range 8).map fun k => .strq (savedReg k) .x3 (saveOff + 16 * k) := rfl
theorem saveRegsAt_eq (off : Nat) :
    saveRegsAt off = (List.range 8).map fun k => .strq (savedReg k) .x3 (off + 16 * k) := rfl
theorem restoreRegs_eq : restoreRegs = (List.range 8).map fun k => .ldrq (savedReg k) .x3 (saveOff + 16 * k) := rfl
theorem restoreRegsAt_eq (off : Nat) :
    restoreRegsAt off = (List.range 8).map fun k => .ldrq (savedReg k) .x3 (off + 16 * k) := rfl

/-- The save area: the 128 bytes at `x3 + 128`. -/
def saveR (s : State) : Region := ⟨s.gpr .x3 + BitVec.ofNat 64 128, 128⟩

theorem read_write_self16 (m : Mem) (a : Addr) (v : BitVec 128) : (m.write a 16 v).read a 16 = v :=
  Mem.read_eq_of_bytes fun i hi => by
    simp only [Mem.write, Mem.sub_ofNat_toNat a (show i < 2 ^ 64 by omega), hi, ite_true]

theorem strqs_run (off : Nat) (hoff : off % 16 = 0 ∧ off + 128 ≤ 4096) : ∀ (n : Nat), n ≤ 8 → ∀ (s : State),
    (∀ k < 8, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (off + 16 * k)) 16) →
    ∃ s', runBlock isa ((List.range n).map fun k => .strq (savedReg k) .x3 (off + 16 * k)) s = some s' ∧
      (∀ k < n, s'.mem.read (s.gpr .x3 + BitVec.ofNat 64 (off + 16 * k)) 16 = s.v (savedReg k)) ∧
      Frame [⟨s.gpr .x3 + BitVec.ofNat 64 off, 128⟩] s.mem s'.mem ∧ s' = { s with mem := s'.mem }
  | 0, _, s, _ => ⟨s, runBlock_nil, fun _ h => absurd h (by omega), Frame.refl _ _, rfl⟩
  | n + 1, hn, s, hW => by
    obtain ⟨s', r, v, f, e⟩ := strqs_run off hoff n (by omega) s hW
    have hW' : InRegions s'.wr (s'.gpr .x3 + BitVec.ofNat 64 (off + 16 * n)) 16 := by
      rw [e]; exact hW n (by omega)
    obtain ⟨s'', r', m', o'⟩ := strq_run (t := s') (savedReg n) .x3 (off := off + 16 * n) (by omega) hW'
    have g' : s'.gpr = s.gpr := by rw [e]
    have v' : s'.v = s.v := by rw [e]
    refine ⟨s'', by rw [List.range_succ, List.map_append]; exact cat_run r r',
      fun k hk => ?_, ?_, ?_⟩
    · rw [m', g', v']
      by_cases hkn : k = n
      · subst hkn; exact read_write_self16 _ _ _
      · rw [Mem.read_write_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact v k (by omega)
    · rw [m', g']
      exact f.write (List.mem_singleton.mpr rfl) _ (Offset.contains _ (by omega) (by omega) (by omega))
    · have hv : s''.v = s.v := funext fun x => (o'.v x (List.not_mem_nil)).trans (by rw [v'])
      rw [o'.eq, e]; simp only [hv]

def savedRegs : List VReg := [.v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15]

theorem savedReg_mem : ∀ k < 8, savedReg k ∈ savedRegs := by decide

theorem ldrqs_run (off : Nat) (hoff : off % 16 = 0 ∧ off + 128 ≤ 4096) : ∀ (n : Nat), n ≤ 8 → ∀ (s : State),
    (∀ k < 8, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (off + 16 * k)) 16) →
    ∃ s', runBlock isa ((List.range n).map fun k => .ldrq (savedReg k) .x3 (off + 16 * k)) s = some s' ∧
      (∀ k < n, s'.v (savedReg k) = s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (off + 16 * k)) 16) ∧
      VOnly savedRegs s s'
  | 0, _, s, _ => ⟨s, runBlock_nil, fun _ h => absurd h (by omega), VOnly.refl _ _⟩
  | n + 1, hn, s, hR => by
    obtain ⟨s', r, v, o⟩ := ldrqs_run off hoff n (by omega) s hR
    obtain ⟨s'', r', v', o'⟩ := ldrq_run (t := s') (savedReg n) .x3 (off := off + 16 * n)
      (by omega) (by rw [o.rd, o.wr, o.gpr]; exact hR n (by omega))
    refine ⟨s'', by rw [List.range_succ, List.map_append]; exact cat_run r r', fun k hk => ?_,
      o.trans (VOnly.mono o' (by simp; exact savedReg_mem n (by omega)))⟩
    by_cases hkn : k = n
    · subst hkn; rw [v', o.mem, o.gpr]
    · rw [o'.2 _ (by simp; exact savedReg_inj k (by omega) n (by omega) hkn), v k (by omega)]

/-- `movz` and `dup .16b` of 64 and 128: the constants. -/
theorem constants_run (s : State) :
    ∃ s', runBlock isa constants s = some s' ∧ Consts s' ∧
      (∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ VOnly [c64, c128] { s with gpr := s'.gpr } s' := by
  let s₁ := s.write .x .x6 ((64 : BitVec 16).setWidth 64 <<< (16 * 0))
  let s₂ := s₁.setV c64 (ofVBytes fun _ => (s₁.gpr .x6).setWidth 8)
  let s₃ := s₂.write .x .x6 ((128 : BitVec 16).setWidth 64 <<< (16 * 0))
  let s₄ := s₃.setV c128 (ofVBytes fun _ => (s₃.gpr .x6).setWidth 8)
  refine ⟨s₄, rfl, ⟨fun e he => ?_, fun e he => ?_⟩, fun r hr => ?_, rfl, rfl, rfl, rfl, ⟨rfl, fun r hr => ?_⟩⟩
  · simp only [s₄, s₃, s₂, v_setV_of_ne _ _ (by decide : c64 ≠ c128), v_write, v_setV_self]
    rw [vbyte_ofVBytes _ he]; rfl
  · simp only [s₄, v_setV_self]
    rw [vbyte_ofVBytes _ he]; rfl
  · simp only [s₄, s₃, s₂, s₁, gpr_setV, gpr_write_of_ne _ _ _ hr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₄, s₃, s₂, s₁, v_setV_of_ne _ _ hr.2, v_write, v_setV_of_ne _ _ hr.1]

/-- What the function may assume: the schedule readable, the `n` blocks and
the working space writable, apart from each other. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 4168⟩]
  wr : s.wr = [⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, 256⟩]
  keyData : (⟨s.gpr .x0, 4168⟩ : Region).Disjoint ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
  keyBuf : (⟨s.gpr .x0, 4168⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  dataBuf : (⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  fit : (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64

theorem ecb_eq (up : Bool) : ecb up =
    .seq (.block (saveRegs ++ constants)) (.seq (wide up) (.seq (tail up) (.block restoreRegs))) := rfl

theorem save_off (s : State) {k : Nat} (hk : k < 8) :
    (⟨s.gpr .x3, 256⟩ : Region).Contains (s.gpr .x3 + BitVec.ofNat 64 (saveOff + 16 * k)) 16 :=
  Offset.contains_base _ (by simp only [saveOff]; omega) (by simp only [saveOff]; omega)

/-- Every block becomes its encryption or decryption, and `q8`–`q15` are
restored. -/
theorem ecb_correct (up : Bool) {s : State} (P : EcbPre s) :
    WP isa (ecb up) s (fun s' => (∀ b < (s.gpr .x2).toNat, blockAt s'.mem (wAt (s.gpr .x1) b) =
      blockOut (scheduleAt s.mem (s.gpr .x0)) up (blockAt s.mem (wAt (s.gpr .x1) b))) ∧
      ∀ r ∈ savedRegs, s'.v r = s.v r) := by
  let n := (s.gpr .x2).toNat
  let D := s.gpr .x1
  let S := s.gpr .x0
  let k := n % 16
  have bufW : (⟨s.gpr .x3, 256⟩ : Region) ∈ s.wr := by rw [P.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  -- the prologue
  obtain ⟨s₁, r₁, v₁, f₁, e₁⟩ := strqs_run saveOff (by decide) 8 (by decide) s fun k hk => ⟨_, bufW, save_off s hk⟩
  obtain ⟨s₂, r₂, c₂, g₂, m₂, rd₂, wr₂, sp₂, o₂⟩ := constants_run s₁
  have g₁ : s₁.gpr = s.gpr := by rw [e₁]
  have hg₂ : ∀ r, r ≠ .x6 → s₂.gpr r = s.gpr r := fun r hr => by rw [g₂ r hr, g₁]
  have hrd₂ : s₂.rd = s.rd := by rw [rd₂, e₁]
  have hwr₂ : s₂.wr = s.wr := by rw [wr₂, e₁]
  have E : Env s₂ := by
    have h0 := hg₂ .x0 (by decide); have h1 := hg₂ .x1 (by decide)
    have h2 := hg₂ .x2 (by decide); have h3 := hg₂ .x3 (by decide)
    exact ⟨by rw [hrd₂, h0]; exact P.rd, by rw [hwr₂, h1, h2, h3]; exact P.wr,
      by rw [h0, h1, h2]; exact P.keyData, by rw [h0, h3]; exact P.keyBuf,
      by rw [h1, h2, h3]; exact P.dataBuf, by rw [h1, h2]; exact P.fit, c₂⟩
  have saveSep : (saveR s).Disjoint ⟨s.gpr .x1, 8 * n⟩ :=
    (P.dataBuf.sub_right (Offset.sub_base _ (by omega))).symm
  have hn₂ : (s₂.gpr .x2).toNat = n := by rw [hg₂ _ (by decide)]
  rw [ecb_eq]
  apply WP.seq
  refine WP.of_runBlock ⟨s₂, by rw [saveRegs_eq]; exact cat_run r₁ r₂, ?_⟩
  apply WP.seq
  apply WP.mono (wide_ok up E)
  intro s₃ w
  rw [hn₂] at w
  have g := w.gpr
  have h0 : s₃.gpr .x0 = S := (g _ (by simp [WideRegs])).trans (hg₂ _ (by decide))
  have h3 : s₃.gpr .x3 = s.gpr .x3 := (g _ (by simp [WideRegs])).trans (hg₂ _ (by decide))
  have h1 : s₃.gpr .x1 = wAt D (n - k) := by rw [w.x1, hg₂ _ (by decide)]
  have hl : 8 * n < 2 ^ 64 := by have := E.len; rw [hn₂] at this; exact this
  have hfit : D.toNat + 8 * n ≤ 2 ^ 64 := P.fit
  have sub₁ : Region.Sub ⟨s₃.gpr .x1, 8 * k⟩ ⟨D, 8 * n⟩ := by
    rw [h1]; exact Offset.sub_base _ (by omega)
  have T : TailEnv s₃ k := by
    refine ⟨Nat.mod_lt _ (by decide), w.x2, fun i hi => ?_, ?_, fun off m h => ?_, ?_, ?_, ?_, ?_⟩
    · rw [w.wr, hwr₂, P.wr, h1, wAt_wAt]
      exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [w.wr, hwr₂, P.wr, h3]; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [w.rd, w.wr, h0, hrd₂, hwr₂, P.rd]
      exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [h0]; exact P.keyData.sub_right sub₁
    · rw [h0, h3]; exact P.keyBuf
    · rw [h3]; exact P.dataBuf.sub_left sub₁
    · exact ⟨fun e he => by rw [w.v _ (by decide)]; exact E.consts.1 e he,
        fun e he => by rw [w.v _ (by decide)]; exact E.consts.2 e he⟩
  apply WP.seq
  apply WP.mono (tail_ok up T)
  intro s₄ t
  -- the epilogue
  have hR₄ : ∀ j < 8, InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x3 + BitVec.ofNat 64 (saveOff + 16 * j)) 16 := by
    intro j hj
    rw [t.rd, t.wr, t.gpr _ (by simp [TailRegs]), w.rd, w.wr, h3, hrd₂, hwr₂]
    exact ⟨_, List.mem_append_right _ bufW, save_off s hj⟩
  obtain ⟨s₅, r₅, v₅, o₅⟩ := ldrqs_run saveOff (by decide) 8 (by decide) s₄ hR₄
  have m₂' : s₂.mem = s₁.mem := m₂
  have hm₅ : s₅.mem = s₄.mem := o₅.mem
  have dataB : (⟨D, 8 * n⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩ := P.dataBuf
  -- the prologue left the data and the schedule as they were
  have pro : Frame [saveR s] s.mem s₂.mem := by rw [m₂']; exact f₁
  have hK₂ : scheduleAt s₂.mem S = scheduleAt s.mem S :=
    scheduleAt_eq_of_frame S pro fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact P.keyBuf.sub_right (Offset.sub_base _ (by omega))
  have hB₂ : ∀ b < n, blockAt s₂.mem (wAt D b) = blockAt s.mem (wAt D b) := fun b hb =>
    blockAt_frame pro fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (saveSep.sub_right (Offset.sub_base _ (by omega))).symm
  refine WP.of_runBlock ⟨s₅, by rw [restoreRegs_eq]; exact r₅, ?_, ?_⟩
  · intro b hb
    rw [hm₅]
    have h1' : s₂.gpr .x1 = D := hg₂ _ (by decide)
    have h0' : s₂.gpr .x0 = S := hg₂ _ (by decide)
    by_cases hbk : b < n - k
    · have e := w.done b hbk
      rw [h1', h0', hK₂, hB₂ b hb] at e
      rw [← e]
      refine blockAt_frame t.frame fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h1]; exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
      · rw [h3]; exact dataB.sub_left (Offset.sub_base _ (by omega)) |>.sub_right (Region.sub_prefix (by omega))
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - k + j := ⟨b - (n - k), by omega⟩
      have e := t.out j (by omega)
      rw [h1, wAt_wAt, h0] at e
      rw [e]
      have hK : scheduleAt s₃.mem S = scheduleAt s₂.mem S :=
        scheduleAt_eq_of_frame S w.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [h1']; exact P.keyData.sub_right (Region.sub_prefix (by omega))
      have hB : blockAt s₃.mem (wAt D (n - k + j)) = blockAt s₂.mem (wAt D (n - k + j)) :=
        blockAt_frame w.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [h1']; exact Offset.disjoint_base D (by omega) (by omega)
      rw [hK, hB, hK₂, hB₂ _ hb]
  · -- the saved registers, from the save area, which nothing else wrote
    have ss : ∀ j < 8, s₅.v (savedReg j) = s.v (savedReg j) := by
      intro j hj
      have hc : (saveR s).Contains (s.gpr .x3 + BitVec.ofNat 64 (saveOff + 16 * j)) 16 :=
        Offset.contains _ (by simp only [saveOff]; omega) (by simp only [saveOff]; omega) (by omega)
      rw [v₅ j hj, t.gpr _ (by simp [TailRegs]), h3,
        t.frame.read hc (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact saveSep.sub_right sub₁
          · rw [h3]; exact Offset.disjoint_base _ (by omega) (by omega)) (by decide),
        w.frame.read hc (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [hg₂ _ (by decide)]; exact saveSep.sub_right (Region.sub_prefix (by omega))) (by decide),
        m₂', v₁ j hj]
    intro r hr
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ss 0 (by decide)
    · exact ss 1 (by decide)
    · exact ss 2 (by decide)
    · exact ss 3 (by decide)
    · exact ss 4 (by decide)
    · exact ss 5 (by decide)
    · exact ss 6 (by decide)
    · exact ss 7 (by decide)

end VG.Proof.Blowfish.AArch64
