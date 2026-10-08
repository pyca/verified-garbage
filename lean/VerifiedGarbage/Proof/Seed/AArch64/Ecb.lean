import VerifiedGarbage.Proof.Seed.AArch64.Setup

/-!
# The function on AArch64

After moving the scratch buffer to `x5` and saving the callee-saved
registers in it, the function runs batches of up to 16 blocks until none are
left (`loop_ok`), then restores the registers (`ecb_ok`).
-/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Impl.Aes.AArch64
  VG.Proof.Seed

theorem toNat_ofNat_le {m n : Nat} (hm : m ≤ n) (hn : 16 * n ≤ 2 ^ 64) : (BitVec.ofNat 64 m).toNat = m := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : Spec.Seed.blockAt m' p = Spec.Seed.blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Seed.blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 16⟩) hd (by show 16 ≤ 2 ^ 64; decide) hi

/-- The keys are as in `m` wherever the frame's regions leave them. -/
theorem keysAt_frame {d : Spec.Seed.Direction} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    {j : Nat} (hd : ∀ r ∈ rs, (⟨kp d p j, 8⟩ : Region).Disjoint r) : keysAt d m' p j = keysAt d m p j := by
  simp only [keysAt]
  congr 1
  · exact hf.readW (contains_prefix (by decide)) hd (by decide)
  · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
    exact hf.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega) (by omega)) hd (by decide)

/-! ## The loop of batches -/

/-- What the loop may assume throughout, of the state it starts in. -/
structure BatchesEnv (d : Spec.Seed.Direction) (s₀ : State) (n : Nat) : Prop where
  room : Room s₀
  dataIn : (⟨s₀.gpr .x1, 16 * n⟩ : Region) ∈ s₀.wr
  dataSep : Region.Disjoint ⟨s₀.gpr .x1, 16 * n⟩ (scratchR s₀)
  fit : 16 * n ≤ 2 ^ 64
  keys : KeysOk d s₀ (s₀.gpr .x0)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s₀.gpr .x0) j, 8⟩ ⟨s₀.gpr .x1, 16 * n⟩

/-- `m` blocks left, the first `n - m` done. -/
structure BatchesInv (d : Spec.Seed.Direction) (s₀ : State) (n m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ n
  x2 : s.gpr .x2 = BitVec.ofNat 64 m
  x1 : s.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 (16 * (n - m))
  regs : ∀ r ∈ [Reg.x0, .x5], s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n - m, Spec.Seed.blockAt s.mem (s₀.gpr .x1 + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .x0))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [workR s₀, ⟨s₀.gpr .x1, 16 * (n - m)⟩] s₀.mem s.mem

structure BatchesPost (d : Spec.Seed.Direction) (s₀ : State) (n : Nat) (s : State) : Prop where
  regs : ∀ r ∈ [Reg.x0, .x5], s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n, Spec.Seed.blockAt s.mem (s₀.gpr .x1 + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .x0))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [workR s₀, ⟨s₀.gpr .x1, 16 * n⟩] s₀.mem s.mem

theorem BatchesInv.batchPre {d : Spec.Seed.Direction} {s₀ : State} {n m : Nat} (E : BatchesEnv d s₀ n)
    {s : State} (h : BatchesInv d s₀ n m s) : BatchPre d s := by
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  have hm : (s.gpr .x2).toNat = m := by rw [h.x2]; exact toNat_ofNat_le h.le E.fit
  have r9 : s.gpr .x5 = s₀.gpr .x5 := h.regs _ (by simp)
  have rdi : s.gpr .x0 = s₀.gpr .x0 := h.regs _ (by simp)
  have scr : scratchR s = scratchR s₀ := by simp only [scratchR, r9]
  let D := s₀.gpr .x1
  have hsub : Region.Sub ⟨s.gpr .x1, 16 * min (s.gpr .x2).toNat 16⟩ ⟨D, 16 * n⟩ := by
    rw [h.x1, hm]; exact Offset.sub_base _ (by omega)
  refine ⟨room_congr E.room r9 h.wr, by omega, fun b hb w hw => ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [h.wr, h.x1, Offset.add_ofNat_add_ofNat]
    rw [hm] at hb
    exact ⟨_, E.dataIn, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [scr]; exact E.dataSep.sub_left hsub
  · rw [rdi]
    intro j hj
    obtain ⟨a, b, c⟩ := E.keys j hj
    exact ⟨by rw [h.rd, h.wr]; exact a, by rw [h.rd, h.wr]; exact b, by rw [scr]; exact c⟩
  · rw [rdi]; exact (E.keyData j hj).sub_right hsub

theorem loop_ok (d : Spec.Seed.Direction) {s₀ : State} {n : Nat} (E : BatchesEnv d s₀ n) (m : Nat) (s : State)
    (hs : BatchesInv d s₀ n m s) : WP isa (.loop (batch d) (.nonzero .x .x2)) s (BatchesPost d s₀ n) := by
  refine WP.loop (M := isa) (BatchesInv d s₀ n) ?_ m s hs
  intro m s h
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  apply WP.mono (batch_ok d (h.batchPre E))
  intro s' q
  have hm : (s.gpr .x2).toNat = m := by rw [h.x2]; exact toNat_ofNat_le h.le E.fit
  obtain ⟨qdone, qrsi, qrdx, qregs, qsp, qrd, qwr, qframe⟩ := q
  rw [hm] at qdone qrsi qrdx qframe
  generalize hk : min m 16 = k at qdone qrsi qrdx qframe
  have hk1 : 1 ≤ k := by omega
  have hkm : k ≤ m := by omega
  let D := s₀.gpr .x1
  let S := s₀.gpr .x0
  have r9 : s.gpr .x5 = s₀.gpr .x5 := h.regs _ (by simp)
  have rdi : s.gpr .x0 = S := h.regs _ (by simp)
  have workR_eq : workR s = workR s₀ := by simp only [workR, r9]
  rw [h.x1, workR_eq] at qframe
  rw [h.x1] at qrsi qdone
  rw [rdi] at qdone
  -- the memory written so far
  have frame' : Frame [workR s₀, ⟨D, 16 * (n - (m - k))⟩] s₀.mem s'.mem := by
    have f₁ : Frame [workR s₀, ⟨D, 16 * (n - (m - k))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 16 * (n - (m - k))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Region.sub_prefix (by omega)⟩
    have f₂ : Frame [workR s₀, ⟨D, 16 * (n - (m - k))⟩] s.mem s'.mem := qframe.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 16 * (n - (m - k))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Offset.sub_base _ (by omega)⟩
    exact f₁.trans f₂
  have workSep : ∀ b, b < n → (⟨D + BitVec.ofNat 64 (16 * b), 16⟩ : Region).Disjoint (workR s₀) := fun b hb =>
    (E.dataSep.sub_left (Offset.sub_base _ (by omega))).sub_right
      (Region.sub_prefix (by unfold scratchSlots; omega))
  have done' : ∀ b < n - (m - k), Spec.Seed.blockAt s'.mem (D + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.crypt (keysAt d s₀.mem S) (Spec.Seed.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * b))) := by
    intro b hb
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine blockAt_frame qframe fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact workSep b (by omega)
      · exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega⟩
      have e := qdone j (by omega)
      rw [Offset.add_ofNat_add_ofNat, show 16 * (n - m) + 16 * j = 16 * (n - m + j) by omega] at e
      rw [e]
      have hK : ∀ i < 16, keysAt d s.mem S i = keysAt d s₀.mem S i := fun i hi =>
        keysAt_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          obtain ⟨-, -, hdis⟩ := E.keys i hi
          rcases hr with rfl | rfl
          · exact hdis.sub_right (Region.sub_prefix (by unfold scratchSlots; omega))
          · exact (E.keyData i hi).sub_right (Region.sub_prefix (by omega))
      have hB : Spec.Seed.blockAt s.mem (D + BitVec.ofNat 64 (16 * (n - m + j))) =
          Spec.Seed.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (n - m + j))) :=
        blockAt_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact workSep _ (by omega)
          · exact Offset.disjoint_base D (by omega) (by omega)
      rw [hB]
      exact crypt_congr hK _
  have rdx' : s'.gpr .x2 = BitVec.ofNat 64 (m - k) := by
    rw [qrdx, h.x2, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hkm]
  have zf' : isa.eval (.nonzero .x .x2) s' = some (BitVec.ofNat 64 (m - k) != 0) := by
    show some (s'.read .x .x2 != 0) = _
    rw [read_x, rdx']
  have regs' : ∀ r ∈ [Reg.x0, .x5], s'.gpr r = s₀.gpr r := fun r hr =>
    (qregs r hr).trans (h.regs r hr)
  have sp' : s'.sp = s₀.sp := qsp.trans h.sp
  have rd' := qrd.trans h.rd
  have wr' := qwr.trans h.wr
  by_cases hend : m ≤ 16
  · have hkm' : k = m := by omega
    left
    refine ⟨?_, regs', sp', rd', wr', ?_, ?_⟩
    · rw [zf', hkm', Nat.sub_self]; rfl
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at done'; exact done'
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at frame'; exact frame'
  · have hk16 : k = 16 := by omega
    right
    refine ⟨?_, m - k, by omega, ⟨by omega, by omega, rdx', ?_, regs', sp', rd', wr', done', frame'⟩⟩
    · rw [zf']
      have : (BitVec.ofNat 64 (m - k) != 0) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        rw [toNat_ofNat_le (show m - k ≤ n by omega) E.fit] at this
        have z : (0 : BitVec 64).toNat = 0 := rfl
        omega
      rw [this]
    · rw [qrsi, Offset.add_ofNat_add_ofNat]; congr 2; omega

/-! ## The keys -/

/-- Where round `j + 1`'s key is in the schedule. -/
def keyOff : Spec.Seed.Direction → Nat → Nat
  | .encrypt, j => 8 * j
  | .decrypt, j => 8 * (15 - j)

theorem keyOff_le (d : Spec.Seed.Direction) {j : Nat} (hj : j < 16) : keyOff d j + 8 ≤ 128 := by
  cases d <;> simp only [keyOff] <;> omega

theorem kp_start_const (d : Spec.Seed.Direction) :
    ∀ j < 16, BitVec.ofNat 64 (keyStart d) + BitVec.ofNat 64 j * stepW d = BitVec.ofNat 64 (keyOff d j) := by
  cases d <;> decide

theorem kp_start (d : Spec.Seed.Direction) (S : Addr) {j : Nat} (hj : j < 16) :
    kp d (S + BitVec.ofNat 64 (keyStart d)) j = S + BitVec.ofNat 64 (keyOff d j) := by
  rw [kp, BitVec.add_assoc, kp_start_const d j hj]

/-- The block function in the direction `d`. -/
def cipher (d : Spec.Seed.Direction) (K : Spec.Seed.Schedule) (b : Spec.Seed.Block) : Spec.Seed.Block :=
  match d with
  | .encrypt => Spec.Seed.encryptBlock K b
  | .decrypt => Spec.Seed.decryptBlock K b

theorem crypt_keysAt (d : Spec.Seed.Direction) (m : Mem) (S : Addr) (b : Spec.Seed.Block) :
    Spec.Seed.crypt (keysAt d m (S + BitVec.ofNat 64 (keyStart d))) b = cipher d (Spec.Seed.scheduleAt m S) b := by
  cases d
  · show _ = Spec.Seed.crypt (Spec.Seed.roundKey (Spec.Seed.scheduleAt m S)) b
    refine crypt_congr (fun j hj => ?_) b
    rw [keysAt, kp_start _ _ hj, roundKey_readW _ _ hj]
    simp only [keyOff]
  · show _ = Spec.Seed.crypt (fun j => Spec.Seed.roundKey (Spec.Seed.scheduleAt m S) (15 - j)) b
    refine crypt_congr (fun j hj => ?_) b
    rw [keysAt, kp_start _ _ hj, roundKey_readW _ _ (by omega)]
    simp only [keyOff]

theorem ecb_blocks (K : Spec.Seed.Schedule) (d : Spec.Seed.Direction) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, Spec.Seed.blockAt m' (D + BitVec.ofNat 64 (16 * b)) =
      cipher d K (Spec.Seed.blockAt m (D + BitVec.ofNat 64 (16 * b)))) :
    Spec.Seed.blocksAt m' D n = Spec.Seed.ecb K d (Spec.Seed.blocksAt m D n) := by
  cases d <;>
  · simp only [Spec.Seed.blocksAt, Spec.Seed.ecb, List.map_map]
    apply List.map_congr_left
    intro b hb
    rw [Function.comp_apply]
    exact h b (List.mem_range.mp hb)

/-! ## The function -/

/-- What the function needs: the scratch buffer and the data writable, the
schedule readable, apart from each other. -/
structure EcbPre (s : State) : Prop where
  scratch : (⟨s.gpr .x3, 8 * scratchSlots⟩ : Region) ∈ s.wr
  dataIn : (⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .x0, 128⟩ : Region) ∈ s.rd
  keyData : (⟨s.gpr .x0, 128⟩ : Region).Disjoint ⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩
  keyBuf : (⟨s.gpr .x0, 128⟩ : Region).Disjoint ⟨s.gpr .x3, 8 * scratchSlots⟩
  dataBuf : (⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, 8 * scratchSlots⟩
  fit : 16 * (s.gpr .x2).toNat ≤ 2 ^ 64

/-- What the function does: every block of the data becomes its encryption or
decryption, the callee-saved registers it uses are restored, and only the
scratch buffer and the data change. -/
structure EcbPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  saved : ∀ p ∈ Impl.Seed.AArch64.savedRegs, s'.gpr p.1 = s.gpr p.1
  done : ∀ b < (s.gpr .x2).toNat, Spec.Seed.blockAt s'.mem (s.gpr .x1 + BitVec.ofNat 64 (16 * b)) =
    cipher d (Spec.Seed.scheduleAt s.mem (s.gpr .x0))
      (Spec.Seed.blockAt s.mem (s.gpr .x1 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [⟨s.gpr .x3, 8 * scratchSlots⟩, ⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩] s.mem s'.mem

theorem savedRegs_ok : ∀ p ∈ Impl.Seed.AArch64.savedRegs, p.2 < scratchSlots ∧ p.1 ≠ .x5 ∧ 112 ≤ p.2 := by
  decide

theorem setup_eq (d : Spec.Seed.Direction) : setup d =
    [movR .x5 .x3] ++ (Impl.Seed.AArch64.savedRegs.map fun p => (p.2, p.1)).map (fun p => stS p.1 p.2) ++
      ([.addImm .x .x0 .x0 (keyStart d)] : List Instr) := rfl

theorem restore_eq : restore = Impl.Seed.AArch64.savedRegs.map (fun p => ldS p.1 p.2) := rfl

theorem keyStart_lt (d : Spec.Seed.Direction) : keyStart d < 4096 := by cases d <;> decide

theorem ecb_ok (d : Spec.Seed.Direction) {s : State} (h : EcbPre s) : WP isa (ecb d) s (EcbPost d s) := by
  let n := (s.gpr .x2).toNat
  let D := s.gpr .x1
  let S := s.gpr .x0
  have hn := h.fit
  rw [ecb]
  apply WP.seq
  -- `x5 := x3`
  let s₁ := s.write .x .x5 (s.gpr .x3)
  have e₁ : runBlock isa [movR .x5 .x3] s = some s₁ := by
    rw [runBlock_cons, exec_movR, runStep_some, runBlock_nil]
  have r9₁ : s₁.gpr .x5 = s.gpr .x3 := by simp [s₁, gpr_write]
  have g₁ : ∀ r, r ≠ .x5 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
  have scr₁ : scratchR s₁ = ⟨s.gpr .x3, 8 * scratchSlots⟩ := by simp only [scratchR, r9₁]
  have room₁ : Room s₁ := by unfold Room; rw [scr₁]; exact h.scratch
  -- the saved registers
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, sp₂, f₂, set₂, keep₂⟩ := stores_ok room₁
    (Impl.Seed.AArch64.savedRegs.map fun p => (p.2, p.1)) (by decide) (by decide)
  -- the key pointer
  let s₅ := s₂.write .x .x0 (s₂.read .x .x0 + BitVec.ofNat _ (keyStart d))
  refine WP.of_runBlock ⟨s₅, by
    rw [setup_eq]
    exact runBlock_trans (runBlock_trans e₁ e₂)
      (by rw [runBlock_cons, exec_addImm_x (keyStart_lt d), runStep_some, runBlock_nil]), ?_⟩
  -- the state after the setup
  have G₅ : ∀ r, r ≠ .x5 → r ≠ .x0 → s₅.gpr r = s.gpr r := fun r a b => by
    rw [gpr_write_of_ne _ _ _ b, g₂, g₁ r a]
  have r9₅ : s₅.gpr .x5 = s.gpr .x3 := by rw [gpr_write_of_ne _ _ _ (by decide), g₂, r9₁]
  have rdi₅ : s₅.gpr .x0 = S + BitVec.ofNat 64 (keyStart d) := by
    simp only [s₅, gpr_write_self, BitVec.setWidth_eq, read_x, g₂, g₁ _ (show Reg.x0 ≠ .x5 by decide)]; rfl
  have rd₅ : s₅.rd = s.rd := by simp only [s₅, rd_write, rd₂]; rfl
  have wr₅ : s₅.wr = s.wr := by simp only [s₅, wr_write, wr₂]; rfl
  have sp₅ : s₅.sp = s.sp := by simp only [s₅, sp_write, sp₂]; rfl
  have mem₅ : s₅.mem = s₂.mem := by simp only [s₅, mem_write]
  have slot₅ : ∀ k, slotW s₅ k = slotW s₂ k := fun k => by
    show s₅.mem.readW (Straight.wordAddr (s₅.gpr .x5) k) 64 = s₂.mem.readW (Straight.wordAddr (s₂.gpr .x5) k) 64
    rw [mem₅, r9₅, g₂, r9₁]
  have scr₅ : scratchR s₅ = ⟨s.gpr .x3, 8 * scratchSlots⟩ := by simp only [scratchR, r9₅]
  have room₅ : Room s₅ := by unfold Room; rw [scr₅, wr₅]; exact h.scratch
  have f₅ : Frame [⟨s.gpr .x3, 8 * scratchSlots⟩] s.mem s₅.mem := by
    rw [mem₅, ← scr₁]; exact f₂
  have zf₅ : isa.eval (.zero .x .x2) s₅ = some (s.gpr .x2 == 0) := by
    show some (s₅.read .x .x2 == 0) = _
    rw [read_x, G₅ _ (by decide) (by decide)]
  have rsi₅ : s₅.gpr .x1 = D := G₅ _ (by decide) (by decide)
  have rdx₅ : s₅.gpr .x2 = s.gpr .x2 := G₅ _ (by decide) (by decide)
  have saved₅ : ∀ p ∈ Impl.Seed.AArch64.savedRegs, slotW s₅ p.2 = s.gpr p.1 := by
    intro p hp
    have hp' := savedRegs_ok p hp
    rw [slot₅, set₂ (p.2, p.1) (List.mem_map_of_mem hp), g₁ _ hp'.2.1]
  -- the keys, in the schedule
  have K₅ : ∀ j < 16, keysAt d s₅.mem (s₅.gpr .x0) j = keysAt d s.mem (S + BitVec.ofNat 64 (keyStart d)) j := by
    intro j hj
    rw [rdi₅]
    refine keysAt_frame f₅ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rw [kp_start _ _ hj]
    exact h.keyBuf.sub_left (Offset.sub_base _ (keyOff_le d hj))
  have B₅ : ∀ b < n, Spec.Seed.blockAt s₅.mem (D + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.blockAt s.mem (D + BitVec.ofNat 64 (16 * b)) := fun b hb =>
    blockAt_frame f₅ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.dataBuf.sub_left (Offset.sub_base _ (by omega))
  -- after the loop (or none), the registers restored
  have finish : ∀ s₆ : State, BatchesPost d s₅ n s₆ → WP isa (.block restore) s₆ (EcbPost d s) := by
    intro s₆ p
    have r9₆ : s₆.gpr .x5 = s₅.gpr .x5 := p.regs _ (by simp)
    have room₆ : Room s₆ := room_congr room₅ r9₆ p.wr
    obtain ⟨s', run', m', sp', set', keep'⟩ := loads_ok room₆ Impl.Seed.AArch64.savedRegs
      (fun q hq => ⟨(savedRegs_ok q hq).1, (savedRegs_ok q hq).2.1⟩) (by decide)
    refine WP.of_runBlock ⟨s', by rw [restore_eq]; exact run', ?_⟩
    have pf := p.frame
    rw [rsi₅] at pf
    have frame : Frame [⟨s.gpr .x3, 8 * scratchSlots⟩, ⟨D, 16 * n⟩] s.mem s'.mem := by
      rw [m']
      refine (f₅.mono (by simp)).trans (pf.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨_, List.mem_cons_self, ?_⟩
        simp only [workR, r9₅]
        exact Region.sub_prefix (by unfold scratchSlots; omega)
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    refine ⟨fun q hq => ?_, fun b hb => ?_, frame⟩
    · have hq' := savedRegs_ok q hq
      rw [set' q hq, ← saved₅ q hq]
      show s₆.mem.readW (Straight.wordAddr (s₆.gpr .x5) q.2) 64 =
        s₅.mem.readW (Straight.wordAddr (s₅.gpr .x5) q.2) 64
      rw [r9₆]
      refine pf.readW (r := ⟨Straight.wordAddr (s₅.gpr .x5) q.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [workR]
        exact Offset.disjoint_base _ (by omega) (by unfold scratchSlots at hq'; omega)
      · rw [r9₅]
        exact (h.dataBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots at hq' ⊢; omega))).symm
    · have e := p.done b hb
      rw [rsi₅] at e
      rw [m', e, B₅ b hb, crypt_congr K₅, crypt_keysAt]
  apply WP.seq
  apply WP.ite (s.gpr .x2 == 0) zf₅
  · intro hz
    apply WP.block_nil
    have hn0 : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz)
      simpa [n] using this
    refine finish s₅ ⟨fun _ _ => rfl, rfl, rfl, rfl, fun b hb => by omega, ?_⟩
    rw [hn0]; exact Frame.refl _ _
  · intro hz
    have hn1 : 1 ≤ n := by
      have : s.gpr .x2 ≠ 0 := by simpa using hz
      have : (s.gpr .x2).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
      omega
    have E : BatchesEnv d s₅ n := by
      refine ⟨room₅, by rw [rsi₅, wr₅]; exact h.dataIn, by rw [rsi₅, scr₅]; exact h.dataBuf, hn,
        fun j hj => ?_, fun j hj => ?_⟩
      · rw [rdi₅, kp_start _ _ hj, rd₅, wr₅, scr₅]
        have hle := keyOff_le d hj
        refine ⟨⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega) (by omega)⟩, ?_,
          h.keyBuf.sub_left (Offset.sub_base _ hle)⟩
        rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_ofNat_add_ofNat]
        exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega) (by omega)⟩
      · rw [rdi₅, kp_start _ _ hj, rsi₅]
        exact h.keyData.sub_left (Offset.sub_base _ (keyOff_le d hj))
    have I : BatchesInv d s₅ n n s₅ := by
      refine ⟨hn1, Nat.le_refl _, ?_, ?_, fun _ _ => rfl, rfl, rfl, rfl, fun b hb => by omega,
        by rw [Nat.sub_self]; exact Frame.refl _ _⟩
      · rw [rdx₅]; exact BitVec.eq_of_toNat_eq (by simp [n])
      · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add]
    exact WP.mono (loop_ok d E n s₅ I) finish

end VG.Proof.Seed.AArch64
