import VerifiedGarbage.Proof.Seed.X86_64.Setup
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# The function on x86-64

After saving the callee-saved registers and writing the masks to the
scratch buffer, the function runs batches of up to 16 blocks until none are
left (`loop_ok`), then restores the registers (`ecb_ok`).
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Impl.Aes.X86_64 VG.Proof.Seed

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
  dataIn : (⟨s₀.gpr .rsi, 16 * n⟩ : Region) ∈ s₀.wr
  dataSep : Region.Disjoint ⟨s₀.gpr .rsi, 16 * n⟩ (scratchR s₀)
  fit : 16 * n ≤ 2 ^ 64
  keys : KeysOk d s₀ (s₀.gpr .rdi)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s₀.gpr .rdi) j, 8⟩ ⟨s₀.gpr .rsi, 16 * n⟩

/-- `m` blocks left, the first `n - m` done. -/
structure BatchesInv (d : Spec.Seed.Direction) (s₀ : State) (n m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ n
  rdx : s.gpr .rdx = BitVec.ofNat 64 m
  rsi : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 (16 * (n - m))
  regs : ∀ r ∈ [Reg.rdi, .r9, .rsp], s.gpr r = s₀.gpr r
  masks : MasksIn s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n - m, Spec.Seed.blockAt s.mem (s₀.gpr .rsi + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .rdi))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 (16 * b)))
  frame : Frame [workR s₀, ⟨s₀.gpr .rsi, 16 * (n - m)⟩] s₀.mem s.mem

structure BatchesPost (d : Spec.Seed.Direction) (s₀ : State) (n : Nat) (s : State) : Prop where
  regs : ∀ r ∈ [Reg.rdi, .r9, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n, Spec.Seed.blockAt s.mem (s₀.gpr .rsi + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .rdi))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 (16 * b)))
  frame : Frame [workR s₀, ⟨s₀.gpr .rsi, 16 * n⟩] s₀.mem s.mem

theorem BatchesInv.batchPre {d : Spec.Seed.Direction} {s₀ : State} {n m : Nat} (E : BatchesEnv d s₀ n)
    {s : State} (h : BatchesInv d s₀ n m s) : BatchPre d s := by
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  have hm : (s.gpr .rdx).toNat = m := by rw [h.rdx]; exact toNat_ofNat_le h.le E.fit
  have r9 : s.gpr .r9 = s₀.gpr .r9 := h.regs _ (by simp)
  have rdi : s.gpr .rdi = s₀.gpr .rdi := h.regs _ (by simp)
  have scr : scratchR s = scratchR s₀ := by simp only [scratchR, r9]
  let D := s₀.gpr .rsi
  have hsub : Region.Sub ⟨s.gpr .rsi, 16 * min (s.gpr .rdx).toNat 16⟩ ⟨D, 16 * n⟩ := by
    rw [h.rsi, hm]; exact Offset.sub_base _ (by omega)
  refine ⟨room_congr E.room r9 h.wr, h.masks, by omega, fun b hb w hw => ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [h.wr, h.rsi, Offset.add_ofNat_add_ofNat]
    rw [hm] at hb
    exact ⟨_, E.dataIn, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [scr]; exact E.dataSep.sub_left hsub
  · rw [rdi]
    intro j hj
    obtain ⟨a, b, c⟩ := E.keys j hj
    exact ⟨by rw [h.rd, h.wr]; exact a, by rw [h.rd, h.wr]; exact b, by rw [scr]; exact c⟩
  · rw [rdi]; exact (E.keyData j hj).sub_right hsub

theorem loop_ok (d : Spec.Seed.Direction) {s₀ : State} {n : Nat} (E : BatchesEnv d s₀ n) (m : Nat) (s : State)
    (hs : BatchesInv d s₀ n m s) : WP isa (.loop (batch d) .ne) s (BatchesPost d s₀ n) := by
  refine WP.loop (M := isa) (BatchesInv d s₀ n) ?_ m s hs
  intro m s h
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  apply WP.mono (batch_ok d (h.batchPre E))
  intro s' q
  have hm : (s.gpr .rdx).toNat = m := by rw [h.rdx]; exact toNat_ofNat_le h.le E.fit
  obtain ⟨qdone, qrsi, qrdx, qzf, qregs, qmasks, qrd, qwr, qframe⟩ := q
  rw [hm] at qdone qrsi qrdx qzf qframe
  generalize hk : min m 16 = k at qdone qrsi qrdx qzf qframe
  have hk1 : 1 ≤ k := by omega
  have hkm : k ≤ m := by omega
  let D := s₀.gpr .rsi
  let S := s₀.gpr .rdi
  have r9 : s.gpr .r9 = s₀.gpr .r9 := h.regs _ (by simp)
  have rdi : s.gpr .rdi = S := h.regs _ (by simp)
  have workR_eq : workR s = workR s₀ := by simp only [workR, r9]
  rw [h.rsi, workR_eq] at qframe
  rw [h.rsi] at qrsi qdone
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
  have rdx' : s'.gpr .rdx = BitVec.ofNat 64 (m - k) := by
    rw [qrdx, h.rdx, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hkm]
  have zf' : s'.zf = some (BitVec.ofNat 64 (m - k) == 0) := by
    rw [qzf, h.rdx, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hkm]
  have regs' : ∀ r ∈ [Reg.rdi, .r9, .rsp], s'.gpr r = s₀.gpr r := fun r hr =>
    (qregs r hr).trans (h.regs r hr)
  have rd' := qrd.trans h.rd
  have wr' := qwr.trans h.wr
  by_cases hend : m ≤ 16
  · have hkm' : k = m := by omega
    left
    refine ⟨?_, regs', rd', wr', ?_, ?_⟩
    · show s'.zf.map (!·) = some false
      rw [zf', hkm', Nat.sub_self]; rfl
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at done'; exact done'
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at frame'; exact frame'
  · have hk16 : k = 16 := by omega
    right
    refine ⟨?_, m - k, by omega, ⟨by omega, by omega, rdx', ?_, regs', qmasks, rd', wr', done', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [zf']
      have : (BitVec.ofNat 64 (m - k) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        rw [toNat_ofNat_le (show m - k ≤ n by omega) E.fit] at this
        have z : (0 : BitVec 64).toNat = 0 := rfl
        omega
      rw [this]; rfl
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
schedule readable, apart from each other and the return address. -/
structure EcbPre (s : State) : Prop where
  scratch : (⟨s.gpr .rcx, 8 * scratchSlots⟩ : Region) ∈ s.wr
  dataIn : (⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .rdi, 128⟩ : Region) ∈ s.rd
  keyData : (⟨s.gpr .rdi, 128⟩ : Region).Disjoint ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
  keyBuf : (⟨s.gpr .rdi, 128⟩ : Region).Disjoint ⟨s.gpr .rcx, 8 * scratchSlots⟩
  dataBuf : (⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, 8 * scratchSlots⟩
  retData : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
  retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 8 * scratchSlots⟩
  fit : 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64

/-- What the function does: every block of the data becomes its encryption or
decryption, the callee-saved registers and the return address are kept, and
only the scratch buffer and the data change. -/
structure EcbPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  gpr : gprPreserved s s'
  done : ∀ b < (s.gpr .rdx).toNat, Spec.Seed.blockAt s'.mem (s.gpr .rsi + BitVec.ofNat 64 (16 * b)) =
    cipher d (Spec.Seed.scheduleAt s.mem (s.gpr .rdi))
      (Spec.Seed.blockAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (16 * b)))
  frame : Frame [⟨s.gpr .rcx, 8 * scratchSlots⟩, ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩] s.mem s'.mem

theorem savedRegs_ok : ∀ p ∈ Impl.Seed.X86_64.savedRegs, p.2 < scratchSlots ∧ p.1 ≠ .r9 ∧ 125 ≤ p.2 := by decide

theorem setup_eq (d : Spec.Seed.Direction) : setup d =
    [movR .r9 .rcx] ++ (Impl.Seed.X86_64.savedRegs.map fun p => (p.2, p.1)).map (fun p => st p.1 p.2) ++ setG16Masks ++
      ([.alu .add .rdi (.imm (BitVec.ofNat 32 (keyStart d))), .alu .cmp .rdx (.imm 0)] : List Instr) := rfl

theorem restore_eq : restore = Impl.Seed.X86_64.savedRegs.map (fun p => movS p.1 p.2) := rfl

theorem keyStart_ext (d : Spec.Seed.Direction) :
    (BitVec.ofNat 32 (keyStart d)).signExtend 64 = BitVec.ofNat 64 (keyStart d) := by
  cases d <;> rfl

theorem ecb_ok (d : Spec.Seed.Direction) {s : State} (h : EcbPre s) : WP isa (ecb d) s (EcbPost d s) := by
  let n := (s.gpr .rdx).toNat
  let D := s.gpr .rsi
  let S := s.gpr .rdi
  have hn := h.fit
  rw [ecb]
  apply WP.seq
  -- `r9 := rcx`
  let s₁ := s.setReg .r9 (s.gpr .rcx)
  have e₁ : runBlock isa [movR .r9 .rcx] s = some s₁ := rfl
  have r9₁ : s₁.gpr .r9 = s.gpr .rcx := gpr_setReg_self (s := s) _ _
  have g₁ : ∀ r, r ≠ .r9 → s₁.gpr r = s.gpr r := fun r hr => gpr_setReg_of_ne (s := s) _ hr
  have scr₁ : scratchR s₁ = ⟨s.gpr .rcx, 8 * scratchSlots⟩ := by simp only [scratchR, r9₁]
  have room₁ : Room s₁ := by unfold Room; rw [scr₁]; exact h.scratch
  -- the saved registers
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, f₂, set₂, keep₂⟩ := stores_ok room₁ (Impl.Seed.X86_64.savedRegs.map fun p => (p.2, p.1))
    (by decide) (by decide)
  have room₂ : Room s₂ := room_congr room₁ (by rw [g₂]) wr₂
  -- the masks
  obtain ⟨s₃, e₃, g₃, rd₃, wr₃, f₃, set₃, keep₃⟩ := masks_ok room₂ maskSlots (by decide) (by decide)
  have r9₃ : s₃.gpr .r9 = s.gpr .rcx := by rw [g₃ _ (by decide), g₂, r9₁]
  -- the key pointer and the test
  obtain ⟨s₄, e₄, rdi₄, g₄, m₄, rd₄, wr₄⟩ := exec_add_imm s₃ .rdi (BitVec.ofNat 32 (keyStart d))
  let s₅ := arithFlags s₄ (s₄.gpr .rdx - (0 : BitVec 32).signExtend 64)
    (decide ((s₄.gpr .rdx).toNat < ((0 : BitVec 32).signExtend 64).toNat))
    (subOverflow (s₄.gpr .rdx) ((0 : BitVec 32).signExtend 64) (s₄.gpr .rdx - (0 : BitVec 32).signExtend 64))
  have e₅ : exec (.alu .cmp .rdx (.imm 0)) s₄ = some s₅ := rfl
  refine WP.of_runBlock ⟨s₅, by
    rw [setup_eq]
    exact runBlock_trans (runBlock_trans (runBlock_trans e₁ e₂) e₃)
      (by rw [runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]), ?_⟩
  -- the state after the setup
  have G₃ : ∀ r, r ≠ .r9 → r ≠ t0 → s₃.gpr r = s.gpr r := fun r a b => by rw [g₃ r b, g₂, g₁ r a]
  have G₅ : ∀ r, r ≠ .r9 → r ≠ t0 → r ≠ .rdi → s₅.gpr r = s.gpr r := fun r a b c => by
    rw [gpr_arithFlags, g₄ r c, G₃ r a b]
  have r9₅ : s₅.gpr .r9 = s.gpr .rcx := by rw [gpr_arithFlags, g₄ _ (by decide), r9₃]
  have rdi₅ : s₅.gpr .rdi = S + BitVec.ofNat 64 (keyStart d) := by
    rw [gpr_arithFlags, rdi₄, G₃ _ (by decide) (by decide), keyStart_ext]
  have rd₅ : s₅.rd = s.rd := by rw [rd_arithFlags, rd₄, rd₃, rd₂]; rfl
  have wr₅ : s₅.wr = s.wr := by rw [wr_arithFlags, wr₄, wr₃, wr₂]; rfl
  have mem₅ : s₅.mem = s₃.mem := by rw [mem_arithFlags, m₄]
  have slot₅ : ∀ k, slotW s₅ k = slotW s₃ k := fun k => by
    show s₅.mem.readW (Straight.wordAddr (s₅.gpr .r9) k) 64 = s₃.mem.readW (Straight.wordAddr (s₃.gpr .r9) k) 64
    rw [mem₅, r9₅, r9₃]
  have scr₅ : scratchR s₅ = ⟨s.gpr .rcx, 8 * scratchSlots⟩ := by simp only [scratchR, r9₅]
  have room₅ : Room s₅ := by unfold Room; rw [scr₅, wr₅]; exact h.scratch
  have masks₅ : MasksIn s₅ := fun kv hkv => by rw [slot₅]; exact set₃ kv hkv
  have f₅ : Frame [⟨s.gpr .rcx, 8 * scratchSlots⟩] s.mem s₅.mem := by
    rw [mem₅, ← scr₁]
    refine f₂.trans ?_
    have : scratchR s₂ = scratchR s₁ := by simp only [scratchR, g₂]
    rw [← this]; exact f₃
  have zf₅ : s₅.zf = some (s.gpr .rdx == 0) := by
    rw [zf_arithFlags, g₄ _ (by decide), G₃ _ (by decide) (by decide),
      show s.gpr .rdx - BitVec.signExtend 64 (0 : BitVec 32) = s.gpr .rdx by simp]
  have rsi₅ : s₅.gpr .rsi = D := G₅ _ (by decide) (by decide) (by decide)
  have rdx₅ : s₅.gpr .rdx = s.gpr .rdx := G₅ _ (by decide) (by decide) (by decide)
  have rsp₅ : s₅.gpr .rsp = s.gpr .rsp := G₅ _ (by decide) (by decide) (by decide)
  have saved₅ : ∀ p ∈ Impl.Seed.X86_64.savedRegs, slotW s₅ p.2 = s.gpr p.1 := by
    intro p hp
    have hp' := savedRegs_ok p hp
    rw [slot₅, keep₃ _ hp'.1 (fun q hq => by have := maskSlots_lt q hq; omega)]
    rw [set₂ (p.2, p.1) (List.mem_map_of_mem hp), g₁ _ hp'.2.1]
  -- the keys, in the schedule
  have K₅ : ∀ j < 16, keysAt d s₅.mem (s₅.gpr .rdi) j = keysAt d s.mem (S + BitVec.ofNat 64 (keyStart d)) j := by
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
    have r9₆ : s₆.gpr .r9 = s₅.gpr .r9 := p.regs _ (by simp)
    have room₆ : Room s₆ := room_congr room₅ r9₆ p.wr
    obtain ⟨s', run', m', set', keep'⟩ := loads_ok room₆ Impl.Seed.X86_64.savedRegs
      (fun q hq => ⟨(savedRegs_ok q hq).1, (savedRegs_ok q hq).2.1⟩) (by decide)
    refine WP.of_runBlock ⟨s', by rw [restore_eq]; exact run', ?_⟩
    have pf := p.frame
    rw [rsi₅] at pf
    have frame : Frame [⟨s.gpr .rcx, 8 * scratchSlots⟩, ⟨D, 16 * n⟩] s.mem s'.mem := by
      rw [m']
      refine (f₅.mono (by simp)).trans (pf.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨_, List.mem_cons_self, ?_⟩
        simp only [workR, r9₅]
        exact Region.sub_prefix (by unfold scratchSlots; omega)
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    refine ⟨⟨fun r hr => ?_, ?_⟩, fun b hb => ?_, frame⟩
    · have saved : ∀ q ∈ Impl.Seed.X86_64.savedRegs, s'.gpr q.1 = s.gpr q.1 := by
        intro q hq
        have hq' := savedRegs_ok q hq
        rw [set' q hq, ← saved₅ q hq]
        show s₆.mem.readW (Straight.wordAddr (s₆.gpr .r9) q.2) 64 =
          s₅.mem.readW (Straight.wordAddr (s₅.gpr .r9) q.2) 64
        rw [r9₆]
        refine pf.readW (r := ⟨Straight.wordAddr (s₅.gpr .r9) q.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [workR]
          exact Offset.disjoint_base _ (by omega) (by unfold scratchSlots at hq'; omega)
        · rw [r9₅]
          exact (h.dataBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots at hq' ⊢; omega))).symm
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact saved (.rbx, 125) (by decide)
      · exact saved (.rbp, 126) (by decide)
      · rw [keep' .rsp (by decide), p.regs _ (by simp), rsp₅]
      · exact saved (.r12, 127) (by decide)
      · exact saved (.r13, 128) (by decide)
      · exact saved (.r14, 129) (by decide)
      · exact saved (.r15, 130) (by decide)
    · refine frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.retBuf
      · exact h.retData
    · have e := p.done b hb
      rw [rsi₅] at e
      rw [m', e, B₅ b hb, crypt_congr K₅, crypt_keysAt]
  apply WP.seq
  apply WP.ite (s.gpr .rdx == 0) zf₅
  · intro hz
    apply WP.block_nil
    have hn0 : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz)
      simpa [n] using this
    refine finish s₅ ⟨fun _ _ => rfl, rfl, rfl, fun b hb => by omega, ?_⟩
    rw [hn0]; exact Frame.refl _ _
  · intro hz
    have hn1 : 1 ≤ n := by
      have : s.gpr .rdx ≠ 0 := by simpa using hz
      have : (s.gpr .rdx).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
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
      refine ⟨hn1, Nat.le_refl _, ?_, ?_, fun _ _ => rfl, masks₅, rfl, rfl, fun b hb => by omega,
        by rw [Nat.sub_self]; exact Frame.refl _ _⟩
      · rw [rdx₅]; exact BitVec.eq_of_toNat_eq (by simp [n])
      · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add]
    exact WP.mono (loop_ok d E n s₅ I) finish

end VG.Proof.Seed.X86_64
