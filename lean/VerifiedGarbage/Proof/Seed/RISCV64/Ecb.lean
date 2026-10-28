module
public import VerifiedGarbage.Proof.Seed.RISCV64.Batch
import VerifiedGarbage.Proof.Seed.RISCV64.Setup

import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Seed.RISCV64.Round
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# The function on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/Ecb.lean`): after the prologue
(`Setup.lean`: the scratch buffer in `a5`, the callee-saved registers saved
in it, `g16`'s masks built), the function runs batches of up to 16 blocks
until none are left (`loop_ok`), then restores the registers (`ecb_ok`).
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.Proof.Seed
open VG.Impl.Aes.RISCV64 (sb movR)

theorem toNat_ofNat_le {m n : Nat} (hm : m ≤ n) (hn : 16 * n ≤ 2 ^ 64) : (BitVec.ofNat 64 m).toNat = m := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]

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
    exact hf.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega_arith) (by omega_arith)) hd (by decide)

/-! ## The loop of batches -/

/-- What the loop may assume throughout, of the state it starts in. -/
structure BatchesEnv (d : Spec.Seed.Direction) (s₀ : State) (n : Nat) : Prop where
  room : Room s₀
  masks : Masks s₀
  dataIn : (⟨s₀.gpr .a1, 16 * n⟩ : Region) ∈ s₀.wr
  dataSep : Region.Disjoint ⟨s₀.gpr .a1, 16 * n⟩ (scratchR s₀)
  fit : 16 * n ≤ 2 ^ 64
  keys : KeysOk d s₀ (s₀.gpr .a0)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s₀.gpr .a0) j, 8⟩ ⟨s₀.gpr .a1, 16 * n⟩

/-- `m` blocks left, the first `n - m` done. -/
structure BatchesInv (d : Spec.Seed.Direction) (s₀ : State) (n m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ n
  a2 : s.gpr .a2 = BitVec.ofNat 64 m
  a1 : s.gpr .a1 = s₀.gpr .a1 + BitVec.ofNat 64 (16 * (n - m))
  regs : ∀ r ∈ [Reg.ra, .a0, .a3, .a5], s.gpr r = s₀.gpr r
  masks : Masks s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n - m, Spec.Seed.blockAt s.mem (s₀.gpr .a1 + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .a0))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [workR s₀, ⟨s₀.gpr .a1, 16 * (n - m)⟩] s₀.mem s.mem

structure BatchesPost (d : Spec.Seed.Direction) (s₀ : State) (n : Nat) (s : State) : Prop where
  regs : ∀ r ∈ [Reg.ra, .a0, .a3, .a5], s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n, Spec.Seed.blockAt s.mem (s₀.gpr .a1 + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .a0))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .a1 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [workR s₀, ⟨s₀.gpr .a1, 16 * n⟩] s₀.mem s.mem

theorem BatchesInv.batchPre {d : Spec.Seed.Direction} {s₀ : State} {n m : Nat} (E : BatchesEnv d s₀ n)
    {s : State} (h : BatchesInv d s₀ n m s) : BatchPre d s := by
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  have hm : (s.gpr .a2).toNat = m := by rw [h.a2]; exact toNat_ofNat_le h.le E.fit
  have r9 : s.gpr sb = s₀.gpr sb := h.regs _ (by simp [sb])
  have rdi : s.gpr .a0 = s₀.gpr .a0 := h.regs _ (by simp)
  have scr : scratchR s = scratchR s₀ := by simp only [scratchR, r9]
  let D := s₀.gpr .a1
  have hsub : Region.Sub ⟨s.gpr .a1, 16 * min (s.gpr .a2).toNat 16⟩ ⟨D, 16 * n⟩ := by
    rw [h.a1, hm]; exact Offset.sub_base _ (by omega_arith)
  refine ⟨room_congr E.room r9 h.wr, h.masks, by omega_arith, fun b hb w hw => ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [h.wr, h.a1, Offset.add_ofNat_add_ofNat]
    rw [hm] at hb
    exact ⟨_, E.dataIn, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [scr]; exact E.dataSep.sub_left hsub
  · rw [rdi]
    intro j hj
    obtain ⟨a, b, c⟩ := E.keys j hj
    exact ⟨by rw [h.rd, h.wr]; exact a, by rw [h.rd, h.wr]; exact b, by rw [scr]; exact c⟩
  · rw [rdi]; exact (E.keyData j hj).sub_right hsub

theorem loop_ok (d : Spec.Seed.Direction) {s₀ : State} {n : Nat} (E : BatchesEnv d s₀ n) (m : Nat) (s : State)
    (hs : BatchesInv d s₀ n m s) : WP isa (.loop (batch d) (.nonzero .a2)) s (BatchesPost d s₀ n) := by
  refine WP.loop (M := isa) (BatchesInv d s₀ n) ?_ m s hs
  intro m s h
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  apply WP.mono (batch_ok d (h.batchPre E))
  intro s' q
  have hm : (s.gpr .a2).toNat = m := by rw [h.a2]; exact toNat_ofNat_le h.le E.fit
  obtain ⟨qdone, qrsi, qrdx, qregs, qmasks, qsp, qrd, qwr, qframe⟩ := q
  rw [hm] at qdone qrsi qrdx qframe
  generalize hk : min m 16 = k at qdone qrsi qrdx qframe
  have hk1 : 1 ≤ k := by omega_arith
  have hkm : k ≤ m := by omega_arith
  let D := s₀.gpr .a1
  let S := s₀.gpr .a0
  have r9 : s.gpr sb = s₀.gpr sb := h.regs _ (by simp [sb])
  have rdi : s.gpr .a0 = S := h.regs _ (by simp)
  have workR_eq : workR s = workR s₀ := by simp only [workR, r9]
  rw [h.a1, workR_eq] at qframe
  rw [h.a1] at qrsi qdone
  rw [rdi] at qdone
  -- the memory written so far
  have frame' : Frame [workR s₀, ⟨D, 16 * (n - (m - k))⟩] s₀.mem s'.mem := by
    have f₁ : Frame [workR s₀, ⟨D, 16 * (n - (m - k))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 16 * (n - (m - k))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Region.sub_prefix (by omega_arith)⟩
    have f₂ : Frame [workR s₀, ⟨D, 16 * (n - (m - k))⟩] s.mem s'.mem := qframe.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 16 * (n - (m - k))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Offset.sub_base _ (by omega_arith)⟩
    exact f₁.trans f₂
  have workSep : ∀ b, b < n → (⟨D + BitVec.ofNat 64 (16 * b), 16⟩ : Region).Disjoint (workR s₀) := fun b hb =>
    (E.dataSep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
      (Region.sub_prefix (by unfold scratchSlots; omega_arith))
  have done' : ∀ b < n - (m - k), Spec.Seed.blockAt s'.mem (D + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.crypt (keysAt d s₀.mem S) (Spec.Seed.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * b))) := by
    intro b hb
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine blockAt_frame qframe fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact workSep b (by omega_arith)
      · exact Offset.disjoint D (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega_arith⟩
      have e := qdone j (by omega_arith)
      rw [Offset.add_ofNat_add_ofNat, show 16 * (n - m) + 16 * j = 16 * (n - m + j) by omega_arith] at e
      rw [e]
      have hK : ∀ i < 16, keysAt d s.mem S i = keysAt d s₀.mem S i := fun i hi =>
        keysAt_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          obtain ⟨-, -, hdis⟩ := E.keys i hi
          rcases hr with rfl | rfl
          · exact hdis.sub_right (Region.sub_prefix (by unfold scratchSlots; omega_arith))
          · exact (E.keyData i hi).sub_right (Region.sub_prefix (by omega_arith))
      have hB : Spec.Seed.blockAt s.mem (D + BitVec.ofNat 64 (16 * (n - m + j))) =
          Spec.Seed.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (n - m + j))) :=
        blockAt_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact workSep _ (by omega_arith)
          · exact Offset.disjoint_base D (by omega_arith) (by omega_arith)
      rw [hB]
      exact crypt_congr hK _
  have rdx' : s'.gpr .a2 = BitVec.ofNat 64 (m - k) := by
    rw [qrdx, h.a2, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) hkm]
  have zf' : isa.eval (.nonzero .a2) s' = some (BitVec.ofNat 64 (m - k) != 0) := by
    rw [RISCV64.Steps.eval_nonzero, rdx']
  have regs' : ∀ r ∈ [Reg.ra, .a0, .a3, .a5], s'.gpr r = s₀.gpr r := fun r hr =>
    (qregs r hr).trans (h.regs r hr)
  have sp' : s'.sp = s₀.sp := qsp.trans h.sp
  have rd' := qrd.trans h.rd
  have wr' := qwr.trans h.wr
  by_cases hend : m ≤ 16
  · have hkm' : k = m := by omega_arith
    left
    refine ⟨?_, regs', sp', rd', wr', ?_, ?_⟩
    · rw [zf', hkm', Nat.sub_self]; rfl
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at done'; exact done'
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at frame'; exact frame'
  · have hk16 : k = 16 := by omega_arith
    right
    refine ⟨?_, m - k, by omega_arith, ⟨by omega_arith, by omega_arith, rdx', ?_, regs', qmasks, sp', rd', wr',
      done', frame'⟩⟩
    · rw [zf']
      have : (BitVec.ofNat 64 (m - k) != 0) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        rw [toNat_ofNat_le (show m - k ≤ n by omega_arith) E.fit] at this
        have z : (0 : BitVec 64).toNat = 0 := rfl
        omega_arith
      rw [this]
    · rw [qrsi, Offset.add_ofNat_add_ofNat]; congr 2; omega_arith

/-! ## The keys -/

/-- Where round `j + 1`'s key is in the schedule. -/
def keyOff : Spec.Seed.Direction → Nat → Nat
  | .encrypt, j => 8 * j
  | .decrypt, j => 8 * (15 - j)

theorem keyOff_le (d : Spec.Seed.Direction) {j : Nat} (hj : j < 16) : keyOff d j + 8 ≤ 128 := by
  cases d <;> simp only [keyOff] <;> omega_arith

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
    rw [keysAt, kp_start _ _ hj, roundKey_readW _ _ (by omega_arith)]
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
  scrAl : (s.gpr .a3).toNat % 8 = 0
  scratch : ∃ n, 8 * scratchSlots ≤ n ∧ (⟨s.gpr .a3, n⟩ : Region) ∈ s.wr
  dataIn : (⟨s.gpr .a1, 16 * (s.gpr .a2).toNat⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .a0, 128⟩ : Region) ∈ s.rd
  keyData : (⟨s.gpr .a0, 128⟩ : Region).Disjoint ⟨s.gpr .a1, 16 * (s.gpr .a2).toNat⟩
  keyBuf : (⟨s.gpr .a0, 128⟩ : Region).Disjoint ⟨s.gpr .a3, 8 * scratchSlots⟩
  dataBuf : (⟨s.gpr .a1, 16 * (s.gpr .a2).toNat⟩ : Region).Disjoint ⟨s.gpr .a3, 8 * scratchSlots⟩
  fit : 16 * (s.gpr .a2).toNat ≤ 2 ^ 64

/-- What the function does: every block of the data becomes its encryption or
decryption, the callee-saved registers and `ra` are as they were, and only
the scratch buffer and the data change. -/
structure EcbPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  saved : ∀ r ∈ RISCV64.preserved, s'.gpr r = s.gpr r
  ra : s'.gpr .ra = s.gpr .ra
  done : ∀ b < (s.gpr .a2).toNat, Spec.Seed.blockAt s'.mem (s.gpr .a1 + BitVec.ofNat 64 (16 * b)) =
    cipher d (Spec.Seed.scheduleAt s.mem (s.gpr .a0))
      (Spec.Seed.blockAt s.mem (s.gpr .a1 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [⟨s.gpr .a3, 8 * scratchSlots⟩, ⟨s.gpr .a1, 16 * (s.gpr .a2).toNat⟩] s.mem s'.mem

theorem keyStart_lt (d : Spec.Seed.Direction) : keyStart d < 2048 := by cases d <;> decide

theorem ecb_ok (d : Spec.Seed.Direction) {s : State} (h : EcbPre s) : WP isa (ecb d) s (EcbPost d s) := by
  let n := (s.gpr .a2).toNat
  let D := s.gpr .a1
  let S := s.gpr .a0
  let X := s.gpr .a3
  have hn := h.fit
  rw [ecb]
  apply WP.seq
  rw [setup, WP.block_append_iff (M := isa)]
  refine WP.mono (prologue_ok h.scrAl h.scratch) fun s₁ P => ?_
  refine RISCV64.Steps.wp_addi (keyStart_lt d) fun s₅ u => WP.block_nil ?_
  -- the state after the setup
  have G₅ : ∀ r, r ≠ sb → r ≠ kb → r ≠ .t0 → r ≠ .t1 → r ≠ .a0 → s₅.gpr r = s.gpr r :=
    fun r a b c e f => by rw [u.other r f, P.regs r a b c e]
  have sb₅ : s₅.gpr sb = X := by rw [u.other _ (by decide), P.base]
  have a0₅ : s₅.gpr .a0 = S + BitVec.ofNat 64 (keyStart d) := by
    rw [u.gpr, P.regs _ (by decide) (by decide) (by decide) (by decide)]
  have rd₅ : s₅.rd = s.rd := by rw [u.rd, P.rd]
  have wr₅ : s₅.wr = s.wr := by rw [u.wr, P.wr]
  have sp₅ : s₅.sp = s.sp := by rw [u.sp, P.sp]
  have mem₅ : s₅.mem = s₁.mem := u.mem
  have scr₅ : scratchR s₅ = ⟨X, 8 * scratchSlots⟩ := by simp only [scratchR, sb₅]
  have room₅ : Room s₅ := room_congr P.room (by rw [u.other _ (by decide)]) u.wr
  have masks₅ : Masks s₅ := P.masks.frame (u.other _ (by decide)) (u.other _ (by decide))
    (by rw [mem₅]; exact Frame.refl _ _)
  have f₅ : Frame [⟨X, 8 * scratchSlots⟩] s.mem s₅.mem := by rw [mem₅]; exact P.frame
  have zf₅ : isa.eval (.zero .a2) s₅ = some (s.gpr .a2 == 0) := by
    rw [RISCV64.Steps.eval_zero, G₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have a1₅ : s₅.gpr .a1 = D := G₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have a2₅ : s₅.gpr .a2 = s.gpr .a2 := G₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have ra₅ : s₅.gpr .ra = s.gpr .ra := G₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have saved₅ : Spill.Saved X s.gpr savedOffs s₅.mem := by rw [mem₅]; exact P.saved
  -- the keys, in the schedule
  have K₅ : ∀ j < 16, keysAt d s₅.mem (s₅.gpr .a0) j = keysAt d s.mem (S + BitVec.ofNat 64 (keyStart d)) j := by
    intro j hj
    rw [a0₅]
    refine keysAt_frame f₅ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rw [kp_start _ _ hj]
    exact h.keyBuf.sub_left (Offset.sub_base _ (keyOff_le d hj))
  have B₅ : ∀ b < n, Spec.Seed.blockAt s₅.mem (D + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.blockAt s.mem (D + BitVec.ofNat 64 (16 * b)) := fun b hb =>
    blockAt_frame f₅ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.dataBuf.sub_left (Offset.sub_base _ (by omega_arith))
  -- after the loop (or none), the registers restored
  have finish : ∀ s₆ : State, BatchesPost d s₅ n s₆ → WP isa (.block seedRestore) s₆ (EcbPost d s) := by
    intro s₆ p
    have sb₆ : s₆.gpr sb = X := (p.regs _ (by simp [sb])).trans sb₅
    have room₆ : Room s₆ := room_congr room₅ (p.regs _ (by simp [sb])) p.wr
    have pf := p.frame
    rw [a1₅] at pf
    have wX : workR s₅ = ⟨X, 8 * 104⟩ := by simp only [workR, sb₅]
    rw [wX] at pf
    have sv₆ : Spill.Saved X s.gpr savedOffs s₆.mem := by
      refine saved₅.frame_in savedOffs_range pf fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact (h.dataBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots; omega))).symm
    rw [seedRestore_eq]
    refine WP.mono (Spill.restore_wp (B := X) (by rw [← sb₆]; exact room₆.1) sb₆ savedOffs_ho
      savedOffs_restorable (fun q hq => room₆.rw ?_) sv₆) fun s' R => ?_
    · rw [← sb₆]
      have := savedOffs_range q hq
      exact Offset.contains_base _ (by unfold scratchSlots; omega) (by omega)
    have frame : Frame [⟨X, 8 * scratchSlots⟩, ⟨D, 16 * n⟩] s.mem s'.mem := by
      rw [R.mem]
      refine (f₅.mono (by simp)).trans (pf.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by unfold scratchSlots; omega_arith)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    refine ⟨fun r hr => ?_, ?_, fun b hb => ?_, frame⟩
    · rw [← savedOffs_regs] at hr
      exact R.gpr_of (Or.inl hr)
    · rw [R.other _ (by decide), p.regs _ (by simp), ra₅]
    · have e := p.done b hb
      rw [a1₅] at e
      rw [R.mem, e, B₅ b hb, crypt_congr K₅, crypt_keysAt]
  apply WP.seq
  apply WP.ite (s.gpr .a2 == 0) zf₅
  · intro hz
    apply WP.block_nil
    have hn0 : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz)
      simpa [n] using this
    refine finish s₅ ⟨fun _ _ => rfl, rfl, rfl, rfl, fun b hb => by omega_arith, ?_⟩
    rw [hn0]; exact Frame.refl _ _
  · intro hz
    have hn1 : 1 ≤ n := by
      have : s.gpr .a2 ≠ 0 := by simpa using hz
      have : (s.gpr .a2).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
      omega_arith
    have E : BatchesEnv d s₅ n := by
      refine ⟨room₅, masks₅, by rw [a1₅, wr₅]; exact h.dataIn, by rw [a1₅, scr₅]; exact h.dataBuf, hn,
        fun j hj => ?_, fun j hj => ?_⟩
      · rw [a0₅, kp_start _ _ hj, rd₅, wr₅, scr₅]
        have hle := keyOff_le d hj
        refine ⟨⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩, ?_,
          h.keyBuf.sub_left (Offset.sub_base _ hle)⟩
        rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_ofNat_add_ofNat]
        exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
      · rw [a0₅, kp_start _ _ hj, a1₅]
        exact h.keyData.sub_left (Offset.sub_base _ (keyOff_le d hj))
    have I : BatchesInv d s₅ n n s₅ := by
      refine ⟨hn1, Nat.le_refl _, ?_, ?_, fun _ _ => rfl, masks₅, rfl, rfl, rfl, fun b hb => by omega_arith,
        by rw [Nat.sub_self]; exact Frame.refl _ _⟩
      · rw [a2₅]; exact BitVec.eq_of_toNat_eq (by simp [n])
      · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add]
    exact WP.mono (loop_ok d E n s₅ I) finish

end VG.Proof.Seed.RISCV64
