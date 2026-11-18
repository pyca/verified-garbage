module

public import VerifiedGarbage.Impl.Argon2.Arm.Derive
public import VerifiedGarbage.Proof.Argon2.Arm.CompressLit
public import VerifiedGarbage.Proof.Argon2.Arm.Derive.Initial
public import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillLoops
public import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Argon2.Arm.Derive.InitialCT
import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Finish
import VerifiedGarbage.Proof.Argon2.Arm.Mix
meta import VerifiedGarbage.Proof.Argon2.Arm.Derive.InitialCT
meta import VerifiedGarbage.Proof.Argon2.References
meta import VerifiedGarbage.Proof.Argon2.Arm.Derive.Initial
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Finish
meta import VerifiedGarbage.Proof.Argon2.Arm.Mix
public import VerifiedGarbage.Proof.Argon2.FillStep
public import VerifiedGarbage.Proof.Argon2.Slices
import VerifiedGarbage.Proof.Argon2.IterationsIndices
import VerifiedGarbage.Proof.Argon2.SegmentIndices
public import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillBlock
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillLoops
meta import VerifiedGarbage.Proof.Argon2.FillStep
meta import VerifiedGarbage.Proof.Argon2.Slices
meta import VerifiedGarbage.Proof.Argon2.IterationsIndices
meta import VerifiedGarbage.Proof.Argon2.SegmentIndices
meta import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillBlock
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCache
meta import VerifiedGarbage.Proof.Argon2.FillPositions
meta import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCache
import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillInput
meta import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCall
meta import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillInput
public import VerifiedGarbage.Proof.Argon2.FinalReduction
import VerifiedGarbage.Proof.Argon2.Serialization
meta import VerifiedGarbage.Proof.Argon2.FinalReduction
meta import VerifiedGarbage.Proof.Argon2.Serialization
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Argon2.Contract

/-! ### `Argon2.Arm.Derive.BodyCT`, which only this module used -/

section

/-! ### `Argon2.Arm.Derive.MemCT`, which only this module used -/

section

/-!
# Argon2 on ARMv7: memory initialization, in two runs

`memoryInit_rel`: clearing the matrix and the calls of H′ for the first two
blocks of every lane leak the same trace in two runs with the same public
data: the calls' arguments are H₀'s place in the locals and the blocks'
addresses, which only the lane fixes.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_imm op2_reg)
open VG.Spec.Blake2 (bytesAt)
open VG.Impl.Argon2.Arm.Derive (argOff columnOff laneWordOff ld st)

/-- The state before block `c` of lane `l`. -/
def IB (s₀ : State) (h0 : List Byte) (l c : Nat) (s : State) : Prop :=
  Inv s₀ s ∧ Prm s₀ s ∧ bytesAt s.mem (State.addr (E s₀)) 64 = h0 ∧ s.gpr .r5 = BitVec.ofNat 32 l ∧
    s.gpr .r6 = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem initBlock_w {h0 : List Byte} {l c : Nat} (hl : l < lanesN s₀) (hc : c < 2) {s : State}
    (h : IB s₀ h0 l c s) : WP isa (Impl.Argon2.Arm.Derive.initBlock c) s (IB s₀ h0 l c) :=
  (initBlock_ok hp h.1 h.2.1 h.2.2.1 hl hc h.2.2.2.1 h.2.2.2.2).mono fun _ ⟨i, p, b, e, d, _, _⟩ =>
    ⟨i, p, b, e.trans h.2.2.2.1, d.trans h.2.2.2.2⟩

omit hp in
theorem nextBlock_w {h0 : List Byte} {l : Nat} {s : State} (h : IB s₀ h0 l 0 s) :
    WP isa (.block [.dp .add .r6 .r6 (.imm 1024)]) s (IB s₀ h0 l 1) :=
  wp_add (op2_imm (by decide)) fun t u => WP.block_nil ⟨h.1.upd u (by decide), h.2.1.of_mem u.mem,
    by rw [u.mem]; exact h.2.2.1, by rw [u.other _ (by decide)]; exact h.2.2.2.1, by
      rw [u.gpr, h.2.2.2.2, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.add_assoc,
        BitVec.ofNat_add_ofNat, show (l * (prm s₀).laneLen + 0) * 1024 + 1024 = (l * (prm s₀).laneLen + 1) * 1024 by
          rw [Nat.add_mul, Nat.add_mul]]⟩

/-- The instructions before `initBlock`'s call of H′. -/
theorem ibBlk_ok {s : State} (h : Inv s₀ s) (c : Nat) (hc : encodable (BitVec.ofNat 32 c) = true) :
    WP isa (.block [.mov .r0 (.imm (BitVec.ofNat 32 c)), st columnOff .r0, st laneWordOff .r5,
      .mov .r0 (.reg .r11), .mov .r1 (.imm 72), .mov .r2 (.reg .r6), .mov .r3 (.imm 1024),
      ld .r12 (argOff 15)]) s fun t => Inv s₀ t ∧ t.gpr .r12 = scrP s₀ ∧ t.gpr .r0 = E s₀ ∧
      t.gpr .r1 = 72 ∧ t.gpr .r3 = 1024 ∧ t.gpr .r2 = s.gpr .r6 := by
  refine wp_mov (op2_imm hc) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide)
  refine wp_stloc hp i₁ (d := 64) (by decide) fun s₂ i₂ _ _ g₂ _ => ?_
  refine wp_stloc hp i₂ (d := 68) (by decide) fun s₃ i₃ _ _ g₃ _ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_imm (by decide)) fun s₇ u₇ => ?_
  have i₇ := (((i₃.upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)
  refine wp_ldarg hp i₇ (i := 15) (by decide) fun s₈ u₈ => WP.block_nil
    ⟨i₇.upd u₈ (by decide), u₈.gpr, ?_, ?_, ?_, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      g₃, g₂, u₁.other _ (by decide), h.r11]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [u₈.other _ (by decide), u₇.gpr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      g₃, g₂, u₁.other _ (by decide)]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `initBlock c` leaks the same trace in two runs at the same lane. -/
theorem initBlock_rel {h₁ h₂ : List Byte} {l c : Nat} (hl : l < lanesN s₀₁) (hc : c < 2)
    (he : encodable (BitVec.ofNat 32 c) = true)
    (hchk : ∃ hc, (VG.Taint.check taint (τB [] []) (.block [.mov .r0 (.imm (BitVec.ofNat 32 c)),
      st columnOff .r0, st laneWordOff .r5, .mov .r0 (.reg .r11), .mov .r1 (.imm 72), .mov .r2 (.reg .r6),
      .mov .r3 (.imm 1024), ld .r12 (argOff 15)]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => IB s₀₁ h₁ l c s₁ ∧ IB s₀₂ h₂ l c s₂) (Impl.Argon2.Arm.Derive.initBlock c)
      fun _ _ => True := by
  have pe := T.pb.prm_eq
  have cellF : ∀ {s₀ : State}, DPre s₀ → l < lanesN s₀ →
      (l * (prm s₀).laneLen + c) * 1024 + 1024 ≤ blocksN s₀ * 1024 ∧ l * (prm s₀).laneLen + c < blocksN s₀ :=
    fun {s₀} hp hl => by
      have L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega_using [this]
      have : l * (prm s₀).laneLen + c < blocksN s₀ := by
        rw [hp.blocks_eq]
        have := Nat.mul_le_mul_right (prm s₀).laneLen (show l + 1 ≤ lanesN s₀ by omega_using [hl])
        rw [Nat.succ_mul] at this
        omega_using [hc, L2, this]
      exact ⟨by omega_using [this], this⟩
  have pre : ∀ {s₀ : State}, DPre s₀ → l < lanesN s₀ → ∀ {s t : State}, IB s₀ h₁ l c s ∨ IB s₀ h₂ l c s →
      Inv s₀ t ∧ t.gpr .r12 = scrP s₀ ∧ t.gpr .r0 = E s₀ ∧ t.gpr .r1 = 72 ∧ t.gpr .r3 = 1024 ∧
        t.gpr .r2 = s.gpr .r6 →
      Inv s₀ t ∧ t.gpr .r12 = scrP s₀ ∧
        (∃ R ∈ [memR s₀, locR s₀], ∃ off, State.addr (t.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .r1).toNat ≤ R.len) ∧ (t.gpr .r0).toNat + (t.gpr .r1).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀, outR s₀], ∃ off, State.addr (t.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .r3).toNat ≤ R.len) ∧ (t.gpr .r2).toNat + (t.gpr .r3).toNat ≤ 2 ^ 32 ∧
        1 ≤ (t.gpr .r3).toNat := fun {s₀} hp hl {s t} hs ⟨i, d, a, c', f, e⟩ => by
    have hE := E_hi hp
    have hm := hp.mem_fits
    obtain ⟨hc', hk⟩ := cellF hp hl
    have ed : t.gpr .r2 = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024) := by
      rw [e]; rcases hs with hs | hs <;> exact hs.2.2.2.2
    have an : (memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)).toNat =
        (memP s₀).toNat + (l * (prm s₀).laneLen + c) * 1024 := add_nat (by omega_using [hm, hc'])
    refine ⟨i, d, ⟨locR s₀, by simp, 0, by rw [a]; simp, by rw [c']; show 0 + 72 ≤ 144; decide⟩,
      by rw [a, c']; show (E s₀).toNat + 72 ≤ 2 ^ 32; omega_using [hE],
      ⟨memR s₀, by simp, (l * (prm s₀).laneLen + c) * 1024, by rw [ed, cell_addr hp hk]; rfl,
        by rw [f]; exact hc'⟩, by rw [ed, f, an]; show _ + 1024 ≤ 2 ^ 32; omega_using [hm, hc'],
      by rw [f]; decide⟩
  unfold Impl.Argon2.Arm.Derive.initBlock
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) hchk)
    (G₁ := fun t => ∃ s, IB s₀₁ h₁ l c s ∧ Inv s₀₁ t ∧ t.gpr .r12 = scrP s₀₁ ∧ t.gpr .r0 = E s₀₁ ∧
      t.gpr .r1 = 72 ∧ t.gpr .r3 = 1024 ∧ t.gpr .r2 = s.gpr .r6)
    (G₂ := fun t => ∃ s, IB s₀₂ h₂ l c s ∧ Inv s₀₂ t ∧ t.gpr .r12 = scrP s₀₂ ∧ t.gpr .r0 = E s₀₂ ∧
      t.gpr .r1 = 72 ∧ t.gpr .r3 = 1024 ∧ t.gpr .r2 = s.gpr .r6)
    (fun s h => (ibBlk_ok T.hp₁ h.1 c he).mono fun t ht => ⟨s, h, ht⟩)
    (fun s h => (ibBlk_ok T.hp₂ h.1 c he).mono fun t ht => ⟨s, h, ht⟩) ?_
  refine T.hcall_rel fun s₁ s₂ ⟨⟨a₁, g₁, k₁⟩, ⟨a₂, g₂, k₂⟩⟩ =>
    ⟨pre T.hp₁ hl (.inl g₁) k₁, pre T.hp₂ (T.pb.lanesN_eq ▸ hl) (.inr g₂) k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.2.2.1, k₂.2.2.1, T.pb.E]
  · rw [k₁.2.2.2.1, k₂.2.2.2.1]
  · rw [k₁.2.2.2.2.2, k₂.2.2.2.2.2, g₁.2.2.2.2, g₂.2.2.2.2, pe, T.pb.memP_eq]
  · rw [k₁.2.2.2.2.1, k₂.2.2.2.2.1]

/-- `initLane` leaks the same trace in two runs at the same lane. -/
theorem initLane_rel {h₁ h₂ : List Byte} {l : Nat} (hl : l < lanesN s₀₁) :
    RelCT isa (fun s₁ s₂ => LI s₀₁ h₁ l s₁ ∧ LI s₀₂ h₂ l s₂) Impl.Argon2.Arm.Derive.initLane fun _ _ => True := by
  have hl₂ : l < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have ib : ∀ {s₀ s : State} {h0 : List Byte}, LI s₀ h0 l s → IB s₀ h0 l 0 s := fun h =>
    ⟨h.inv, h.pr, h.b0, h.r5, by rw [Nat.add_zero]; exact h.r6⟩
  unfold Impl.Argon2.Arm.Derive.initLane
  refine (RelCT.seqW (T.initBlock_rel hl (by decide) (by decide) ⟨_, by taint_decide⟩)
    (fun s h => initBlock_w T.hp₁ hl (by decide) h)
    (fun s h => initBlock_w T.hp₂ hl₂ (by decide) h) ?_).mono (fun _ _ h => ⟨ib h.1, ib h.2⟩) fun _ _ h => h
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => nextBlock_w h) (fun s h => nextBlock_w h) ?_
  refine RelCT.seqW (T.initBlock_rel hl (by decide) (by decide) ⟨_, by taint_decide⟩)
    (fun s h => initBlock_w T.hp₁ hl (by decide) h)
    (fun s h => initBlock_w T.hp₂ hl₂ (by decide) h) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩

/-- `memoryInit` leaks the same trace in two runs. -/
theorem memoryInit_rel {h₁ h₂ : List Byte} :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁ ∧ bytesAt s₁.mem (State.addr (E s₀₁)) 64 = h₁) ∧
      (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂ ∧ bytesAt s₂.mem (State.addr (E s₀₂)) 64 = h₂))
      Impl.Argon2.Arm.Derive.memoryInit fun _ _ => True := by
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  unfold Impl.Argon2.Arm.Derive.memoryInit
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => clearW_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => clearW_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => laneStart_ok T.hp₁ h) (fun s h => laneStart_ok T.hp₂ h) ?_
  generalize hN : lanesN s₀₁ = N at hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      LI s₀₁ h₁ l s₁ ∧ LI s₀₂ h₂ l s₂) ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega_using [], hl1, h.1, h.2⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, g₁, g₂⟩ e₁ e₂
  obtain ⟨ht, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩ := rel_wp (T.initLane_rel (by rw [hN]; exact hl))
    (fun s h => lane_ok T.hp₁ (by rw [hN]; exact hl) h) (fun s h => lane_ok T.hp₂ (by rw [hN₂]; exact hl) h)
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨g₁, g₂⟩ e₁ e₂
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show VG.Arm.eval .ne s₁' = VG.Arm.eval .ne s₂'; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 ≠ N := by
    rw [show isa.eval .ne s₁' = VG.Arm.eval .ne s₁' from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega_using [hn, hl], l + 1, rfl, by omega_using [hl, e], k₁, k₂⟩

end Two

end VG.Proof.Argon2.Arm.Derive

end

end

/-! ### `Argon2.Arm.Derive.ReduceCT`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.Derive.Reduce`, which this module and modules that import it used -/

section

/-!
# Argon2 on ARMv7: the final block and the tag

`reduce_ok`: the memory's first block becomes the XOR of every lane's last
block (`Proof.Argon2.reduction`), the other blocks kept; `finalOutput_ok`:
H′ of it to `out`, the tag (`Proof.Argon2.finish_reduction`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_sub wp_str op2_imm op2_reg)
open VG.Spec.Argon2 (Block zeroBlock FillState compress xorBlock)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2.Arm (blk ofWords blk_of_words xor_words)
open VG.Proof.Sha512.Arm (Only A)
open VG.Impl.Argon2.Arm.Derive (laneOff laneLenOff argOff divisorOff segLenOff strideOff)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `n` stores of `r0 = 0` to `[r3, #4k]`, `r3` the memory matrix. -/
theorem memZeros_ok {s : State} (h : Inv s₀ s) (hx : s.gpr .r3 = memP s₀) (ha : s.gpr .r0 = 0) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).map fun k => Instr.str .r0 .r3 (4 * k))) s fun t =>
      Inv s₀ t ∧ t.gpr = s.gpr ∧ Frame [⟨matrixCell (memB s₀) 0, 1024⟩] s.mem t.mem ∧
      ∀ i < n, mw s₀ t.mem (4 * i) = 0
  | 0, _ => WP.block_nil ⟨h, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have b1 := blocks_pos hp
    have hb := blocks22 hp
    have hm := hp.mem_fits
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append ((memZeros_ok h hx ha n (by omega_arith)).mono fun t ⟨it, gt, ft, wt⟩ => ?_)
    have ea : State.addr (t.gpr .r3 + BitVec.ofNat 32 (4 * n)) = A (memP s₀) (4 * n) := by rw [gt, hx]
    have ea' : A (memP s₀) (4 * n) = memB s₀ + BitVec.ofNat 64 (4 * n) := mem_addr' hp (by omega_arith)
    have hc : (memR s₀).Contains (A (memP s₀) (4 * n)) 4 := by
      rw [ea']; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    have hc' : (⟨matrixCell (memB s₀) 0, 1024⟩ : Region).Contains (A (memP s₀) (4 * n)) 4 := by
      rw [ea', show matrixCell (memB s₀) 0 = memB s₀ by simp [matrixCell]]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    refine wp_str (by omega_arith) ea ⟨_, by rw [it.wr]; exact mem_mem hp, hc⟩ fun t₁ u₁ => WP.block_nil
      ⟨it.store (R := memR s₀) (by simp) hc u₁, by rw [u₁.gpr, gt], ?_, fun i hi => ?_⟩
    · rw [u₁.mem]
      exact ft.writeW (List.mem_singleton_self _) _ hc'
    · rw [u₁.mem, gt, show 4 * n = 0 + 4 * n by omega_arith, show 4 * i = 0 + 4 * i by omega_arith,
        mw_store hp _ (by omega_arith) (by omega_arith) (by omega_arith), ha]
      by_cases e : 0 + 4 * n = 0 + 4 * i
      · rw [ite_eq_left e]
      · rw [ite_eq_right e, show 0 + 4 * i = 4 * i by omega_arith]; exact wt i (by omega_arith)

end

theorem reduction_snoc (p : Spec.Argon2.Params) (M : Array Block) (l : Nat) (acc : Block) :
    Proof.Argon2.reduction p M 0 (l + 1) acc =
      xorBlock (Proof.Argon2.reduction p M 0 l acc) (M[Proof.Argon2.lastIndex p l]?.getD zeroBlock) := by
  unfold Proof.Argon2.reduction
  rw [foldl_range'_snoc, Nat.zero_add]

/-- The state of the reduction after `l` lanes. -/
structure RI (s₀ : State) (M : Array Block) (l : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  lane : lw s₀ s laneOff = BitVec.ofNat 32 l
  first : blockAt s.mem (matrixCell (memB s₀) 0) = Proof.Argon2.reduction (prm s₀) M 0 l zeroBlock
  rest : ∀ k < (prm s₀).blocks, k ≠ 0 → blockAt s.mem (matrixCell (memB s₀) k) = M[k]?.getD zeroBlock

theorem cell0 (s₀ : State) : matrixCell (memB s₀) 0 = memB s₀ := by simp [matrixCell]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- One lane of the reduction. -/
theorem reduceLane_ok {s : State} {M : Array Block} {l : Nat} (h : RI s₀ M l s) (hl : l < lanesN s₀) :
    WP isa (.block (Impl.Argon2.Arm.Derive.reduceLane ++
      Impl.Argon2.Arm.Derive.advance laneOff (argOff Impl.Argon2.Arm.Derive.lanesArg)))
      s fun t => RI s₀ M (l + 1) t ∧ VG.Arm.eval .ne t = some (!decide (l + 1 = lanesN s₀)) := by
  have L8 := laneLen_ge hp
  have hlt := hp.lanes_lt
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  obtain ⟨cl, _⟩ := cell_fits hp hl (col := (prm s₀).laneLen - 1) (by omega_arith)
  have last : Proof.Argon2.lastIndex (prm s₀) l = l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) := by
    unfold Proof.Argon2.lastIndex; rw [Nat.succ_mul]; omega_arith
  have ne0 : l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) ≠ 0 := by omega_arith
  unfold Impl.Argon2.Arm.Derive.reduceLane Impl.Argon2.Arm.Derive.writeBlock
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldloc hp h.inv (d := laneOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide)
  refine wp_ldloc hp i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => wp_sub (op2_imm (by decide)) fun s₃ u₃ => ?_
  have i₃ := (i₁.upd u₂ (by decide)).upd u₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine blockAddr_ok hp i₃ (h.pr.of_mem m₃) hl (col := (prm s₀).laneLen - 1) (by omega_arith)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.lane])
    (by rw [u₃.gpr, u₂.gpr, lw_mem u₁.mem, h.pr.laneLen, ofNat_pred (by omega_arith) rfl]) fun s₄ a₄ k₄ => ?_
  have i₄ := i₃.only k₄ (by decide)
  refine wp_mov (op2_reg _ _) fun s₅ u₅ => ?_
  have i₅ := i₄.upd u₅ (by decide)
  refine wp_ldarg hp i₅ (i := 13) (by decide) fun s₆ u₆ => ?_
  have i₆ := i₅.upd u₆ (by decide)
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, k₄.mem, m₃]
  have hm := hp.mem_fits
  have b22 := blocks22 hp
  have b1 := blocks_pos hp
  generalize hc : l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) = c at cl a₄ ne0 last
  have hc' : c * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_using [cl]
  have sx : s₆.gpr .r1 = memP s₀ + BitVec.ofNat 32 (c * 1024) := by
    rw [u₆.other _ (by decide), u₅.gpr, a₄]
  have dx : s₆.gpr .r3 = memP s₀ + BitVec.ofNat 32 (0 * 1024) := by
    rw [u₆.gpr]; simp
  refine WP.block_append ((writeWords_ok hp i₆ (cur := 0) b1 true sx
    (by rw [add_nat (by omega_using [hc', hm])]; omega_using [hc', hm])
    ⟨memR s₀, by simp, c * 1024, cell_addr hp cl, hc'⟩
    (by rw [cell_addr hp cl]; exact cell_other hp cl b1 ne0) dx 256 (Nat.le_refl _)).mono
    fun t₇ ⟨i₇, g₇, f₇, w₇⟩ => ?_)
  have lt₇ : ∀ d, d + 4 ≤ 144 → lw s₀ t₇ d = lw s₀ s d := fun d hd => by
    rw [← lw_mem m₆ d]
    exact f₇.readW (r := ⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).sub_right (cell_in_mem b1)) (by decide)
  refine (advance_ok hp i₇ (d := laneOff) (n := l) (by decide) (by rw [lt₇ _ (by decide)]; exact h.lane)
    (by omega_arith) (o := argOff 7) (B := lanesN s₀) (by decide) (by omega_arith) (fun v iv => iv.arg_in hp (by decide))
    fun v iv _ => iv.arg hp (by decide) |>.trans (by simp)).mono fun t ⟨it, mt, ct, _⟩ => ⟨?_, ct⟩
  obtain ⟨lt, _, ct⟩ := loc_store hp (d := laneOff) (by decide) mt
  have new : blockAt t₇.mem (matrixCell (memB s₀) 0) =
      xorBlock (blockAt s.mem (matrixCell (memB s₀) c)) (blockAt s.mem (matrixCell (memB s₀) 0)) := by
    rw [cell_blk hp _ b1, cell_blk hp _ b1, cell_blk hp _ cl,
      blk_of_words (f := fun i => mw s₀ s.mem (c * 1024 + 4 * i) ^^^ mw s₀ s.mem (0 * 1024 + 4 * i)) fun i hi => by
        rw [← mw, w₇ i hi, ite_eq_left hi, ite_eq_left (rfl : true = true), m₆, A_shift],
      blk_of_words (m := s.mem) (B := memP s₀) (o := c * 1024) (f := fun i => mw s₀ s.mem (c * 1024 + 4 * i))
        fun _ _ => rfl,
      blk_of_words (m := s.mem) (B := memP s₀) (o := 0 * 1024) (f := fun i => mw s₀ s.mem (0 * 1024 + 4 * i))
        fun _ _ => rfl, xor_words]
  refine ⟨it, Prm.of_lw h.pr fun d hd => ?_, ?_, ?_, fun k hk k0 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    have hd4 : d + 4 ≤ 144 := by rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [lt d (by omega_arith) (by rcases hd with rfl | rfl | rfl | rfl <;> decide), lt₇ d hd4]
  · show t.mem.readW _ 32 = _
    rw [mt, Mem.readW_writeW_self32]
  · rw [ct _ (by rw [← hb]; exact b1), new, h.first, h.rest _ (by rw [← hb]; exact cl) ne0, reduction_snoc,
      Proof.Argon2.xorBlock_comm, last]
  · rw [ct _ hk, blockAt_keep f₇ (fun r hr => ?_), m₆, h.rest k hk k0]
    simp only [List.mem_singleton] at hr; subst hr
    exact cell_other hp (by rw [hb]; exact hk) b1 k0

/-- The first block of `reduce`: the memory's first block cleared, and the lane `0`. -/
theorem reduceStart_ok {s : State} {M : Array Block} (h : Inv s₀ s) (pr : Prm s₀ s)
    (hm : Represents s.mem (memB s₀) (prm s₀).blocks M) :
    WP isa (.block (Impl.Argon2.Arm.Derive.reduceClear ++ Impl.Argon2.Arm.Derive.setLocal laneOff 0)) s
      (RI s₀ M 0) := by
  have b1 := blocks_pos hp
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.Arm.Derive.reduceClear Impl.Argon2.Arm.Derive.setLocal
  simp only [List.cons_append, List.nil_append]
  refine wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have i₂ := (h.upd u₁ (by decide)).upd u₂ (by decide)
  refine WP.block_append ((memZeros_ok hp i₂ (by rw [u₂.other _ (by decide), u₁.gpr]) u₂.gpr 256
    (Nat.le_refl _)).mono fun s₃ ⟨i₃, _, f₃, z₃⟩ => ?_)
  refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide)
  refine wp_stloc hp i₄ (d := laneOff) (by decide) fun s₅ i₅ v₅ _ _ m₅ => WP.block_nil ?_
  obtain ⟨l₅, _, c₅⟩ := loc_store hp (d := laneOff) (by decide) m₅
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have lt₃ : ∀ d, d + 4 ≤ 144 → lw s₀ s₃ d = lw s₀ s d := fun d hd => by
    rw [← lw_mem m₂ d]
    exact f₃.readW (r := ⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).sub_right (cell_in_mem b1)) (by decide)
  refine ⟨i₅, Prm.of_lw pr fun d hd => ?_, by rw [v₅, u₄.gpr]; rfl, ?_, fun k hk k0 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    have hd4 : d + 4 ≤ 144 := by rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [l₅ d (by omega_arith) (by rcases hd with rfl | rfl | rfl | rfl <;> decide), lw_mem u₄.mem, lt₃ d hd4]
  · rw [c₅ _ (by rw [← hb]; exact b1), u₄.mem, cell_blk hp _ b1,
      blk_of_words (f := fun _ => 0) fun i hi => by rw [← mw, Nat.zero_mul, Nat.zero_add]; exact z₃ i hi,
      ofWords_zero]
    rfl
  · rw [c₅ _ hk, u₄.mem, blockAt_keep f₃ (fun r hr => ?_), m₂, hm.block k hk]
    simp only [List.mem_singleton] at hr; subst hr
    exact cell_other hp (by rw [hb]; exact hk) b1 k0

/-- `reduce`: the XOR of every lane's last block, to the memory's first block. -/
theorem reduce_ok {s : State} {M : Array Block} (h : Inv s₀ s) (pr : Prm s₀ s)
    (hm : Represents s.mem (memB s₀) (prm s₀).blocks M) :
    WP isa Impl.Argon2.Arm.Derive.reduce s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      blockAt t.mem (matrixCell (memB s₀) 0) = Proof.Argon2.reduction (prm s₀) M 0 (lanesN s₀) zeroBlock := by
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.Arm.Derive.reduce
  refine WP.seq ((reduceStart_ok hp h pr hm).mono fun s₅ start => ?_)
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧ RI s₀ M l t) ?_ (lanesN s₀) s₅
    ⟨0, by omega_arith, hl1, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (reduceLane_ok hp ht hl).mono fun u ⟨hu, cu⟩ => ?_
  by_cases e : l + 1 = lanesN s₀
  · refine .inl ⟨by show VG.Arm.eval .ne u = _; rw [cu]; simp [e], hu.inv, hu.pr, ?_⟩
    rw [hu.first, e]
  · exact .inr ⟨by show VG.Arm.eval .ne u = _; rw [cu]; simp [e], _, by omega_arith, l + 1, rfl, by omega_arith, hu⟩

/-- `finalOutput`: H′ of the memory's first block, to `out`. -/
theorem finalOutput_ok {s : State} (h : Inv s₀ s) :
    WP isa Impl.Argon2.Arm.Derive.finalOutput s fun t => Inv s₀ t ∧
      bytesAt t.mem (State.addr (outP s₀)) (outL s₀) =
        Spec.Argon2.hPrime (outL s₀) (Spec.Argon2.serialize (blockAt s.mem (matrixCell (memB s₀) 0))) := by
  have b1 := blocks_pos hp
  have hm := hp.mem_fits
  have ho := hp.out_fits
  have tg := hp.tag_ge
  unfold Impl.Argon2.Arm.Derive.finalOutput
  refine WP.seq (wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => ?_)
  have i₁ := h.upd u₁ (by decide)
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide)
  refine wp_ldarg hp i₂ (i := 16) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide)
  refine wp_ldarg hp i₃ (i := 17) (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide)
  refine wp_ldarg hp i₄ (i := 15) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have i₅ := i₄.upd u₅ (by decide)
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have si : s₅.gpr .r0 = memP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ax : (s₅.gpr .r1).toNat = 1024 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl
  have di : s₅.gpr .r2 = outP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have cx : (s₅.gpr .r3).toNat = outL s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr]
  refine hcall_ok hp i₅ u₅.gpr
    ⟨memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ blocksN s₀ * 1024; omega_arith⟩
    (by rw [si, ax]; omega_arith) ⟨outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + outL s₀ ≤ outL s₀; omega_arith⟩
    (by rw [di, cx]; exact ho) (by rw [cx]; omega_arith) fun t it _ _ post => ⟨it, ?_⟩
  rw [← di, ← cx, post, cx, ax, si, m₅, cell0, Proof.Argon2.serialize_blockAt]

end

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: the final block and the tag, in two runs

`reduce_rel`: XORing every lane's last block into the first leaks the same
trace in two runs (the lane's last block's address is related by
correctness); `finalOutput_rel`: so does the call of H′ that writes the tag.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd wp_mov wp_sub op2_imm op2_reg)
open VG.Proof.Sha512.Arm (Only)
open VG.Spec.Argon2 (Block zeroBlock)
open VG.Impl.Argon2.Arm.Derive (argOff laneOff laneLenOff ld st)

theorem RI.of_only {s₀ s t : State} {M : Array Block} {l : Nat} (h : RI s₀ M l s) {ds : List Reg}
    (k : Only ds s t) (h11 : Reg.r11 ∉ ds) : RI s₀ M l t :=
  ⟨h.inv.only k h11, h.pr.of_mem k.mem, by rw [lw_mem k.mem]; exact h.lane, by rw [k.mem]; exact h.first,
    fun j hj j0 => by rw [k.mem]; exact h.rest j hj j0⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The first part of a lane's reduction: `r0 :=` the address of its last block. -/
theorem redPart1_ok {s : State} {M : Array Block} {l : Nat} (h : RI s₀ M l s) (hl : l < lanesN s₀) :
    WP isa (.block (([ld .r0 laneOff, ld .r1 laneLenOff, .dp .sub .r1 .r1 (.imm 1)] : List Instr) ++
      Impl.Argon2.Arm.Derive.blockAddr)) s fun t => RI s₀ M l t ∧
      t.gpr .r0 = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + ((prm s₀).laneLen - 1)) * 1024) := by
  have L8 := laneLen_ge hp
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h.inv (d := laneOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide)
  refine wp_ldloc hp i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => wp_sub (op2_imm (by decide)) fun s₃ u₃ => ?_
  have o₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  have i₃ := h.inv.only o₃ (by decide)
  rw [← List.append_nil Impl.Argon2.Arm.Derive.blockAddr]
  refine blockAddr_ok hp i₃ (h.pr.of_mem o₃.mem) hl (col := (prm s₀).laneLen - 1) (by omega_using [L8])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.lane])
    (by rw [u₃.gpr, u₂.gpr, lw_mem u₁.mem, h.pr.laneLen, ofNat_pred (by omega_using [L8]) rfl]) fun s₄ a₄ k₄ =>
      WP.block_nil ⟨h.of_only (o₃.trans k₄) (by decide), a₄⟩

/-- The instructions before `finalOutput`'s call of H′. -/
theorem foBlk_ok {s : State} (h : Inv s₀ s) :
    WP isa (.block [ld .r0 (argOff 13), .mov .r1 (.imm 1024), ld .r2 (argOff 16), ld .r3 (argOff 17),
      ld .r12 (argOff 15)]) s fun t => Inv s₀ t ∧ t.gpr .r12 = scrP s₀ ∧
      t.gpr .r0 = memP s₀ ∧ t.gpr .r1 = 1024 ∧ t.gpr .r2 = outP s₀ ∧ t.gpr .r3 = arg s₀ 17 := by
  refine wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide)
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide)
  refine wp_ldarg hp i₂ (i := 16) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide)
  refine wp_ldarg hp i₃ (i := 17) (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide)
  refine wp_ldarg hp i₄ (i := 15) (by decide) fun s₅ u₅ => WP.block_nil ⟨i₄.upd u₅ (by decide),
    u₅.gpr, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `reduce` leaks the same trace in two runs. -/
theorem reduce_rel {M₁ M₂ : Array Block} :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁ ∧ Represents s₁.mem (memB s₀₁) (prm s₀₁).blocks M₁) ∧
      (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂ ∧ Represents s₂.mem (memB s₀₂) (prm s₀₂).blocks M₂))
      Impl.Argon2.Arm.Derive.reduce fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  unfold Impl.Argon2.Arm.Derive.reduce
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => reduceStart_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => reduceStart_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  generalize hN : lanesN s₀₁ = N at hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      RI s₀₁ M₁ l s₁ ∧ RI s₀₂ M₂ l s₂) ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega_using [], hl1, h.1, h.2⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, g₁, g₂⟩ e₁ e₂
  have body : RelCT isa (fun s₁ s₂ => RI s₀₁ M₁ l s₁ ∧ RI s₀₂ M₂ l s₂)
      (.block (Impl.Argon2.Arm.Derive.reduceLane ++ Impl.Argon2.Arm.Derive.advance laneOff
        (argOff Impl.Argon2.Arm.Derive.lanesArg))) fun _ _ => True := by
    rw [show Impl.Argon2.Arm.Derive.reduceLane ++ Impl.Argon2.Arm.Derive.advance laneOff
        (argOff Impl.Argon2.Arm.Derive.lanesArg) =
      (([ld .r0 laneOff, ld .r1 laneLenOff, .dp .sub .r1 .r1 (.imm 1)] : List Instr) ++
        Impl.Argon2.Arm.Derive.blockAddr) ++
      (([.mov .r1 (.reg .r0), ld .r3 (argOff Impl.Argon2.Arm.Derive.memoryArg)] : List Instr) ++
        (Impl.Argon2.Arm.Derive.writeBlock true ++ Impl.Argon2.Arm.Derive.advance laneOff
          (argOff Impl.Argon2.Arm.Derive.lanesArg))) by
      simp only [Impl.Argon2.Arm.Derive.reduceLane, List.append_assoc]]
    refine RelCT.block_split (RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩)
        ⟨_, by taint_decide⟩)
      (fun s h => redPart1_ok T.hp₁ h (by rw [hN]; exact hl))
      (fun s h => redPart1_ok T.hp₂ h (by rw [hN₂]; exact hl)) ?_)
    exact T.leafI [.r0] (fun s₁ s₂ h => ⟨h.1.1.inv, h.2.1.inv, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2, h.2.2, pe, T.pb.memP_eq]⟩) ⟨_, by taint_decide⟩
  obtain ⟨ht, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩ := rel_wp body
    (fun s h => reduceLane_ok T.hp₁ h (by rw [hN]; exact hl))
    (fun s h => reduceLane_ok T.hp₂ h (by rw [hN₂]; exact hl)) s₁ s₂ t₁ t₂ s₁' s₂' ⟨g₁, g₂⟩ e₁ e₂
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show VG.Arm.eval .ne s₁' = VG.Arm.eval .ne s₂'; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 ≠ N := by
    rw [show isa.eval .ne s₁' = VG.Arm.eval .ne s₁' from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega_using [hn, hl], l + 1, rfl, by omega_using [hl, e], k₁, k₂⟩

/-- `finalOutput` leaks the same trace in two runs. -/
theorem finalOutput_rel :
    RelCT isa (fun s₁ s₂ => Inv s₀₁ s₁ ∧ Inv s₀₂ s₂) Impl.Argon2.Arm.Derive.finalOutput fun _ _ => True := by
  have pre : ∀ {s₀ : State}, DPre s₀ → ∀ {t : State}, Inv s₀ t ∧ t.gpr .r12 = scrP s₀ ∧
      t.gpr .r0 = memP s₀ ∧ t.gpr .r1 = 1024 ∧ t.gpr .r2 = outP s₀ ∧ t.gpr .r3 = arg s₀ 17 →
      Inv s₀ t ∧ t.gpr .r12 = scrP s₀ ∧
        (∃ R ∈ [memR s₀, locR s₀], ∃ off, State.addr (t.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .r1).toNat ≤ R.len) ∧ (t.gpr .r0).toNat + (t.gpr .r1).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀, outR s₀], ∃ off, State.addr (t.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .r3).toNat ≤ R.len) ∧ (t.gpr .r2).toNat + (t.gpr .r3).toNat ≤ 2 ^ 32 ∧
        1 ≤ (t.gpr .r3).toNat := fun {s₀} hp {t} ⟨i, d, si, ax, di, cx⟩ => by
    have b1 := blocks_pos hp
    have hm := hp.mem_fits
    have ho := hp.out_fits
    have tg := hp.tag_ge
    refine ⟨i, d, ⟨memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ blocksN s₀ * 1024; omega_using [b1]⟩,
      by rw [si, ax]; show _ + 1024 ≤ 2 ^ 32; omega_using [b1, hm],
      ⟨outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + outL s₀ ≤ outL s₀; omega_using []⟩,
      by rw [di, cx]; exact ho, by rw [cx]; show 1 ≤ outL s₀; omega_using [tg]⟩
  unfold Impl.Argon2.Arm.Derive.finalOutput
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => foBlk_ok T.hp₁ h) (fun s h => foBlk_ok T.hp₂ h) ?_
  refine T.hcall_rel fun s₁ s₂ ⟨k₁, k₂⟩ => ⟨pre T.hp₁ k₁, pre T.hp₂ k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.2.2.1, k₂.2.2.1, T.pb.memP_eq]
  · rw [k₁.2.2.2.1, k₂.2.2.2.1]
  · rw [k₁.2.2.2.2.1, k₂.2.2.2.2.1, T.pb.outP_eq]
  · rw [k₁.2.2.2.2.2, k₂.2.2.2.2.2, T.pb.arg_eq (by decide)]

end Two

end VG.Proof.Argon2.Arm.Derive

end

end

/-! ### `Argon2.Arm.Derive.FillCT3`, which only this module used -/

section

/-! ### `Argon2.Arm.Derive.FillCT2`, which only this module used -/

section

/-! ### `Argon2.Arm.Derive.FillCT1`, which only this module used -/

section

/-!
# Argon2 on ARMv7: the random word, in two runs

`W`: the public words of the filling loops' locals (the parameters, the
position and the counter), which `Two.leafF` makes public for the taint
analysis, with any registers the runs agree on. A store of a secret through
a register that is not `r11` makes the analysis forget every public word, so
the pieces are cut after such stores (and around the calls of G), and the
runs related again from what correctness says the locals and registers hold.
`randomSource_rel`: the random word's trace depends only on the position.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_imm op2_reg)
open VG.Proof.Sha512.Arm (Only)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff ld st)

/-- An empty block. -/
theorem RelCT.nil {P Q : State → State → Prop} (h : ∀ x y, P x y → Q x y) :
    RelCT isa P (.block []) Q := by
  intro x y t₁ t₂ x' y' hp e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨rfl, h _ _ hp⟩

/-- The public words of the filling loops' locals. -/
structure W (s₀ : State) (pass slice lane index ctr : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  pos : Pos s₀ s pass slice lane index
  ctr : lw s₀ s counterOff = BitVec.ofNat 32 ctr

theorem FS.w {s₀ s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) : W s₀ pass slice lane index ctr s :=
  ⟨h.inv, h.pr, h.pos, h.cache.2.1⟩

theorem W.of_only {s₀ s t : State} {pass slice lane index ctr : Nat} (h : W s₀ pass slice lane index ctr s)
    {ds : List Reg} (k : Only ds s t) (h11 : Reg.r11 ∉ ds) : W s₀ pass slice lane index ctr t :=
  ⟨h.inv.only k h11, h.pr.of_mem k.mem, h.pos.of_mem k.mem, by rw [lw_mem k.mem]; exact h.ctr⟩

/-- The words `W` is about. -/
abbrev ws0 : List Nat := [72, 76, 80, 84, 88, 92, 96, 100, 132]

/-- Their slots. -/
abbrev sl0 : List (Nat × Nat × Nat) := [(0, 72, 32), (0, 132, 4)]

theorem slotsOk0 (rs : List Reg) : VG.Arm.Taint.SlotsOk (τB sl0 rs) := by
  intro x hx
  simp only [τB, sl0, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp [τB]

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

theorem words {pass slice lane index ctr : Nat} {s₁ s₂ : State} (h₁ : W s₀₁ pass slice lane index ctr s₁)
    (h₂ : W s₀₂ pass slice lane index ctr s₂) : ∀ d ∈ ws0, lw s₀₁ s₁ d = lw s₀₂ s₂ d := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  intro d hd
  simp only [ws0, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁.pos.pass.trans h₂.pos.pass.symm
  · exact h₁.pos.lane.trans h₂.pos.lane.symm
  · exact h₁.pos.slice.trans h₂.pos.slice.symm
  · exact h₁.pos.index.trans h₂.pos.index.symm
  · exact h₁.ctr.trans h₂.ctr.symm
  · exact (h₁.pr.laneLen.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.laneLen) pe)).trans
      h₂.pr.laneLen.symm
  · exact (h₁.pr.stride.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 (p.laneLen * 1024)) pe)).trans
      h₂.pr.stride.symm
  · exact (h₁.pr.segLen.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.segmentLen) pe)).trans
      h₂.pr.segLen.symm
  · exact (h₁.pr.divisor.trans (congrArg (fun n : Nat => BitVec.ofNat 32 (4 * n)) le)).trans h₂.pr.divisor.symm

/-- A piece the taint analysis proves from the public words `W` and the
registers `rs`, which both runs agree on. -/
theorem leafF {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → (∃ pass slice lane index ctr, W s₀₁ pass slice lane index ctr s₁ ∧
      W s₀₂ pass slice lane index ctr s₂) ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (τB sl0 rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  T.leaf ws0 sl0 rs (slotsOk0 rs) (by decide) (fun s₁ s₂ h =>
    let ⟨⟨_, _, _, _, _, w₁, w₂⟩, hr⟩ := hag s₁ s₂ h
    ⟨w₁.inv, w₂.inv, T.words w₁ w₂, hr⟩) hc

end Two

/-! ## The address block -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The instructions before G's call in `stage x y o`. -/
theorem stageBlk_ok {s : State} (h : Inv s₀ s) {x y o : Nat} (ex : encodable (BitVec.ofNat 32 x) = true)
    (ey : encodable (BitVec.ofNat 32 y) = true) (eo : encodable (BitVec.ofNat 32 o) = true) :
    WP isa (.block [ld .r3 (argOff 15), .dp .add .r0 .r3 (.imm (BitVec.ofNat 32 x)),
      .dp .add .r1 .r3 (.imm (BitVec.ofNat 32 y)), .dp .add .r2 .r3 (.imm (BitVec.ofNat 32 o))]) s fun t =>
      Inv s₀ t ∧ t.gpr .r3 = scrP s₀ ∧ t.gpr .r0 = scrP s₀ + BitVec.ofNat 32 x ∧
      t.gpr .r1 = scrP s₀ + BitVec.ofNat 32 y ∧ t.gpr .r2 = scrP s₀ + BitVec.ofNat 32 o := by
  refine wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_add (op2_imm ex) fun s₂ u₂ =>
    wp_add (op2_imm ey) fun s₃ u₃ => wp_add (op2_imm eo) fun s₄ u₄ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]

/-- The counter, stored. -/
theorem stctr_w {s : State} {pass slice lane index ctr c : Nat} (h : W s₀ pass slice lane index ctr s)
    (ha : s.gpr .r0 = BitVec.ofNat 32 c) :
    WP isa (.block [st counterOff .r0]) s (W s₀ pass slice lane index c) :=
  wp_stloc hp h.inv (d := counterOff) (by decide) fun t it vt ot _ _ => WP.block_nil
    ⟨it, Prm.of_lw h.pr fun d hd => ot d (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl <;> decide),
    h.pos.of_lw fun d hd => ot d (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl <;> decide),
    by rw [vt, ha]⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `dependentWord` leaks the same trace in two runs at the same position. -/
theorem dependentWord_rel {pass slice lane index ctr : Nat} :
    RelCT isa (fun s₁ s₂ => W s₀₁ pass slice lane index ctr s₁ ∧ W s₀₂ pass slice lane index ctr s₂)
      Impl.Argon2.Arm.Derive.dependentWord fun _ _ => True :=
  T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩

/-- `stage x y o` leaks the same trace in two runs. -/
theorem stage_rel {x y o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384)
    (hx : 4096 ≤ x) (hx' : x + 1024 ≤ 16384) (hxo : x + 1024 ≤ o ∨ o + 1024 ≤ x)
    (hy : 4096 ≤ y) (hy' : y + 1024 ≤ 16384) (hyo : y + 1024 ≤ o ∨ o + 1024 ≤ y)
    (ex : encodable (BitVec.ofNat 32 x) = true) (ey : encodable (BitVec.ofNat 32 y) = true)
    (eo : encodable (BitVec.ofNat 32 o) = true)
    (hc : ∃ hc, (VG.Taint.check taint (τB [] []) (.block [ld .r3 (argOff 15),
      .dp .add .r0 .r3 (.imm (BitVec.ofNat 32 x)), .dp .add .r1 .r3 (.imm (BitVec.ofNat 32 y)),
      .dp .add .r2 .r3 (.imm (BitVec.ofNat 32 o))]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => Inv s₀₁ s₁ ∧ Inv s₀₂ s₂) (Impl.Argon2.Arm.Derive.stage x y o) fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.stage
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) hc)
    (fun s h => stageBlk_ok T.hp₁ h ex ey eo) (fun s h => stageBlk_ok T.hp₂ h ex ey eo) ?_
  refine T.ccall_rel ho ho' fun s₁ s₂ ⟨⟨i₁, d₁, a₁, e₁, c₁⟩, ⟨i₂, d₂, a₂, e₂, c₂⟩⟩ =>
    ⟨⟨i₁, d₁, c₁, by rw [a₁]; exact .inr ⟨x, hx, hx', hxo, rfl⟩, by rw [e₁]; exact .inr ⟨y, hy, hy', hyo, rfl⟩⟩,
     ⟨i₂, d₂, c₂, by rw [a₂]; exact .inr ⟨x, hx, hx', hxo, rfl⟩, by rw [e₂]; exact .inr ⟨y, hy, hy', hyo, rfl⟩⟩,
     by rw [a₁, a₂, T.pb.scrP_eq], by rw [e₁, e₂, T.pb.scrP_eq]⟩

/-- `addressCalls` leaks the same trace in two runs at the same position. -/
theorem addressCalls_rel {pass slice lane index c : Nat} (h₁ : pass < 2 ^ 32) (h₂ : lane < 2 ^ 32)
    (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    RelCT isa (fun s₁ s₂ => W s₀₁ pass slice lane index c s₁ ∧ W s₀₂ pass slice lane index c s₂)
      Impl.Argon2.Arm.Derive.addressCalls fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.addressCalls
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (input_ok T.hp₁ h.inv h.pos h.ctr h₁ h₂ h₃ h₄).mono fun t ht => ht.1)
    (fun s h => (input_ok T.hp₂ h.inv h.pos h.ctr h₁ h₂ h₃ h₄).mono fun t ht => ht.1) ?_
  refine RelCT.seqW (T.stage_rel (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩)
    (fun s h => (stage_ok T.hp₁ h (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono
      fun t ht => ht.1)
    (fun s h => (stage_ok T.hp₂ h (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono
      fun t ht => ht.1) ?_
  exact T.stage_rel (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩

/-- `addressCache` leaks the same trace in two runs at the same position. -/
theorem addressCache_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.Arm.Derive.addressCache fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have sl := segLen_lt T.hp₁
  have hlt := T.hp₁.lanes_lt
  unfold Impl.Argon2.Arm.Derive.addressCache
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => cacheCheck_ok T.hp₁ h hi) (fun s h => cacheCheck_ok T.hp₂ h hi₂) ?_
  refine RelCT.seqW (RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show VG.Arm.eval .eq s₁ = VG.Arm.eval .eq s₂
      rw [h₁.2.2, h₂.2.2, h₁.1.cache.2.1, h₂.1.cache.2.1])
    (RelCT.nil fun _ _ _ => trivial) ?_)
    (fun s h => cacheFill_ok T.hp₁ h.1 hpass hl hs hi h.2.1 h.2.2)
    (fun s h => cacheFill_ok T.hp₂ h.1 hpass hl₂ hs hi₂ h.2.1 h.2.2)
    (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.2.1.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
  refine RelCT.seqW (G₁ := W s₀₁ pass slice lane index (index / 128 + 1))
    (G₂ := W s₀₂ pass slice lane index (index / 128 + 1))
    (T.leafF [.r0] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.2.1.w⟩, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2.1, h.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun s h => stctr_w T.hp₁ h.1.w h.2.1) (fun s h => stctr_w T.hp₂ h.1.w h.2.1) ?_
  exact T.addressCalls_rel hpass (by omega_using [hl, hlt]) (by omega_using [hs]) (by omega_using [hi, sl])

/-- `randomSource` leaks the same trace in two runs at the same position. -/
theorem randomSource_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.Arm.Derive.randomSource fun _ _ => True := by
  have pe := T.pb.prm_eq
  unfold Impl.Argon2.Arm.Derive.randomSource
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => FS s₀₁ pass slice lane index ctr st₁ t ∧
      VG.Arm.eval .eq t = some (!Spec.Argon2.independent (prm s₀₁) pass slice))
    (G₂ := fun t => FS s₀₂ pass slice lane index ctr st₂ t ∧
      VG.Arm.eval .eq t = some (!Spec.Argon2.independent (prm s₀₂) pass slice))
    (fun s h => (addressMode_ok T.hp₁ h.inv h.pos hpass hs).mono fun t ⟨z, k⟩ => ⟨h.of_only k (by decide), z⟩)
    (fun s h => (addressMode_ok T.hp₂ h.inv h.pos hpass hs).mono fun t ⟨z, k⟩ => ⟨h.of_only k (by decide), z⟩) ?_
  refine RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show VG.Arm.eval .eq s₁ = VG.Arm.eval .eq s₂
      rw [h₁.2, h₂.2, pe])
    (T.dependentWord_rel.mono (fun _ _ h => ⟨h.1.1.w, h.2.1.w⟩) fun _ _ h => h)
    ((T.addressCache_rel hpass hl hs hi).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)

end Two

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: a block of the filling loops, in two runs

`fillBlock_rel`: one block's trace depends only on its position and on the
reference block's index, which the leakage permits (`Spec.Argon2.references`):
the reference is computed from the random word in the locals, with no
address or branch depending on it (`reference_rel`), G is called on the
previous and the reference blocks (`fillCompress_rel`), and its output is
written to the current block (`fillWrite_rel`), whose address the runs agree
on.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_imm op2_reg)
open VG.Proof.Sha512.Arm (Only)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff j1Off j2Off refLaneOff tmpOff curOff ld st)

/-- The slots of the words `ws0` and `ex`. -/
abbrev slx (ex : List Nat) : List (Nat × Nat × Nat) := sl0 ++ ex.map fun d => (0, d, 4)

theorem slotsOkX {ex : List Nat} (hex : ∀ d ∈ ex, d % 4 = 0 ∧ d + 4 ≤ 144) (rs : List Reg) :
    VG.Arm.Taint.SlotsOk (τB (slx ex) rs) := by
  intro x hx
  simp only [τB, slx, List.append_assoc, List.mem_append, List.mem_map] at hx
  rcases hx with hx | ⟨d, hd, rfl⟩ | hx
  · exact slotsOk0 rs x (by simp only [τB]; exact List.mem_append_left _ hx)
  · have := hex d hd; simp [τB]; omega_using [this]
  · exact slotsOk0 rs x (by simp only [τB]; exact List.mem_append_right _ hx)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- As `leafF`, with the words `ex` of the locals public too. -/
theorem leafX {P : State → State → Prop} {c : Prog isa} (rs : List Reg) (ex : List Nat)
    (hex : ∀ d ∈ ex, d % 4 = 0 ∧ d + 4 ≤ 144)
    (hag : ∀ s₁ s₂, P s₁ s₂ → (∃ pass slice lane index ctr, W s₀₁ pass slice lane index ctr s₁ ∧
      W s₀₂ pass slice lane index ctr s₂) ∧ (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧
      ∀ d ∈ ex, lw s₀₁ s₁ d = lw s₀₂ s₂ d)
    (hc : ∃ hc, (VG.Taint.check taint (τB (slx ex) rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  refine T.leaf (ws0 ++ ex) (slx ex) rs (slotsOkX hex rs) (fun x hx => ?_) (fun s₁ s₂ h => ?_) hc
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨h0, hj⟩ := (show ∀ x ∈ sl0, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ ws0 by decide) x hx
      exact ⟨h0, fun j hj' => List.mem_append_left _ (hj j hj')⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      refine ⟨rfl, fun j hj => List.mem_append_right _ ?_⟩
      have := (hex d hd).1
      rw [show 4 * ((d + j) / 4) = d by simp only at hj; omega_using [hj, this]]
      exact hd
  · obtain ⟨⟨_, _, _, _, _, w₁, w₂⟩, hr, he⟩ := hag s₁ s₂ h
    refine ⟨w₁.inv, w₂.inv, fun d hd => ?_, hr⟩
    rcases List.mem_append.mp hd with hd | hd
    · exact T.words w₁ w₂ d hd
    · exact he d hd

/-- `reference` leaks the same trace in two runs at the same position: it
reads the random word, but neither branches on it nor addresses memory with it. -/
theorem reference_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} {J1 J2 J1' J2' : BitVec 32} :
    RelCT isa (fun s₁ s₂ => RS s₀₁ pass slice lane index ctr st₁ J1 J2 s₁ ∧
      RS s₀₂ pass slice lane index ctr st₂ J1' J2' s₂) Impl.Argon2.Arm.Derive.reference fun _ _ => True :=
  T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩) ⟨_, by taint_decide⟩

end Two

/-! ## G and the new block -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The instructions before `fillCompress`'s call of G. -/
theorem fcBlk_ok {s : State} {pass slice lane index ctr : Nat} (h : W s₀ pass slice lane index ctr s)
    {P R : Nat} (ha : s.gpr .r0 = memP s₀ + BitVec.ofNat 32 (P * 1024))
    (htmp : lw s₀ s tmpOff = memP s₀ + BitVec.ofNat 32 (R * 1024)) :
    WP isa (.block [ld .r1 tmpOff, ld .r3 (argOff 15), .dp .add .r2 .r3 (.imm 4096)]) s fun t =>
      Inv s₀ t ∧ t.gpr .r3 = scrP s₀ ∧ t.gpr .r2 = scrP s₀ + BitVec.ofNat 32 4096 ∧
      t.gpr .r0 = memP s₀ + BitVec.ofNat 32 (P * 1024) ∧ t.gpr .r1 = memP s₀ + BitVec.ofNat 32 (R * 1024) := by
  refine wp_ldloc hp h.inv (d := tmpOff) (by decide) fun s₂ u₂ => wp_ldarg hp (h.inv.upd u₂ (by decide))
    (i := 15) (by decide) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil
    ⟨((h.inv.upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide), ?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr]
  · rw [u₄.gpr, u₃.gpr]; rfl
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), ha]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, htmp]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `fillCompress` leaks the same trace in two runs at the same position and
with the same reference block. -/
theorem fillCompress_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hl : lane < lanesN s₀₁)
    (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen) {R : Nat} (hR : R < blocksN s₀₁) :
    RelCT isa (fun s₁ s₂ => (FS s₀₁ pass slice lane index ctr st₁ s₁ ∧
        lw s₀₁ s₁ tmpOff = memP s₀₁ + BitVec.ofNat 32 (R * 1024)) ∧
      (FS s₀₂ pass slice lane index ctr st₂ s₂ ∧ lw s₀₂ s₂ tmpOff = memP s₀₂ + BitVec.ofNat 32 (R * 1024)))
      Impl.Argon2.Arm.Derive.fillCompress fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have hR₂ : R < blocksN s₀₂ := T.pb.blocksN_eq ▸ hR
  have L8 := laneLen_ge T.hp₁
  obtain ⟨cl, _⟩ := cell_fits T.hp₁ hl (col := (slice * (prm s₀₁).segmentLen + index + (prm s₀₁).laneLen - 1) %
    (prm s₀₁).laneLen) (Nat.mod_lt _ (by omega_using [L8]))
  have L8₂ := laneLen_ge T.hp₂
  obtain ⟨cl₂, _⟩ := cell_fits T.hp₂ hl₂ (col := (slice * (prm s₀₂).segmentLen + index + (prm s₀₂).laneLen - 1) %
    (prm s₀₂).laneLen) (Nat.mod_lt _ (by omega_using [L8₂]))
  unfold Impl.Argon2.Arm.Derive.fillCompress
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.2.1.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => W s₀₁ pass slice lane index ctr t ∧ t.gpr .r0 = memP s₀₁ + BitVec.ofNat 32
      ((lane * (prm s₀₁).laneLen + (slice * (prm s₀₁).segmentLen + index + (prm s₀₁).laneLen - 1) %
        (prm s₀₁).laneLen) * 1024) ∧ lw s₀₁ t tmpOff = memP s₀₁ + BitVec.ofNat 32 (R * 1024))
    (G₂ := fun t => W s₀₂ pass slice lane index ctr t ∧ t.gpr .r0 = memP s₀₂ + BitVec.ofNat 32
      ((lane * (prm s₀₂).laneLen + (slice * (prm s₀₂).segmentLen + index + (prm s₀₂).laneLen - 1) %
        (prm s₀₂).laneLen) * 1024) ∧ lw s₀₂ t tmpOff = memP s₀₂ + BitVec.ofNat 32 (R * 1024))
    (fun s h => (prevPointer_ok T.hp₁ h.1.inv h.1.pr h.1.pos hl hs hi).mono fun t ⟨a, k⟩ =>
      ⟨h.1.w.of_only k (by decide), a, by rw [lw_mem k.mem]; exact h.2⟩)
    (fun s h => (prevPointer_ok T.hp₂ h.1.inv h.1.pr h.1.pos hl₂ hs hi₂).mono fun t ⟨a, k⟩ =>
      ⟨h.1.w.of_only k (by decide), a, by rw [lw_mem k.mem]; exact h.2⟩) ?_
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1, h.2.1⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => fcBlk_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => fcBlk_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine T.ccall_rel (o := 4096) (by decide) (by decide) fun s₁ s₂ ⟨⟨i₁, d₁, c₁, a₁, e₁⟩, ⟨i₂, d₂, c₂, a₂, e₂⟩⟩ =>
    ⟨⟨i₁, d₁, c₁, by rw [a₁]; exact .inl ⟨_, cl, rfl⟩, by rw [e₁]; exact .inl ⟨R, hR, rfl⟩⟩,
     ⟨i₂, d₂, c₂, by rw [a₂]; exact .inl ⟨_, cl₂, rfl⟩, by rw [e₂]; exact .inl ⟨R, hR₂, rfl⟩⟩,
     by rw [a₁, a₂, pe, T.pb.memP_eq], by rw [e₁, e₂, T.pb.memP_eq]⟩

/-- `fillWrite` leaks the same trace in two runs at the same position. -/
theorem fillWrite_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} :
    RelCT isa (fun s₁ s₂ => (FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂) ∧
      lw s₀₁ s₁ curOff = lw s₀₂ s₂ curOff) Impl.Argon2.Arm.Derive.fillWrite fun _ _ => True :=
  T.leafX [] [curOff] (by decide) (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.1.2.w⟩, by simp, by
    simp only [List.mem_singleton, forall_eq]; exact h.2⟩) ⟨_, by taint_decide⟩

/-- `fillBlock` leaks the same trace in two runs at the same position whose
reference blocks agree. -/
theorem fillBlock_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : index < (prm s₀₁).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index)
    (href : Spec.Argon2.reference (prm s₀₁) pass lane slice index
        (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory) =
      Spec.Argon2.reference (prm s₀₂) pass lane slice index
        (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.Arm.Derive.fillBlock fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have hb₁ : blocksN s₀₁ = (prm s₀₁).blocks := T.hp₁.blocks
  have refLt := Proof.Argon2.reference_cell_lt (prm s₀₁) T.hp₁.lanes_pos T.hp₁.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory) hl
  simp only at refLt
  generalize hR : (Spec.Argon2.reference (prm s₀₁) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory)).1 * (prm s₀₁).laneLen +
    (Spec.Argon2.reference (prm s₀₁) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice index st₁.memory)).2 = R at refLt
  have hR₂ : (Spec.Argon2.reference (prm s₀₂) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)).1 * (prm s₀₂).laneLen +
    (Spec.Argon2.reference (prm s₀₂) pass lane slice index
      (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice index st₂.memory)).2 = R := by
    rw [← href, ← pe]; exact hR
  generalize hC : lane * (prm s₀₁).laneLen + (slice * (prm s₀₁).segmentLen + index) = C
  have hC₂ : lane * (prm s₀₂).laneLen + (slice * (prm s₀₂).segmentLen + index) = C := by rw [← pe]; exact hC
  unfold Impl.Argon2.Arm.Derive.fillBlock
  refine RelCT.seqW (T.randomSource_rel hpass hl hs hi)
    (fun s h => randomSource_ok T.hp₁ h hpass hl hs hi) (fun s h => randomSource_ok T.hp₂ h hpass hl₂ hs hi₂) ?_
  refine RelCT.seq (rel_wp (G := fun t =>
      FS s₀₁ pass slice lane index (ctrNext (prm s₀₁) pass slice index ctr) st₁ t ∧
      lw s₀₁ t tmpOff = memP s₀₁ + BitVec.ofNat 32 (R * 1024) ∧
      lw s₀₁ t curOff = memP s₀₁ + BitVec.ofNat 32 (C * 1024))
    (G' := fun t => FS s₀₂ pass slice lane index (ctrNext (prm s₀₂) pass slice index ctr) st₂ t ∧
      lw s₀₂ t tmpOff = memP s₀₂ + BitVec.ofNat 32 (R * 1024) ∧
      lw s₀₂ t curOff = memP s₀₂ + BitVec.ofNat 32 (C * 1024))
    (RelCT.of_eq fun s₁ s₂ ⟨g₁, g₂⟩ => (T.reference_rel (J1 := lw s₀₁ s₁ j1Off) (J2 := lw s₀₁ s₁ j2Off)
      (J1' := lw s₀₂ s₂ j1Off) (J2' := lw s₀₂ s₂ j2Off)).mono (fun a b ⟨ha, hb⟩ => by
        subst a b
        rw [← pe] at g₂
        exact ⟨⟨g₁.1, rfl, rfl⟩, ⟨g₂.1, rfl, rfl⟩⟩) fun _ _ h => h)
    (fun s g => (reference_ok T.hp₁ ⟨g.1, rfl, rfl⟩ hpass hl hs hi active).mono fun t ⟨r, tmp, cur⟩ =>
      ⟨r.fs, by rw [tmp, g.2, hR], by rw [cur, hC]⟩)
    (fun s g => (reference_ok T.hp₂ ⟨g.1, rfl, rfl⟩ hpass hl₂ hs hi₂ active).mono fun t ⟨r, tmp, cur⟩ =>
      ⟨r.fs, by rw [tmp, g.2, hR₂], by rw [cur, hC₂]⟩)) ?_
  rw [show ctrNext (prm s₀₂) pass slice index ctr = ctrNext (prm s₀₁) pass slice index ctr by rw [pe]]
  refine RelCT.seq (rel_wp (G := fun t =>
      FS s₀₁ pass slice lane index (ctrNext (prm s₀₁) pass slice index ctr) st₁ t ∧
      lw s₀₁ t curOff = memP s₀₁ + BitVec.ofNat 32 (C * 1024))
    (G' := fun t => FS s₀₂ pass slice lane index (ctrNext (prm s₀₁) pass slice index ctr) st₂ t ∧
      lw s₀₂ t curOff = memP s₀₂ + BitVec.ofNat 32 (C * 1024))
    ((T.fillCompress_rel hl hs hi (by rw [hb₁]; exact refLt)).mono
      (fun _ _ h => ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1, h.2.2.1⟩⟩) fun _ _ h => h)
    (fun s g => (fillCompress_ok T.hp₁ g.1 hl hs hi (by rw [hb₁]; exact refLt) g.2.1).mono
      fun t ⟨f, l, _⟩ => ⟨f, by rw [l _ (by decide), g.2.2]⟩)
    (fun s g => (fillCompress_ok T.hp₂ g.1 hl₂ hs hi₂ (by rw [← T.pb.blocksN_eq, hb₁]; exact refLt) g.2.1).mono
      fun t ⟨f, l, _⟩ => ⟨f, by rw [l _ (by decide), g.2.2]⟩)) ?_
  exact T.fillWrite_rel.mono (fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, by rw [h.1.2, h.2.2, T.pb.memP_eq]⟩) fun _ _ h => h

end Two

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: the filling loops, in two runs

The loops run in lockstep in two runs with the same public data: their
positions and counters agree, and so do the indices of the data-dependent
references still to be made (the rest of `Spec.Argon2.references`), from
which each block's reference agrees (`ref_same`). `passes_rel`: the filling
loops leak the same trace in two runs whose references agree.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff ld st)

/-- A block's reference, in two runs whose references from it on agree. -/
theorem ref_same (p : Spec.Argon2.Params) (pass lane slice i count : Nat) (X₁ X₂ : FillState)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i)
    (h : (Proof.Argon2.segment p pass lane slice i (count + 1) X₁).indices =
      (Proof.Argon2.segment p pass lane slice i (count + 1) X₂).indices) :
    Spec.Argon2.reference p pass lane slice i (Proof.Argon2.FillStep.random p pass lane slice i X₁.memory) =
      Spec.Argon2.reference p pass lane slice i (Proof.Argon2.FillStep.random p pass lane slice i X₂.memory) := by
  cases hind : Spec.Argon2.independent p pass slice
  · exact Proof.Argon2.segment_first_reference p pass lane slice i count X₁ X₂ active h hind
  · unfold Proof.Argon2.FillStep.random
    rw [hind]
    rfl

/-- The words of the locals a lane's state fixes. -/
abbrev wsL : List Nat := [72, 76, 80, 92, 96, 100, 132]

theorem slotsOkL : VG.Arm.Taint.SlotsOk (τB [(0, 72, 12), (0, 92, 12), (0, 132, 4)]) := by
  intro x hx
  simp only [τB, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [τB]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `setLocal d v`, alone. -/
theorem setLocal_w {s : State} {st : FillState} (h : FB s₀ st s) {d : Nat} (hd : d + 4 ≤ 144)
    (hd' : ∀ e ∈ [divisorOff, segLenOff, laneLenOff, strideOff], e + 4 ≤ d ∨ d + 4 ≤ e) {v : BitVec 32}
    (hv : encodable v = true) :
    WP isa (.block (Impl.Argon2.Arm.Derive.setLocal d v)) s fun t => FB s₀ st t ∧ lw s₀ t d = v ∧
      ∀ e, e + 4 ≤ 256 → (d + 4 ≤ e ∨ e + 4 ≤ d) → lw s₀ t e = lw s₀ s e := by
  rw [← List.append_nil (Impl.Argon2.Arm.Derive.setLocal _ _)]
  exact setLocal_ok hp h hd hd' hv fun t f v o _ => WP.block_nil ⟨f, v, o⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

theorem wordsL {st₁ st₂ : FillState} {pass slice lane : Nat} {s₁ s₂ : State}
    (h₁ : LS s₀₁ st₁ pass slice lane s₁) (h₂ : LS s₀₂ st₂ pass slice lane s₂) :
    ∀ d ∈ wsL, lw s₀₁ s₁ d = lw s₀₂ s₂ d := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  intro d hd
  simp only [wsL, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁.pass.trans h₂.pass.symm
  · exact h₁.lane.trans h₂.lane.symm
  · exact h₁.slice.trans h₂.slice.symm
  · exact (h₁.fb.pr.laneLen.trans (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.laneLen) pe)).trans
      h₂.fb.pr.laneLen.symm
  · exact (h₁.fb.pr.stride.trans
      (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 (p.laneLen * 1024)) pe)).trans h₂.fb.pr.stride.symm
  · exact (h₁.fb.pr.segLen.trans
      (congrArg (fun p : Spec.Argon2.Params => BitVec.ofNat 32 p.segmentLen) pe)).trans h₂.fb.pr.segLen.symm
  · exact (h₁.fb.pr.divisor.trans (congrArg (fun n : Nat => BitVec.ofNat 32 (4 * n)) le)).trans
      h₂.fb.pr.divisor.symm

/-- `segmentStart` leaks the same trace in two runs at the same lane. -/
theorem segmentStart_rel {pass slice lane : Nat} {st₁ st₂ : FillState} :
    RelCT isa (fun s₁ s₂ => LS s₀₁ st₁ pass slice lane s₁ ∧ LS s₀₂ st₂ pass slice lane s₂)
      Impl.Argon2.Arm.Derive.segmentStart fun _ _ => True :=
  T.leaf wsL [(0, 72, 12), (0, 92, 12), (0, 132, 4)] [] slotsOkL (by decide)
    (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, T.wordsL h.1 h.2, by simp⟩) ⟨_, by taint_decide⟩

/-- A block of a segment and the index advanced, in two runs at the same
position whose reference blocks agree. -/
theorem segBody_rel {pass slice lane i c : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀₁) (hs : slice < 4) (hi : i < (prm s₀₁).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i)
    (href : Spec.Argon2.reference (prm s₀₁) pass lane slice i
        (Proof.Argon2.FillStep.random (prm s₀₁) pass lane slice i X₁.memory) =
      Spec.Argon2.reference (prm s₀₂) pass lane slice i
        (Proof.Argon2.FillStep.random (prm s₀₂) pass lane slice i X₂.memory)) :
    RelCT isa (fun s₁ s₂ => FS s₀₁ pass slice lane i c X₁ s₁ ∧ FS s₀₂ pass slice lane i c X₂ s₂)
      (.seq Impl.Argon2.Arm.Derive.fillBlock
        (.block (Impl.Argon2.Arm.Derive.advance indexOff segLenOff)))
      fun v₁ v₂ => (FS s₀₁ pass slice lane (i + 1) (ctrNext (prm s₀₁) pass slice i c)
          (Spec.Argon2.fillBlock (prm s₀₁) pass slice lane i X₁) v₁ ∧
          VG.Arm.eval .ne v₁ = some (!decide (i + 1 = (prm s₀₁).segmentLen))) ∧
        (FS s₀₂ pass slice lane (i + 1) (ctrNext (prm s₀₂) pass slice i c)
          (Spec.Argon2.fillBlock (prm s₀₂) pass slice lane i X₂) v₂ ∧
          VG.Arm.eval .ne v₂ = some (!decide (i + 1 = (prm s₀₂).segmentLen))) := by
  have pe := T.pb.prm_eq
  have hi₂ : i < (prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  refine rel_wp (RelCT.seqW (T.fillBlock_rel hpass hl hs hi active href)
    (fun s h => fillBlock_ok T.hp₁ h hpass hl hs hi active)
    (fun s h => fillBlock_ok T.hp₂ h hpass hl₂ hs hi₂ active)
    (T.leafF [] (fun s₁ s₂ h => by
      have h₂ := h.2
      rw [← pe] at h₂
      exact ⟨⟨_, _, _, _, _, h.1.w, h₂.w⟩, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => segStep_ok T.hp₁ h hpass hl hs hi active) (fun s h => segStep_ok T.hp₂ h hpass hl₂ hs hi₂ active)

/-- `segment` leaks the same trace in two runs at the same lane whose
references in it agree. -/
theorem segment_rel {pass slice lane : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hl : lane < lanesN s₀₁)
    (hind : (Proof.Argon2.segment (prm s₀₁) pass lane slice 0 (prm s₀₁).segmentLen st₁).indices =
      (Proof.Argon2.segment (prm s₀₁) pass lane slice 0 (prm s₀₁).segmentLen st₂).indices) :
    RelCT isa (fun s₁ s₂ => LS s₀₁ st₁ pass slice lane s₁ ∧ LS s₀₂ st₂ pass slice lane s₂)
      Impl.Argon2.Arm.Derive.segment fun _ _ => True := by
  have pe := T.pb.prm_eq
  have s2 := T.hp₁.segLen_two
  have hS : Proof.Argon2.segmentStart pass slice ≤ 2 := by unfold Proof.Argon2.segmentStart; split <;> omega_arith
  have hS2 : pass = 0 → slice = 0 → Proof.Argon2.segmentStart pass slice = 2 := fun a b => by
    unfold Proof.Argon2.segmentStart; rw [ite_eq_left ⟨a, b⟩]
  rw [Proof.Argon2.segment_start _ _ _ _ _ s2, Proof.Argon2.segment_start _ _ _ _ _ s2] at hind
  generalize hSd : Proof.Argon2.segmentStart pass slice = S at hS hS2 hind
  generalize hL : (prm s₀₁).segmentLen = L at hind s2
  have hL₂ : (prm s₀₂).segmentLen = L := by rw [← pe, hL]
  unfold Impl.Argon2.Arm.Derive.segment
  refine RelCT.seq (rel_wp T.segmentStart_rel
    (fun s h => segmentStart_ok T.hp₁ h hpass hs) (fun s h => segmentStart_ok T.hp₂ h hpass hs)) ?_
  rw [hSd]
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => segCmp_ok T.hp₁ h hS) (fun s h => segCmp_ok T.hp₂ h hS) ?_
  refine RelCT.ite (fun s₁ s₂ h => by
      show VG.Arm.eval .eq s₁ = VG.Arm.eval .eq s₂
      rw [h.1.2, h.2.2, hL, hL₂]) (RelCT.nil fun _ _ _ => trivial) ?_
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ i, n = L - i ∧ S ≤ i ∧ i < L ∧ ∃ c,
      FS s₀₁ pass slice lane i c (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₁) s₁ ∧
      FS s₀₂ pass slice lane i c (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₂) s₂ ∧
      (Proof.Argon2.segment (prm s₀₁) pass lane slice i (L - i)
          (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₁)).indices =
        (Proof.Argon2.segment (prm s₀₁) pass lane slice i (L - i)
          (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) st₂)).indices) ?step (L - S)).mono
    (fun s₁ s₂ ⟨⟨⟨h₁, c₁⟩, ⟨h₂, _⟩⟩, e⟩ => ?init) fun _ _ h => h
  case init =>
    have hb : S < L := by
      rw [show isa.eval .eq s₁ = VG.Arm.eval .eq s₁ from rfl, c₁, hL] at e
      have := of_decide_eq_false (Option.some.inj e)
      omega_arith
    exact ⟨S, rfl, Nat.le_refl _, hb, 0, by rw [Nat.sub_self]; exact h₁, by rw [Nat.sub_self]; exact h₂,
      by rw [Nat.sub_self]; exact hind⟩
  case step =>
    intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨i, hn, hSi, hi, c, h₁, h₂, hidx⟩ e₁ e₂
    have active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i := by
      by_cases a : pass = 0
      · by_cases b : slice = 0
        · have := hS2 a b; omega_arith
        · exact .inr (.inl b)
      · exact .inl a
    rw [show L - i = (L - (i + 1)) + 1 by omega_arith] at hidx
    have href := ref_same (prm s₀₁) pass lane slice i (L - (i + 1)) _ _ active hidx
    rw [Proof.Argon2.segment_succ, Proof.Argon2.segment_succ] at hidx
    obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.segBody_rel (c := c) hpass hl hs (by rw [hL]; exact hi) active
      (by rw [← pe]; exact href) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
    rw [← pe] at g₂ c₂
    have eq₁ : ∀ X, Proof.Argon2.segment (prm s₀₁) pass lane slice S (i + 1 - S) X =
        Spec.Argon2.fillBlock (prm s₀₁) pass slice lane i (Proof.Argon2.segment (prm s₀₁) pass lane slice S (i - S) X) :=
      fun X => by rw [show i + 1 - S = (i - S) + 1 by omega_arith, segment_snoc, show S + (i - S) = i by omega_arith]
    rw [← eq₁] at g₁ g₂ hidx
    rw [← eq₁] at hidx
    rw [hL] at c₁ c₂
    refine ⟨ht, by show VG.Arm.eval .ne s₁' = VG.Arm.eval .ne s₂'; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
    have e : i + 1 ≠ L := by
      rw [show isa.eval .ne s₁' = VG.Arm.eval .ne s₁' from rfl, c₁] at hc
      simpa using hc
    exact ⟨L - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, by omega_arith, _, g₁, g₂, hidx⟩

/-- A lane's segment and the lane advanced, in two runs. -/
theorem laneBody_rel {pass slice l : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hl : l < lanesN s₀₁)
    (hind : (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₁).indices =
      (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₂).indices) :
    RelCT isa (fun s₁ s₂ => LS s₀₁ X₁ pass slice l s₁ ∧ LS s₀₂ X₂ pass slice l s₂)
      (.seq Impl.Argon2.Arm.Derive.segment (.block (Impl.Argon2.Arm.Derive.advance laneOff (argOff 7))))
      fun v₁ v₂ => (LS s₀₁ (Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen X₁) pass slice
          (l + 1) v₁ ∧ VG.Arm.eval .ne v₁ = some (!decide (l + 1 = lanesN s₀₁))) ∧
        (LS s₀₂ (Proof.Argon2.segment (prm s₀₂) pass l slice 0 (prm s₀₂).segmentLen X₂) pass slice (l + 1) v₂ ∧
          VG.Arm.eval .ne v₂ = some (!decide (l + 1 = lanesN s₀₂))) := by
  have hl₂ : l < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  exact rel_wp (RelCT.seqW (T.segment_rel hpass hs hl hind)
    (fun s h => segment_ok T.hp₁ h hpass hs hl) (fun s h => segment_ok T.hp₂ h hpass hs hl₂)
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => laneStep_ok T.hp₁ h hpass hs hl) (fun s h => laneStep_ok T.hp₂ h hpass hs hl₂)

/-- `lanesLoop` leaks the same trace in two runs at the same slice whose
references in it agree. -/
theorem lanes_rel {pass slice : Nat} {Y₁ Y₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hind : (Proof.Argon2.lanes (prm s₀₁) pass slice 0 (lanesN s₀₁) Y₁).indices =
      (Proof.Argon2.lanes (prm s₀₁) pass slice 0 (lanesN s₀₁) Y₂).indices) :
    RelCT isa (fun s₁ s₂ => SS s₀₁ Y₁ pass slice s₁ ∧ SS s₀₂ Y₂ pass slice s₂)
      Impl.Argon2.Arm.Derive.lanesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.Arm.Derive.lanesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (setLocal_w T.hp₁ h.fb (d := laneOff) (by decide) (by decide) (by decide)).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, by rw [o _ (by decide) (by decide)]; exact h.slice,
        v⟩ : LS s₀₁ Y₁ pass slice 0 t))
    (fun s h => (setLocal_w T.hp₂ h.fb (d := laneOff) (by decide) (by decide) (by decide)).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, by rw [o _ (by decide) (by decide)]; exact h.slice,
        v⟩ : LS s₀₂ Y₂ pass slice 0 t)) ?_
  generalize hN : lanesN s₀₁ = N at hind hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      LS s₀₁ (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₁) pass slice l s₁ ∧
      LS s₀₂ (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₂) pass slice l s₂ ∧
      (Proof.Argon2.lanes (prm s₀₁) pass slice l (N - l) (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₁)).indices =
        (Proof.Argon2.lanes (prm s₀₁) pass slice l (N - l) (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l Y₂)).indices)
    ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega_arith, hl1, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, h₁, h₂, hidx⟩ e₁ e₂
  rw [show N - l = (N - (l + 1)) + 1 by omega_arith] at hidx
  have hseg := Proof.Argon2.lanes_first_segment (prm s₀₁) pass slice l (N - (l + 1)) _ _ s2 hidx
  rw [Proof.Argon2.lanes_succ, Proof.Argon2.lanes_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.laneBody_rel hpass hs (by rw [hN]; exact hl) hseg
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe] at g₂
  have eq : ∀ X, Proof.Argon2.segment (prm s₀₁) pass l slice 0 (prm s₀₁).segmentLen
      (Proof.Argon2.lanes (prm s₀₁) pass slice 0 l X) = Proof.Argon2.lanes (prm s₀₁) pass slice 0 (l + 1) X :=
    fun X => by unfold Proof.Argon2.lanes; rw [foldl_range'_snoc, Nat.zero_add]
  rw [eq] at g₁ g₂ hidx
  rw [eq] at hidx
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show VG.Arm.eval .ne s₁' = VG.Arm.eval .ne s₂'; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 ≠ N := by
    rw [show isa.eval .ne s₁' = VG.Arm.eval .ne s₁' from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega_arith, l + 1, rfl, by omega_arith, g₁, g₂, hidx⟩

/-- A slice's lanes and the slice advanced, in two runs. -/
theorem sliceBody_rel {pass j : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32) (hj : j < 4)
    (hind : (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₁).indices =
      (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₂).indices) :
    RelCT isa (fun s₁ s₂ => SS s₀₁ X₁ pass j s₁ ∧ SS s₀₂ X₂ pass j s₂)
      (.seq Impl.Argon2.Arm.Derive.lanesLoop (.block (Impl.Argon2.Arm.Derive.advanceImm sliceOff 4)))
      fun v₁ v₂ => (SS s₀₁ (Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) X₁) pass (j + 1) v₁ ∧
          VG.Arm.eval .ne v₁ = some (!decide (j + 1 = 4))) ∧
        (SS s₀₂ (Proof.Argon2.lanes (prm s₀₂) pass j 0 (lanesN s₀₂) X₂) pass (j + 1) v₂ ∧
          VG.Arm.eval .ne v₂ = some (!decide (j + 1 = 4))) :=
  rel_wp (RelCT.seqW (T.lanes_rel hpass hj hind)
    (fun s h => lanes_ok T.hp₁ h hpass hj) (fun s h => lanes_ok T.hp₂ h hpass hj)
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => sliceStep_ok T.hp₁ h hpass hj) (fun s h => sliceStep_ok T.hp₂ h hpass hj)

/-- `slicesLoop` leaks the same trace in two runs at the same pass whose
references in it agree. -/
theorem slices_rel {pass : Nat} {Z₁ Z₂ : FillState} (hpass : pass < 2 ^ 32)
    (hind : (Proof.Argon2.slices (prm s₀₁) pass 0 4 Z₁).indices =
      (Proof.Argon2.slices (prm s₀₁) pass 0 4 Z₂).indices) :
    RelCT isa (fun s₁ s₂ => PS s₀₁ Z₁ pass s₁ ∧ PS s₀₂ Z₂ pass s₂)
      Impl.Argon2.Arm.Derive.slicesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.Arm.Derive.slicesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (setLocal_w T.hp₁ h.fb (d := sliceOff) (by decide) (by decide) (by decide)).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, v⟩ : SS s₀₁ Z₁ pass 0 t))
    (fun s h => (setLocal_w T.hp₂ h.fb (d := sliceOff) (by decide) (by decide) (by decide)).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, v⟩ : SS s₀₂ Z₂ pass 0 t)) ?_
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ j, n = 4 - j ∧ j < 4 ∧
      SS s₀₁ (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₁) pass j s₁ ∧
      SS s₀₂ (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₂) pass j s₂ ∧
      (Proof.Argon2.slices (prm s₀₁) pass j (4 - j) (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₁)).indices =
        (Proof.Argon2.slices (prm s₀₁) pass j (4 - j) (Proof.Argon2.slices (prm s₀₁) pass 0 j Z₂)).indices)
    ?step 4).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, rfl, by decide, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, hn, hj, h₁, h₂, hidx⟩ e₁ e₂
  rw [show 4 - j = (3 - j) + 1 by omega_arith] at hidx
  have hl := Proof.Argon2.slices_first_lane_fold (prm s₀₁) pass j (3 - j) _ _ s2 hidx
  rw [Proof.Argon2.slices_succ, Proof.Argon2.slices_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.sliceBody_rel hpass hj hl s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe, ← le] at g₂
  have eq : ∀ X, Proof.Argon2.lanes (prm s₀₁) pass j 0 (lanesN s₀₁) (Proof.Argon2.slices (prm s₀₁) pass 0 j X) =
      Proof.Argon2.slices (prm s₀₁) pass 0 (j + 1) X :=
    fun X => by unfold Proof.Argon2.slices; rw [foldl_range'_snoc, Nat.zero_add]; rfl
  rw [eq] at g₁ g₂
  rw [show 3 - j = 4 - (j + 1) by omega_arith] at hidx
  refine ⟨ht, by show VG.Arm.eval .ne s₁' = VG.Arm.eval .ne s₂'; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : j + 1 ≠ 4 := by
    rw [show isa.eval .ne s₁' = VG.Arm.eval .ne s₁' from rfl, c₁] at hc
    simpa using hc
  refine ⟨4 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, g₁, g₂, ?_⟩
  rw [← eq, ← eq]
  exact hidx

/-- A pass and the pass advanced, in two runs. -/
theorem passBody_rel {k : Nat} {X₁ X₂ : FillState} (hk : k < itersN s₀₁)
    (hind : (Spec.Argon2.fillPass (prm s₀₁) X₁ k).indices = (Spec.Argon2.fillPass (prm s₀₁) X₂ k).indices) :
    RelCT isa (fun s₁ s₂ => PS s₀₁ X₁ k s₁ ∧ PS s₀₂ X₂ k s₂)
      (.seq Impl.Argon2.Arm.Derive.slicesLoop (.block (Impl.Argon2.Arm.Derive.advance passOff (argOff 5))))
      fun v₁ v₂ => (PS s₀₁ (Spec.Argon2.fillPass (prm s₀₁) X₁ k) (k + 1) v₁ ∧
          VG.Arm.eval .ne v₁ = some (!decide (k + 1 = itersN s₀₁))) ∧
        (PS s₀₂ (Spec.Argon2.fillPass (prm s₀₂) X₂ k) (k + 1) v₂ ∧
          VG.Arm.eval .ne v₂ = some (!decide (k + 1 = itersN s₀₂))) := by
  have hk₂ : k < itersN s₀₂ := T.pb.itersN_eq ▸ hk
  have hpl : itersN s₀₁ < 2 ^ 32 := (arg s₀₁ 5).isLt
  rw [← Proof.Argon2.slices_pass, ← Proof.Argon2.slices_pass] at hind
  exact rel_wp (RelCT.seqW (T.slices_rel (by omega_arith) hind)
    (fun s h => slices_ok T.hp₁ h (by omega_arith)) (fun s h => slices_ok T.hp₂ h (by omega_arith))
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => passStep_ok T.hp₁ h hk) (fun s h => passStep_ok T.hp₂ h hk₂)

/-- `passesLoop` leaks the same trace in two runs whose references agree. -/
theorem passes_rel {W₁ W₂ : FillState}
    (hind : (Proof.Argon2.iterations (prm s₀₁) 0 (itersN s₀₁) W₁).indices =
      (Proof.Argon2.iterations (prm s₀₁) 0 (itersN s₀₁) W₂).indices) :
    RelCT isa (fun s₁ s₂ => FB s₀₁ W₁ s₁ ∧ FB s₀₂ W₂ s₂) Impl.Argon2.Arm.Derive.passesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have ie := T.pb.itersN_eq
  have hp1 := T.hp₁.passes_pos
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.Arm.Derive.passesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (setLocal_w T.hp₁ h (d := passOff) (by decide) (by decide) (by decide)).mono fun t ⟨f, v, _⟩ =>
      (⟨f, v⟩ : PS s₀₁ W₁ 0 t))
    (fun s h => (setLocal_w T.hp₂ h (d := passOff) (by decide) (by decide) (by decide)).mono fun t ⟨f, v, _⟩ =>
      (⟨f, v⟩ : PS s₀₂ W₂ 0 t)) ?_
  generalize hN : itersN s₀₁ = N at hind hp1
  have hN₂ : itersN s₀₂ = N := by rw [← ie, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ k, n = N - k ∧ k < N ∧
      PS s₀₁ (Proof.Argon2.iterations (prm s₀₁) 0 k W₁) k s₁ ∧
      PS s₀₂ (Proof.Argon2.iterations (prm s₀₁) 0 k W₂) k s₂ ∧
      (Proof.Argon2.iterations (prm s₀₁) k (N - k) (Proof.Argon2.iterations (prm s₀₁) 0 k W₁)).indices =
        (Proof.Argon2.iterations (prm s₀₁) k (N - k) (Proof.Argon2.iterations (prm s₀₁) 0 k W₂)).indices)
    ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega_arith, by omega_arith, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨k, hn, hk, h₁, h₂, hidx⟩ e₁ e₂
  rw [show N - k = (N - (k + 1)) + 1 by omega_arith] at hidx
  have hpass := Proof.Argon2.iterations_first_pass (prm s₀₁) k (N - (k + 1)) _ _ s2 hidx
  rw [Proof.Argon2.iterations_succ, Proof.Argon2.iterations_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.passBody_rel (by rw [hN]; exact hk) hpass s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe] at g₂
  have eq : ∀ X, Spec.Argon2.fillPass (prm s₀₁) (Proof.Argon2.iterations (prm s₀₁) 0 k X) k =
      Proof.Argon2.iterations (prm s₀₁) 0 (k + 1) X :=
    fun X => by unfold Proof.Argon2.iterations; rw [foldl_range'_snoc, Nat.zero_add]
  rw [eq] at g₁ g₂ hidx
  rw [eq] at hidx
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show VG.Arm.eval .ne s₁' = VG.Arm.eval .ne s₂'; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : k + 1 ≠ N := by
    rw [show isa.eval .ne s₁' = VG.Arm.eval .ne s₁' from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, g₁, g₂, hidx⟩

end Two

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: the derivation is constant time

`body_rel`: the body leaks the same trace in two runs with the same public
data and the same data-dependent references (`deriveArm.pub`), piece by
piece; `derive_ct`: so does the whole function, in its frames.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Spec.Blake2 (bytesAt)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- The parameters' block leaks the same trace in two runs. -/
theorem parameters_rel :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂)
      (.block (.addSp .r11 0 :: Impl.Argon2.Arm.Derive.parameters)) fun _ _ => True := by
  rw [← List.singleton_append]
  refine RelCT.block_split (RelCT.seqW (F₁ := fun s => s = entry s₀₁) (F₂ := fun s => s = entry s₀₂)
    (RelCT.quiet fun _ => rfl)
    (fun s h => by subst h; exact inv_start fun t i _ _ => WP.block_nil i)
    (fun s h => by subst h; exact inv_start fun t i _ _ => WP.block_nil i) ?_)
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) ⟨_, by taint_decide⟩

/-- The body leaks the same trace in two runs with the same data-dependent
references. -/
theorem body_rel
    (href : Spec.Argon2.references (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁) =
      Spec.Argon2.references (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)) :
    RelCT isa (fun s₁ s₂ => s₁ = entry s₀₁ ∧ s₂ = entry s₀₂) Impl.Argon2.Arm.Derive.body fun _ _ => True := by
  have pe := T.pb.prm_eq
  have L8 := laneLen_ge T.hp₁
  have hind := Proof.Argon2.references_injective (prm s₀₁) (by omega_using [L8]) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁)
    (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂) (by rw [href, pe])
  rw [← Proof.Argon2.iterations_fill, ← Proof.Argon2.iterations_fill] at hind
  unfold Impl.Argon2.Arm.Derive.body
  refine RelCT.seqW T.parameters_rel (G₁ := fun t => Inv s₀₁ t ∧ Prm s₀₁ t)
    (G₂ := fun t => Inv s₀₂ t ∧ Prm s₀₂ t)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.addSp .r11 0 :: Impl.Argon2.Arm.Derive.parameters)]
      exact parameters_ok T.hp₁ fun t i p => WP.block_nil ⟨i, p⟩)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.addSp .r11 0 :: Impl.Argon2.Arm.Derive.parameters)]
      exact parameters_ok T.hp₂ fun t i p => WP.block_nil ⟨i, p⟩) ?_
  refine RelCT.seqW T.code_rel (fun s h => code_ok T.hp₁ h.1 h.2) (fun s h => code_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW T.memoryInit_rel (fun s h => memoryInit_ok T.hp₁ h.1 h.2.1 h.2.2)
    (fun s h => memoryInit_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW ((T.passes_rel (W₁ := Spec.Argon2.initMemory (prm s₀₁)
      (Spec.Argon2.initialHash (prm s₀₁) (pwB s₀₁) (saltB s₀₁) (secB s₀₁) (adB s₀₁)))
      (W₂ := Spec.Argon2.initMemory (prm s₀₂)
      (Spec.Argon2.initialHash (prm s₀₂) (pwB s₀₂) (saltB s₀₂) (secB s₀₂) (adB s₀₂)))
      (by rw [← pe]; exact hind)).mono (fun _ _ h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => passes_ok T.hp₁ ⟨h.1, h.2.1, h.2.2⟩) (fun s h => passes_ok T.hp₂ ⟨h.1, h.2.1, h.2.2⟩) ?_
  refine RelCT.seqW (T.reduce_rel.mono (fun _ _ h => ⟨⟨h.1.inv, h.1.pr, h.1.mem⟩, ⟨h.2.inv, h.2.pr, h.2.mem⟩⟩)
      fun _ _ h => h)
    (fun s h => reduce_ok T.hp₁ h.inv h.pr h.mem) (fun s h => reduce_ok T.hp₂ h.inv h.pr h.mem) ?_
  exact T.finalOutput_rel.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h

end Two

/-! ## The frames -/

theorem alloc_eq {n : Nat} {s a : State} (h : isa.push (.alloc n) s = some a) : a = allocated n s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

/-- Two runs of a frame that reserves stack leak the same trace if the runs of
its body do; the stack pointer is where it was. -/
theorem RelCT.allocFrame {n : Nat} {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hb : RelCT isa (fun x y => ∃ a b, P a b ∧ isa.push (.alloc n) a = some x ∧ isa.push (.alloc n) b = some y)
      body fun _ _ => True) :
    RelCT isa P (.frame (.alloc n) body (.free n)) fun a' b' => a'.sp = b'.sp := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have q₁ := Exec.sp e₁
  have q₂ := Exec.sp e₂
  cases e₁ with
  | frame p₁ b₁ _ =>
    cases e₂ with
    | frame p₂ b₂ _ =>
      obtain ⟨ht, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, p₁, p₂⟩ b₁ b₂
      refine ⟨?_, show s₁'.sp = s₂'.sp by rw [q₁, q₂, hsp _ _ hp]⟩
      rw [ht]
      rfl

/-- Loads from the stack pointer leak the same trace from the same stack pointer. -/
theorem ldrSps_trace : ∀ (l : List (Reg × Nat)) (s₁ s₂ : State) {a₁ a₂ : State} {t₁ t₂ : List Leak},
    s₁.sp = s₂.sp → execBlock isa (l.map fun p => Instr.ldrSp p.1 p.2) s₁ = some (a₁, t₁) →
    execBlock isa (l.map fun p => Instr.ldrSp p.1 p.2) s₂ = some (a₂, t₂) → t₁ = t₂
  | [], s₁, s₂, a₁, a₂, t₁, t₂, _, h₁, h₂ => by
    simp only [List.map_nil, execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    rw [← h₁.2, ← h₂.2]
  | p :: l, s₁, s₂, a₁, a₂, t₁, t₂, hsp, h₁, h₂ => by
    simp only [List.map_cons, execBlock] at h₁ h₂
    split at h₁
    · cases h₁
    rename_i b₁ x₁
    split at h₂
    · cases h₂
    rename_i b₂ x₂
    rw [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨⟨c₁, u₁⟩, r₁, e₁⟩ := h₁
    obtain ⟨⟨c₂, u₂⟩, r₂, e₂⟩ := h₂
    simp only [Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2, ldrSps_trace l b₁ b₂ (by rw [exec_sp x₁, exec_sp x₂, hsp]) r₁ r₂]
    simp only [addrs, hsp]

theorem RelCT.restore {P : State → State → Prop} (hsp : ∀ a b, P a b → a.sp = b.sp) :
    RelCT isa P (.block Impl.Argon2.Arm.Derive.restoreRegs) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨ldrSps_trace _ s₁ s₂ (hsp _ _ hp) e₁ e₂, trivial⟩

/-- The derivation leaks the same trace in two runs with the same public data. -/
theorem derive_rel :
    RelCT isa (fun s₁ s₂ => deriveArm.pre s₁ ∧ deriveArm.pre s₂ ∧ deriveArm.pub s₁ s₂)
      Impl.Argon2.Arm.Derive.derive fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.derive
  refine RelCT.frame (fun s₁ s₂ h => h.2.2.1.1) (RelCT.frame (fun a b ⟨s₁, s₂, h, pa, pb⟩ => by
      rw [push_push_sp pa, push_push_sp pb, h.2.2.1.1]) ?_)
  refine RelCT.seq (RelCT.allocFrame (fun a b ⟨x, y, ⟨s₁, s₂, h, pa, pb⟩, qa, qb⟩ => by
      rw [push_push_sp qa, push_push_sp qb, push_push_sp pa, push_push_sp pb, h.2.2.1.1]) ?_)
    (RelCT.restore fun _ _ h => h)
  intro a b t₁ t₂ a' b' ⟨x, y, ⟨u, v, ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, pu, pv⟩, px, py⟩, ha, hb⟩ e₁ e₂
  have eu := VG.Proof.Argon2.Arm.push_eq (by decide) pu
  have ev := VG.Proof.Argon2.Arm.push_eq (by decide) pv
  have ex := VG.Proof.Argon2.Arm.push_eq (by decide) px
  have ey := VG.Proof.Argon2.Arm.push_eq (by decide) py
  have ea := alloc_eq ha
  have eb := alloc_eq hb
  subst eu ev ex ey ea eb
  exact Two.body_rel ⟨h₁, h₂, hpub.1⟩ hpub.2 _ _ t₁ t₂ a' b' ⟨rfl, rfl⟩ e₁ e₂

theorem derive_ct : ConstantTime isa deriveArm.pre deriveArm.pub Impl.Argon2.Arm.Derive.derive :=
  derive_rel.constantTime

end VG.Proof.Argon2.Arm.Derive

end

end

/-! ### `Argon2.Arm.Derive.Correct`, which only this module used -/

section

/-!
# Argon2 on ARMv7: the derivation is correct

`body_ok`: the body computes the parameters and H₀, initializes and fills
the memory, and writes the tag (`Spec.Argon2.derive`) to `out`; `correct`:
the whole function, in its frames, keeps the ABI's registers too.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Spec.Blake2 (bytesAt)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem body_ok : WP isa Impl.Argon2.Arm.Derive.body (entry s₀) fun t => BodyDone s₀ t ∧
    t.wr = (entry s₀).wr ∧ bytesAt t.mem (State.addr (outP s₀)) (outL s₀) =
      Spec.Argon2.derive (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀) := by
  unfold Impl.Argon2.Arm.Derive.body
  refine WP.seq ?_
  rw [← List.append_nil (Instr.addSp .r11 0 :: Impl.Argon2.Arm.Derive.parameters)]
  refine parameters_ok hp fun s₁ i₁ p₁ => WP.block_nil ?_
  refine WP.seq ((code_ok hp i₁ p₁).mono fun s₂ ⟨i₂, p₂, b₂⟩ => ?_)
  refine WP.seq ((memoryInit_ok hp i₂ p₂ b₂).mono fun s₃ ⟨i₃, p₃, m₃⟩ => ?_)
  refine WP.seq ((passes_ok hp (st := Spec.Argon2.initMemory (prm s₀)
    (Spec.Argon2.initialHash (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀))) ⟨i₃, p₃, m₃⟩).mono
    fun s₄ f₄ => ?_)
  rw [show itersN s₀ = (prm s₀).passes from rfl, Proof.Argon2.iterations_fill] at f₄
  refine WP.seq ((reduce_ok hp f₄.inv f₄.pr f₄.mem).mono fun s₅ ⟨i₅, _, b₅⟩ => ?_)
  refine (finalOutput_ok hp i₅).mono fun t ⟨it, ot⟩ => ⟨it.done hp, it.wr, ?_⟩
  rw [ot, b₅, Spec.Argon2.derive, Proof.Argon2.finish_reduction]
  rfl

theorem correct : WP isa Impl.Argon2.Arm.Derive.derive s₀ fun t => abiPreserved s₀ t ∧ deriveArm.post s₀ t :=
  frames_ok (by have := hp.sp_lo; omega_using [this]) (body_ok hp) fun t u q f => by
    show bytesAt u.mem _ _ = _
    have sub : Region.Sub (Proof.Argon2.Arm.stkR (E0 s₀) 200) (stkR0 s₀) :=
      Offset.sub_below _ (by decide) (by decide)
    have hd : ∀ r ∈ [Proof.Argon2.Arm.stkR (E0 s₀) 200], (outR s₀).Disjoint r := fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (hp.stk_all (outR s₀) (by simp)).symm.sub_right sub
    have fit : (outR s₀).len ≤ 2 ^ 64 := by
      have := hp.out_fits; change outL s₀ ≤ _; omega_using [this]
    refine Eq.trans (List.map_congr_left fun _ hi => ?_) q
    exact f.bytes hd fit (List.mem_range.mp hi)

end

end VG.Proof.Argon2.Arm.Derive

end

end


/-!
# Argon2 on ARMv7: the derivation is verified

`derive_verified`: the derivation against `deriveArm` (correct, constant
time, and satisfiable: `satState`). `deriveShared_verified`: against the
shared contract `Spec.Argon2.deriveContract`, through `deriveFlat`, whose
precondition spells `DPre` out as `Sig.contract` lays the regions out.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.Argon2.Arm (stkR)

/-! ## A state satisfying the precondition -/

/-- The stack arguments: Argon2d, empty inputs, one pass over 8 KiB in one
lane, a 4-byte tag (the register arguments are zero). -/
def satStack : List Nat := [0, 1, 8, 1, 1, 0, 0, 0, 0, 0x10000, 8, 0x20000, 0x30000, 4]

/-- Memory holding `satStack` at `0x40000`. -/
def satMem (a : Addr) : Byte :=
  if 0x40000 ≤ a.toNat ∧ a.toNat < 0x40038 then
    ((BitVec.ofNat 32 (satStack[(a.toNat - 0x40000) / 4]?.getD 0)) >>> (8 * ((a.toNat - 0x40000) % 4))).setWidth 8
  else 0

def satState : State where
  gpr _ := 0
  sp := 0x40000
  n := false
  z := false
  c := false
  v := false
  mem := satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40000, 56⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

/-- The arguments of `satState`. -/
def satArgs : List Nat := [0, 0, 0, 0] ++ satStack

theorem sat_args : ∀ i < 18, arg satState i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := by decide

theorem sat_pre : DPre satState := by
  have a : ∀ i < 18, arg satState i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := sat_args
  have e : stackArgAddr satState 0 = 0x40000 := by decide
  have sp : satState.sp = 0x40000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [pwR, saltR, secR, adR, memR, scrR, outR, argR, stkR0, stkR, pwP, pwL, saltP, saltL, secP,
    secL, adP, adL, memP, blocksN, scrP, outP, outL, E0, kindV, itersN, mcostN, lanesN, threadsN, prm,
    a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide), a 5 (by decide),
    a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide), a 11 (by decide),
    a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide), a 16 (by decide), a 17 (by decide),
    e, sp]
  all_goals first
    | rfl
    | decide
    | (intro r hr w hw
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
       rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
         exact Region.disjoint_of_sep (by decide))
    | (intro r hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))
    | exact Region.disjoint_of_sep (by decide)

theorem derive_verified : Verified Arm.target Impl.Argon2.Arm.Derive.derive deriveArm :=
  ⟨fun _ hs => correct hs, derive_ct, ⟨satState, sat_pre⟩⟩

/-! ## The shared contract -/

/-- `deriveArm`, its precondition spelt out as `Sig.contract` lays the regions
out. -/
def deriveFlat : Contract Arm.isa :=
  { deriveArm with
    pre := fun s =>
      let pw : Region := ⟨State.addr (arg s 1), (arg s 2).toNat⟩
      let salt : Region := ⟨State.addr (arg s 3), (arg s 4).toNat⟩
      let sec : Region := ⟨State.addr (arg s 9), (arg s 10).toNat⟩
      let ad : Region := ⟨State.addr (arg s 11), (arg s 12).toNat⟩
      let mem : Region := ⟨State.addr (arg s 13), (arg s 14).toNat * 1024⟩
      let scr : Region := ⟨State.addr (arg s 15), 16384⟩
      let out : Region := ⟨State.addr (arg s 16), (arg s 17).toNat⟩
      let args : Region := ⟨stackArgAddr s 0, 56⟩
      let stack : Region := stkR s.sp 240
      s.rd = [pw, salt, sec, ad, args] ∧ s.wr = [mem, scr, out] ∧
      pw.Disjoint mem ∧ pw.Disjoint scr ∧ pw.Disjoint out ∧ salt.Disjoint mem ∧ salt.Disjoint scr ∧
      salt.Disjoint out ∧ sec.Disjoint mem ∧ sec.Disjoint scr ∧ sec.Disjoint out ∧ ad.Disjoint mem ∧
      ad.Disjoint scr ∧ ad.Disjoint out ∧ args.Disjoint mem ∧ args.Disjoint scr ∧ args.Disjoint out ∧
      mem.Disjoint scr ∧ mem.Disjoint out ∧ scr.Disjoint out ∧
      stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint sec ∧ stack.Disjoint ad ∧ stack.Disjoint mem ∧
      stack.Disjoint scr ∧ stack.Disjoint out ∧
      (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 9).toNat + (arg s 10).toNat ≤ 2 ^ 32 ∧ (arg s 11).toNat + (arg s 12).toNat ≤ 2 ^ 32 ∧
      (arg s 13).toNat + (arg s 14).toNat * 1024 ≤ 2 ^ 32 ∧ (arg s 15).toNat + 16384 ≤ 2 ^ 32 ∧
      (arg s 16).toNat + (arg s 17).toNat ≤ 2 ^ 32 ∧ 240 ≤ s.sp.toNat ∧ s.sp.toNat + 56 ≤ 2 ^ 32 ∧
      (arg s 0).toNat ≤ 2 ∧
      Spec.Argon2.valid (Spec.Argon2.params (arg s 0).toNat (arg s 5).toNat (arg s 6).toNat (arg s 7).toNat
        (arg s 17).toNat) (arg s 2).toNat (arg s 4).toNat (arg s 10).toNat (arg s 12).toNat ∧
      1 ≤ (arg s 8).toNat ∧ (arg s 8).toNat < 2 ^ 24 ∧
      (arg s 14).toNat = (Spec.Argon2.params (arg s 0).toNat (arg s 5).toNat (arg s 6).toNat (arg s 7).toNat
        (arg s 17).toNat).blocks }

theorem deriveFlat_pre {s : State} (h : deriveFlat.pre s) : DPre s := by
  obtain ⟨hrd, hwr, d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈, d₉, d₁₀, d₁₁, d₁₂, d₁₃, d₁₄, d₁₅, m₁, m₂, m₃,
    k₁, k₂, k₃, k₄, k₅, k₆, k₇, f₁, f₂, f₃, f₄, f₅, f₆, f₇, lo, hi, kd, vd, t₁, t₂, bl⟩ := h
  refine
    { rd := hrd
      wr := hwr
      ro_w := ?_
      mem_scr := m₁
      mem_out := m₂
      scr_out := m₃
      stk_all := ?_
      pw_fits := f₁
      salt_fits := f₂
      sec_fits := f₃
      ad_fits := f₄
      mem_fits := f₅
      scr_fits := f₆
      out_fits := f₇
      sp_lo := lo
      sp_hi := hi
      kind_le := kd
      valid := vd
      threads := ⟨t₁, t₂⟩
      blocks := bl }
  · intro r hr w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    exacts [d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈, d₉, d₁₀, d₁₁, d₁₂, d₁₃, d₁₄, d₁₅]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [k₁, k₂, k₃, k₄, k₅, k₆, k₇]

theorem deriveFlat_implies : deriveArm.Implies deriveFlat :=
  ⟨fun _ h => deriveFlat_pre h, fun _ _ _ h => h, fun _ _ _ _ h => h,
    ⟨satState, by
      have a : ∀ i < 18, arg satState i = BitVec.ofNat 32 (satArgs[i]?.getD 0) := sat_args
      have e : stackArgAddr satState 0 = 0x40000 := by decide
      simp only [deriveFlat, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
        a 5 (by decide), a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide),
        a 11 (by decide), a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide),
        a 16 (by decide), a 17 (by decide), e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide, by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩⟩

theorem flat_implies : deriveFlat.Implies (Spec.Argon2.deriveContract Arm.abi 240) := by
  sig_implies [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, deriveFlat, deriveArm, stkR, arg, prm, pwB,
    saltB, secB, adB, pwR, saltR, secR, adR, pwP, pwL, saltP, saltL, secP, secL, adP, adL, kindV, itersN, mcostN,
    lanesN, outL, outP,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [satState, satMem, satStack, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read, Spec.Argon2.params,
      Spec.Argon2.valid, Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen] using satState

/-- The emitted function, against the shared contract. -/
theorem deriveShared_verified :
    Verified Arm.target Impl.Argon2.Arm.Derive.derive (Spec.Argon2.deriveContract Arm.abi 240) :=
  (derive_verified.of_implies deriveFlat_implies).of_implies flat_implies

end VG.Proof.Argon2.Arm.Derive
