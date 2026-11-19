module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCache
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Initial
public import VerifiedGarbage.Proof.Argon2.Slices
public import VerifiedGarbage.Proof.Argon2.FinalReduction
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Argon2.Serialization
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.HCall
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.SegmentStart
public import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Argon2.RISCV64.Compress
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCall
public import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.Dimensions

/-! ### `Argon2.RISCV64.Derive.Reduce`, which this module and modules that import it used -/

section

/-! ### `Argon2.RISCV64.Derive.FillLoops`, which this module and modules that import it used -/

section

/-! ### `Argon2.RISCV64.Derive.FillBlock`, which this module and modules that import it used -/

section

/-! ### `Argon2.RISCV64.Derive.FillPtr`, which this module and modules that import it used -/

section

/-! ### `Argon2.RISCV64.Derive.FillRef`, which this module and modules that import it used -/

section

/-!
# Argon2 on RISC-V: the reference lane, the window's start, and its base

`refLane_ok`: J₂ mod the lane count (by the fixed-time division), or the
current lane in the first slice of the first pass, to the frame;
`refStart_ok`: where the window of eligible blocks starts; `countBase_ok`:
the blocks before the current segment it may use. `RS` is the filling state
with J₁ and J₂ in the frame.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd Mupd wp_add wp_addi wp_sub wp_subi wp_li)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Impl.Argon2.RISCV64.Derive (sliceOff segLenOff indexOff laneOff laneLenOff passOff
  j1Off j2Off refLaneOff startOff ld st ldw)

/-- The filling state, with J₁ and J₂ in the frame. -/
structure RS (s₀ : State) (pass slice lane index ctr : Nat) (σ : FillState) (J1 J2 : BitVec 64)
    (s : State) : Prop where
  fs : FS s₀ pass slice lane index ctr σ s
  j1 : lw s₀ s j1Off = J1
  j2 : lw s₀ s j2Off = J2

theorem RS.of_only {s₀ s t : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) {ds : List Reg} (o : Only ds s t)
    (hd : ∀ r ∈ ds, Free r := by decide) : RS s₀ pass slice lane index ctr σ J1 J2 t :=
  ⟨h.fs.of_only o hd, by rw [lw_mem o.mem]; exact h.j1, by rw [lw_mem o.mem]; exact h.j2⟩

/-- The reference lane: J₂ mod the lane count, but the current lane in the first
slice of the first pass. -/
def refLaneV (lanes pass slice lane j2 : Nat) : Nat := if pass = 0 ∧ slice = 0 then lane else j2 % lanes

/-- Where the window starts. -/
def startV (segLen laneLen pass slice : Nat) : Nat :=
  if pass = 0 then 0 else (slice + 1) * segLen % laneLen

/-- The blocks before the current segment that a reference may use. -/
def baseV (segLen laneLen pass slice : Nat) : Nat := if pass = 0 then slice * segLen else laneLen - segLen

theorem or_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b == 0) = decide (a = 0 ∧ b = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

theorem zero_eval {s : State} {r : Reg} {n : Nat} (hn : n < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 n) :
    isa.eval (.zero r) s = some (decide (n = 0)) := by
  rw [show isa.eval _ s = VG.RISCV64.eval _ s from rfl, VG.RISCV64.Wp.eval_zero, h,
    VG.RISCV64.Steps.ofNat_beq_zero hn]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem RS.store {s t : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) (it : Inv s₀ t) {d : Nat} (hd : 272 ≤ d)
    (hd' : d + 8 ≤ 320) {v : BitVec 64} (hm : t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) v)
    (ho : ∀ e, e + 8 ≤ 320 → d + 8 ≤ e ∨ e + 8 ≤ d → lw s₀ t e = lw s₀ s e) :
    RS s₀ pass slice lane index ctr σ J1 J2 t :=
  ⟨h.fs.store hp it (by omega_using [hd]) hd' hm, by rw [ho j1Off (by decide) (by simp [j1Off]; omega_using [hd])]; exact h.j1,
    by rw [ho j2Off (by decide) (by simp [j2Off]; omega_using [hd])]; exact h.j2⟩

/-- The block of `refLane`: J₂ mod lanes, to the frame, and `a0` zero in the
first slice of the first pass. -/
theorem refLaneBlk_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) (hj2 : J2.toNat < 2 ^ 32) (hpass : pass < 2 ^ 32)
    (hs : slice < 4) :
    WP isa (.block ([ld .a1 j2Off, ldw .a2 Impl.Argon2.RISCV64.Derive.lanesArg] ++
      Impl.Argon2.RISCV64.Divide.code ++
      [st refLaneOff .a4, ld .a0 passOff, ld .a1 sliceOff, .logic .or .a0 .a0 .a1])) s fun t =>
      RS s₀ pass slice lane index ctr σ J1 J2 t ∧
      isa.eval (.zero .a0) t = some (decide (pass = 0 ∧ slice = 0)) ∧
      lw s₀ t refLaneOff = BitVec.ofNat 64 (J2.toNat % lanesN s₀) := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  rw [List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc h.fs.inv (d := j2Off) (by decide) fun s₁ u₁ =>
    wp_ldw hp (h.fs.inv.upd u₁) (i := 7) (by decide) fun s₂ u₂ => ?_
  have h₂ := h.of_only ((Only.of_upd u₁).trans (Only.of_upd u₂))
  refine Divide.code_ok (D := lanesN s₀) (by omega_using [hl1]) (by omega_using [hlt]) (by rw [u₂.gpr, toNat_ext32])
    fun s₃ _ r₃ k₃ => ?_
  have h₃ := h₂.of_only (Divide.KeepD.only k₃)
  refine wp_stloc h₃.fs.inv (d := refLaneOff) (by decide) fun s₄ i₄ v₄ o₄ g₄ m₄ => ?_
  have h₄ := h₃.store hp i₄ (d := refLaneOff) (by decide) (by decide) m₄ o₄
  refine wp_ldloc h₄.fs.inv (d := passOff) (by decide) fun s₅ u₅ => ?_
  have h₅ := h₄.of_only (Only.of_upd u₅)
  refine wp_ldloc h₅.fs.inv (d := sliceOff) (by decide) fun s₆ u₆ => wp_or fun t u₇ => WP.block_nil ?_
  have h₇ := h₅.of_only ((Only.of_upd u₆).trans (Only.of_upd u₇))
  have r : s₃.gpr .a4 = BitVec.ofNat 64 (J2.toNat % lanesN s₀) := by
    have hm : J2.toNat % lanesN s₀ < 2 ^ 64 := by have := Nat.mod_le J2.toNat (lanesN s₀); omega_using [this]
    apply BitVec.eq_of_toNat_eq
    rw [r₃, u₂.other _ (by decide), u₁.gpr, h.j2, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hj2,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  refine ⟨h₇, ?_, by rw [lw_mem u₇.mem, lw_mem u₆.mem, lw_mem u₅.mem, v₄, r]⟩
  rw [VG.RISCV64.Wp.eval_zero, u₇.gpr,
    u₆.other _ (by decide), u₅.gpr, u₆.gpr, lw_mem u₅.mem, h₄.fs.pos.slice, h₄.fs.pos.pass,
    or_zero (by omega_using [hpass]) (by omega_using [hs])]

/-- `refLane`: the reference lane, to the frame. -/
theorem refLane_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) (hj2 : J2.toNat < 2 ^ 32) (hpass : pass < 2 ^ 32)
    (hs : slice < 4) :
    WP isa Impl.Argon2.RISCV64.Derive.refLane s fun t => RS s₀ pass slice lane index ctr σ J1 J2 t ∧
      lw s₀ t refLaneOff = BitVec.ofNat 64 (refLaneV (lanesN s₀) pass slice lane J2.toNat) := by
  unfold Impl.Argon2.RISCV64.Derive.refLane
  refine WP.seq ((refLaneBlk_ok hp h hj2 hpass hs).mono fun s₅ ⟨h₅, z₅, e₃⟩ => ?_)
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) z₅ (fun hb => ?_) fun hb => ?_
  · have hb' : pass = 0 ∧ slice = 0 := of_decide_eq_true hb
    refine wp_ldloc h₅.fs.inv (d := laneOff) (by decide) fun s₆ u₆ => ?_
    have h₆ := h₅.of_only (Only.of_upd u₆)
    refine wp_stloc h₆.fs.inv (d := refLaneOff) (by decide) fun t it vt ot _ mt => WP.block_nil ⟨?_, ?_⟩
    · exact h₆.store hp it (d := refLaneOff) (by decide) (by decide) mt ot
    · rw [vt, u₆.gpr, h₅.fs.pos.lane, refLaneV, ite_eq_left hb']
  · have hb' : ¬(pass = 0 ∧ slice = 0) := of_decide_eq_false hb
    refine WP.block_nil ⟨h₅, ?_⟩
    rw [e₃, refLaneV, ite_eq_right hb']

/-- `refStart`: where the window starts, to the frame. -/
theorem refStart_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.RISCV64.Derive.refStart s fun t => RS s₀ pass slice lane index ctr σ J1 J2 t ∧
      lw s₀ t refLaneOff = lw s₀ s refLaneOff ∧
      lw s₀ t startOff = BitVec.ofNat 64 (startV (prm s₀).segmentLen (prm s₀).laneLen pass slice) := by
  have sl := segLen_lt hp
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  unfold Impl.Argon2.RISCV64.Derive.refStart
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  have h₁ := h.of_only (Only.of_upd u₁)
  refine wp_stloc h₁.fs.inv (d := startOff) (by decide) fun s₂ i₂ v₂ o₂ _ m₂ => ?_
  have h₂ := h₁.store hp i₂ (d := startOff) (by decide) (by decide) m₂ o₂
  refine wp_ldloc h₂.fs.inv (d := passOff) (by decide) fun s₄ u₃ => WP.block_nil ?_
  have h₄ := h₂.of_only (Only.of_upd u₃)
  have m₄ : s₄.mem = s₂.mem := u₃.mem
  have r₂ : lw s₀ s₂ refLaneOff = lw s₀ s refLaneOff := by
    rw [o₂ _ (by decide) (by decide), lw_mem u₁.mem]
  refine WP.ite (decide (pass = 0)) (zero_eval (by omega_using [hpass]) (by rw [u₃.gpr, h₂.fs.pos.pass]))
    (fun hb => ?_) fun hb => ?_
  · refine WP.block_nil ⟨h₄, by rw [lw_mem m₄, r₂], ?_⟩
    rw [lw_mem m₄, v₂, u₁.gpr, startV, ite_eq_left (of_decide_eq_true hb)]
  · have hp0 : pass ≠ 0 := of_decide_eq_false hb
    refine WP.seq (wp_ldloc h₄.fs.inv (d := sliceOff) (by decide) fun s₅ u₅ =>
      wp_subi (by decide) fun s₆ u₆ => WP.block_nil ?_)
    have h₆ := h₄.of_only ((Only.of_upd u₅).trans (Only.of_upd u₆))
    have m₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, m₄]
    refine WP.ite (decide (slice = 3)) (by
      rw [show isa.eval _ s₆ = VG.RISCV64.eval _ s₆ from rfl, VG.RISCV64.Wp.eval_zero, u₆.gpr,
        u₅.gpr, h₄.fs.pos.slice, sub_beq (by omega_using [hs]) (by decide)])
      (fun hb' => ?_) fun hb' => ?_
    · refine WP.block_nil ⟨h₆, by rw [lw_mem m₆, r₂], ?_⟩
      rw [lw_mem m₆, v₂, u₁.gpr, startV, ite_eq_right hp0, of_decide_eq_true hb', ll, Nat.mod_self]
    · have hs3 : slice ≠ 3 := of_decide_eq_false hb'
      refine wp_ldloc h₆.fs.inv (d := sliceOff) (by decide) fun s₇ u₇ => wp_addi (by decide)
        fun s₈ u₈ => ?_
      have h₈ := h₆.of_only ((Only.of_upd u₇).trans (Only.of_upd u₈))
      refine wp_ldloc h₈.fs.inv (d := segLenOff) (by decide) fun s₉ u₉ => wp_mul fun s₁₀ u₁₀ => ?_
      have h₁₀ := h₈.of_only ((Only.of_upd u₉).trans (Only.of_upd u₁₀))
      have m₁₀ : s₁₀.mem = s₂.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆]
      refine wp_stloc h₁₀.fs.inv (d := startOff) (by decide) fun t it vt ot _ mt =>
        WP.block_nil ⟨?_, ?_, ?_⟩
      · exact h₁₀.store hp it (d := startOff) (by decide) (by decide) mt ot
      · rw [ot _ (by decide) (by decide), lw_mem m₁₀, r₂]
      · have : (slice + 1) * (prm s₀).segmentLen < (prm s₀).laneLen := by
          rw [ll]; exact Nat.mul_lt_mul_of_pos_right (by omega_using [hs, hs3]) (by omega_using [s2])
        rw [vt, u₁₀.gpr, u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₉.gpr, lw_mem u₈.mem, lw_mem u₇.mem,
          h₆.fs.pr.segLen, lw_mem (show s₆.mem = s₂.mem from m₆), h₂.fs.pos.slice,
          BitVec.ofNat_add_ofNat, ofNat_mul_ofNat, startV, ite_eq_right hp0, Nat.mod_eq_of_lt this]

/-- `countBase`: `r3 :=` the blocks before the current segment that a reference may use. -/
theorem countBase_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) (hpass : pass < 2 ^ 32) :
    WP isa Impl.Argon2.RISCV64.Derive.countBase s fun t => Only [.a0, .a1, .a2] s t ∧
      t.gpr .a0 = BitVec.ofNat 64 (baseV (prm s₀).segmentLen (prm s₀).laneLen pass slice) := by
  have sl := segLen_lt hp
  have ll := hp.laneLen_eq
  unfold Impl.Argon2.RISCV64.Derive.countBase
  refine WP.seq (wp_ldloc h.fs.inv (d := passOff) (by decide) fun s₂ u₁ => WP.block_nil ?_)
  have k₂ := Only.of_upd u₁
  have h₂ := h.of_only k₂
  refine WP.ite (decide (pass = 0)) (zero_eval (by omega_using [hpass]) (by rw [u₁.gpr, h.fs.pos.pass]))
    (fun hb => ?_) fun hb => ?_
  · refine wp_ldloc h₂.fs.inv (d := sliceOff) (by decide) fun s₃ u₃ =>
      wp_ldloc (h₂.of_only (Only.of_upd u₃)).fs.inv (d := segLenOff) (by decide) fun s₄ u₄ =>
      wp_mul fun t u => WP.block_nil ⟨(((k₂.trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans
        (Only.of_upd u)).mono (by simp), ?_⟩
    rw [u.gpr, u₄.other _ (by decide), u₃.gpr, u₄.gpr, lw_mem u₃.mem, h₂.fs.pos.slice, h₂.fs.pr.segLen,
      ofNat_mul_ofNat, baseV, ite_eq_left (of_decide_eq_true hb)]
  · refine wp_ldloc h₂.fs.inv (d := laneLenOff) (by decide) fun s₃ u₃ =>
      wp_ldloc (h₂.of_only (Only.of_upd u₃)).fs.inv (d := segLenOff) (by decide) fun s₄ u₄ =>
      wp_sub fun t u => WP.block_nil ⟨(((k₂.trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans
        (Only.of_upd u)).mono (by simp), ?_⟩
    rw [u.gpr, u₄.other _ (by decide), u₃.gpr, u₄.gpr, lw_mem u₃.mem, h₂.fs.pr.laneLen, h₂.fs.pr.segLen,
      sub_ofNat (by omega_using [ll]), baseV, ite_eq_right (of_decide_eq_false hb)]

end

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: the reference block's column and the block pointers

`relative_ok`: the position in the window that J₁ selects (RFC 9106
§3.4.2); `wrap_ok`: its column, from the window's start, modulo the lane
length, by a subtraction corrected by its sign; `refPointer_ok` and
`curPointer_ok`: the reference and current blocks' addresses, to the frame.
-/

@[expose] public section

/-!
# Argon2 on RISC-V: the reference window's size

`countSelect_ok`: the number of eligible reference blocks, chosen between
the current lane's and another lane's by a mask (`sel`), to the frame.
-/

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd wp_add wp_subi)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.RISCV64.Derive (indexOff laneOff refLaneOff cntOff)

theorem sel (a c : BitVec 64) (p : Prop) [Decidable p] :
    a ^^^ ((c ^^^ a) &&& (if p then BitVec.allOnes 64 else 0)) = if p then c else a := by
  by_cases hp : p
  · simp only [hp, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm c a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp [hp]

theorem add_allOnes {x : Nat} (h : 1 ≤ x) (h' : x < 2 ^ 64) :
    BitVec.ofNat 64 x + BitVec.allOnes 64 = BitVec.ofNat 64 (x - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_allOnes, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_eq_zero {n : Nat} (h : n < 2 ^ 64) : BitVec.ofNat 64 n = 0 ↔ n = 0 := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
  · rintro rfl; rfl

theorem xor_eq_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b = 0 ↔ a = b := by
  constructor
  · intro e
    have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp e)
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · rintro rfl; simp

/-- The window's size. -/
def countV (base index : Nat) (same : Bool) : Nat :=
  if same then base + index - 1 else base - (if index = 0 then 1 else 0)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `countSelect`: the window's size, to the frame and `a0`. -/
theorem countSelect_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) {base rl : Nat} (hb : base < 2 ^ 32)
    (hi : index < (prm s₀).segmentLen) (hl : lane < lanesN s₀) (hrl : rl < lanesN s₀)
    (ha : s.gpr .a0 = BitVec.ofNat 64 base) (hr : lw s₀ s refLaneOff = BitVec.ofNat 64 rl)
    (hsame : rl = lane → 1 ≤ base + index) (hother : rl ≠ lane → index = 0 → 1 ≤ base)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr σ J1 J2 t →
      t.gpr .a0 = BitVec.ofNat 64 (countV base index (rl == lane)) →
      lw s₀ t cntOff = BitVec.ofNat 64 (countV base index (rl == lane)) →
      (∀ e, e + 8 ≤ 320 → (cntOff + 8 ≤ e ∨ e + 8 ≤ cntOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r ∉ [Reg.a0, .a1, .a2, .a3], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.countSelect ++ is)) s Q := by
  obtain sl := segLen_lt hp
  have lt := hp.lanes_lt
  unfold Impl.Argon2.RISCV64.Derive.countSelect
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldloc h.fs.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_add fun s₂ u₂ =>
    wp_subi (by decide) fun s₃ u₃ => nonzero_ok (by decide) fun s₄ v₄ o₄ =>
    wp_subi (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ => ?_
  obtain o₆ := (((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans o₄).trans
    (Only.of_upd u₅)).trans (Only.of_upd u₆)
  obtain h₆ := h.of_only o₆
  refine wp_ldloc h₆.fs.inv (d := refLaneOff) (by decide) fun s₇ u₇ =>
    wp_ldloc (h₆.of_only (Only.of_upd u₇)).fs.inv (d := laneOff) (by decide) fun s₈ u₈ =>
    wp_xor fun s₉ u₉ => nonzero_ok (by decide) fun s₁₀ v₁₀ o₁₀ =>
    wp_subi (by decide) fun s₁₁ u₁₁ => wp_xor fun s₁₂ u₁₂ => wp_and fun s₁₃ u₁₃ =>
    wp_xor fun s₁₄ u₁₄ => ?_
  obtain o₁₄ := o₆.trans ((((((((Only.of_upd u₇).trans (Only.of_upd u₈)).trans (Only.of_upd u₉)).trans
    o₁₀).trans (Only.of_upd u₁₁)).trans (Only.of_upd u₁₂)).trans (Only.of_upd u₁₃)).trans
    (Only.of_upd u₁₄))
  obtain h₁₄ := h.of_only o₁₄
  obtain m : ∀ {t : State} {ds : List Reg}, Only ds s t → ∀ d, lw s₀ t d = lw s₀ s d :=
    fun k d => lw_mem k.mem d
  -- The values.
  obtain r5₁ : s₁.gpr .a2 = BitVec.ofNat 64 index := by rw [u₁.gpr, h.fs.pos.index]
  obtain X : s₁₁.gpr .a1 = BitVec.ofNat 64 base + BitVec.ofNat 64 index - BitVec.ofNat 64 1 := by
    rw [u₁₁.other _ (by decide), o₁₀.gpr _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), o₄.gpr _ (by decide),
      u₃.gpr, u₂.gpr, u₁.other _ (by decide), ha, r5₁]
  obtain M₁ : s₅.gpr .a3 = if index = 0 then BitVec.allOnes 64 else 0 := by
    rw [u₅.gpr, v₄, u₃.other _ (by decide), u₂.other _ (by decide), r5₁]
    by_cases h0 : index = 0
    · subst h0; decide
    · rw [ite_eq_right (mt (ofNat_eq_zero (by omega_using [hi, sl])).mp h0), ite_eq_right h0]; decide
  obtain Y : s₁₁.gpr .a0 = BitVec.ofNat 64 base + (if index = 0 then BitVec.allOnes 64 else 0) := by
    rw [u₁₁.other _ (by decide), o₁₀.gpr _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), o₄.gpr _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ha, M₁]
  obtain M₂ : s₁₁.gpr .a2 = if rl = lane then BitVec.allOnes 64 else 0 := by
    rw [u₁₁.gpr, v₁₀, u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₈.gpr, lw_mem u₇.mem, m o₆, hr,
      (h.of_only o₆).fs.pos.lane]
    by_cases hs : rl = lane
    · rw [hs, BitVec.xor_self, ite_eq_left rfl]; decide
    · rw [ite_eq_right (mt (xor_eq_zero (by omega_using [hrl, lt]) (by omega_using [hl, lt])).mp hs), ite_eq_right hs]; decide
  obtain val : s₁₄.gpr .a0 = BitVec.ofNat 64 (countV base index (rl == lane)) := by
    rw [u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₃.gpr, u₁₂.gpr,
      u₁₂.other _ (by decide), X, Y, M₂, sel, countV]
    by_cases hs : rl = lane
    · rw [ite_eq_left hs, show (rl == lane) = true from beq_iff_eq.mpr hs, BitVec.ofNat_add_ofNat,
        sub_ofNat (hsame hs)]
      rfl
    · rw [ite_eq_right hs, show (rl == lane) = false from beq_eq_false_iff_ne.mpr hs]
      simp only [Bool.false_eq_true, ite_false]
      by_cases hi0 : index = 0
      · simp only [hi0, ite_true]; exact add_allOnes (hother hs hi0) (by omega_using [hb])
      · simp only [hi0, ite_false, Nat.sub_zero]; exact BitVec.add_zero _
  refine wp_stloc h₁₄.fs.inv (d := cntOff) (by decide) fun t it vt ot gt mt =>
    k t (h₁₄.store hp it (d := cntOff) (by decide) (by decide) mt ot) (by rw [gt, val]) (by rw [vt, val])
      (fun e he hd => by rw [ot e he hd, m o₁₄])
      (fun r hr => by rw [gt, (o₁₄.mono (es := [.a0, .a1, .a2, .a3]) (by simp)).gpr r hr])

end

end VG.Proof.Argon2.RISCV64.Derive

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd wp_add wp_addi wp_sub wp_subi)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.RISCV64.Derive (laneOff laneLenOff j1Off refLaneOff startOff cntOff tmpOff curOff)

/-- The position in the window that `j1` selects. -/
def relV (cnt j1 : Nat) : Nat := cnt - 1 - cnt * (j1 * j1 / 2 ^ 32) / 2 ^ 32

theorem mulHi {a b : Nat} (h : a * b < 2 ^ 64) :
    (BitVec.ofNat 64 a * BitVec.ofNat 64 b) >>> 32 = BitVec.ofNat 64 (a * b / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : a % 2 ^ 64 * (b % 2 ^ 64) = a * b := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right a hb) h),
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left b ha) h)]
  rw [this, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_arith)]

/-- The sign of `sum - L` as a bit. -/
theorem sign_sub {a b : Nat} (ha : a < 2 ^ 63) (hb : b ≤ 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = if a < b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  by_cases c : a < b
  · rw [ite_eq_left c, show (1 : BitVec 64).toNat = 1 from rfl]; omega_arith
  · rw [ite_eq_right c, show (0 : BitVec 64).toNat = 0 from rfl]; omega_arith

theorem wrap_eq {a b : Nat} (ha : a < 2 * b) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) + (if a < b then (1 : BitVec 64) else 0) * BitVec.ofNat 64 b =
      BitVec.ofNat 64 (a % b) := by
  rw [Proof.Argon2.reference_wrap a b ha]
  by_cases c : a < b
  · rw [ite_eq_left c, ite_eq_left c, show (1 : BitVec 64) * BitVec.ofNat 64 b = BitVec.ofNat 64 b by simp,
      BitVec.sub_add_cancel]
  · rw [ite_eq_right c, ite_eq_right c, sub_ofNat (by omega_arith)]
    simp

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem laneLen_lt : (prm s₀).laneLen < 2 ^ 32 := by
  have := segLen_lt hp
  have := hp.laneLen_eq
  omega_arith

omit hp in
/-- `relative`: `r3 :=` the position in the window. -/
theorem relative_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) (hj : J1.toNat < 2 ^ 32) {cnt : Nat} (hc : 1 ≤ cnt)
    (hc' : cnt < 2 ^ 32) (hcnt : lw s₀ s cntOff = BitVec.ofNat 64 cnt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .a0 = BitVec.ofNat 64 (relV cnt J1.toNat) → Only [.a0, .a1, .a2] s t →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.relative ++ is)) s Q := by
  obtain x32 := Proof.Argon2.reference_scaled_bound J1.toNat hj
  obtain lt := Proof.Argon2.reference_scale_lt_count cnt J1.toNat (by omega_arith) hj
  obtain sq : J1.toNat * J1.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt hj hj) (by decide)
  obtain cx : cnt * (J1.toNat * J1.toNat / 2 ^ 32) < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt hc' x32) (by decide)
  unfold Impl.Argon2.RISCV64.Derive.relative
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc h.fs.inv (d := j1Off) (by decide) fun s₁ u₁ => wp_mul fun s₂ u₂ =>
    wp_srl (by decide) fun s₃ u₃ => ?_
  obtain O₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  refine wp_ldloc (h.of_only O₃).fs.inv (d := cntOff) (by decide) fun s₄ u₄ => wp_mul fun s₅ u₅ =>
    wp_srl (by decide) fun s₆ u₆ => wp_subi (by decide) fun s₇ u₇ => wp_sub fun t u => k t ?_ ?_
  · have x₃ : s₃.gpr .a1 = BitVec.ofNat 64 (J1.toNat * J1.toNat / 2 ^ 32) := by
      apply BitVec.eq_of_toNat_eq
      rw [u₃.gpr, u₂.gpr, u₁.gpr, h.j1, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul,
        Nat.mod_eq_of_lt sq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    obtain c₄ : s₄.gpr .a2 = BitVec.ofNat 64 cnt := by rw [u₄.gpr, lw_mem O₃.mem, hcnt]
    obtain y₆ : s₆.gpr .a1 = BitVec.ofNat 64 (cnt * (J1.toNat * J1.toNat / 2 ^ 32) / 2 ^ 32) := by
      rw [u₆.gpr, u₅.gpr, c₄, u₄.other .a1 (by decide), x₃, mulHi cx]
    rw [u.gpr, u₇.gpr, u₇.other .a1 (by decide), u₆.other .a2 (by decide), u₅.other .a2 (by decide), c₄, y₆,
      sub_ofNat hc, sub_ofNat (by omega_arith), relV]
  · exact (O₃.trans (((((Only.of_upd u₄).trans (Only.of_upd u₅)).trans (Only.of_upd u₆)).trans
      (Only.of_upd u₇)).trans (Only.of_upd u))).mono (by simp)

/-- `wrap`: `r3 := (start + r3) mod laneLen`. -/
theorem wrap_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) {rel stt : Nat} (hr : rel < (prm s₀).laneLen)
    (hs : stt < (prm s₀).laneLen) (ha : s.gpr .a0 = BitVec.ofNat 64 rel)
    (hst : lw s₀ s startOff = BitVec.ofNat 64 stt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .a0 = BitVec.ofNat 64 ((stt + rel) % (prm s₀).laneLen) → Only [.a0, .a1, .a2, .a3] s t →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.wrap ++ is)) s Q := by
  obtain L32 := laneLen_lt hp
  unfold Impl.Argon2.RISCV64.Derive.wrap
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc h.fs.inv (d := startOff) (by decide) fun s₁ u₁ => wp_add fun s₂ u₂ => ?_
  obtain O₂ := (Only.of_upd u₁).trans (Only.of_upd u₂)
  refine wp_ldloc (h.of_only O₂).fs.inv (d := laneLenOff) (by decide) fun s₃ u₃ =>
    wp_sub fun s₄ u₄ => wp_srl (by decide) fun s₅ u₅ => wp_mul fun s₆ u₆ => wp_add fun t u => k t ?_ ?_
  · have x₂ : s₂.gpr .a0 = BitVec.ofNat 64 (stt + rel) := by
      rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), ha, hst, BitVec.ofNat_add_ofNat, Nat.add_comm]
    obtain l₃ : s₃.gpr .a1 = BitVec.ofNat 64 (prm s₀).laneLen := by
      rw [u₃.gpr, lw_mem O₂.mem]; exact h.fs.pr.laneLen
    obtain d₄ : s₄.gpr .a2 = BitVec.ofNat 64 (stt + rel) - BitVec.ofNat 64 (prm s₀).laneLen := by
      rw [u₄.gpr, u₃.other _ (by decide), x₂, l₃]
    rw [u.gpr, u₆.other .a2 (by decide), u₆.gpr, u₅.other .a2 (by decide), u₅.gpr, u₅.other .a1 (by decide),
      d₄, u₄.other .a1 (by decide), l₃, sign_sub (by omega_arith) (by omega_arith), wrap_eq (by omega_arith)]
  · exact (O₂.trans (((((Only.of_upd u₃).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans
      (Only.of_upd u₆)).trans (Only.of_upd u))).mono (by simp)

/-- `refPointer`: the address of block `a0` of the reference lane, to the frame. -/
theorem refPointer_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) {col rl : Nat} (hc : col < (prm s₀).laneLen)
    (hrl : rl < lanesN s₀) (ha : s.gpr .a0 = BitVec.ofNat 64 col)
    (hr : lw s₀ s refLaneOff = BitVec.ofNat 64 rl) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr σ J1 J2 t →
      lw s₀ t tmpOff = memP s₀ + BitVec.ofNat 64 ((rl * (prm s₀).laneLen + col) * 1024) →
      (∀ e, e + 8 ≤ 320 → (tmpOff + 8 ≤ e ∨ e + 8 ≤ tmpOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r ∉ [Reg.a0, .a1, .a2], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.refPointer ++ is)) s Q := by
  unfold Impl.Argon2.RISCV64.Derive.refPointer Impl.Argon2.RISCV64.HPrime.mov
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_addi (by decide) fun s₁ u₁ => ?_
  refine wp_ldloc (h.of_only (Only.of_upd u₁)).fs.inv (d := refLaneOff) (by decide) fun s₂ u₂ => ?_
  obtain K₂ := (Only.of_upd u₁).trans (Only.of_upd u₂)
  obtain h₂ := h.of_only K₂
  refine blockAddr_ok hp h₂.fs.inv h₂.fs.pr hrl hc (by rw [u₂.gpr, lw_mem u₁.mem, hr])
    (by rw [u₂.other _ (by decide), u₁.gpr, ha, BitVec.ofNat_add_ofNat, Nat.add_zero]) fun s₃ a₃ k₃ => ?_
  obtain K₃ := K₂.trans k₃
  obtain h₃ := h.of_only K₃
  refine wp_stloc h₃.fs.inv (d := tmpOff) (by decide) fun t it vt ot gt mt =>
    k t (h₃.store hp it (d := tmpOff) (by decide) (by decide) mt ot) (by rw [vt, a₃])
      (fun e he hd => by rw [ot e he hd, lw_mem K₃.mem]) (fun r hr => by
        rw [gt, (K₃.mono (es := [.a0, .a1, .a2]) (by simp)).gpr r hr])

/-- `curPointer`: the address of the current block, to the frame. -/
theorem curPointer_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {J1 J2 : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ J1 J2 s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr σ J1 J2 t →
      lw s₀ t curOff = memP s₀ + BitVec.ofNat 64
        ((lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index)) * 1024) →
      (∀ e, e + 8 ≤ 320 → (curOff + 8 ≤ e ∨ e + 8 ≤ curOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r ∉ [Reg.a0, .a1, .a2], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.curPointer ++ is)) s Q := by
  obtain hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  unfold Impl.Argon2.RISCV64.Derive.curPointer
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine column_ok h.fs.inv h.fs.pr h.fs.pos fun s₁ c₁ k₁ => ?_
  obtain h₁ := h.of_only k₁
  refine wp_ldloc h₁.fs.inv (d := laneOff) (by decide) fun s₂ u₂ => ?_
  obtain K₂ := k₁.trans (Only.of_upd u₂)
  obtain h₂ := h.of_only K₂
  refine blockAddr_ok hp h₂.fs.inv h₂.fs.pr hl hc (by rw [u₂.gpr]; exact h₁.fs.pos.lane)
    (by rw [u₂.other _ (by decide), c₁]) fun s₃ a₃ k₃ => ?_
  obtain K₃ := K₂.trans k₃
  obtain h₃ := h.of_only K₃
  refine wp_stloc h₃.fs.inv (d := curOff) (by decide) fun t it vt ot gt mt =>
    k t (h₃.store hp it (d := curOff) (by decide) (by decide) mt ot) (by rw [vt, a₃])
      (fun e he hd => by rw [ot e he hd, lw_mem K₃.mem]) (fun r hr => by
        rw [gt, (K₃.mono (es := [.a0, .a1, .a2]) (by simp)).gpr r hr])

end

theorem count_eq (p : Spec.Argon2.Params) (pass slice index : Nat) (same : Bool) :
    Spec.Argon2.referenceCount p pass slice index same =
      countV (baseV p.segmentLen p.laneLen pass slice) index same := by
  unfold Spec.Argon2.referenceCount countV baseV
  by_cases h : pass = 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

theorem ref_eq (p : Spec.Argon2.Params) (pass lane slice index : Nat) (w : BitVec 64) :
    Spec.Argon2.reference p pass lane slice index w =
      (refLaneV p.lanes pass slice lane (w >>> 32).toNat,
        (startV p.segmentLen p.laneLen pass slice +
          relV (countV (baseV p.segmentLen p.laneLen pass slice) index
            (refLaneV p.lanes pass slice lane (w >>> 32).toNat == lane)) (w &&& 0xffffffff).toNat) %
          p.laneLen) := by
  unfold Spec.Argon2.reference
  simp only [count_eq]
  rfl

theorem lo_lt (w : BitVec 64) : (w &&& 0xffffffff).toNat < 2 ^ 32 := by
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem hi_lt (w : BitVec 64) : (w >>> 32).toNat < 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega_arith

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `reference`: the reference and current blocks' addresses, to the frame. -/
theorem reference_ok {s : State} {pass slice lane index ctr : Nat} {σ : FillState} {w : BitVec 64}
    (h : RS s₀ pass slice lane index ctr σ (w &&& 0xffffffff) (w >>> 32) s) (hpass : pass < 2 ^ 32)
    (hl : lane < lanesN s₀) (hs : slice < 4) (hi : index < (prm s₀).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.RISCV64.Derive.reference s fun t =>
      RS s₀ pass slice lane index ctr σ (w &&& 0xffffffff) (w >>> 32) t ∧
      lw s₀ t tmpOff = memP s₀ + BitVec.ofNat 64
        (((Spec.Argon2.reference (prm s₀) pass lane slice index w).1 * (prm s₀).laneLen +
          (Spec.Argon2.reference (prm s₀) pass lane slice index w).2) * 1024) ∧
      lw s₀ t curOff = memP s₀ + BitVec.ofNat 64
        ((lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index)) * 1024) := by
  obtain L32 := laneLen_lt hp
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  have hl1 := hp.lanes_pos
  rw [ref_eq]
  generalize hRL : refLaneV (prm s₀).lanes pass slice lane (w >>> 32).toNat = RL
  have hRL' : refLaneV (lanesN s₀) pass slice lane (w >>> 32).toNat = RL := hRL
  obtain rl_lt : RL < lanesN s₀ := by
    rw [← hRL', refLaneV]; split
    · exact hl
    · exact Nat.mod_lt _ (by omega_arith)
  obtain first : pass = 0 → slice = 0 → RL = lane := fun a b => by rw [← hRL', refLaneV, ite_eq_left ⟨a, b⟩]
  generalize hB : baseV (prm s₀).segmentLen (prm s₀).laneLen pass slice = B
  obtain b_le : B ≤ (prm s₀).laneLen := by
    rw [← hB, baseV]; split
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (show slice ≤ 3 by omega_arith)) (by omega_arith))
    · omega_arith
  generalize hST : startV (prm s₀).segmentLen (prm s₀).laneLen pass slice = ST
  obtain st_lt : ST < (prm s₀).laneLen := by
    rw [← hST, startV]; split
    · omega_arith
    · exact Nat.mod_lt _ (by omega_arith)
  obtain cpos := Proof.Argon2.reference_count_positive (prm s₀) hp.lanes_pos hp.memory_ge pass slice index
    (RL == lane) active fun a b => by simp [first a b]
  obtain clt := Proof.Argon2.reference_count_lt_lane (prm s₀) hp.lanes_pos hp.memory_ge pass slice index
    (RL == lane) hs hi
  rw [count_eq, hB] at cpos clt
  unfold Impl.Argon2.RISCV64.Derive.reference
  refine WP.seq ((refLane_ok hp h (hi_lt w) hpass hs).mono fun t₁ ⟨h₁, r₁⟩ => ?_)
  rw [hRL'] at r₁
  refine WP.seq ((refStart_ok hp h₁ hpass hs).mono fun t₂ ⟨h₂, r₂, st₂⟩ => ?_)
  rw [hST] at st₂
  refine WP.seq ((countBase_ok hp h₂ hpass).mono fun t₃ ⟨k₃, a₃⟩ => ?_)
  rw [hB] at a₃
  obtain h₃ := h₂.of_only k₃
  simp only [List.append_assoc]
  rw [← List.append_nil Impl.Argon2.RISCV64.Derive.curPointer]
  refine countSelect_ok hp h₃ (base := B) (rl := RL) (by omega_arith) hi hl rl_lt a₃
    (by rw [lw_mem k₃.mem, r₂, r₁]) (fun e => ?_) (fun e e0 => ?_) fun t₄ h₄ a₄ c₄ o₄ g₄ => ?_
  · rw [← hB, baseV]; split
    · rename_i hp0
      by_cases hs0 : slice = 0
      · omega_arith
      · have := Nat.mul_le_mul_right (prm s₀).segmentLen (show 1 ≤ slice by omega_arith); omega_arith
    · omega_arith
  · have : ¬(pass = 0 ∧ slice = 0) := fun ⟨a, b⟩ => e (first a b)
    rw [← hB, baseV]; split
    · rename_i hp0
      have := Nat.mul_le_mul_right (prm s₀).segmentLen (show 1 ≤ slice by omega_arith); omega_arith
    · omega_arith
  refine relative_ok h₄ (lo_lt w) (cnt := countV B index (RL == lane)) cpos (by omega_arith) c₄
    fun t₅ a₅ k₅ => ?_
  obtain h₅ := h₄.of_only k₅
  obtain rel_lt : relV (countV B index (RL == lane)) (w &&& 0xffffffff).toNat < (prm s₀).laneLen := by
    unfold relV; omega_arith
  refine wrap_ok hp h₅ rel_lt st_lt a₅ (by
      rw [lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, st₂]) fun t₆ a₆ k₆ => ?_
  obtain h₆ := h₅.of_only k₆
  refine refPointer_ok hp h₆ (Nat.mod_lt _ (by omega_arith)) rl_lt a₆ (by
      rw [lw_mem k₆.mem, lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, r₂, r₁])
    fun t₇ h₇ p₇ o₇ _ => ?_
  refine curPointer_ok hp h₇ hl hs hi fun t h' c' o' _ => WP.block_nil ⟨h', ?_, c'⟩
  rw [o' _ (by decide) (by decide), p₇]

end

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-! ### `Argon2.RISCV64.Derive.FillWrite`, which this module and modules that import it used -/

section

/-!
# Argon2 on RISC-V: writing the new block

`writeWords_ok`: the doublewords of a block (at `a1`: G's output, or a
lane's last block) to the current block (at `a3`), XORed into the old ones
after the first pass.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)

open VG.Impl.Argon2.RISCV64.Derive (writeWord)

/-- Doublewords of the memory matrix. -/
abbrev md (s₀ : State) (m : Mem) (o : Nat) : BitVec 64 := m.readW (memP s₀ + BitVec.ofNat 64 o) 64

theorem cell_get {s₀ : State} (m : Mem) (C : Nat) {j : Nat} (hj : j < 128) :
    (blockAt m (matrixCell (memP s₀) C))[j] = md s₀ m (C * 1024 + 8 * j) := by
  rw [blockAt_get _ _ hj, matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A doubleword of the matrix after a store to another, or the same. -/
theorem md_store (m : Mem) {a b : Nat} (ha : a + 8 ≤ blocksN s₀ * 1024) (hb : b + 8 ≤ blocksN s₀ * 1024)
    (h : a = b ∨ a + 8 ≤ b ∨ b + 8 ≤ a) (v : BitVec 64) :
    md s₀ (m.writeW (memP s₀ + BitVec.ofNat 64 a) v) b = if a = b then v else md s₀ m b := by
  have := hp.mem_fits
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self64 _ _ _
  · rw [ite_eq_right e]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega_using [h, e]) (by omega_using [hb, this]) (by omega_using [ha, this])) (by decide)

/-- The doublewords of the current block, `n` of them written. -/
theorem writeWords_ok {s : State} (h : Inv s₀ s) {cur : Nat} (hc : cur < blocksN s₀) (xo : Bool)
    {P : Addr} (h4 : s.gpr .a1 = P) (hPa : P.toNat % 8 = 0)
    (hPw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, P = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len)
    (hPC : Region.Disjoint ⟨P, 1024⟩ ⟨matrixCell (memP s₀) cur, 1024⟩)
    (h6 : s.gpr .a3 = memP s₀ + BitVec.ofNat 64 (cur * 1024)) :
    ∀ n ≤ 128, WP isa (.block ((List.range n).flatMap (writeWord xo))) s fun t =>
      Inv s₀ t ∧ (∀ r, r ≠ .a0 → r ≠ .a2 → t.gpr r = s.gpr r) ∧
      Frame [⟨matrixCell (memP s₀) cur, 1024⟩] s.mem t.mem ∧
      ∀ i < 128, md s₀ t.mem (cur * 1024 + 8 * i) = if i < n then
        (if xo then s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64 ^^^ md s₀ s.mem (cur * 1024 + 8 * i)
          else s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64)
        else md s₀ s.mem (cur * 1024 + 8 * i)
  | 0, _ => WP.block_nil ⟨h, fun _ _ _ => rfl, Frame.refl _ _, fun i _ => by rw [ite_eq_right (by omega_using [])]⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    have hm := hp.mem_fits
    obtain hc' : cur * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_using [hc]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((writeWords_ok h hc xo h4 hPa hPw hPC h6 n (by omega_using [hn])).mono
      fun t ⟨it, gt, ft, wt⟩ => ?_)
    have cell : matrixCell (memP s₀) cur = memP s₀ + BitVec.ofNat 64 (cur * 1024) := rfl
    obtain b1 : cur * 1024 + 8 * n + 8 ≤ blocksN s₀ * 1024 := by omega_using [hc, hn]
    -- The source doubleword is kept: only the current block has been written.
    obtain sw_t : t.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64 = s.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64 := by
      refine ft.readW (r := ⟨P + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hPC.sub_left (Offset.sub_base _ (by omega_using [hn]))
    obtain ea : t.gpr .a1 + BitVec.ofNat 64 (8 * n) = P + BitVec.ofNat 64 (8 * n) := by
      rw [gt _ (by decide) (by decide), h4]
    obtain eb : t.gpr .a3 + BitVec.ofNat 64 (8 * n) = memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n) := by
      rw [gt _ (by decide) (by decide), h6, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    obtain inS : InRegions (t.rd ++ t.wr) (P + BitVec.ofNat 64 (8 * n)) 8 := by
      obtain ⟨R, hR, off, bR, lR⟩ := hPw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      obtain RW : R ∈ t.wr ∧ R.len ≤ 2 ^ 64 := by
        rw [it.wr]
        rcases hR with rfl | rfl
        · exact ⟨scr_mem hp, by show 16384 ≤ 2 ^ 64; decide⟩
        · exact ⟨mem_mem hp, Nat.le_trans (Nat.le_add_left _ _) hm⟩
      rw [bR, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨R, List.mem_append_right _ RW.1, Offset.contains_base _ (by omega_using [hn, lR]) (by have := RW.2; omega_using [hn, lR, this])⟩
    obtain inMc : (memR s₀).Contains (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) 8 :=
      Offset.contains_base _ b1 (by omega_using [hc, hn, hm])
    obtain inC : (⟨matrixCell (memP s₀) cur, 1024⟩ : Region).Contains
        (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) 8 := by
      obtain bl := blocks_lt' hp
      rw [cell]
      exact Offset.contains (e := cur * 1024) (k := 1024) (d := cur * 1024 + 8 * n) (n := 8) _
        (Nat.le_add_right _ _) (by omega_using [hn]) (by omega_using [hc, bl])
    obtain inM : ∀ u : State, Inv s₀ u → InRegions u.wr (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) 8 :=
      fun u iu => ⟨memR s₀, by rw [iu.wr]; exact mem_mem hp, inMc⟩
    obtain o8 : 8 * n < 2048 := by omega_using [hn]
    obtain aP : (P + BitVec.ofNat 64 (8 * n)).toNat % 8 = 0 := Spill.al8 hPa (by omega_using [])
    obtain aC : (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)).toNat % 8 = 0 :=
      Spill.al8 hp.mem_al (by omega_using [])
    -- The doubleword.
    obtain fin : ∀ (v : BitVec 64) (u : State), u.mem = t.mem.writeW (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) v →
        u.rd = t.rd → u.wr = t.wr → u.sp = t.sp → (∀ r, r ≠ .a0 → r ≠ .a2 → u.gpr r = s.gpr r) →
        v = (if xo then s.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64 ^^^ md s₀ s.mem (cur * 1024 + 8 * n)
          else s.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64) →
        Inv s₀ u ∧ (∀ r, r ≠ .a0 → r ≠ .a2 → u.gpr r = s.gpr r) ∧
        Frame [⟨matrixCell (memP s₀) cur, 1024⟩] s.mem u.mem ∧
        ∀ i < 128, md s₀ u.mem (cur * 1024 + 8 * i) = if i < n + 1 then
          (if xo then s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64 ^^^ md s₀ s.mem (cur * 1024 + 8 * i)
            else s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64)
          else md s₀ s.mem (cur * 1024 + 8 * i) := fun v u hmu hrd hwr hsp gu ev => by
      obtain fu : Frame [⟨matrixCell (memP s₀) cur, 1024⟩] s.mem u.mem := by
        rw [hmu]; exact ft.writeW (List.mem_singleton_self _) v inC
      obtain iu : Inv s₀ u := it.step hsp (by rw [gu _ (by decide) (by decide), gt _ (by decide) (by decide)])
        (by rw [gu _ (by decide) (by decide), gt _ (by decide) (by decide)])
        (by rw [gu _ (by decide) (by decide), gt _ (by decide) (by decide)])
        (fun r hr => by
          rw [gu r (by revert hr; revert r; decide) (by revert hr; revert r; decide),
            gt r (by revert hr; revert r; decide) (by revert hr; revert r; decide)])
        hrd hwr (by rw [hmu]; exact (Frame.refl _ _).writeW (r := memR s₀) (by simp) v inMc)
      refine ⟨iu, gu, fu, fun i hi => ?_⟩
      rw [hmu, md_store hp _ b1 (by omega_using [hc, hi]) (by omega_using []), wt i hi]
      by_cases e : i = n
      · subst e
        rw [ite_eq_left rfl, ite_eq_left (show i < i + 1 by omega_using []), ev]
      · rw [ite_eq_right (show ¬cur * 1024 + 8 * n = cur * 1024 + 8 * i by omega_using [e])]
        by_cases c : i < n
        · rw [ite_eq_left c, ite_eq_left (show i < n + 1 by omega_using [c])]
        · rw [ite_eq_right c, ite_eq_right (show ¬i < n + 1 by omega_using [e, c])]
    cases xo
    · simp only [writeWord, Bool.false_eq_true, ite_false, List.nil_append]
      refine wp_ld o8 ea aP inS fun u₁ v₁ => ?_
      refine wp_sd (a := memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) o8 (by rw [v₁.other .a3 (by decide)]; exact eb) aC (by rw [v₁.wr]; exact inM _ it)
        fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₁.mem, v₁.gpr]) (by rw [mu.rd, v₁.rd]) (by rw [mu.wr, v₁.wr])
        (by rw [mu.sp, v₁.sp]) (fun r a b => by rw [mu.gpr, v₁.other r a, gt r a b]) ?_
      simp only [Bool.false_eq_true, ite_false]
      rw [← sw_t]
    · simp only [writeWord, ite_true, List.cons_append, List.nil_append]
      refine wp_ld o8 ea aP inS fun u₁ v₁ => ?_
      refine wp_ld (a := memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) o8 (by rw [v₁.other .a3 (by decide)]; exact eb) aC
        (by rw [v₁.rd, v₁.wr]; exact ⟨memR s₀, List.mem_append_right _ (by rw [it.wr]; exact mem_mem hp), inMc⟩)
        fun u₂ v₂ => wp_xor fun u₃ v₃ => ?_
      refine wp_sd (a := memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) o8 (by rw [v₃.other .a3 (by decide), v₂.other .a3 (by decide), v₁.other .a3 (by decide)]; exact eb) aC
        (by rw [v₃.wr, v₂.wr, v₁.wr]; exact inM _ it) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₃.mem, v₂.mem, v₁.mem, v₃.gpr]) (by rw [mu.rd, v₃.rd, v₂.rd, v₁.rd])
        (by rw [mu.wr, v₃.wr, v₂.wr, v₁.wr]) (by rw [mu.sp, v₃.sp, v₂.sp, v₁.sp])
        (fun r a b => by rw [mu.gpr, v₃.other r a, v₂.other r b, v₁.other r a, gt r a b]) ?_
      simp only [ite_true]
      rw [v₂.other .a0 (by decide), v₁.gpr, v₂.gpr, v₁.mem]
      change t.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64 ^^^ md s₀ t.mem (cur * 1024 + 8 * n) = _
      rw [sw_t, wt n (by omega_using [hn]),
        ite_eq_right (show ¬n < n by omega_using [])]

end

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: one block of the filling loops

`fillCompress_ok`: G of the previous and reference blocks to
`scratch`; `fillWrite_ok`: the current block, copied or XORed;
`fillBlock_ok`: the filling state after one block (`Spec.Argon2.fillBlock`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.Spec.Argon2 (Block zeroBlock FillState compress xorBlock)
open VG.Impl.Argon2.RISCV64.Derive (passOff counterOff tmpOff curOff)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem outside_work : Outside s₀ ⟨gwP s₀, 4096⟩ :=
  outside_scr hp (o := 4096) (n := 4096) (.inr ⟨by decide, by decide⟩)

/-- `fillCompress`: G of the previous and reference blocks, to `scratch`. -/
theorem fillCompress_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {R : Nat} (hR : R < blocksN s₀)
    (htmp : lw s₀ s tmpOff = memP s₀ + BitVec.ofNat 64 (R * 1024)) :
    WP isa Impl.Argon2.RISCV64.Derive.fillCompress s fun t => FS s₀ pass slice lane index ctr st t ∧
      (∀ d, d + 8 ≤ 320 → lw s₀ t d = lw s₀ s d) ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 0) =
        compress (blockAt s.mem (matrixCell (memP s₀) (lane * (prm s₀).laneLen +
          (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))
        (blockAt s.mem (matrixCell (memP s₀) R)) := by
  have L8 := laneLen_ge hp
  obtain ⟨cl, _⟩ := cell_fits hp hl (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) (Nat.mod_lt _ (by omega_arith))
  unfold Impl.Argon2.RISCV64.Derive.fillCompress Impl.Argon2.RISCV64.HPrime.mov
    Impl.Argon2.RISCV64.Derive.gScratch
  simp only [List.cons_append, List.nil_append]
  refine WP.seq ((prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = P at cl a₁ ⊢
  have h₁ := h.of_only k₁
  refine WP.seq (wp_ldloc h₁.inv (d := tmpOff) (by decide) fun s₂ u₂ => wp_addi (by decide) fun s₃ u₃ =>
    wp_addi (imm := 1024) (by decide) fun s₄ u₄ => wp_addi (imm := 1024) (by decide) fun s₅ u₅ =>
      WP.block_nil ?_)
  have k₄ := (((Only.of_upd u₂).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)
  have h₄ := h₁.of_only k₄
  have m₄ : s₅.mem = s.mem := by rw [k₄.mem, k₁.mem]
  have ax : s₅.gpr .a0 = memP s₀ + BitVec.ofNat 64 (P * 1024) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), a₁]
  have sx : s₅.gpr .a1 = memP s₀ + BitVec.ofNat 64 (R * 1024) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, lw_mem k₁.mem, htmp]
  have cx : s₅.gpr .a2 = scrP s₀ + BitVec.ofNat 64 0 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), h₁.inv.s4]
  have dx : s₅.gpr .a3 = gwP s₀ := by
    rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h₁.inv.s0, BitVec.add_assoc,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  refine ccall_ok hp h₄.inv dx (o := 0) (by decide) (by decide) cx (by rw [ax]; exact .inl ⟨P, cl, rfl⟩)
    (by rw [sx]; exact .inl ⟨R, hR, rfl⟩) fun t it _ f post => ?_
  have ho : ∀ r ∈ [⟨scrP s₀ + BitVec.ofNat 64 0, 1024⟩, ⟨gwP s₀, 4096⟩], Outside s₀ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact outside_scr hp (.inl (by decide))
    · exact outside_work hp
  refine ⟨h₄.frame hp it f ho, fun d h₁ => ?_, ?_⟩
  · rw [lw_keep hp f (fun r hr => ⟨scrR s₀, by simp, ?_⟩) h₁, lw_mem m₄]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scr_sub (by decide)
    · exact scr_sub (o := 4096) (n := 4096) (by decide)
  · rw [post, ax, sx, m₄]; rfl

/-- `fillWrite`: G's output to the current block, XORed into it after the first pass. -/
theorem fillWrite_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) {C : Nat} (hC : C < blocksN s₀)
    (hcur : lw s₀ s curOff = memP s₀ + BitVec.ofNat 64 (C * 1024)) :
    WP isa Impl.Argon2.RISCV64.Derive.fillWrite s fun t => Inv s₀ t ∧
      Frame [⟨matrixCell (memP s₀) C, 1024⟩] s.mem t.mem ∧
      blockAt t.mem (matrixCell (memP s₀) C) = if pass = 0 then blockAt s.mem (scrP s₀ + BitVec.ofNat 64 0)
        else xorBlock (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 0)) (blockAt s.mem (matrixCell (memP s₀) C)) := by
  unfold Impl.Argon2.RISCV64.Derive.fillWrite Impl.Argon2.RISCV64.HPrime.mov
  refine WP.seq (wp_addi (by decide) fun s₁ u₁ => ?_)
  have h₁ := h.of_only (Only.of_upd u₁)
  refine wp_ldloc h₁.inv (d := curOff) (by decide) fun s₂ u₂ => ?_
  have h₂ := h₁.of_only (Only.of_upd u₂)
  refine wp_ldloc h₂.inv (d := passOff) (by decide) fun s₃ u₃ => WP.block_nil ?_
  have h₃ := h₂.of_only (Only.of_upd u₃)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have si : s₃.gpr .a1 = scrP s₀ + BitVec.ofNat 64 0 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.inv.s4]
  have di : s₃.gpr .a3 = memP s₀ + BitVec.ofNat 64 (C * 1024) := by
    rw [u₃.other _ (by decide), u₂.gpr, lw_mem u₁.mem, hcur]
  have Pw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, scrP s₀ + BitVec.ofNat 64 0 = R.base + BitVec.ofNat 64 off ∧
      off + 1024 ≤ R.len := ⟨scrR s₀, by simp, 0, rfl, show 0 + 1024 ≤ 16384 by decide⟩
  have PC : Region.Disjoint ⟨scrP s₀ + BitVec.ofNat 64 0, 1024⟩ ⟨matrixCell (memP s₀) C, 1024⟩ :=
    (hp.mem_scr.symm.sub_left (scr_sub (by decide))).sub_right (Proof.Argon2.matrixCell_sub _ _ _ hC)
  have done : ∀ (xo : Bool) (t : State), (∀ i < 128, md s₀ t.mem (C * 1024 + 8 * i) = if i < 128 then
        (if xo then s₃.mem.readW (scrP s₀ + BitVec.ofNat 64 0 + BitVec.ofNat 64 (8 * i)) 64 ^^^
            md s₀ s₃.mem (C * 1024 + 8 * i)
          else s₃.mem.readW (scrP s₀ + BitVec.ofNat 64 0 + BitVec.ofNat 64 (8 * i)) 64)
        else md s₀ s₃.mem (C * 1024 + 8 * i)) →
      blockAt t.mem (matrixCell (memP s₀) C) = if xo then
        xorBlock (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 0)) (blockAt s.mem (matrixCell (memP s₀) C))
        else blockAt s.mem (scrP s₀ + BitVec.ofNat 64 0) :=
    fun xo t wt => by
      apply Vector.ext
      intro j hj
      rw [cell_get _ _ hj, wt j hj, ite_eq_left hj, m₃]
      cases xo
      · simp only [Bool.false_eq_true, ite_false]; rw [blockAt_get _ _ hj]
      · simp only [ite_true]
        rw [xorBlock, Vector.getElem_zipWith, blockAt_get _ _ hj, cell_get _ _ hj]
  refine WP.ite (decide (pass = 0)) (zero_eval (by omega_arith) (by rw [u₃.gpr, h₂.pos.pass]))
    (fun hb => ?_) fun hb => ?_
  · refine ((writeWords_ok hp h₃.inv hC false si (by rw [BitVec.add_zero]; exact h₃.inv.sal) Pw PC di 128 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₃]; exact ft, ?_⟩)
    rw [done false t wt, ite_eq_left (of_decide_eq_true hb)]; rfl
  · refine ((writeWords_ok hp h₃.inv hC true si (by rw [BitVec.add_zero]; exact h₃.inv.sal) Pw PC di 128 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₃]; exact ft, ?_⟩)
    rw [done true t wt, ite_eq_right (of_decide_eq_false hb)]; rfl

/-- `fillBlock`: one block of the filling loops. -/
theorem fillBlock_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.RISCV64.Derive.fillBlock s fun t =>
      FS s₀ pass slice lane index (ctrNext (prm s₀) pass slice index ctr)
        (Spec.Argon2.fillBlock (prm s₀) pass slice lane index st) t := by
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.RISCV64.Derive.fillBlock
  refine WP.seq ((randomSource_ok hp h hpass hl hs hi).mono fun t₁ ⟨h₁, w₁⟩ => ?_)
  refine WP.seq ((reference_ok hp ⟨h₁, w₁.1, w₁.2⟩ hpass hl hs hi active).mono fun t₂ ⟨h₂, tmp₂, cur₂⟩ => ?_)
  have refLt := Proof.Argon2.reference_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory) hl
  have curLt := Proof.Argon2.current_cell_lt (prm s₀) hp.lanes_pos hl hs hi
  have prevLt := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
    (column := slice * (prm s₀).segmentLen + index) hl
  simp only at refLt
  refine WP.seq ((fillCompress_ok hp h₂.fs hl hs hi (by rw [hb]; exact refLt) tmp₂).mono
    fun t₃ ⟨h₃, l₃, c₃⟩ => ?_)
  refine (fillWrite_ok hp h₃ hpass (C := lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index))
    (by rw [hb]; exact curLt) (by rw [l₃ _ (by decide)]; exact cur₂)).mono
    fun t ⟨it, ft, bt⟩ => ?_
  have cur' : lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index) < blocksN s₀ := by
    rw [hb]; exact curLt
  have kept : ∀ j < (prm s₀).blocks, j ≠ lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index) →
      blockAt t.mem (matrixCell (memP s₀) j) = blockAt t₃.mem (matrixCell (memP s₀) j) := fun j hj ne =>
    blockAt_keep ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact cell_other hp (by rw [hb]; exact hj) cur' ne
  have lt : ∀ d, d + 8 ≤ 320 → lw s₀ t d = lw s₀ t₃ d := fun d h₁ =>
    lw_keep hp ft (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨memR s₀, by simp, Proof.Argon2.matrixCell_sub _ _ _ cur'⟩) h₁
  refine ⟨it, Prm.of_lw h₃.pr fun d h₁ h₂ => lt d (by omega_arith),
    h₃.pos.of_lw fun d h₁ h₂ => lt d (by omega_arith), ?_, ?_⟩
  · obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h₃.cache
    · exact ⟨c0, by rw [lt _ (by decide)]; exact c1, .inl c2⟩
    · refine ⟨c0, by rw [lt _ (by decide)]; exact c1, .inr ⟨c3, ?_⟩⟩
      rw [blockAt_keep ft (fun r hr => ?_), c4]
      simp only [List.mem_singleton] at hr; subst hr
      exact ((cell_disj hp cur' (scrR s₀) (by simp)).symm.sub_left (scr_sub (by decide)))
  · rw [Proof.Argon2.FillStep.memory _ _ _ _ _ _ active]
    simp only [Proof.Argon2.FillStep.update]
    refine Represents.update h₃.mem _ curLt _ ?_ kept
    rw [bt, c₃, h₂.fs.mem.block _ prevLt, h₂.fs.mem.block _ refLt, h₃.mem.block _ curLt]

end

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: the filling loops

`FB s₀ st`: the body with the memory matrix holding `st`'s. `segment_ok`:
a segment, from its first index (`Proof.Argon2.segmentStart`), through
`fillBlock_ok`; `lanes_ok`, `slices_ok` and `passes_ok` the loops around
it, and `passes_ok` all passes, from the initialized memory. Each loop
counts up in the frame and runs while the count differs from its bound.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Impl.Argon2.RISCV64.Derive (sliceOff segLenOff indexOff laneOff passOff counterOff ld st)

/-- The body, the memory matrix holding `st`'s. -/
structure FB (s₀ : State) (st : FillState) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  mem : Represents s.mem (memP s₀) (prm s₀).blocks st.memory

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A store to the frame keeps the cached address block and the matrix. -/
theorem loc_keep {m : Mem} {d : Nat} (h₂ : d + 8 ≤ 320) (v : BitVec 64) :
    blockAt (m.writeW (E s₀ + BitVec.ofNat 64 d) v) (scrP s₀ + BitVec.ofNat 64 2048) =
      blockAt m (scrP s₀ + BitVec.ofNat 64 2048) ∧
    ∀ k < (prm s₀).blocks, blockAt (m.writeW (E s₀ + BitVec.ofNat 64 d) v) (matrixCell (memP s₀) k) =
      blockAt m (matrixCell (memP s₀) k) := by
  have f := frame_loc (s₀ := s₀) (m := m) (d := d) v
  refine ⟨blockAt_keep f fun r hr => ?_, fun k hk => blockAt_keep f fun r hr => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact (loc_disj hp h₂ (scrR s₀) (by simp)).symm.sub_left (scr_sub (by decide))
  · simp only [List.mem_singleton] at hr; subst hr
    have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
    exact (loc_disj hp h₂ (memR s₀) (by simp)).symm.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk')

/-- A store to a loop variable keeps `FB`. -/
theorem FB.store {st : FillState} {s t : State} (h : FB s₀ st s) (it : Inv s₀ t) {d : Nat}
    (hd' : d + 8 ≤ 224) {v : BitVec 64} (hm : t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) v)
    (ho : ∀ e, e + 8 ≤ 320 → (d + 8 ≤ e ∨ e + 8 ≤ d) → lw s₀ t e = lw s₀ s e) : FB s₀ st t :=
  ⟨it, Prm.of_lw h.pr fun e h₁ h₂ => ho e (by omega_arith) (.inl (by omega_arith)),
    Represents.keep h.mem fun k hk => by rw [hm]; exact (loc_keep hp (by omega_arith) v).2 k hk⟩

omit hp in
theorem FB.of_only {st : FillState} {s t : State} {ds : List Reg} (h : FB s₀ st s) (o : Only ds s t)
    (hd : ∀ r ∈ ds, Free r := by decide) : FB s₀ st t :=
  ⟨h.inv.only o hd, h.pr.of_mem o.mem, by rw [o.mem]; exact h.mem⟩

omit hp in
/-- `[s3 + d] += 1`, and `a1 :=` its difference with `B`, by `tail`. -/
theorem advanceTail_ok {s : State} (h : Inv s₀ s) {d n : Nat} (hd : VarOff d) (hl : LocOff d)
    (hn : lw s₀ s d = BitVec.ofNat 64 n) (hn' : n + 1 < 2 ^ 64) {B : Nat} (hB : B < 2 ^ 64)
    {tail : List Instr}
    (ht : ∀ t : State, Inv s₀ t → t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) (BitVec.ofNat 64 (n + 1)) →
      t.gpr .a0 = BitVec.ofNat 64 (n + 1) →
      WP isa (.block tail) t fun u => Only [.a1] t u ∧ u.gpr .a1 = BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 B) :
    WP isa (.block (ld .a0 d :: .addi .a0 .a0 1 :: st d .a0 :: tail)) s fun t => Inv s₀ t ∧
      t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) (BitVec.ofNat 64 (n + 1)) ∧
      (∀ e, e + 8 ≤ 320 → (d + 8 ≤ e ∨ e + 8 ≤ d) → lw s₀ t e = lw s₀ s e) ∧
      VG.RISCV64.eval (.nonzero .a1) t = some (!decide (n + 1 = B)) := by
  refine wp_ldloc h (d := d) hl fun s₁ u₁ => wp_addi (by decide) fun s₂ u₂ => ?_
  have i₂ := (h.upd u₁).upd u₂
  have a₂ : s₂.gpr .a0 = BitVec.ofNat 64 (n + 1) := by rw [u₂.gpr, u₁.gpr, hn, BitVec.ofNat_add_ofNat]
  refine wp_stloc i₂ (d := d) hd fun s₃ i₃ _ o₃ g₃ m₃ => ?_
  have m₃' : s₃.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) (BitVec.ofNat 64 (n + 1)) := by
    rw [m₃, a₂, u₂.mem, u₁.mem]
  refine (ht s₃ i₃ m₃' (by rw [g₃, a₂])).mono fun t ⟨o, z⟩ =>
    ⟨i₃.only o, by rw [o.mem, m₃'], fun e he hde => by
      rw [lw_mem o.mem, o₃ e he hde, lw_mem u₂.mem, lw_mem u₁.mem], ?_⟩
  rw [VG.RISCV64.Wp.eval_nonzero, z, ofNat_sub_beq hn' hB]

end

/-- The body at a lane of the filling loops. -/
structure LS (s₀ : State) (st : FillState) (pass slice lane : Nat) (s : State) : Prop where
  fb : FB s₀ st s
  pass : lw s₀ s passOff = BitVec.ofNat 64 pass
  slice : lw s₀ s sliceOff = BitVec.ofNat 64 slice
  lane : lw s₀ s laneOff = BitVec.ofNat 64 lane

theorem FS.ls {s₀ s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) : LS s₀ st pass slice lane s :=
  ⟨⟨h.inv, h.pr, h.mem⟩, h.pos.pass, h.pos.slice, h.pos.lane⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The index advanced. -/
theorem FS.next {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (it : Inv s₀ t)
    (hm : t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 indexOff) (BitVec.ofNat 64 (index + 1)))
    (ho : ∀ e, e + 8 ≤ 320 → (indexOff + 8 ≤ e ∨ e + 8 ≤ indexOff) → lw s₀ t e = lw s₀ s e) :
    FS s₀ pass slice lane (index + 1) ctr st t := by
  have k := loc_keep hp (m := s.mem) (d := indexOff) (by decide) (BitVec.ofNat 64 (index + 1))
  rw [← hm] at k
  refine ⟨it, Prm.of_lw h.pr fun e h₁ h₂ => ho e (by omega_arith) (.inl (by simp only [indexOff]; omega_arith)),
    ⟨by rw [ho _ (by decide) (by decide)]; exact h.pos.pass, by rw [ho _ (by decide) (by decide)]; exact h.pos.slice,
      by rw [ho _ (by decide) (by decide)]; exact h.pos.lane, by rw [lw, hm, Mem.readW_writeW_self64]⟩, ?_,
    Represents.keep h.mem k.2⟩
  obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h.cache
  · exact ⟨c0, by rw [ho _ (by decide) (by decide)]; exact c1, .inl c2⟩
  · exact ⟨c0, by rw [ho _ (by decide) (by decide)]; exact c1, .inr ⟨c3, by rw [k.1]; exact c4⟩⟩

/-- `setLocal d v`. -/
theorem setLocal_ok {s : State} {st : FillState} (h : FB s₀ st s) {d : Nat} (hd : VarOff d)
    (hd₂ : d + 8 ≤ 224) {v : Nat} (hv : v < 2048) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, FB s₀ st t → lw s₀ t d = BitVec.ofNat 64 v →
      (∀ e, e + 8 ≤ 320 → (d + 8 ≤ e ∨ e + 8 ≤ d) → lw s₀ t e = lw s₀ s e) →
      (∀ r ∉ [Reg.a0], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.setLocal d v ++ is)) s Q := by
  unfold Impl.Argon2.RISCV64.Derive.setLocal
  simp only [List.cons_append, List.nil_append]
  refine wp_li hv fun s₁ u₁ => ?_
  have f₁ := h.of_only (Only.of_upd u₁)
  refine wp_stloc f₁.inv (d := d) hd fun t it vt ot gt mt =>
    k t (f₁.store hp it hd₂ mt ot) (by rw [vt, u₁.gpr]) (fun e he hde => by rw [ot e he hde, lw_mem u₁.mem])
      fun r hr => by rw [gt, u₁.other _ (fun e => hr (by simp [e]))]

/-- The block of `segmentStart`: the counter cleared, and `a0` zero in the
first slice of the first pass. -/
theorem segStartBlk_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.setLocal counterOff 0 ++
      ([ld .a0 passOff, ld .a1 sliceOff, .logic .or .a0 .a0 .a1] : List Instr))) s
      fun t => LS s₀ st pass slice lane t ∧ lw s₀ t counterOff = BitVec.ofNat 64 0 ∧
        isa.eval (.zero .a0) t = some (decide (pass = 0 ∧ slice = 0)) := by
  refine setLocal_ok hp h.fb (d := counterOff) (by decide) (by decide) (by decide)
    fun s₂ f₂ v₂ o₂ _ => ?_
  have L₂ : ∀ d ∈ [passOff, sliceOff, laneOff], lw s₀ s₂ d = lw s₀ s d := fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    exact o₂ d (by rcases hd with rfl | rfl | rfl <;> decide) (by rcases hd with rfl | rfl | rfl <;> decide)
  refine wp_ldloc f₂.inv (d := passOff) (by decide) fun s₃ u₃ =>
    wp_ldloc (f₂.inv.upd u₃) (d := sliceOff) (by decide) fun s₄ u₄ =>
    wp_or fun t u₅ => WP.block_nil ?_
  have o := ((Only.of_upd u₃).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)
  have ft := f₂.of_only o
  have m : t.mem = s₂.mem := o.mem
  refine ⟨⟨ft, by rw [lw_mem m, L₂ _ (by simp)]; exact h.pass, by rw [lw_mem m, L₂ _ (by simp)]; exact h.slice,
    by rw [lw_mem m, L₂ _ (by simp)]; exact h.lane⟩, by rw [lw_mem m, v₂], ?_⟩
  rw [show isa.eval _ t = VG.RISCV64.eval _ t from rfl, VG.RISCV64.Wp.eval_zero, u₅.gpr,
    u₄.other _ (by decide), u₄.gpr, u₃.gpr, lw_mem u₃.mem, L₂ _ (by simp), L₂ _ (by simp), h.pass, h.slice,
    or_zero (by omega_arith) (by omega_arith)]

/-- `segmentStart`: the counter cleared, and the segment's first index. -/
theorem segmentStart_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.RISCV64.Derive.segmentStart s
      (FS s₀ pass slice lane (Proof.Argon2.segmentStart pass slice) 0 st) := by
  unfold Impl.Argon2.RISCV64.Derive.segmentStart
  refine WP.seq ((segStartBlk_ok hp h hpass hs).mono fun s₄ ⟨f₄, c₄, z₄⟩ => ?_)
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) z₄ (fun hb => ?_) fun hb => ?_
  all_goals
    rw [← List.append_nil (Impl.Argon2.RISCV64.Derive.setLocal _ _)]
    refine setLocal_ok hp f₄.fb (d := indexOff) (by decide) (by decide) (by decide)
      fun t ft vt ot _ => WP.block_nil ?_
    have Lt : ∀ d ∈ [passOff, sliceOff, laneOff, counterOff], lw s₀ t d = lw s₀ s₄ d := fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      exact ot d (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
    refine ⟨ft.inv, ft.pr, ⟨by rw [Lt _ (by simp)]; exact f₄.pass, by rw [Lt _ (by simp)]; exact f₄.slice,
      by rw [Lt _ (by simp)]; exact f₄.lane, ?_⟩, ⟨by decide, by rw [Lt _ (by simp), c₄], .inl rfl⟩, ft.mem⟩
    rw [vt, Proof.Argon2.segmentStart]
  · rw [ite_eq_left (of_decide_eq_true hb)]
  · rw [ite_eq_right (of_decide_eq_false hb)]

end

theorem segment_snoc (p : Spec.Argon2.Params) (pass lane slice start k : Nat) (st : FillState) :
    Proof.Argon2.segment p pass lane slice start (k + 1) st =
      Spec.Argon2.fillBlock p pass slice lane (start + k) (Proof.Argon2.segment p pass lane slice start k st) := by
  rw [Proof.Argon2.segment_append, Proof.Argon2.segment_succ, Proof.Argon2.segment_zero]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The comparison of the segment's first index with its length. -/
theorem segCmp_ok {s : State} {pass slice lane S ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane S ctr st s) (hS : S ≤ 2) :
    WP isa (.block [ld .a0 indexOff, ld .a1 segLenOff, .sub .a1 .a0 .a1]) s
      fun t => FS s₀ pass slice lane S ctr st t ∧
        isa.eval (.zero .a1) t = some (decide (S = (prm s₀).segmentLen)) := by
  have sl := segLen_lt hp
  refine wp_ldloc h.inv (d := indexOff) (by decide) fun t₁ u₁ =>
    wp_ldloc (h.inv.upd u₁) (d := segLenOff) (by decide) fun t₂ u₂ =>
    wp_sub fun t u => WP.block_nil ?_
  refine ⟨h.of_only (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u)), ?_⟩
  rw [show isa.eval _ t = VG.RISCV64.eval _ t from rfl, VG.RISCV64.Wp.eval_zero, u.gpr,
    u₂.other _ (by decide), u₁.gpr, u₂.gpr, lw_mem u₁.mem, h.pr.segLen, h.pos.index,
    sub_beq (by omega_arith) (by omega_arith)]

/-- One block of a segment, and the index advanced. -/
theorem segStep_ok {t : State} {pass slice lane i c : Nat} {X : FillState}
    (ht : FS s₀ pass slice lane i c X t) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : i < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i) :
    WP isa (.seq Impl.Argon2.RISCV64.Derive.fillBlock
      (.block (Impl.Argon2.RISCV64.Derive.advanceBy indexOff (ld .a1 segLenOff)))) t
      fun v => FS s₀ pass slice lane (i + 1) (ctrNext (prm s₀) pass slice i c)
        (Spec.Argon2.fillBlock (prm s₀) pass slice lane i X) v ∧
        VG.RISCV64.eval (.nonzero .a1) v = some (!decide (i + 1 = (prm s₀).segmentLen)) := by
  have sl := segLen_lt hp
  refine WP.seq ((fillBlock_ok hp ht hpass hl hs hi active).mono fun u hu => ?_)
  unfold Impl.Argon2.RISCV64.Derive.advanceBy
  refine (advanceTail_ok hu.inv (d := indexOff) (n := i) (by decide) (by decide) hu.pos.index (by omega_arith)
    (B := (prm s₀).segmentLen) (by omega_arith) fun v iv mv av => ?_).mono
    fun v ⟨iv, mv, ov, cv⟩ => ⟨hu.next hp iv mv ov, cv⟩
  have sv : lw s₀ v segLenOff = BitVec.ofNat 64 (prm s₀).segmentLen := by
    rw [lw, mv, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact hu.pr.segLen
  refine wp_ldloc iv (d := segLenOff) (by decide) fun v₁ u₁ => wp_sub fun w u => WP.block_nil
    ⟨((Only.of_upd u₁).trans (Only.of_upd u)).mono (by simp), ?_⟩
  rw [u.gpr, u₁.other _ (by decide), av, u₁.gpr, sv]

/-- `segment`: a segment of the filling loops. -/
theorem segment_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) (hl : lane < lanesN s₀) :
    WP isa Impl.Argon2.RISCV64.Derive.segment s
      (LS s₀ (Proof.Argon2.segment (prm s₀) pass lane slice 0 (prm s₀).segmentLen st) pass slice lane) := by
  have s2 := hp.segLen_two
  have sl := segLen_lt hp
  have hS : Proof.Argon2.segmentStart pass slice ≤ 2 := by unfold Proof.Argon2.segmentStart; split <;> omega_arith
  have hS2 : pass = 0 → slice = 0 → Proof.Argon2.segmentStart pass slice = 2 := fun a b => by
    unfold Proof.Argon2.segmentStart; rw [ite_eq_left ⟨a, b⟩]
  generalize hSd : Proof.Argon2.segmentStart pass slice = S at hS hS2
  rw [Proof.Argon2.segment_start _ _ _ _ _ s2, hSd]
  unfold Impl.Argon2.RISCV64.Derive.segment
  refine WP.seq ((segmentStart_ok hp h hpass hs).mono fun t₁ h₁ => ?_)
  rw [hSd] at h₁
  refine WP.seq ((segCmp_ok hp h₁ hS).mono fun t₃ ⟨h₃, c₃⟩ => ?_)
  refine WP.ite (decide (S = (prm s₀).segmentLen)) c₃ (fun hb => ?_) fun hb => ?_
  · have hb' : S = (prm s₀).segmentLen := of_decide_eq_true hb
    refine WP.block_nil ?_
    rw [show (prm s₀).segmentLen - S = 0 by omega_arith, Proof.Argon2.segment_zero]
    exact h₃.ls
  · have hb' : S < (prm s₀).segmentLen := by have := of_decide_eq_false hb; omega_arith
    refine WP.loop (M := isa) (fun n t => ∃ i, n = (prm s₀).segmentLen - i ∧ S ≤ i ∧ i < (prm s₀).segmentLen ∧
      ∃ c, FS s₀ pass slice lane i c (Proof.Argon2.segment (prm s₀) pass lane slice S (i - S) st) t) ?_
      ((prm s₀).segmentLen - S) t₃ ⟨S, rfl, Nat.le_refl _, hb', 0, by rw [Nat.sub_self]; exact h₃⟩
    rintro n t ⟨i, rfl, hSi, hi, c, ht⟩
    refine (segStep_ok hp ht hpass hl hs hi (by
        by_cases a : pass = 0
        · by_cases b : slice = 0
          · have := hS2 a b; omega_arith
          · exact .inr (.inl b)
        · exact .inl a)).mono fun v ⟨hv, cv⟩ => ?_
    have eq : Proof.Argon2.segment (prm s₀) pass lane slice S (i + 1 - S) st =
        Spec.Argon2.fillBlock (prm s₀) pass slice lane i
          (Proof.Argon2.segment (prm s₀) pass lane slice S (i - S) st) := by
      rw [show i + 1 - S = (i - S) + 1 by omega_arith, segment_snoc, show S + (i - S) = i by omega_arith]
    rw [← eq] at hv
    by_cases e : i + 1 = (prm s₀).segmentLen
    · refine .inl ⟨cv.trans (by rw [e]; simp), ?_⟩
      rw [show (prm s₀).segmentLen - S = i + 1 - S by omega_arith]
      exact hv.ls
    · exact .inr ⟨cv.trans (by rw [decide_eq_false e]; rfl), _, by omega_arith, i + 1, rfl, by omega_arith, by omega_arith, _, hv⟩

end

theorem foldl_range'_snoc {α : Type} (f : α → Nat → α) (start k : Nat) (x : α) :
    (List.range' start (k + 1)).foldl f x = f ((List.range' start k).foldl f x) (start + k) := by
  rw [List.range'_concat, List.foldl_append]
  simp

/-- The body at a slice of the filling loops. -/
structure SS (s₀ : State) (st : FillState) (pass slice : Nat) (s : State) : Prop where
  fb : FB s₀ st s
  pass : lw s₀ s passOff = BitVec.ofNat 64 pass
  slice : lw s₀ s sliceOff = BitVec.ofNat 64 slice

/-- The body at a pass of the filling loops. -/
structure PS (s₀ : State) (st : FillState) (pass : Nat) (s : State) : Prop where
  fb : FB s₀ st s
  pass : lw s₀ s passOff = BitVec.ofNat 64 pass

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `a1 :=` the difference of `a0` with argument `i`, a `u32`. -/
theorem argTail_ok {t : State} (it : Inv s₀ t) {i : Nat} (hi : i < 18) {n : Nat}
    (at' : t.gpr .a0 = BitVec.ofNat 64 n) :
    WP isa (.block [Impl.Argon2.RISCV64.Derive.ldw .a1 i, .sub .a1 .a0 .a1]) t fun u =>
      Only [.a1] t u ∧ u.gpr .a1 = BitVec.ofNat 64 n - BitVec.ofNat 64 (arg32 s₀ i).toNat := by
  refine wp_ldw hp it hi fun t₁ u₁ => wp_sub fun u v => WP.block_nil
    ⟨((Only.of_upd u₁).trans (Only.of_upd v)).mono (by simp), ?_⟩
  rw [v.gpr, u₁.other _ (by decide), at', u₁.gpr, ofNat_toNat (toNat_ext32 _)]

/-- A lane's segment of a slice, and the lane advanced. -/
theorem laneStep_ok {t : State} {pass slice l : Nat} {X : FillState} (ht : LS s₀ X pass slice l t)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) (hl : l < lanesN s₀) :
    WP isa (.seq Impl.Argon2.RISCV64.Derive.segment
      (.block (Impl.Argon2.RISCV64.Derive.advanceBy laneOff
        (Impl.Argon2.RISCV64.Derive.ldw .a1 Impl.Argon2.RISCV64.Derive.lanesArg)))) t fun v =>
      LS s₀ (Proof.Argon2.segment (prm s₀) pass l slice 0 (prm s₀).segmentLen X) pass slice (l + 1) v ∧
      VG.RISCV64.eval (.nonzero .a1) v = some (!decide (l + 1 = lanesN s₀)) := by
  have hlt := hp.lanes_lt
  refine WP.seq ((segment_ok hp ht hpass hs hl).mono fun u hu => ?_)
  unfold Impl.Argon2.RISCV64.Derive.advanceBy
  refine (advanceTail_ok hu.fb.inv (d := laneOff) (n := l) (by decide) (by decide) hu.lane (by omega_arith)
    (B := lanesN s₀) (by omega_arith) fun v iv _ av => argTail_ok hp iv (i := 7) (by decide) av).mono
    fun v ⟨iv, mv, ov, cv⟩ => ⟨?_, cv⟩
  refine ⟨hu.fb.store hp iv (d := laneOff) (by decide) mv ov, ?_, ?_, ?_⟩
  · rw [ov _ (by decide) (by decide)]; exact hu.pass
  · rw [ov _ (by decide) (by decide)]; exact hu.slice
  · rw [lw, mv, Mem.readW_writeW_self64]

/-- `lanesLoop`: every lane's segment of a slice. -/
theorem lanes_ok {s : State} {pass slice : Nat} {st : FillState} (h : SS s₀ st pass slice s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.RISCV64.Derive.lanesLoop s
      (SS s₀ (Proof.Argon2.lanes (prm s₀) pass slice 0 (lanesN s₀) st) pass slice) := by
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.RISCV64.Derive.lanesLoop
  rw [← List.append_nil (Impl.Argon2.RISCV64.Derive.setLocal _ _)]
  refine WP.seq (setLocal_ok hp h.fb (d := laneOff) (by decide) (by decide) (by decide)
    fun t₁ f₁ v₁ o₁ _ => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧
    LS s₀ (Proof.Argon2.lanes (prm s₀) pass slice 0 l st) pass slice l t) ?_ (lanesN s₀) t₁
    ⟨0, by omega_arith, hl1, f₁, by rw [o₁ _ (by decide) (by decide)]; exact h.pass,
      by rw [o₁ _ (by decide) (by decide)]; exact h.slice, v₁⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (laneStep_ok hp ht hpass hs hl).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Proof.Argon2.segment (prm s₀) pass l slice 0 (prm s₀).segmentLen
      (Proof.Argon2.lanes (prm s₀) pass slice 0 l st) = Proof.Argon2.lanes (prm s₀) pass slice 0 (l + 1) st from by
    unfold Proof.Argon2.lanes; rw [foldl_range'_snoc, Nat.zero_add]] at hv
  by_cases e : l + 1 = lanesN s₀
  · refine .inl ⟨cv.trans (by rw [e]; simp), ?_⟩
    rw [← e]
    exact ⟨hv.fb, hv.pass, hv.slice⟩
  · exact .inr ⟨cv.trans (by rw [decide_eq_false e]; rfl), _, by omega_arith, l + 1, rfl, by omega_arith, hv⟩

/-- A slice of a pass, and the slice advanced. -/
theorem sliceStep_ok {t : State} {pass j : Nat} {X : FillState} (ht : SS s₀ X pass j t)
    (hpass : pass < 2 ^ 32) (hj : j < 4) :
    WP isa (.seq Impl.Argon2.RISCV64.Derive.lanesLoop
      (.block (Impl.Argon2.RISCV64.Derive.advanceImm sliceOff 4))) t fun v =>
      SS s₀ (Proof.Argon2.lanes (prm s₀) pass j 0 (lanesN s₀) X) pass (j + 1) v ∧
      VG.RISCV64.eval (.nonzero .a1) v = some (!decide (j + 1 = 4)) := by
  refine WP.seq ((lanes_ok hp ht hpass hj).mono fun u hu => ?_)
  unfold Impl.Argon2.RISCV64.Derive.advanceImm
  refine (advanceTail_ok hu.fb.inv (d := sliceOff) (n := j) (by decide) (by decide) hu.slice (by omega_arith)
    (B := 4) (by decide) fun t it _ at' => wp_subi (by decide) fun u v =>
      WP.block_nil ⟨Only.of_upd v, by rw [v.gpr, at']⟩).mono
    fun v ⟨iv, mv, ov, cv⟩ => ⟨?_, cv⟩
  refine ⟨hu.fb.store hp iv (d := sliceOff) (by decide) mv ov, ?_, ?_⟩
  · rw [ov _ (by decide) (by decide)]; exact hu.pass
  · rw [lw, mv, Mem.readW_writeW_self64]

/-- `slicesLoop`: one pass. -/
theorem slices_ok {s : State} {pass : Nat} {st : FillState} (h : PS s₀ st pass s) (hpass : pass < 2 ^ 32) :
    WP isa Impl.Argon2.RISCV64.Derive.slicesLoop s (PS s₀ (Spec.Argon2.fillPass (prm s₀) st pass) pass) := by
  unfold Impl.Argon2.RISCV64.Derive.slicesLoop
  rw [← Proof.Argon2.slices_pass, ← List.append_nil (Impl.Argon2.RISCV64.Derive.setLocal _ _)]
  refine WP.seq (setLocal_ok hp h.fb (d := sliceOff) (by decide) (by decide) (by decide)
    fun t₁ f₁ v₁ o₁ _ => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun n t => ∃ j, n = 4 - j ∧ j < 4 ∧
    SS s₀ (Proof.Argon2.slices (prm s₀) pass 0 j st) pass j t) ?_ 4 t₁
    ⟨0, rfl, by decide, f₁, by rw [o₁ _ (by decide) (by decide)]; exact h.pass, v₁⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine (sliceStep_ok hp ht hpass hj).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Proof.Argon2.lanes (prm s₀) pass j 0 (lanesN s₀) (Proof.Argon2.slices (prm s₀) pass 0 j st) =
      Proof.Argon2.slices (prm s₀) pass 0 (j + 1) st from by
    unfold Proof.Argon2.slices; rw [foldl_range'_snoc, Nat.zero_add]; rfl] at hv
  by_cases e : j + 1 = 4
  · refine .inl ⟨cv.trans (by rw [e]; simp), ?_⟩
    rw [show (4 : Nat) = j + 1 by omega_arith]
    exact ⟨hv.fb, hv.pass⟩
  · exact .inr ⟨cv.trans (by rw [decide_eq_false e]; rfl), _, by omega_arith, j + 1, rfl, by omega_arith, hv⟩

/-- A pass, and the pass advanced. -/
theorem passStep_ok {t : State} {k : Nat} {X : FillState} (ht : PS s₀ X k t) (hk : k < itersN s₀) :
    WP isa (.seq Impl.Argon2.RISCV64.Derive.slicesLoop
      (.block (Impl.Argon2.RISCV64.Derive.advanceBy passOff
        (Impl.Argon2.RISCV64.Derive.ldw .a1 Impl.Argon2.RISCV64.Derive.iterationsArg)))) t fun v =>
      PS s₀ (Spec.Argon2.fillPass (prm s₀) X k) (k + 1) v ∧
        VG.RISCV64.eval (.nonzero .a1) v = some (!decide (k + 1 = itersN s₀)) := by
  have hpl : itersN s₀ < 2 ^ 32 := (arg32 s₀ 5).isLt
  refine WP.seq ((slices_ok hp ht (by omega_arith)).mono fun u hu => ?_)
  unfold Impl.Argon2.RISCV64.Derive.advanceBy
  refine (advanceTail_ok hu.fb.inv (d := passOff) (n := k) (by decide) (by decide) hu.pass (by omega_arith)
    (B := itersN s₀) (by omega_arith) fun v iv _ av => argTail_ok hp iv (i := 5) (by decide) av).mono
    fun v ⟨iv, mv, ov, cv⟩ => ⟨?_, cv⟩
  refine ⟨hu.fb.store hp iv (d := passOff) (by decide) mv ov, ?_⟩
  rw [lw, mv, Mem.readW_writeW_self64]

/-- `passesLoop`: every pass. -/
theorem passes_ok {s : State} {st : FillState} (h : FB s₀ st s) :
    WP isa Impl.Argon2.RISCV64.Derive.passesLoop s (FB s₀ (Proof.Argon2.iterations (prm s₀) 0 (itersN s₀) st)) := by
  have hp1 := hp.passes_pos
  unfold Impl.Argon2.RISCV64.Derive.passesLoop
  rw [← List.append_nil (Impl.Argon2.RISCV64.Derive.setLocal _ _)]
  refine WP.seq (setLocal_ok hp h (d := passOff) (by decide) (by decide) (by decide)
    fun t₁ f₁ v₁ _ _ => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun n t => ∃ k, n = itersN s₀ - k ∧ k < itersN s₀ ∧
    PS s₀ (Proof.Argon2.iterations (prm s₀) 0 k st) k t) ?_ (itersN s₀) t₁ ⟨0, by omega_arith, by omega_arith, f₁, v₁⟩
  rintro n t ⟨k, rfl, hk, ht⟩
  refine (passStep_ok hp ht hk).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Spec.Argon2.fillPass (prm s₀) (Proof.Argon2.iterations (prm s₀) 0 k st) k =
      Proof.Argon2.iterations (prm s₀) 0 (k + 1) st from by
    unfold Proof.Argon2.iterations; rw [foldl_range'_snoc, Nat.zero_add]] at hv
  by_cases e : k + 1 = itersN s₀
  · refine .inl ⟨cv.trans (by rw [e]; simp), ?_⟩
    rw [← e]
    exact hv.fb
  · exact .inr ⟨cv.trans (by rw [decide_eq_false e]; rfl), _, by omega_arith, k + 1, rfl, by omega_arith, hv⟩

end

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: the final block and the tag

`reduce_ok`: the memory's first block becomes the XOR of every lane's last
block (`Proof.Argon2.reduction`), the other blocks kept; `finalOutput_ok`:
H′ of it to `out`, the tag (`Proof.Argon2.finish_reduction`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.Spec.Argon2 (Block zeroBlock FillState xorBlock)
open VG.Spec.Blake2 (bytesAt)
open VG.Impl.Argon2.RISCV64.Derive (laneOff laneLenOff)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `n` stores of `a0 = 0` to `[a3 + 8k]`, `a3` the memory matrix. -/
theorem memZeros_ok {s : State} (h : Inv s₀ s) (hx : s.gpr .a3 = memP s₀) (ha : s.gpr .a0 = 0) :
    ∀ n ≤ 128, WP isa (.block ((List.range n).map fun k => Instr.store .d .a0 .a3 (8 * k))) s fun t =>
      Inv s₀ t ∧ t.gpr = s.gpr ∧ Frame [⟨matrixCell (memP s₀) 0, 1024⟩] s.mem t.mem ∧
      ∀ i < n, md s₀ t.mem (8 * i) = 0
  | 0, _ => WP.block_nil ⟨h, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have b1 := blocks_pos hp
    have hm := hp.mem_fits
    have b1k : 1024 ≤ blocksN s₀ * 1024 := Nat.le_mul_of_pos_left _ b1
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append ((memZeros_ok h hx ha n (by omega_arith)).mono fun t ⟨it, gt, ft, wt⟩ => ?_)
    have hc : (memR s₀).Contains (memP s₀ + BitVec.ofNat 64 (8 * n)) 8 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    have hc' : (⟨matrixCell (memP s₀) 0, 1024⟩ : Region).Contains (memP s₀ + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [show matrixCell (memP s₀) 0 = memP s₀ by simp [matrixCell]]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    refine wp_sd (a := memP s₀ + BitVec.ofNat 64 (8 * n)) (by omega_arith) (by rw [gt, hx])
      (Spill.al8 hp.mem_al (by omega_arith))
      ⟨_, by rw [it.wr]; exact mem_mem hp, hc⟩ fun t₁ u₁ => WP.block_nil
      ⟨it.mupd u₁ ((Frame.refl _ _).writeW (r := memR s₀) (by simp) _ hc), by rw [u₁.gpr, gt], ?_,
        fun i hi => ?_⟩
    · rw [u₁.mem]
      exact ft.writeW (List.mem_singleton_self _) _ hc'
    · rw [u₁.mem, gt, md_store hp _ (by omega_arith) (by omega_arith) (by omega_arith), ha]
      by_cases e : 8 * n = 8 * i
      · rw [ite_eq_left e]
      · rw [ite_eq_right e]; exact wt i (by omega_arith)

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
  lane : lw s₀ s laneOff = BitVec.ofNat 64 l
  first : blockAt s.mem (matrixCell (memP s₀) 0) = Proof.Argon2.reduction (prm s₀) M 0 l zeroBlock
  rest : ∀ k < (prm s₀).blocks, k ≠ 0 → blockAt s.mem (matrixCell (memP s₀) k) = M[k]?.getD zeroBlock

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- One lane of the reduction. -/
theorem reduceLane_ok {s : State} {M : Array Block} {l : Nat} (h : RI s₀ M l s) (hl : l < lanesN s₀) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.reduceLane ++
      Impl.Argon2.RISCV64.Derive.advanceBy laneOff
        (Impl.Argon2.RISCV64.Derive.ldw .a1 Impl.Argon2.RISCV64.Derive.lanesArg)))
      s fun t => RI s₀ M (l + 1) t ∧ VG.RISCV64.eval (.nonzero .a1) t = some (!decide (l + 1 = lanesN s₀)) := by
  have L8 := laneLen_ge hp
  have hlt := hp.lanes_lt
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  have b1 := blocks_pos hp
  obtain ⟨cl, hc'⟩ := cell_fits hp hl (col := (prm s₀).laneLen - 1) (by omega_arith)
  have last : Proof.Argon2.lastIndex (prm s₀) l = l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) := by
    unfold Proof.Argon2.lastIndex; rw [Nat.succ_mul]; omega_arith
  have ne0 : l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) ≠ 0 := by omega_arith
  unfold Impl.Argon2.RISCV64.Derive.reduceLane Impl.Argon2.RISCV64.Derive.writeBlock
    Impl.Argon2.RISCV64.HPrime.mov
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldloc h.inv (d := laneOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁
  refine wp_ldloc i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => wp_subi (by decide) fun s₃ u₃ => ?_
  have i₃ := (i₁.upd u₂).upd u₃
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine blockAddr_ok hp i₃ (h.pr.of_mem m₃) hl (col := (prm s₀).laneLen - 1) (by omega_arith)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.lane])
    (by rw [u₃.gpr, u₂.gpr, lw_mem u₁.mem, h.pr.laneLen, sub_ofNat (b := 1) (by omega_arith)])
    fun s₄ a₄ k₄ => ?_
  have i₄ := i₃.only k₄
  refine wp_addi (by decide) fun s₅ u₅ => ?_
  have i₅ := i₄.upd u₅
  refine wp_lda hp i₅ (i := 13) (by decide) fun s₆ u₆ => ?_
  have i₆ := i₅.upd u₆
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, k₄.mem, m₃]
  generalize hc : l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) = c at cl hc' a₄ ne0 last
  have sx : s₆.gpr .a1 = matrixCell (memP s₀) c := by
    rw [u₆.other _ (by decide), u₅.gpr, a₄]; simp [matrixCell]
  have dx : s₆.gpr .a3 = memP s₀ + BitVec.ofNat 64 (0 * 1024) := by
    rw [u₆.gpr]; simp
  refine WP.block_append ((writeWords_ok hp i₆ (cur := 0) b1 true sx
    (by rw [matrixCell]; exact Spill.al8 hp.mem_al (by omega_arith))
    ⟨memR s₀, by simp, c * 1024, rfl, hc'⟩ (cell_other hp cl b1 ne0) dx 128 (Nat.le_refl _)).mono
    fun t₇ ⟨i₇, _, f₇, w₇⟩ => ?_)
  have lt₇ : ∀ d, d + 8 ≤ 320 → lw s₀ t₇ d = lw s₀ s d := fun d h₁ => by
    rw [← lw_mem m₆ d]
    exact lw_keep hp f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨memR s₀, by simp, Proof.Argon2.matrixCell_sub _ _ _ b1⟩) h₁
  unfold Impl.Argon2.RISCV64.Derive.advanceBy
  refine (advanceTail_ok i₇ (d := laneOff) (n := l) (by decide) (by decide)
    (by rw [lt₇ _ (by decide)]; exact h.lane) (by omega_arith) (B := lanesN s₀) (by omega_arith)
    fun v iv _ av => argTail_ok hp iv (i := 7) (by decide) av).mono fun t ⟨it, mt, ot, ct⟩ => ⟨?_, ct⟩
  have kt := loc_keep hp (m := t₇.mem) (d := laneOff) (by decide) (BitVec.ofNat 64 (l + 1))
  rw [← mt] at kt
  have new : blockAt t₇.mem (matrixCell (memP s₀) 0) =
      xorBlock (blockAt s.mem (matrixCell (memP s₀) c)) (blockAt s.mem (matrixCell (memP s₀) 0)) := by
    apply Vector.ext
    intro j hj
    rw [cell_get _ _ hj, w₇ j hj, ite_eq_left hj, xorBlock, Vector.getElem_zipWith, blockAt_get _ _ hj,
      cell_get _ _ hj, m₆]
    rfl
  refine ⟨it, Prm.of_lw h.pr fun d h₁ h₂ => ?_, by rw [lw, mt, Mem.readW_writeW_self64], ?_,
    fun k hk k0 => ?_⟩
  · rw [ot d (by omega_arith) (.inl (by simp only [laneOff]; omega_arith)), lt₇ d (by omega_arith)]
  · rw [kt.2 _ (by rw [← hb]; exact b1), new, h.first, h.rest _ (by rw [← hb]; exact cl) ne0, reduction_snoc,
      Proof.Argon2.xorBlock_comm, last]
  · rw [kt.2 _ hk, blockAt_keep f₇ (fun r hr => ?_), m₆, h.rest k hk k0]
    simp only [List.mem_singleton] at hr; subst hr
    exact cell_other hp (by rw [hb]; exact hk) b1 k0

/-- The first block of `reduce`: the memory's first block cleared, and the lane `0`. -/
theorem reduceStart_ok {s : State} {M : Array Block} (h : Inv s₀ s) (pr : Prm s₀ s)
    (hm : Represents s.mem (memP s₀) (prm s₀).blocks M) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.reduceClear ++ Impl.Argon2.RISCV64.Derive.setLocal laneOff 0)) s
      (RI s₀ M 0) := by
  have b1 := blocks_pos hp
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.RISCV64.Derive.reduceClear Impl.Argon2.RISCV64.Derive.setLocal
  simp only [List.cons_append, List.nil_append]
  refine wp_lda hp h (i := 13) (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => ?_
  have i₂ := (h.upd u₁).upd u₂
  refine WP.block_append ((memZeros_ok hp i₂ (by rw [u₂.other _ (by decide), u₁.gpr]) u₂.gpr 128
    (Nat.le_refl _)).mono fun s₃ ⟨i₃, _, f₃, z₃⟩ => ?_)
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have lt₃ : ∀ d, d + 8 ≤ 320 → lw s₀ s₃ d = lw s₀ s d := fun d h₁ => by
    rw [← lw_mem m₂ d]
    exact lw_keep hp f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨memR s₀, by simp, Proof.Argon2.matrixCell_sub _ _ _ b1⟩) h₁
  refine wp_li (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄
  refine wp_stloc i₄ (d := laneOff) (by decide) fun s₅ i₅ v₅ o₅ _ m₅ => WP.block_nil ?_
  have k₅ := loc_keep hp (m := s₄.mem) (d := laneOff) (by decide) (s₄.gpr .a0)
  rw [← m₅] at k₅
  refine ⟨i₅, Prm.of_lw pr fun d h₁ h₂ => ?_, by rw [v₅, u₄.gpr], ?_, fun k hk k0 => ?_⟩
  · rw [o₅ d (by omega_arith) (.inl (by simp only [laneOff]; omega_arith)), lw_mem u₄.mem, lt₃ d (by omega_arith)]
  · rw [k₅.2 _ (by rw [← hb]; exact b1), u₄.mem, Proof.Argon2.reduction_zero]
    apply Vector.ext
    intro j hj
    rw [cell_get _ _ hj, Nat.zero_mul, Nat.zero_add, z₃ j hj]
    simp [zeroBlock]
  · rw [k₅.2 _ hk, u₄.mem, blockAt_keep f₃ (fun r hr => ?_), m₂, hm.block k hk]
    simp only [List.mem_singleton] at hr; subst hr
    exact cell_other hp (by rw [hb]; exact hk) b1 k0


/-- `reduce`: the XOR of every lane's last block, to the memory's first block. -/
theorem reduce_ok {s : State} {M : Array Block} (h : Inv s₀ s) (pr : Prm s₀ s)
    (hm : Represents s.mem (memP s₀) (prm s₀).blocks M) :
    WP isa Impl.Argon2.RISCV64.Derive.reduce s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      blockAt t.mem (matrixCell (memP s₀) 0) = Proof.Argon2.reduction (prm s₀) M 0 (lanesN s₀) zeroBlock := by
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.RISCV64.Derive.reduce
  refine WP.seq ((reduceStart_ok hp h pr hm).mono fun s₅ start => ?_)
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧ RI s₀ M l t) ?_ (lanesN s₀) s₅
    ⟨0, by omega_arith, hl1, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (reduceLane_ok hp ht hl).mono fun u ⟨hu, cu⟩ => ?_
  by_cases e : l + 1 = lanesN s₀
  · refine .inl ⟨cu.trans (by rw [e]; simp), hu.inv, hu.pr, ?_⟩
    rw [hu.first, e]
  · exact .inr ⟨cu.trans (by rw [decide_eq_false e]; rfl), _, by omega_arith, l + 1, rfl, by omega_arith, hu⟩

/-- `finalOutput`: H′ of the memory's first block, to `out`. -/
theorem finalOutput_ok {s : State} (h : Inv s₀ s) :
    WP isa Impl.Argon2.RISCV64.Derive.finalOutput s fun t => Inv s₀ t ∧
      bytesAt t.mem (outP s₀) (outL s₀) =
        Spec.Argon2.hPrime (outL s₀) (Spec.Argon2.serialize (blockAt s.mem (matrixCell (memP s₀) 0))) := by
  have b1 := blocks_pos hp
  have tg := hp.tag_ge
  have tl := hp.tag_lt
  have b1k : 1024 ≤ blocksN s₀ * 1024 := Nat.le_mul_of_pos_left _ b1
  unfold Impl.Argon2.RISCV64.Derive.finalOutput Impl.Argon2.RISCV64.HPrime.mov
  refine WP.seq (wp_lda hp h (i := 13) (by decide) fun s₁ u₁ => ?_)
  have i₁ := h.upd u₁
  refine wp_li (by decide) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂
  refine wp_lda hp i₂ (i := 16) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃
  refine wp_lda hp i₃ (i := 17) (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄
  refine wp_addi (by decide) fun s₅ u₅ => WP.block_nil ?_
  have i₅ := i₄.upd u₅
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have si : s₅.gpr .a0 = memP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ax : (s₅.gpr .a1).toNat = 1024 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl
  have di : s₅.gpr .a2 = outP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have cx : (s₅.gpr .a3).toNat = outL s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr]
  have r7 : s₅.gpr .a4 = scrP s₀ := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.s4]; simp
  refine hcall_ok hp i₅ r7
    ⟨memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ blocksN s₀ * 1024; omega_arith⟩
    ⟨outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + outL s₀ ≤ outL s₀; omega_arith⟩
    (by rw [ax]; decide) (by rw [cx]; exact ⟨by omega_arith, tl⟩) fun t it _ _ post => ⟨it, ?_⟩
  rw [← di, ← cx, post, cx, ax, si, m₅, show matrixCell (memP s₀) 0 = memP s₀ by simp [matrixCell],
    Proof.Argon2.serialize_blockAt]
end

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: the derivation is correct

`body_ok`: the body computes the parameters and H₀, initializes and fills
the memory, and writes the tag (`Spec.Argon2.derive`) to `out`; `correct`:
the whole function, in its frame, keeps the ABI's registers too.
-/

@[expose] public section

/-!
# Argon2 on RISC-V: the derivation's frame

`restore_ok`: the body's last instructions give the return address and the
caller's registers back, from the frame; `frames_ok`: the frame's push and
pop around a body that ends so give the caller's stack pointer back.
-/

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.Impl.Argon2.RISCV64.Derive (savedSlots argSlots restoreSlots)

/-- What the body ends with, for the frame's pop to restore the caller's
state. -/
structure BodyDone (s₀ t : State) : Prop where
  sp : t.sp = E s₀
  wr : t.wr = (entry s₀).wr
  regs : ∀ r ∈ preserved, t.gpr r = s₀.gpr r
  ra : t.gpr .ra = s₀.gpr .ra

theorem restore_ok {s₀ : State} (hp : DPre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block Impl.Argon2.RISCV64.Derive.restore) s fun t =>
      BodyDone s₀ t ∧ t.mem = s.mem := by
  have sub : ∀ p ∈ restoreSlots, p ∈ savedSlots ++ argSlots := by decide
  have bounds : ∀ p ∈ restoreSlots, p.2 + 8 ≤ 120 := by decide
  rw [show Impl.Argon2.RISCV64.Derive.restore = Spill.restoreCode .s3 restoreSlots from rfl]
  refine WP.mono (Spill.restore_wp (b := .s3) (B := E s₀) (g := s₀.gpr) (by have := E_al hp; omega_using [this]) h.s3
    (by decide) (by decide) (fun p hp' => loc_in' h (by have := bounds p hp'; omega_using [this]))
    (fun p hp' => h.saved hp (sub p hp'))) fun t ut => ⟨⟨?_, ?_, fun r hr => ?_, ?_⟩, ut.mem⟩
  · rw [ut.sp, h.sp]
  · rw [ut.wr, h.wr]
  · refine ut.gpr_of ?_
    by_cases hm : r ∈ restoreSlots.map Prod.fst
    · exact .inl hm
    · refine .inr ?_
      have hu : r ∈ untouched := by revert hm; revert hr; revert r; decide
      exact h.keep r hu
  · exact ut.gpr (.ra, Impl.Argon2.RISCV64.Derive.raOff) (by decide)

theorem frames_ok {s₀ : State} (hp : DPre s₀) {Q : Mem → Prop}
    (hQ : ∀ m m', Frame [below s₀.sp 320] m m' → Q m → Q m')
    (hb : WP isa Impl.Argon2.RISCV64.Derive.body (entry s₀) fun t => BodyDone s₀ t ∧ Q t.mem) :
    WP isa Impl.Argon2.RISCV64.Derive.derive s₀ fun u => abiPreserved s₀ u ∧ Q u.mem := by
  refine WP.alloc (by decide) hp.sp_lo (hb.mono fun t ⟨d, q⟩ m _ fl => ?_)
  refine ⟨⟨d.regs, ?_, d.ra⟩, hQ _ _ fl q⟩
  show t.sp + BitVec.ofNat 64 320 = _
  rw [d.sp, BitVec.sub_add_cancel]

end VG.Proof.Argon2.RISCV64.Derive

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Spec.Blake2 (bytesAt)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem body_ok : WP isa Impl.Argon2.RISCV64.Derive.body (entry s₀) fun t => BodyDone s₀ t ∧
    bytesAt t.mem (outP s₀) (outL s₀) =
      Spec.Argon2.derive (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀) := by
  unfold Impl.Argon2.RISCV64.Derive.body
  refine WP.seq ?_
  rw [← List.append_nil Impl.Argon2.RISCV64.Derive.parameters, ← List.append_assoc]
  refine setup_ok hp fun s₁ i₁ _ => parameters_ok hp i₁ fun s₂ i₂ p₂ => WP.block_nil ?_
  refine WP.seq ((code_ok hp i₂ p₂).mono fun s₃ ⟨i₃, p₃, b₃⟩ => ?_)
  refine WP.seq ((memoryInit_ok hp i₃ p₃ b₃).mono fun s₄ ⟨i₄, p₄, m₄⟩ => ?_)
  refine WP.seq ((passes_ok hp (st := Spec.Argon2.initMemory (prm s₀)
    (Spec.Argon2.initialHash (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀))) ⟨i₄, p₄, m₄⟩).mono
    fun s₅ f₅ => ?_)
  rw [show itersN s₀ = (prm s₀).passes from rfl, Proof.Argon2.iterations_fill] at f₅
  refine WP.seq ((reduce_ok hp f₅.inv f₅.pr f₅.mem).mono fun s₆ ⟨i₆, _, b₆⟩ => ?_)
  refine WP.seq ((finalOutput_ok hp i₆).mono fun s₇ ⟨i₇, o₇⟩ => ?_)
  refine (restore_ok hp i₇).mono fun t ⟨d, m⟩ => ⟨d, ?_⟩
  rw [m, o₇, b₆, Spec.Argon2.derive, Proof.Argon2.finish_reduction]
  rfl

theorem correct :
    WP isa Impl.Argon2.RISCV64.Derive.derive s₀ fun t => abiPreserved s₀ t ∧ deriveRV.post s₀ t :=
  frames_ok hp (Q := fun m => bytesAt m (outP s₀) (outL s₀) =
    Spec.Argon2.derive (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀))
    -- The `free` loses the frame's bytes, which lie apart from the output.
    (fun _ _ f q => Eq.trans (List.map_congr_left fun i hi =>
      lost_byte f (R := outR s₀) (hp.stk_all _ (by simp)).symm (List.mem_range.mp hi)) q)
    (body_ok hp)

end

end VG.Proof.Argon2.RISCV64.Derive
