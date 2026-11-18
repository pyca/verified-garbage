module

public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillDep
public import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCache
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Initial
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.MemoryInit
import VerifiedGarbage.Proof.Argon2.RISCV64.Compress
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillCall
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.Dimensions

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
