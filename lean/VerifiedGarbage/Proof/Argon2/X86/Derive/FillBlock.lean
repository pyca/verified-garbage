module

public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Argon2.FillStep
public import VerifiedGarbage.Proof.Argon2.X86.Derive.FillDep
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCache
import VerifiedGarbage.Proof.Argon2.X86.Derive.MemoryInit
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Proof.Argon2.Dimensions

/-! ### `Argon2.X86.Derive.FillPtr`, which this module and modules that import it used -/

section

@[expose] public section

section

section

/-!
# Argon2 on x86 (32-bit): the reference block's lane, start and base

`RS`: the filling state with J₁ and J₂ in the locals. `refLane_ok`: the
reference lane (RFC 9106 §3.4.2); `refStart_ok`: where the window of
eligible blocks starts; `countBase_ok`: the blocks before the current
segment that a reference may use.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

/-- The filling state, with J₁ and J₂ in the locals. -/
structure RS (s₀ : State) (pass slice lane index ctr : Nat) (st : FillState) (J1 J2 : BitVec 32) (s : State) :
    Prop where
  fs : FS s₀ pass slice lane index ctr st s
  j1 : lw s₀ s j1Off = J1
  j2 : lw s₀ s j2Off = J2

theorem RS.of_keep {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (k : Divide.Keep s t) : RS s₀ pass slice lane index ctr st J1 J2 t :=
  ⟨h.fs.of_keep k, by rw [lw_mem k.mem]; exact h.j1, by rw [lw_mem k.mem]; exact h.j2⟩

/-- The reference lane: J₂ mod the lane count, but the current lane in the first slice of the first pass. -/
def refLaneV (lanes pass slice lane j2 : Nat) : Nat := if pass = 0 ∧ slice = 0 then lane else j2 % lanes

/-- Where the window starts. -/
def startV (segLen laneLen pass slice : Nat) : Nat :=
  if pass = 0 then 0 else (slice + 1) * segLen % laneLen

/-- The blocks before the current segment that a reference may use. -/
def baseV (segLen laneLen pass slice : Nat) : Nat := if pass = 0 then slice * segLen else laneLen - segLen

theorem or_zero {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a ||| BitVec.ofNat 32 b == 0) = decide (a = 0 ∧ b = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_or, Wp.toNat_ofNat_lt ha, Wp.toNat_ofNat_lt hb] at this
    simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem RS.store {s t : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (it : Inv s₀ t) {d : Nat} (hd : d + 4 ≤ 144) (ha : d % 4 = 0)
    (hd' : d ∉ fsOffs) (h1 : d ≠ j1Off) (h2 : d ≠ j2Off) {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (addr (E s₀) d) v) : RS s₀ pass slice lane index ctr st J1 J2 t := by
  refine ⟨h.fs.store hp it hd ha hd' hm, ?_, ?_⟩
  · show t.mem.readW _ 32 = _
    rw [hm, lw_store hp (by omega_arith) (by decide) (by simp [j1Off] at h1 ⊢; omega_arith)]; exact h.j1
  · show t.mem.readW _ 32 = _
    rw [hm, lw_store hp (by omega_arith) (by decide) (by simp [j2Off] at h2 ⊢; omega_arith)]; exact h.j2

/-- The block of `refLane`: J₂ mod lanes, to the locals, and ZF in the first
slice of the first pass. -/
theorem refLaneBlk_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block (.mov .ecx (Impl.Argon2.X86.Derive.fr j2Off) :: Impl.Argon2.X86.Divide.code (argOff 7) ++
      [Impl.Argon2.X86.Derive.st refLaneOff .eax, .mov .eax (Impl.Argon2.X86.Derive.fr passOff),
        .alu .or .eax (Impl.Argon2.X86.Derive.fr sliceOff)])) s fun t =>
      RS s₀ pass slice lane index ctr st J1 J2 t ∧ t.zf = some (decide (pass = 0 ∧ slice = 0)) ∧
      lw s₀ t refLaneOff = BitVec.ofNat 32 (J2.toNat % lanesN s₀) := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  have e7 : lanesN s₀ = (arg s₀ 7).toNat := rfl
  simp only [List.cons_append]
  refine wp_ldloc hp h.fs.inv (d := j2Off) (by decide) fun s₁ u₁ => ?_
  obtain h₁ := h.of_keep (Divide.Keep.of_upd u₁ (by simp))
  refine Divide.code_ok (D := arg s₀ 7) (by omega_arith) (by omega_arith) h₁.fs.inv.ebp (h₁.fs.inv.arg_in hp (by decide))
    (h₁.fs.inv.arg hp (by decide)) fun s₂ _ r₂ k₂ => ?_
  obtain h₂ := h₁.of_keep k₂
  refine wp_stloc hp h₂.fs.inv (d := refLaneOff) (by decide) fun s₃ i₃ v₃ _ g₃ m₃ => ?_
  obtain h₃ := h₂.store hp i₃ (d := refLaneOff) (by decide) (by decide) (by decide) (by decide) (by decide) m₃
  refine wp_ldloc hp h₃.fs.inv (d := passOff) (by decide) fun s₄ u₄ => ?_
  obtain h₄ := h₃.of_keep (Divide.Keep.of_upd u₄ (by simp))
  refine wp_orm h₄.fs.inv.ebp (loc_in' hp h₄.fs.inv (d := sliceOff) (by decide)) fun s₅ u₅ z₅ => WP.block_nil ?_
  obtain h₅ := h₄.of_keep (Divide.Keep.of_upd u₅ (by simp))
  obtain r : s₂.gpr .eax = BitVec.ofNat 32 (J2.toNat % lanesN s₀) := BitVec.eq_of_toNat_eq (by
    rw [r₂, u₁.gpr, h.j2, Wp.toNat_ofNat_lt (by have := J2.isLt; have := Nat.mod_le J2.toNat (lanesN s₀); omega_arith)])
  refine ⟨h₅, ?_, by rw [lw_mem u₅.mem, lw_mem u₄.mem, v₃, r]⟩
  rw [z₅, u₄.gpr, show s₄.mem.readW (addr (E s₀) sliceOff) 32 = lw s₀ s₄ sliceOff from rfl, h₄.fs.pos.slice,
    h₃.fs.pos.pass, or_zero hpass (by omega_arith)]

/-- `refLane`: the reference lane, to the locals. -/
theorem refLane_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.X86.Derive.refLane s fun t => RS s₀ pass slice lane index ctr st J1 J2 t ∧
      lw s₀ t refLaneOff = BitVec.ofNat 32 (refLaneV (lanesN s₀) pass slice lane J2.toNat) := by
  unfold Impl.Argon2.X86.Derive.refLane
  refine WP.seq ((refLaneBlk_ok hp h hpass hs).mono fun s₅ ⟨h₅, z₅, e₃⟩ => ?_)
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) z₅ (fun hb => ?_) fun hb => ?_
  · have hb' : pass = 0 ∧ slice = 0 := of_decide_eq_true hb
    refine wp_ldloc hp h₅.fs.inv (d := laneOff) (by decide) fun s₆ u₆ => ?_
    obtain h₆ := h₅.of_keep (Divide.Keep.of_upd u₆ (by simp))
    refine wp_stloc hp h₆.fs.inv (d := refLaneOff) (by decide) fun t it vt _ _ mt => WP.block_nil ⟨?_, ?_⟩
    · exact h₆.store hp it (d := refLaneOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt
    · rw [vt, u₆.gpr, h₅.fs.pos.lane, refLaneV, ite_eq_left hb']
  · have hb' : ¬(pass = 0 ∧ slice = 0) := of_decide_eq_false hb
    refine WP.block_nil ⟨h₅, ?_⟩
    rw [e₃, refLaneV, ite_eq_right hb']

end


section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `refStart`: where the window starts, to the locals. -/
theorem refStart_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.X86.Derive.refStart s fun t => RS s₀ pass slice lane index ctr st J1 J2 t ∧
      lw s₀ t refLaneOff = lw s₀ s refLaneOff ∧
      lw s₀ t startOff = BitVec.ofNat 32 (startV (prm s₀).segmentLen (prm s₀).laneLen pass slice) := by
  obtain sl := segLen_lt hp
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  unfold Impl.Argon2.X86.Derive.refStart
  refine WP.seq (wp_movi fun s₁ u₁ => ?_)
  obtain h₁ := h.of_keep (Divide.Keep.of_upd u₁ (by simp))
  refine wp_stloc hp h₁.fs.inv (d := startOff) (by decide) fun s₂ i₂ v₂ o₂ _ m₂ => ?_
  obtain h₂ := h₁.store hp i₂ (d := startOff) (by decide) (by decide) (by decide) (by decide) (by decide) m₂
  refine wp_ldloc hp h₂.fs.inv (d := passOff) (by decide) fun s₃ u₃ => wp_cmpi fun s₄ f₄ _ z₄ => WP.block_nil ?_
  obtain h₄ := (h₂.of_keep (Divide.Keep.of_upd u₃ (by simp))).of_keep (Divide.Keep.of_fupd f₄)
  obtain m₄ : s₄.mem = s₂.mem := by rw [f₄.mem, u₃.mem]
  obtain r₂ : lw s₀ s₂ refLaneOff = lw s₀ s refLaneOff := by
    rw [o₂ _ (by decide) (by decide), lw_mem u₁.mem]
  obtain z : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
  refine WP.ite (decide (pass = 0)) (by
    show s₄.zf = _
    rw [z₄, u₃.gpr, h₂.fs.pos.pass, z, Wp.ofNat_beq_zero hpass]) (fun hb => ?_) fun hb => ?_
  · refine WP.block_nil ⟨h₄, by rw [lw_mem m₄, r₂], ?_⟩
    rw [lw_mem m₄, v₂, u₁.gpr, startV, ite_eq_left (of_decide_eq_true hb)]; rfl
  · have hp0 : pass ≠ 0 := of_decide_eq_false hb
    refine WP.seq (wp_ldloc hp h₄.fs.inv (d := sliceOff) (by decide) fun s₅ u₅ => wp_cmpi fun s₆ f₆ _ z₆ =>
      WP.block_nil ?_)
    obtain h₆ := (h₄.of_keep (Divide.Keep.of_upd u₅ (by simp))).of_keep (Divide.Keep.of_fupd f₆)
    obtain m₆ : s₆.mem = s₂.mem := by rw [f₆.mem, u₅.mem, m₄]
    refine WP.ite (decide (slice = 3)) (by
      show s₆.zf = _
      rw [z₆, u₅.gpr, h₄.fs.pos.slice, show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl,
        Wp.sub_beq (by omega_arith) (by decide)]) (fun hb' => ?_) fun hb' => ?_
    · refine WP.block_nil ⟨h₆, by rw [lw_mem m₆, r₂], ?_⟩
      rw [lw_mem m₆, v₂, u₁.gpr, startV, ite_eq_right hp0, of_decide_eq_true hb', ll, Nat.mod_self]; rfl
    · have hs3 : slice ≠ 3 := of_decide_eq_false hb'
      refine wp_ldloc hp h₆.fs.inv (d := sliceOff) (by decide) fun s₇ u₇ => wp_addi fun s₈ u₈ =>
        wp_ldloc hp ((h₆.of_keep (Divide.Keep.of_upd u₇ (by simp))).of_keep (Divide.Keep.of_upd u₈ (by simp))).fs.inv
          (d := segLenOff) (by decide) fun s₉ u₉ => wp_mul fun s₁₀ a₁₀ _ k₁₀ _ => ?_
      obtain h₁₀ := ((((h₆.of_keep (Divide.Keep.of_upd u₇ (by simp))).of_keep (Divide.Keep.of_upd u₈ (by simp))).of_keep
        (Divide.Keep.of_upd u₉ (by simp))).of_keep k₁₀)
      obtain m₁₀ : s₁₀.mem = s₂.mem := by rw [k₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆]
      refine wp_stloc hp h₁₀.fs.inv (d := startOff) (by decide) fun t it vt ot _ mt => WP.block_nil ⟨?_, ?_, ?_⟩
      · exact h₁₀.store hp it (d := startOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt
      · rw [ot _ (by decide) (by decide), lw_mem m₁₀, r₂]
      · have : (slice + 1) * (prm s₀).segmentLen < (prm s₀).laneLen := by
          rw [ll]; exact Nat.mul_lt_mul_of_pos_right (by omega_arith) (by omega_arith)
        rw [vt, a₁₀, u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₉.gpr, lw_mem u₈.mem, lw_mem u₇.mem,
          h₆.fs.pr.segLen, lw_mem (show s₆.mem = s₂.mem from m₆), h₂.fs.pos.slice,
          show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat, Wp.toNat_ofNat_lt (by omega_arith),
          Wp.toNat_ofNat_lt (by omega_arith), startV, ite_eq_right hp0, Nat.mod_eq_of_lt this]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `countBase`: `eax :=` the blocks before the current segment that a reference may use. -/
theorem countBase_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.X86.Derive.countBase s fun t => Divide.Keep s t ∧
      t.gpr .eax = BitVec.ofNat 32 (baseV (prm s₀).segmentLen (prm s₀).laneLen pass slice) := by
  obtain sl := segLen_lt hp
  have ll := hp.laneLen_eq
  unfold Impl.Argon2.X86.Derive.countBase
  refine WP.seq (wp_ldloc hp h.fs.inv (d := passOff) (by decide) fun s₁ u₁ => wp_cmpi fun s₂ f₂ _ z₂ =>
    WP.block_nil ?_)
  obtain k₂ := (Divide.Keep.of_upd u₁ (by simp)).trans (Divide.Keep.of_fupd f₂)
  obtain h₂ := h.of_keep k₂
  obtain z : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
  refine WP.ite (decide (pass = 0)) (by
    show s₂.zf = _
    rw [z₂, u₁.gpr, h.fs.pos.pass, z, Wp.ofNat_beq_zero hpass]) (fun hb => ?_) fun hb => ?_
  · refine wp_ldloc hp h₂.fs.inv (d := sliceOff) (by decide) fun s₃ u₃ =>
      wp_ldloc hp (h₂.of_keep (Divide.Keep.of_upd u₃ (by simp))).fs.inv (d := segLenOff) (by decide) fun s₄ u₄ =>
      wp_mul fun t a _ k _ => WP.block_nil ⟨k₂.trans ((Divide.Keep.of_upd u₃ (by simp)).trans
        ((Divide.Keep.of_upd u₄ (by simp)).trans k)), ?_⟩
    rw [a, u₄.other _ (by decide), u₃.gpr, u₄.gpr, lw_mem u₃.mem, h₂.fs.pos.slice, h₂.fs.pr.segLen,
      Wp.toNat_ofNat_lt (by omega_arith), Wp.toNat_ofNat_lt (by omega_arith), baseV, ite_eq_left (of_decide_eq_true hb)]
  · refine wp_ldloc hp h₂.fs.inv (d := laneLenOff) (by decide) fun s₃ u₃ =>
      Divide.wp_subm (h₂.of_keep (Divide.Keep.of_upd u₃ (by simp))).fs.inv.ebp
        (loc_in' hp (h₂.of_keep (Divide.Keep.of_upd u₃ (by simp))).fs.inv (d := segLenOff) (by decide))
        fun t u _ => WP.block_nil ⟨k₂.trans ((Divide.Keep.of_upd u₃ (by simp)).trans
          (Divide.Keep.of_upd u (by simp))), ?_⟩
    rw [u.gpr, u₃.gpr, show s₃.mem.readW (addr (E s₀) segLenOff) 32 = lw s₀ s₃ segLenOff from rfl,
      lw_mem u₃.mem, h₂.fs.pr.laneLen, h₂.fs.pr.segLen, Wp.sub_ofNat (by omega_arith), baseV,
      ite_eq_right (of_decide_eq_false hb)]

end
end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the reference window's size

`countSelect_ok`: the number of eligible reference blocks, chosen between
the current lane's and another lane's by a mask (`sel`), to the locals.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

theorem sel (a c : BitVec 32) (b : Bool) :
    a ^^^ ((c ^^^ a) &&& (if b then BitVec.allOnes 32 else 0)) = if b then c else a := by
  cases b
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm c a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem add_allOnes {x : Nat} (h : 1 ≤ x) (h' : x < 2 ^ 32) :
    BitVec.ofNat 32 x + BitVec.allOnes 32 = BitVec.ofNat 32 (x - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, Wp.toNat_ofNat_lt h', Wp.toNat_ofNat_lt (by omega_arith), BitVec.toNat_allOnes]
  omega_arith

theorem xor_lt_one {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    decide ((BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b).toNat < (1 : BitVec 32).toNat) = decide (a = b) := by
  rw [show (1 : BitVec 32).toNat = 1 from rfl, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · intro h
    obtain e : BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b = 0#32 :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega_arith)
    have := congrArg (· ^^^ BitVec.ofNat 32 b) e
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor] at this
    have := congrArg BitVec.toNat this
    rwa [Wp.toNat_ofNat_lt ha, Wp.toNat_ofNat_lt hb] at this
  · rintro rfl; simp

theorem lt_one {n : Nat} (h : n < 2 ^ 32) :
    decide ((BitVec.ofNat 32 n).toNat < (1 : BitVec 32).toNat) = decide (n = 0) := by
  rw [Wp.toNat_ofNat_lt h]
  simp only [show (1 : BitVec 32).toNat = 1 from rfl, Nat.lt_one_iff]

/-- The window's size. -/
def countV (base index : Nat) (same : Bool) : Nat :=
  if same then base + index - 1 else base - (if index = 0 then 1 else 0)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `countSelect`: the window's size, to the locals and `eax`. -/
theorem countSelect_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {base rl : Nat} (hb : base < 2 ^ 31)
    (hi : index < (prm s₀).segmentLen) (hl : lane < lanesN s₀) (hrl : rl < lanesN s₀)
    (ha : s.gpr .eax = BitVec.ofNat 32 base) (hr : lw s₀ s refLaneOff = BitVec.ofNat 32 rl)
    (hsame : rl = lane → 1 ≤ base + index) (hother : rl ≠ lane → index = 0 → 1 ≤ base)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr st J1 J2 t →
      t.gpr .eax = BitVec.ofNat 32 (countV base index (rl == lane)) →
      lw s₀ t countOff = BitVec.ofNat 32 (countV base index (rl == lane)) →
      (∀ e, e + 4 ≤ 236 → (countOff + 4 ≤ e ∨ e + 4 ≤ countOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.countSelect ++ is)) s Q := by
  obtain sl := segLen_lt hp
  have lt := hp.lanes_lt
  unfold Impl.Argon2.X86.Derive.countSelect
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => ?_
  obtain h₁ := h.of_keep (Divide.Keep.of_upd u₁ (by simp))
  refine wp_addm h₁.fs.inv.ebp (loc_in' hp h₁.fs.inv (d := indexOff) (by decide)) fun s₂ u₂ =>
    wp_subi fun s₃ u₃ _ _ => ?_
  obtain K₃ : Divide.Keep s s₃ :=
    ((Divide.Keep.of_upd u₁ (by simp)).trans (Divide.Keep.of_upd u₂ (by simp))).trans (Divide.Keep.of_upd u₃ (by simp))
  refine wp_ldloc hp (h.of_keep K₃).fs.inv (d := indexOff) (by decide) fun s₄ u₄ => wp_subi fun s₅ u₅ c₅ _ =>
    wp_sbb_self c₅ fun s₆ u₆ => wp_add fun s₇ u₇ _ => ?_
  obtain K₇ : Divide.Keep s s₇ := (((K₃.trans (Divide.Keep.of_upd u₄ (by simp))).trans
    (Divide.Keep.of_upd u₅ (by simp))).trans (Divide.Keep.of_upd u₆ (by simp))).trans (Divide.Keep.of_upd u₇ (by simp))
  refine wp_ldloc hp (h.of_keep K₇).fs.inv (d := refLaneOff) (by decide) fun s₈ u₈ => ?_
  obtain K₈ := K₇.trans (Divide.Keep.of_upd u₈ (by simp))
  refine wp_xorm (h.of_keep K₈).fs.inv.ebp (loc_in' hp (h.of_keep K₈).fs.inv (d := laneOff) (by decide))
    fun s₉ u₉ => wp_subi fun s₁₀ u₁₀ c₁₀ _ => wp_sbb_self c₁₀ fun s₁₁ u₁₁ => wp_xor fun s₁₂ u₁₂ =>
    wp_and fun s₁₃ u₁₃ => wp_xor fun s₁₄ u₁₄ => ?_
  obtain K₁₄ : Divide.Keep s s₁₄ := ((((((K₈.trans (Divide.Keep.of_upd u₉ (by simp))).trans
    (Divide.Keep.of_upd u₁₀ (by simp))).trans (Divide.Keep.of_upd u₁₁ (by simp))).trans
    (Divide.Keep.of_upd u₁₂ (by simp))).trans (Divide.Keep.of_upd u₁₃ (by simp))).trans
    (Divide.Keep.of_upd u₁₄ (by simp)))
  obtain h₁₄ := h.of_keep K₁₄
  -- The value.
  have hix : lw s₀ s indexOff = BitVec.ofNat 32 index := h.fs.pos.index
  have hln : lw s₀ s laneOff = BitVec.ofNat 32 lane := h.fs.pos.lane
  obtain m : ∀ {t : State}, Divide.Keep s t → ∀ d, lw s₀ t d = lw s₀ s d := fun k d => lw_mem k.mem d
  obtain e₃ : s₃.gpr .ecx = BitVec.ofNat 32 base + BitVec.ofNat 32 index - 1 := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, ha, show s₁.mem.readW (addr (E s₀) indexOff) 32 = lw s₀ s₁ indexOff from rfl,
      m (Divide.Keep.of_upd u₁ (by simp)), hix]
  obtain e₇ : s₇.gpr .eax = BitVec.ofNat 32 base + (if decide (index = 0) then BitVec.allOnes 32 else 0) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .eax (by decide), u₅.other .eax (by decide), u₄.other .eax (by decide),
      u₃.other .eax (by decide), u₂.other .eax (by decide), u₁.other .eax (by decide), ha, u₄.gpr, m K₃, hix,
      lt_one (by omega_arith)]
  obtain e₁₁ : s₁₁.gpr .edx = if decide (rl = lane) then BitVec.allOnes 32 else 0 := by
    rw [u₁₁.gpr, u₉.gpr, u₈.gpr, show s₈.mem.readW (addr (E s₀) laneOff) 32 = lw s₀ s₈ laneOff from rfl, m K₇, m K₈,
      hr, hln, xor_lt_one (by omega_arith) (by omega_arith)]
  obtain e₁₄ : s₁₄.gpr .eax = if decide (rl = lane) then s₃.gpr .ecx else s₇.gpr .eax := by
    rw [u₁₄.gpr, u₁₃.gpr, u₁₃.other .eax (by decide), u₁₂.gpr, u₁₂.other .eax (by decide), u₁₂.other .edx (by decide),
      e₁₁, u₁₁.other .eax (by decide), u₁₁.other .ecx (by decide), u₁₀.other .eax (by decide),
      u₁₀.other .ecx (by decide), u₉.other .eax (by decide), u₉.other .ecx (by decide), u₈.other .eax (by decide),
      u₈.other .ecx (by decide), u₇.other .ecx (by decide), u₆.other .ecx (by decide), u₅.other .ecx (by decide),
      u₄.other .ecx (by decide), sel]
  obtain val : s₁₄.gpr .eax = BitVec.ofNat 32 (countV base index (rl == lane)) := by
    rw [e₁₄, countV]
    by_cases hs : rl = lane
    · simp only [decide_eq_true hs, show (rl == lane) = true from beq_iff_eq.mpr hs, ↓reduceIte]
      rw [e₃, BitVec.ofNat_add_ofNat, Wp.ofNat_pred (hsame hs)]
    · simp only [decide_eq_false hs, show (rl == lane) = false from beq_eq_false_iff_ne.mpr hs, ↓reduceIte,
        Bool.false_eq_true]
      rw [e₇]
      by_cases hi0 : index = 0
      · rw [decide_eq_true hi0, ite_eq_left (rfl : true = true), ite_eq_left hi0,
          add_allOnes (hother hs hi0) (by omega_arith)]
      · rw [decide_eq_false hi0, ite_eq_right (by decide : ¬(false = true)), ite_eq_right hi0, Nat.sub_zero]
        simp
  refine wp_stloc hp h₁₄.fs.inv (d := countOff) (by decide) fun t it vt ot gt mt => k t ?_ (by rw [gt, val])
    (by rw [vt, val]) (fun e he hd => by rw [ot e he hd, m K₁₄]) (fun r a b c => by rw [gt, K₁₄.other r a b c])
  exact h₁₄.store hp it (d := countOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt

end

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the reference block's column and the block pointers

`relative_ok`: the position in the window that J₁ selects (RFC 9106
§3.4.2); `wrap_ok`: its column, from the window's start, modulo the lane
length; `refPointer_ok` and `curPointer_ok`: the reference and current
blocks' addresses, to the locals.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block zeroBlock FillState)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

/-- The position in the window that `j1` selects. -/
def relV (cnt j1 : Nat) : Nat := cnt - 1 - cnt * (j1 * j1 / 2 ^ 32) / 2 ^ 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `relative`: `eax :=` the position in the window. -/
theorem relative_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {cnt : Nat} (hc : 1 ≤ cnt) (hc' : cnt < 2 ^ 32)
    (hcnt : lw s₀ s countOff = BitVec.ofNat 32 cnt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .eax = BitVec.ofNat 32 (relV cnt J1.toNat) → Divide.Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.relative ++ is)) s Q := by
  have jb := J1.isLt
  obtain x32 := Proof.Argon2.reference_scaled_bound J1.toNat jb
  obtain lt := Proof.Argon2.reference_scale_lt_count cnt J1.toNat (by omega_arith) jb
  unfold Impl.Argon2.X86.Derive.relative
  simp only [List.cons_append, List.nil_append]
  refine wp_ldloc hp h.fs.inv (d := j1Off) (by decide) fun s₁ u₁ => wp_mul fun s₂ _ d₂ k₂ _ => wp_mov fun s₃ u₃ => ?_
  obtain K₃ := ((Divide.Keep.of_upd u₁ (by simp)).trans k₂).trans (Divide.Keep.of_upd u₃ (by simp))
  refine wp_ldloc hp (h.of_keep K₃).fs.inv (d := countOff) (by decide) fun s₄ u₄ => wp_mul fun s₅ _ d₅ k₅ o₅ =>
    wp_mov fun s₆ u₆ => wp_subi fun s₇ u₇ _ _ => wp_sub fun t u _ => k t ?_ ?_
  · have x₃ : (s₃.gpr .eax).toNat = J1.toNat * J1.toNat / 2 ^ 32 := by
      rw [u₃.gpr, d₂, u₁.gpr, h.j1, Wp.toNat_ofNat_lt x32]
    obtain c₄ : (s₄.gpr .ecx).toNat = cnt := by
      rw [u₄.gpr, lw_mem K₃.mem, hcnt, Wp.toNat_ofNat_lt hc']
    rw [u.gpr, u₇.gpr, u₇.other .edx (by decide), u₆.gpr, u₆.other .edx (by decide), o₅ .ecx (by decide) (by decide),
      d₅, u₄.other .eax (by decide), x₃, c₄, u₄.gpr, lw_mem K₃.mem, hcnt, Wp.ofNat_pred hc,
      Wp.sub_ofNat (by rw [Nat.mul_comm]; omega_arith), relV, Nat.mul_comm (J1.toNat * J1.toNat / 2 ^ 32) cnt]
  · exact (((((K₃.trans (Divide.Keep.of_upd u₄ (by simp))).trans k₅).trans (Divide.Keep.of_upd u₆ (by simp))).trans
      (Divide.Keep.of_upd u₇ (by simp))).trans (Divide.Keep.of_upd u (by simp)))


/-- `wrap`: `eax := (start + eax) mod laneLen`. -/
theorem wrap_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {rel stt : Nat} (hr : rel < (prm s₀).laneLen)
    (hs : stt < (prm s₀).laneLen) (ha : s.gpr .eax = BitVec.ofNat 32 rel)
    (hst : lw s₀ s startOff = BitVec.ofNat 32 stt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .eax = BitVec.ofNat 32 ((stt + rel) % (prm s₀).laneLen) → Divide.Keep s t →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.wrap ++ is)) s Q := by
  obtain L22 : (prm s₀).laneLen < 2 ^ 22 := by
    have := Nat.le_mul_of_pos_left (prm s₀).laneLen (show 0 < lanesN s₀ from hp.lanes_pos)
    have e := hp.blocks_eq
    have := hp.blocks_lt
    omega_arith
  unfold Impl.Argon2.X86.Derive.wrap
  simp only [List.cons_append, List.nil_append]
  refine wp_addm h.fs.inv.ebp (loc_in' hp h.fs.inv (d := startOff) (by decide)) fun s₁ u₁ => ?_
  obtain K₁ := Divide.Keep.of_upd u₁ (by simp)
  refine Divide.wp_subm (h.of_keep K₁).fs.inv.ebp (loc_in' hp (h.of_keep K₁).fs.inv (d := laneLenOff) (by decide))
    fun s₂ u₂ c₂ => wp_sbb_self c₂ fun s₃ u₃ => ?_
  obtain K₃ := (K₁.trans (Divide.Keep.of_upd u₂ (by simp))).trans (Divide.Keep.of_upd u₃ (by simp))
  refine Divide.wp_andm (h.of_keep K₃).fs.inv.ebp (loc_in' hp (h.of_keep K₃).fs.inv (d := laneLenOff) (by decide))
    fun s₄ u₄ => wp_add fun t u _ => k t ?_ ?_
  · have x₁ : s₁.gpr .eax = BitVec.ofNat 32 (stt + rel) := by
      rw [u₁.gpr, ha, show s.mem.readW (addr (E s₀) startOff) 32 = lw s₀ s startOff from rfl, hst,
        BitVec.ofNat_add_ofNat, Nat.add_comm]
    obtain L₁ : s₁.mem.readW (addr (E s₀) laneLenOff) 32 = BitVec.ofNat 32 (prm s₀).laneLen := by
      show lw s₀ s₁ laneLenOff = _
      rw [lw_mem K₁.mem]; exact h.fs.pr.laneLen
    obtain L₃ : s₃.mem.readW (addr (E s₀) laneLenOff) 32 = BitVec.ofNat 32 (prm s₀).laneLen := by
      show lw s₀ s₃ laneLenOff = _
      rw [lw_mem K₃.mem]; exact h.fs.pr.laneLen
    rw [u.gpr, u₄.other _ (by decide), u₄.gpr, L₃, u₃.gpr, u₃.other _ (by decide), u₂.gpr, x₁, L₁,
      Wp.toNat_ofNat_lt (by omega_arith), Wp.toNat_ofNat_lt (by omega_arith),
      Proof.Argon2.reference_wrap (stt + rel) (prm s₀).laneLen (by omega_arith)]
    by_cases c : stt + rel < (prm s₀).laneLen
    · simp only [c, decide_true, ite_true, BitVec.allOnes_and, BitVec.sub_add_cancel]
    · simp only [c, decide_false, ite_false, Bool.false_eq_true]
      rw [Wp.sub_ofNat (by omega_arith)]
      simp
  · exact (K₃.trans (Divide.Keep.of_upd u₄ (by simp))).trans (Divide.Keep.of_upd u (by simp))

/-- `refPointer`: the address of block `eax` of the reference lane, to the locals. -/
theorem refPointer_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) {col rl : Nat} (hc : col < (prm s₀).laneLen)
    (hrl : rl < lanesN s₀) (ha : s.gpr .eax = BitVec.ofNat 32 col)
    (hr : lw s₀ s refLaneOff = BitVec.ofNat 32 rl) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr st J1 J2 t →
      lw s₀ t tmpOff = memP s₀ + BitVec.ofNat 32 ((rl * (prm s₀).laneLen + col) * 1024) →
      (∀ e, e + 4 ≤ 236 → (tmpOff + 4 ≤ e ∨ e + 4 ≤ tmpOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.refPointer ++ is)) s Q := by
  unfold Impl.Argon2.X86.Derive.refPointer
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov fun s₁ u₁ => ?_
  obtain K₁ := Divide.Keep.of_upd u₁ (by simp)
  refine wp_ldloc hp (h.of_keep K₁).fs.inv (d := refLaneOff) (by decide) fun s₂ u₂ => ?_
  obtain K₂ := K₁.trans (Divide.Keep.of_upd u₂ (by simp))
  refine blockAddr_ok hp (h.of_keep K₂).fs.inv (h.of_keep K₂).fs.pr hrl hc
    (by rw [u₂.gpr, lw_mem K₁.mem, hr]) (by rw [u₂.other _ (by decide), u₁.gpr, ha]) fun s₃ a₃ _ k₃ => ?_
  obtain K₃ := K₂.trans k₃
  refine wp_stloc hp (h.of_keep K₃).fs.inv (d := tmpOff) (by decide) fun t it vt ot gt mt =>
    k t ?_ (by rw [vt, a₃]) (fun e he hd => by rw [ot e he hd, lw_mem K₃.mem]) (fun r a b c => by
      rw [gt, K₃.other r a b c])
  exact (h.of_keep K₃).store hp it (d := tmpOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt

/-- `curPointer`: the address of the current block, to the locals. -/
theorem curPointer_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, RS s₀ pass slice lane index ctr st J1 J2 t →
      lw s₀ t curOff = memP s₀ + BitVec.ofNat 32
        ((lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index)) * 1024) →
      (∀ e, e + 4 ≤ 236 → (curOff + 4 ≤ e ∨ e + 4 ≤ curOff) → lw s₀ t e = lw s₀ s e) →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.curPointer ++ is)) s Q := by
  obtain hc := Proof.Argon2.column_lt (prm s₀) hp.lanes_pos hs hi
  unfold Impl.Argon2.X86.Derive.curPointer
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine column_ok hp h.fs.inv h.fs.pr h.fs.pos hs hi fun s₁ _ c₁ k₁ => ?_
  refine wp_ldloc hp (h.of_keep k₁).fs.inv (d := laneOff) (by decide) fun s₂ u₂ => ?_
  obtain K₂ := k₁.trans (Divide.Keep.of_upd u₂ (by simp))
  refine blockAddr_ok hp (h.of_keep K₂).fs.inv (h.of_keep K₂).fs.pr hl hc
    (by rw [u₂.gpr, lw_mem k₁.mem]; exact h.fs.pos.lane) (by rw [u₂.other _ (by decide), c₁])
    fun s₃ a₃ _ k₃ => ?_
  obtain K₃ := K₂.trans k₃
  refine wp_stloc hp (h.of_keep K₃).fs.inv (d := curOff) (by decide) fun t it vt ot gt mt =>
    k t ?_ (by rw [vt, a₃]) (fun e he hd => by rw [ot e he hd, lw_mem K₃.mem]) (fun r a b c => by
      rw [gt, K₃.other r a b c])
  exact (h.of_keep K₃).store hp it (d := curOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt
end


theorem j2_eq (J1 J2 : BitVec 32) : ((J2 ++ J1 : BitVec 64) >>> 32).toNat = J2.toNat := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← Proof.Sha512.Word64.hi_toNat,
    Proof.Sha512.Word64.hi_append]

theorem j1_eq (J1 J2 : BitVec 32) : ((J2 ++ J1 : BitVec 64) &&& 0xffffffff).toNat = J1.toNat := by
  rw [BitVec.toNat_and, show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    ← Proof.Sha512.Word64.lo_toNat, Proof.Sha512.Word64.lo_append]

theorem count_eq (p : Spec.Argon2.Params) (pass slice index : Nat) (same : Bool) :
    Spec.Argon2.referenceCount p pass slice index same =
      countV (baseV p.segmentLen p.laneLen pass slice) index same := by
  unfold Spec.Argon2.referenceCount countV baseV
  by_cases h : pass = 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

theorem ref_eq (p : Spec.Argon2.Params) (pass lane slice index : Nat) (J1 J2 : BitVec 32) :
    Spec.Argon2.reference p pass lane slice index (J2 ++ J1) =
      (refLaneV p.lanes pass slice lane J2.toNat,
        (startV p.segmentLen p.laneLen pass slice +
          relV (countV (baseV p.segmentLen p.laneLen pass slice) index
            (refLaneV p.lanes pass slice lane J2.toNat == lane)) J1.toNat) % p.laneLen) := by
  unfold Spec.Argon2.reference
  simp only [j1_eq, j2_eq, count_eq]
  rfl

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `reference`: the reference and current blocks' addresses, to the locals. -/
theorem reference_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.X86.Derive.reference s fun t => RS s₀ pass slice lane index ctr st J1 J2 t ∧
      lw s₀ t tmpOff = memP s₀ + BitVec.ofNat 32
        (((Spec.Argon2.reference (prm s₀) pass lane slice index (J2 ++ J1)).1 * (prm s₀).laneLen +
          (Spec.Argon2.reference (prm s₀) pass lane slice index (J2 ++ J1)).2) * 1024) ∧
      lw s₀ t curOff = memP s₀ + BitVec.ofNat 32
        ((lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index)) * 1024) := by
  obtain L22 : (prm s₀).laneLen < 2 ^ 22 := by
    have := Nat.le_mul_of_pos_left (prm s₀).laneLen (show 0 < lanesN s₀ from hp.lanes_pos)
    have e := hp.blocks_eq
    have := hp.blocks_lt
    omega_arith
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  have hl1 := hp.lanes_pos
  rw [ref_eq]
  generalize hRL : refLaneV (prm s₀).lanes pass slice lane J2.toNat = RL
  have hRL' : refLaneV (lanesN s₀) pass slice lane J2.toNat = RL := hRL
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
  unfold Impl.Argon2.X86.Derive.reference
  refine WP.seq ((refLane_ok hp h hpass hs).mono fun t₁ ⟨h₁, r₁⟩ => ?_)
  rw [hRL'] at r₁
  refine WP.seq ((refStart_ok hp h₁ hpass hs).mono fun t₂ ⟨h₂, r₂, st₂⟩ => ?_)
  rw [hST] at st₂
  refine WP.seq ((countBase_ok hp h₂ hpass hs).mono fun t₃ ⟨k₃, a₃⟩ => ?_)
  rw [hB] at a₃
  obtain h₃ := h₂.of_keep k₃
  rw [← List.append_nil Impl.Argon2.X86.Derive.curPointer]
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
  refine relative_ok hp h₄ (cnt := countV B index (RL == lane)) cpos (by omega_arith) c₄ fun t₅ a₅ k₅ => ?_
  obtain h₅ := h₄.of_keep k₅
  obtain rel_lt : relV (countV B index (RL == lane)) J1.toNat < (prm s₀).laneLen := by
    unfold relV; omega_arith
  refine wrap_ok hp h₅ rel_lt st_lt a₅ (by
      rw [lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, st₂]) fun t₆ a₆ k₆ => ?_
  obtain h₆ := h₅.of_keep k₆
  refine refPointer_ok hp h₆ (Nat.mod_lt _ (by omega_arith)) rl_lt a₆ (by
      rw [lw_mem k₆.mem, lw_mem k₅.mem, o₄ _ (by decide) (by decide), lw_mem k₃.mem, r₂, r₁])
    fun t₇ h₇ p₇ o₇ _ => ?_
  refine curPointer_ok hp h₇ hl hs hi fun t h' c' o' _ => WP.block_nil ⟨h', ?_, c'⟩
  rw [o' _ (by decide) (by decide), p₇]

end
end VG.Proof.Argon2.X86.Derive

end

end

@[expose] public section

section

/-!
# Argon2 on x86 (32-bit): the new block

`fillCompress_ok`: G of the previous and reference blocks, to
`scratch + 4096`. `writeWords_ok`: its words to the current block, XORed
into the old ones after the first pass; `fillWrite_ok`: the current block
after the step, as `FillStep.update` has it.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.X86 (blk ofWords blk_of_words)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff writeWord writeBlock)

/-- Words of the memory matrix. -/
abbrev mw (s₀ : State) (m : Mem) (o : Nat) : BitVec 32 := m.readW (addr (memP s₀) o) 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem blocks22 : blocksN s₀ < 2 ^ 22 := by
  have hb := hp.blocks_lt
  omega_arith

theorem mem_addr' {o : Nat} (ho : o < blocksN s₀ * 1024) : addr (memP s₀) o = memB s₀ + BitVec.ofNat 64 o :=
  addr_eq (by have := hp.mem_fits; omega_arith)

/-- A word of the matrix after a store to another, or the same. -/
theorem mw_store (m : Mem) {a b : Nat} (ha : a + 4 ≤ blocksN s₀ * 1024) (hb : b + 4 ≤ blocksN s₀ * 1024)
    (h : a = b ∨ a + 4 ≤ b ∨ b + 4 ≤ a) (v : BitVec 32) :
    mw s₀ (m.writeW (addr (memP s₀) a) v) b = if a = b then v else mw s₀ m b := by
  have := blocks22 hp
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right e, mw, mw, mem_addr' hp (by omega_arith), mem_addr' hp (by omega_arith)]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

/-- The words of the current block from word `b`, `n` of them written. -/
theorem writeWords_ok {s : State} (h : Inv s₀ s) {cur : Nat} (hc : cur < blocksN s₀) (xo : Bool)
    {P : BitVec 32} {b : Nat} (hsi : s.gpr .esi = P + BitVec.ofNat 32 (4 * b)) (hPfit : P.toNat + 1024 ≤ 2 ^ 32)
    (hPw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, P.setWidth 64 = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len)
    (hPC : Region.Disjoint ⟨P.setWidth 64, 1024⟩ ⟨matrixCell (memB s₀) cur, 1024⟩)
    (hdi : s.gpr .edi = memP s₀ + BitVec.ofNat 32 (cur * 1024 + 4 * b)) :
    ∀ n, b + n ≤ 256 → WP isa (.block ((List.range n).flatMap (writeWord xo))) s fun t =>
      Inv s₀ t ∧ (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧
      Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem t.mem ∧
      ∀ i < 256, mw s₀ t.mem (cur * 1024 + 4 * i) = if b ≤ i ∧ i < b + n then
        (if xo then s.mem.readW (addr P (4 * i)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * i) else s.mem.readW (addr P (4 * i)) 32)
        else mw s₀ s.mem (cur * 1024 + 4 * i)
  | 0, _ => WP.block_nil ⟨h, fun _ _ => rfl, Frame.refl _ _, fun i _ => by rw [ite_eq_right (by omega_arith)]⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    have hm := hp.mem_fits
    obtain hb := blocks22 hp
    obtain hc' : cur * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_arith
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((writeWords_ok h hc xo hsi hPfit hPw hPC hdi n (by omega_arith)).mono
      fun t ⟨it, gt, ft, wt⟩ => ?_)
    have cell : matrixCell (memB s₀) cur = memB s₀ + BitVec.ofNat 64 (cur * 1024) := rfl
    -- The source word is kept: only the current block has been written.
    obtain eP : addr P (4 * (b + n)) = P.setWidth 64 + BitVec.ofNat 64 (4 * (b + n)) :=
      addr_eq (by omega_using [hPfit, hn])
    obtain sw_t : t.mem.readW (addr P (4 * (b + n))) 32 = s.mem.readW (addr P (4 * (b + n))) 32 := by
      rw [eP]
      refine ft.readW (r := ⟨P.setWidth 64 + BitVec.ofNat 64 (4 * (b + n)), 4⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hPC.sub_left (Offset.sub_base _ (by omega_using [hn]))
    obtain ea : addr (t.gpr .esi) (4 * n) = addr P (4 * (b + n)) := by
      rw [gt _ (by decide), hsi, addr_shift, Nat.mul_add]
    obtain eb : addr (t.gpr .edi) (4 * n) = addr (memP s₀) (cur * 1024 + 4 * (b + n)) := by
      rw [gt _ (by decide), hdi, addr_shift, Nat.mul_add, Nat.add_assoc]
    obtain b1 : cur * 1024 + 4 * (b + n) + 4 ≤ blocksN s₀ * 1024 := by omega_using [hc', hn]
    obtain b2 : cur * 1024 + 1024 < 2 ^ 64 := by omega_using [hc', hb]
    obtain inS : InRegions (t.rd ++ t.wr) (addr (t.gpr .esi) (4 * n)) 4 := by
      obtain ⟨R, hR, off, bR, lR⟩ := hPw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      obtain RW : R ∈ t.wr ∧ R.len ≤ 2 ^ 32 := by
        rw [it.wr]
        rcases hR with rfl | rfl
        · exact ⟨scr_mem hp, by show 16384 ≤ 2 ^ 32; decide⟩
        · exact ⟨mem_mem hp, by show blocksN s₀ * 1024 ≤ 2 ^ 32; omega_using [hm]⟩
      rw [ea, eP, bR, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨R, List.mem_append_right _ RW.1, Offset.contains_base _ (by omega_using [lR, hn])
        (by have := RW.2; omega_using [lR, hn, this])⟩
    obtain inMc : (memR s₀).Contains (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [eb, mem_addr' hp (by omega_using [b1])]
      exact Offset.contains_base _ b1 (by omega_using [b1, hb])
    obtain inC : (⟨matrixCell (memB s₀) cur, 1024⟩ : Region).Contains (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [eb, mem_addr' hp (by omega_using [b1]), cell]
      exact Offset.contains _ (by omega_using []) (by omega_using [hn]) b2
    obtain inM : InRegions t.wr (addr (t.gpr .edi) (4 * n)) 4 := ⟨memR s₀, by rw [it.wr]; exact mem_mem hp, inMc⟩
    -- The word.
    obtain fin : ∀ (v : BitVec 32) (u : State), u.mem = t.mem.writeW (addr (t.gpr .edi) (4 * n)) v →
        u.rd = t.rd → u.wr = t.wr → (∀ r, r ≠ .eax → u.gpr r = s.gpr r) →
        v = (if xo then s.mem.readW (addr P (4 * (b + n))) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * (b + n))
          else s.mem.readW (addr P (4 * (b + n))) 32) →
        Inv s₀ u ∧ (∀ r, r ≠ .eax → u.gpr r = s.gpr r) ∧
        Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem u.mem ∧
        ∀ i < 256, mw s₀ u.mem (cur * 1024 + 4 * i) = if b ≤ i ∧ i < b + (n + 1) then
          (if xo then s.mem.readW (addr P (4 * i)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * i)
            else s.mem.readW (addr P (4 * i)) 32)
          else mw s₀ s.mem (cur * 1024 + 4 * i) := fun v u hm hrd hwr gu ev => by
      obtain fu : Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem u.mem := by
        rw [hm]; exact ft.writeW (List.mem_singleton_self _) v inC
      obtain iu : Inv s₀ u := it.step (by rw [gu _ (by decide), gt _ (by decide)])
        (by rw [gu _ (by decide), gt _ (by decide)]) hrd hwr
        (by rw [hm]; exact (Frame.refl _ _).writeW (r := memR s₀) (by simp) v inMc)
      refine ⟨iu, gu, fu, fun i hi => ?_⟩
      rw [hm, eb, mw_store hp _ b1 (by omega_using [hi, hc', hb]) (by omega_using []), wt i hi]
      by_cases e : i = b + n
      · subst e
        rw [ite_eq_left rfl, ite_eq_left (show b ≤ b + n ∧ b + n < b + (n + 1) by omega_using []), ev]
      · rw [ite_eq_right (show ¬cur * 1024 + 4 * (b + n) = cur * 1024 + 4 * i by omega_using [e])]
        by_cases c : b ≤ i ∧ i < b + n
        · rw [ite_eq_left c, ite_eq_left (show b ≤ i ∧ i < b + (n + 1) by omega_using [c])]
        · rw [ite_eq_right c, ite_eq_right (show ¬(b ≤ i ∧ i < b + (n + 1)) by omega_using [c, e])]
    cases xo
    · simp only [writeWord, Bool.false_eq_true, ite_false, List.nil_append]
      refine wp_ldm rfl inS fun u₁ v₁ => ?_
      refine wp_stm (b := .edi) (v₁.other .edi (by decide)) (by rw [v₁.wr]; exact inM) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₁.mem]) (by rw [mu.rd, v₁.rd]) (by rw [mu.wr, v₁.wr])
        (fun r hr => by rw [mu.gpr, v₁.other r hr, gt r hr]) ?_
      simp only [Bool.false_eq_true, ite_false]
      rw [v₁.gpr, ea, sw_t]
    · simp only [writeWord, ite_true, List.cons_append, List.nil_append]
      refine wp_ldm rfl inS fun u₁ v₁ => ?_
      refine wp_xorm (b := .edi) (v₁.other .edi (by decide)) (by rw [v₁.rd, v₁.wr]; exact
        ⟨memR s₀, List.mem_append_right _ (by rw [it.wr]; exact mem_mem hp), inMc⟩) fun u₂ v₂ => ?_
      refine wp_stm (b := .edi) (by rw [v₂.other .edi (by decide), v₁.other .edi (by decide)])
        (by rw [v₂.wr, v₁.wr]; exact inM) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₂.mem, v₁.mem]) (by rw [mu.rd, v₂.rd, v₁.rd]) (by rw [mu.wr, v₂.wr, v₁.wr])
        (fun r hr => by rw [mu.gpr, v₂.other r hr, v₁.other r hr, gt r hr]) ?_
      simp only [ite_true]
      rw [v₂.gpr, v₁.gpr, v₁.mem, ea, sw_t, eb, ← mw, wt (b + n) (by omega_using [hn]),
        ite_eq_right (show ¬(b ≤ b + n ∧ b + n < b + n) by omega_using [])]

/-- What `writeBlock xo` writes to word `i` of the current block, from memory `m`. -/
abbrev wnew (s₀ : State) (cur : Nat) (xo : Bool) (P : BitVec 32) (m : Mem) (i : Nat) : BitVec 32 :=
  if xo then m.readW (addr P (4 * i)) 32 ^^^ mw s₀ m (cur * 1024 + 4 * i) else m.readW (addr P (4 * i)) 32

/-- `writeBlock xo`: the 256 words, 64 per iteration of its loop. -/
theorem writeBlock_ok {s : State} (h : Inv s₀ s) {cur : Nat} (hc : cur < blocksN s₀) (xo : Bool)
    {P : BitVec 32} (hsi : s.gpr .esi = P) (hPfit : P.toNat + 1024 ≤ 2 ^ 32)
    (hPw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, P.setWidth 64 = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len)
    (hPC : Region.Disjoint ⟨P.setWidth 64, 1024⟩ ⟨matrixCell (memB s₀) cur, 1024⟩)
    (hdi : s.gpr .edi = memP s₀ + BitVec.ofNat 32 (cur * 1024)) :
    WP isa (writeBlock xo) s fun t => Inv s₀ t ∧
      Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem t.mem ∧
      ∀ i < 256, mw s₀ t.mem (cur * 1024 + 4 * i) = if i < 256 then wnew s₀ cur xo P s.mem i
        else mw s₀ s.mem (cur * 1024 + 4 * i) := by
  have hm := hp.mem_fits
  obtain hb := blocks22 hp
  obtain hc' : cur * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_arith
  -- After `k` iterations.
  let WI : Nat → State → Prop := fun k t => Inv s₀ t ∧ t.gpr .esi = P + BitVec.ofNat 32 (4 * (64 * k)) ∧
    t.gpr .edi = memP s₀ + BitVec.ofNat 32 (cur * 1024 + 4 * (64 * k)) ∧ t.gpr .ecx = BitVec.ofNat 32 (4 - k) ∧
    Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem t.mem ∧
    ∀ i < 256, mw s₀ t.mem (cur * 1024 + 4 * i) = if i < 64 * k then wnew s₀ cur xo P s.mem i
      else mw s₀ s.mem (cur * 1024 + 4 * i)
  -- The source is outside the current block.
  obtain src : ∀ (m : Mem), Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem m → ∀ i < 256,
      m.readW (addr P (4 * i)) 32 = s.mem.readW (addr P (4 * i)) 32 := fun m f i hi => by
    rw [addr_eq (by omega_using [hPfit, hi])]
    refine f.readW (r := ⟨P.setWidth 64 + BitVec.ofNat 64 (4 * i), 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact hPC.sub_left (Offset.sub_base _ (by omega_using [hi]))
  unfold writeBlock
  refine WP.seq (wp_movi fun s₁ u₁ => WP.block_nil ?_)
  refine (WP.loop (M := isa) (Q := WI 4) (fun n t => ∃ k, n = 4 - k ∧ k < 4 ∧ WI k t) ?_ 4 s₁
    ⟨0, rfl, by decide, h.upd u₁ (by decide) (by decide),
      by rw [u₁.other _ (by decide), hsi]; simp, by rw [u₁.other _ (by decide), hdi]; simp, u₁.gpr,
      by rw [u₁.mem]; exact Frame.refl _ _, fun i _ => by rw [ite_eq_right (by omega_arith), u₁.mem]⟩).mono ?_
  · rintro n t ⟨k, rfl, hk, it, si, di, ci, ft, wt⟩
    unfold Impl.Argon2.X86.Derive.writeChunk
    refine WP.block_append ((writeWords_ok hp it hc xo (b := 64 * k) si hPfit hPw hPC di 64 (by omega_arith)).mono
      fun u ⟨iu, gu, fu, wu⟩ => ?_)
    refine wp_addi fun u₁ v₁ => wp_addi fun u₂ v₂ => wp_subi fun u₃ v₃ _ z₃ => WP.block_nil ?_
    obtain i₃ := ((iu.upd v₁ (by decide) (by decide)).upd v₂ (by decide) (by decide)).upd v₃ (by decide) (by decide)
    obtain m₃ : u₃.mem = u.mem := by rw [v₃.mem, v₂.mem, v₁.mem]
    obtain next : WI (k + 1) u₃ := by
      refine ⟨i₃, ?_, ?_, ?_, by rw [m₃]; exact ft.trans fu, fun i hi => ?_⟩
      · rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, gu _ (by decide), si,
          show (256 : BitVec 32) = BitVec.ofNat 32 256 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 4 * (64 * k) + 256 = 4 * (64 * (k + 1)) by omega_arith]
      · rw [v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), gu _ (by decide), di,
          show (256 : BitVec 32) = BitVec.ofNat 32 256 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show cur * 1024 + 4 * (64 * k) + 256 = cur * 1024 + 4 * (64 * (k + 1)) by omega_arith]
      · rw [v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), gu _ (by decide), ci, Wp.ofNat_pred (by omega_arith)]
        congr 1
      · rw [m₃, wu i hi]
        by_cases e : 64 * k ≤ i ∧ i < 64 * k + 64
        · rw [ite_eq_left e, ite_eq_left (show i < 64 * (k + 1) by omega_arith), src t.mem ft i hi,
            wt i hi, ite_eq_right (show ¬i < 64 * k by omega_arith)]
        · rw [ite_eq_right e, wt i hi]
          by_cases c : i < 64 * k
          · rw [ite_eq_left c, ite_eq_left (show i < 64 * (k + 1) by omega_arith)]
          · rw [ite_eq_right c, ite_eq_right (show ¬i < 64 * (k + 1) by omega_arith)]
    obtain z : u₃.zf = some (decide (4 - (k + 1) = 0)) := by
      rw [z₃, v₂.other _ (by decide), v₁.other _ (by decide), gu _ (by decide), ci, Wp.ofNat_pred (by omega_arith),
        Wp.ofNat_beq_zero (by omega_arith)]
      rfl
    by_cases done : k + 1 = 4
    · refine .inl ⟨?_, done ▸ next⟩
      simp only [eval, z, show 4 - (k + 1) = 0 by omega_arith, decide_true, Option.map_some, Bool.not_true]
    · refine .inr ⟨?_, 4 - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, next⟩
      simp only [eval, z, show 4 - (k + 1) ≠ 0 by omega_arith, decide_false, Option.map_some, Bool.not_false]
  · rintro t ⟨it, _, _, _, ft, wt⟩
    refine ⟨it, ft, fun i hi => ?_⟩
    rw [wt i hi, ite_eq_left (show i < 64 * 4 by omega_arith)]

end

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): one block of the filling loops

`fillCompress_ok`: G of the previous and reference blocks to
`scratch + 4096`; `fillWrite_ok`: the current block, copied or XORed;
`fillBlock_ok`: the filling state after one block (`Spec.Argon2.fillBlock`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.X86 (blk ofWords blk_of_words xor_words)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff writeBlock)

theorem FS.of_upd {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState} {r : Reg} {v : BitVec 32}
    (h : FS s₀ pass slice lane index ctr st s) (u : Upd s t r v) (h1 : r ≠ .esp) (h2 : r ≠ .ebp) :
    FS s₀ pass slice lane index ctr st t :=
  h.keep (h.inv.upd u h1 h2) (fun d _ => lw_mem u.mem d) (by rw [u.mem]) fun _ _ => by rw [u.mem]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem outside_work : Outside s₀ ⟨scrB s₀, 4096⟩ := by
  have := outside_scr hp (o := 0) (n := 4096) (.inl (by decide))
  simpa using this

/-- The locals are kept by writes outside them. -/
theorem lw_outside {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem) (ho : ∀ r ∈ rs, Outside s₀ r)
    {d : Nat} (hd : d + 4 ≤ 144) : lw s₀ t d = lw s₀ s d :=
  f.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _)
    (fun r hr => (ho r hr).1.symm.sub_left (loc_word_sub hp hd)) (by decide)

/-- `fillCompress`: G of the previous and reference blocks, to `scratch + 4096`. -/
theorem fillCompress_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {R : Nat} (hR : R < blocksN s₀)
    (htmp : lw s₀ s tmpOff = memP s₀ + BitVec.ofNat 32 (R * 1024)) :
    WP isa Impl.Argon2.X86.Derive.fillCompress s fun t => FS s₀ pass slice lane index ctr st t ∧
      (∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d) ∧
      blk t.mem (scrP s₀) 4096 = compress (blockAt s.mem (matrixCell (memB s₀) (lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))
        (blockAt s.mem (matrixCell (memB s₀) R)) := by
  obtain L8 := laneLen_ge hp
  obtain ⟨cl, _⟩ := cell_fits hp hl (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) (Nat.mod_lt _ (by omega_arith))
  unfold Impl.Argon2.X86.Derive.fillCompress Impl.Argon2.X86.Derive.compressCall
  refine WP.seq ((prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = P at cl a₁ ⊢
  obtain h₁ := h.of_keep k₁
  refine WP.seq (wp_ldloc hp h₁.inv (d := tmpOff) (by decide) fun s₂ u₂ => ?_)
  obtain h₂ := h₁.of_upd u₂ (by decide) (by decide)
  refine wp_ldarg hp h₂.inv (i := 15) (by decide) fun s₃ u₃ => ?_
  obtain h₃ := h₂.of_upd u₃ (by decide) (by decide)
  refine wp_mov fun s₄ u₄ => ?_
  obtain h₄ := h₃.of_upd u₄ (by decide) (by decide)
  refine wp_addi fun s₅ u₅ => WP.block_nil ?_
  obtain h₅ := h₄.of_upd u₅ (by decide) (by decide)
  obtain m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, k₁.mem]
  obtain ax : s₅.gpr .eax = memP s₀ + BitVec.ofNat 32 (P * 1024) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), a₁]
  obtain sx : s₅.gpr .esi = memP s₀ + BitVec.ofNat 32 (R * 1024) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, lw_mem k₁.mem, htmp]
  obtain dx : s₅.gpr .edx = scrP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  obtain cx : s₅.gpr .ecx = scrP s₀ + BitVec.ofNat 32 4096 := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr]; rfl
  refine ccall_ok hp h₅.inv dx (o := 4096) (by decide) (by decide) cx (by rw [ax]; exact .inl ⟨P, cl, rfl⟩)
    (by rw [sx]; exact .inl ⟨R, hR, rfl⟩) fun t it _ f post => ?_
  obtain ho : ∀ r ∈ [⟨scrB s₀ + BitVec.ofNat 64 4096, 1024⟩, ⟨scrB s₀, 4096⟩, callR s₀], Outside s₀ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact outside_scr hp (.inl (by decide))
    · exact outside_work hp
    · exact outside_call hp
  refine ⟨h₅.frame hp it f ho, fun d hd => by rw [lw_outside hp f ho hd, lw_mem m₅], ?_⟩
  rw [post, ax, sx, cell_addr hp cl, cell_addr hp hR, m₅]

end


section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `fillWrite`: G's output to the current block, XORed into it after the first pass. -/
theorem fillWrite_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) {C : Nat} (hC : C < blocksN s₀)
    (hcur : lw s₀ s curOff = memP s₀ + BitVec.ofNat 32 (C * 1024)) :
    WP isa Impl.Argon2.X86.Derive.fillWrite s fun t => Inv s₀ t ∧
      Frame [⟨matrixCell (memB s₀) C, 1024⟩] s.mem t.mem ∧
      blockAt t.mem (matrixCell (memB s₀) C) = if pass = 0 then blk s.mem (scrP s₀) 4096 else
        xorBlock (blk s.mem (scrP s₀) 4096) (blockAt s.mem (matrixCell (memB s₀) C)) := by
  unfold Impl.Argon2.X86.Derive.fillWrite
  refine WP.seq (wp_ldarg hp h.inv (i := 15) (by decide) fun s₁ u₁ => ?_)
  obtain h₁ := h.of_upd u₁ (by decide) (by decide)
  refine wp_addi fun s₂ u₂ => ?_
  obtain h₂ := h₁.of_upd u₂ (by decide) (by decide)
  refine wp_ldloc hp h₂.inv (d := curOff) (by decide) fun s₃ u₃ => ?_
  obtain h₃ := h₂.of_upd u₃ (by decide) (by decide)
  refine wp_ldloc hp h₃.inv (d := passOff) (by decide) fun s₄ u₄ => wp_cmpi fun s₅ f₅ _ z₅ => WP.block_nil ?_
  obtain h₅ := (h₃.of_upd u₄ (by decide) (by decide)).of_keep (Divide.Keep.of_fupd f₅)
  obtain m₅ : s₅.mem = s.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain si : s₅.gpr .esi = scrP s₀ + BitVec.ofNat 32 4096 := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]; rfl
  obtain di : s₅.gpr .edi = memP s₀ + BitVec.ofNat 32 (C * 1024) := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, lw_mem u₂.mem, lw_mem u₁.mem, hcur]
  obtain z : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
  have hsf := hp.scr_fits
  obtain eP : (scrP s₀ + BitVec.ofNat 32 4096).setWidth 64 = scrB s₀ + BitVec.ofNat 64 4096 :=
    HPrime.setWidth_add (by omega_arith)
  obtain Pfit : (scrP s₀ + BitVec.ofNat 32 4096).toNat + 1024 ≤ 2 ^ 32 := by rw [add_nat (by omega_arith)]; omega_arith
  obtain Pw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, (scrP s₀ + BitVec.ofNat 32 4096).setWidth 64 =
      R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len := ⟨scrR s₀, by simp, 4096, eP, by show 4096 + 1024 ≤ 16384; decide⟩
  obtain PC : Region.Disjoint ⟨(scrP s₀ + BitVec.ofNat 32 4096).setWidth 64, 1024⟩ ⟨matrixCell (memB s₀) C, 1024⟩ := by
    rw [eP]
    exact (hp.mem_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (cell_in_mem hC)
  obtain nxt : blk s.mem (scrP s₀) 4096 = ofWords fun i => sw s₀ s.mem (4096 + 4 * i) :=
    blk_of_words fun _ _ => rfl
  obtain old : blockAt s.mem (matrixCell (memB s₀) C) = ofWords fun i => mw s₀ s.mem (C * 1024 + 4 * i) := by
    rw [cell_blk hp _ hC]; exact blk_of_words fun _ _ => rfl
  obtain done : ∀ (xo : Bool) (t : State), (∀ i < 256, mw s₀ t.mem (C * 1024 + 4 * i) = if i < 256 then
        (if xo then s₅.mem.readW (addr (scrP s₀ + BitVec.ofNat 32 4096) (4 * i)) 32 ^^^ mw s₀ s₅.mem (C * 1024 + 4 * i)
          else s₅.mem.readW (addr (scrP s₀ + BitVec.ofNat 32 4096) (4 * i)) 32)
        else mw s₀ s₅.mem (C * 1024 + 4 * i)) →
      blockAt t.mem (matrixCell (memB s₀) C) = if xo then
        xorBlock (blk s.mem (scrP s₀) 4096) (blockAt s.mem (matrixCell (memB s₀) C)) else blk s.mem (scrP s₀) 4096 :=
    fun xo t wt => by
      obtain e : blockAt t.mem (matrixCell (memB s₀) C) = ofWords fun i => if xo then
          sw s₀ s.mem (4096 + 4 * i) ^^^ mw s₀ s.mem (C * 1024 + 4 * i) else sw s₀ s.mem (4096 + 4 * i) := by
        rw [cell_blk hp _ hC]
        exact blk_of_words fun i hi => by rw [← mw, wt i hi, ite_eq_left hi, m₅, addr_shift]
      rw [e, nxt, old]
      cases xo
      · rfl
      · simp only [ite_true]; rw [xor_words]
  refine WP.ite (decide (pass = 0)) (by
    show s₅.zf = _
    rw [z₅, u₄.gpr, lw_mem u₃.mem, lw_mem u₂.mem, lw_mem u₁.mem, h.pos.pass, z, Wp.ofNat_beq_zero hpass])
    (fun hb => ?_) fun hb => ?_
  · refine ((writeBlock_ok hp h₅.inv hC false si Pfit Pw PC di).mono fun t ⟨it, ft, wt⟩ =>
      ⟨it, by rw [← m₅]; exact ft, ?_⟩)
    rw [done false t wt, ite_eq_left (of_decide_eq_true hb)]; rfl
  · refine ((writeBlock_ok hp h₅.inv hC true si Pfit Pw PC di).mono fun t ⟨it, ft, wt⟩ =>
      ⟨it, by rw [← m₅]; exact ft, ?_⟩)
    rw [done true t wt, ite_eq_right (of_decide_eq_false hb)]; rfl

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `fillBlock`: one block of the filling loops. -/
theorem fillBlock_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.X86.Derive.fillBlock s fun t =>
      FS s₀ pass slice lane index (ctrNext (prm s₀) pass slice index ctr)
        (Spec.Argon2.fillBlock (prm s₀) pass slice lane index st) t := by
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.X86.Derive.fillBlock
  refine WP.seq ((randomSource_ok hp h hpass hl hs hi).mono fun t₁ ⟨h₁, w₁⟩ => ?_)
  refine WP.seq ((reference_ok hp ⟨h₁, rfl, rfl⟩ hpass hl hs hi active).mono fun t₂ ⟨h₂, tmp₂, cur₂⟩ => ?_)
  rw [w₁] at tmp₂
  obtain refLt := Proof.Argon2.reference_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory) hl
  obtain curLt := Proof.Argon2.current_cell_lt (prm s₀) hp.lanes_pos hl hs hi
  obtain prevLt := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
    (column := slice * (prm s₀).segmentLen + index) hl
  simp only at refLt
  refine WP.seq ((fillCompress_ok hp h₂.fs hl hs hi (by rw [hb]; exact refLt) tmp₂).mono
    fun t₃ ⟨h₃, l₃, c₃⟩ => ?_)
  refine (fillWrite_ok hp h₃ hpass (C := lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index))
    (by rw [hb]; exact curLt) (by rw [l₃ _ (by decide)]; exact cur₂)).mono
    fun t ⟨it, ft, bt⟩ => ?_
  obtain kept : ∀ j < (prm s₀).blocks, j ≠ lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index) →
      blockAt t.mem (matrixCell (memB s₀) j) = blockAt t₃.mem (matrixCell (memB s₀) j) := fun j hj ne =>
    blockAt_keep ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact cell_other hp (by rw [hb]; exact hj) (by rw [hb]; exact curLt) ne
  obtain lt : ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ t₃ d := fun d hd =>
    ft.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).sub_right (cell_in_mem (by rw [hb]; exact curLt))) (by decide)
  refine ⟨it, Prm.of_lw h₃.pr fun d hd => lt d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    h₃.pos.of_lw fun d hd => lt d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    ?_, ?_⟩
  · obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h₃.cache
    · exact ⟨c0, by rw [lt _ (by decide)]; exact c1, .inl c2⟩
    · refine ⟨c0, by rw [lt _ (by decide)]; exact c1, .inr ⟨c3, ?_⟩⟩
      rw [scr_blk hp _ (by decide), blockAt_keep ft (fun r hr => ?_), ← scr_blk hp _ (by decide), c4]
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.mem_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right
        (cell_in_mem (by rw [hb]; exact curLt))
  · rw [Proof.Argon2.FillStep.memory _ _ _ _ _ _ active]
    simp only [Proof.Argon2.FillStep.update]
    refine Represents.update h₃.mem _ curLt _ ?_ kept
    rw [bt, c₃, h₂.fs.mem.block _ prevLt, h₂.fs.mem.block _ refLt, h₃.mem.block _ curLt]

end
end VG.Proof.Argon2.X86.Derive
