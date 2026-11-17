module

import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MdStream.Arm.Common
public import VerifiedGarbage.Impl.Argon2.Arm.Derive
public import VerifiedGarbage.Proof.Argon2.Arm.Push
public import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Argon2.Arm.CompressLit
import VerifiedGarbage.Proof.Framework.Arm.Lost

/-! ### `Argon2.Arm.Derive.Body`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.Derive.Frame`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.Derive.Contract`, which this module and modules that import it used -/

section

/-!
# Argon2 on ARMv7: the contract of the derivation's proof

`deriveArm`: `vg_argon2`'s contract, its fourteen stack arguments only read
(as `Spec.Argon2.deriveContract` has them on ARMv7, whose calling convention
keeps them read-only), its precondition a structure (`DPre`;
`Derive/Verified.lean` reaches the shared contract). The derivation
uses the 240 bytes of stack below the stack pointer: 16 for its register
arguments, 40 for the saved registers, 144 for the locals, and 40 for a call
of `vg_argon2_hprime` (its stack argument, padding, and H′'s own 32 bytes).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Spec.Argon2
open VG.Proof.Argon2.Arm (stkR)
open VG.Spec.Blake2 (bytesAt)

/-- Argument `i`: `r0`–`r3`, then the stack arguments. -/
def arg (s : State) : Nat → BitVec 32
  | 0 => s.gpr .r0
  | 1 => s.gpr .r1
  | 2 => s.gpr .r2
  | 3 => s.gpr .r3
  | i + 4 => stackArg s i

section
variable (s₀ : State)

abbrev kindV : BitVec 32 := arg s₀ 0
abbrev pwP : BitVec 32 := arg s₀ 1
abbrev pwL : Nat := (arg s₀ 2).toNat
abbrev saltP : BitVec 32 := arg s₀ 3
abbrev saltL : Nat := (arg s₀ 4).toNat
abbrev itersN : Nat := (arg s₀ 5).toNat
abbrev mcostN : Nat := (arg s₀ 6).toNat
abbrev lanesN : Nat := (arg s₀ 7).toNat
abbrev threadsN : Nat := (arg s₀ 8).toNat
abbrev secP : BitVec 32 := arg s₀ 9
abbrev secL : Nat := (arg s₀ 10).toNat
abbrev adP : BitVec 32 := arg s₀ 11
abbrev adL : Nat := (arg s₀ 12).toNat
abbrev memP : BitVec 32 := arg s₀ 13
abbrev blocksN : Nat := (arg s₀ 14).toNat
abbrev scrP : BitVec 32 := arg s₀ 15
abbrev outP : BitVec 32 := arg s₀ 16
abbrev outL : Nat := (arg s₀ 17).toNat
abbrev E0 : BitVec 32 := s₀.sp

/-- The parameters. -/
abbrev prm : Params := params (kindV s₀).toNat (itersN s₀) (mcostN s₀) (lanesN s₀) (outL s₀)

abbrev pwR : Region := ⟨State.addr (pwP s₀), pwL s₀⟩
abbrev saltR : Region := ⟨State.addr (saltP s₀), saltL s₀⟩
abbrev secR : Region := ⟨State.addr (secP s₀), secL s₀⟩
abbrev adR : Region := ⟨State.addr (adP s₀), adL s₀⟩
abbrev memR : Region := ⟨State.addr (memP s₀), blocksN s₀ * 1024⟩
abbrev scrR : Region := ⟨State.addr (scrP s₀), 16384⟩
abbrev outR : Region := ⟨State.addr (outP s₀), outL s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 56⟩
abbrev stkR0 : Region := stkR (E0 s₀) 240

/-- The inputs, on entry. -/
abbrev pwB : List Byte := bytesAt s₀.mem (pwR s₀).base (pwL s₀)
abbrev saltB : List Byte := bytesAt s₀.mem (saltR s₀).base (saltL s₀)
abbrev secB : List Byte := bytesAt s₀.mem (secR s₀).base (secL s₀)
abbrev adB : List Byte := bytesAt s₀.mem (adR s₀).base (adL s₀)

end

/-- The facts of `deriveArm`'s precondition. -/
structure DPre (s₀ : State) : Prop where
  rd : s₀.rd = [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀]
  wr : s₀.wr = [memR s₀, scrR s₀, outR s₀]
  ro_w : ∀ r ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀], ∀ w ∈ [memR s₀, scrR s₀, outR s₀],
    r.Disjoint w
  mem_scr : (memR s₀).Disjoint (scrR s₀)
  mem_out : (memR s₀).Disjoint (outR s₀)
  scr_out : (scrR s₀).Disjoint (outR s₀)
  stk_all : ∀ r ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀], (stkR0 s₀).Disjoint r
  pw_fits : (pwP s₀).toNat + pwL s₀ ≤ 2 ^ 32
  salt_fits : (saltP s₀).toNat + saltL s₀ ≤ 2 ^ 32
  sec_fits : (secP s₀).toNat + secL s₀ ≤ 2 ^ 32
  ad_fits : (adP s₀).toNat + adL s₀ ≤ 2 ^ 32
  mem_fits : (memP s₀).toNat + blocksN s₀ * 1024 ≤ 2 ^ 32
  scr_fits : (scrP s₀).toNat + 16384 ≤ 2 ^ 32
  out_fits : (outP s₀).toNat + outL s₀ ≤ 2 ^ 32
  sp_lo : 240 ≤ (E0 s₀).toNat
  sp_hi : (E0 s₀).toNat + 56 ≤ 2 ^ 32
  kind_le : (kindV s₀).toNat ≤ 2
  valid : valid (prm s₀) (pwL s₀) (saltL s₀) (secL s₀) (adL s₀)
  threads : 1 ≤ threadsN s₀ ∧ threadsN s₀ < 2 ^ 24
  blocks : blocksN s₀ = (prm s₀).blocks

/-- `vg_argon2`, with its stack arguments only read. -/
def deriveArm : Contract Arm.isa where
  pre := DPre
  post s s' := bytesAt s'.mem (State.addr (outP s)) (outL s) =
    derive (prm s) (pwB s) (saltB s) (secB s) (adB s)
  pub s₁ s₂ := (s₁.sp = s₂.sp ∧ ∀ i < 18, arg s₁ i = arg s₂ i) ∧
    references (prm s₁) (pwB s₁) (saltB s₁) (secB s₁) (adB s₁) =
      references (prm s₂) (pwB s₂) (saltB s₂) (secB s₂) (adB s₂)

/-! ## Facts of the precondition -/

/-- Two disjoint, nonempty regions within `[0, N)` have at most `N` bytes in all. -/
theorem disjoint_total {a b : Region} (h : a.Disjoint b) {N : Nat}
    (ha : a.base.toNat + a.len ≤ N) (hb : b.base.toNat + b.len ≤ N) (pa : 0 < a.len) (pb : 0 < b.len) :
    a.len + b.len ≤ N := by
  have key : ∀ {a b : Region}, a.Disjoint b → a.base.toNat ≤ b.base.toNat → b.base.toNat + b.len ≤ N →
      0 < b.len → a.base.toNat + a.len ≤ b.base.toNat := fun {a b} h hle hb pb => by
    by_contra hlt
    refine h b.base ?_ ?_
    · simp only [Region.Contains]
      rw [BitVec.toNat_sub_of_le (by simpa [BitVec.le_def] using hle)]
      omega_using [hle, hlt]
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [pb]
  rcases Nat.le_total a.base.toNat b.base.toNat with hle | hle
  · have := key h hle hb pb; omega_using [hb, this]
  · have := key h.symm hle ha pa; omega_using [ha, this]

namespace DPre
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem lanes_pos : 1 ≤ lanesN s₀ := hp.valid.1
theorem lanes_lt : lanesN s₀ < 2 ^ 24 := hp.valid.2.1
theorem passes_pos : 1 ≤ itersN s₀ := hp.valid.2.2.1
theorem memory_ge : 8 * lanesN s₀ ≤ mcostN s₀ := hp.valid.2.2.2.2.1
theorem tag_ge : 4 ≤ outL s₀ := hp.valid.2.2.2.2.2.2.1

theorem segLen_two : 2 ≤ (prm s₀).segmentLen :=
  Proof.Argon2.segmentLen_ge_two _ hp.lanes_pos hp.memory_ge

theorem segLen_eq : (prm s₀).segmentLen = mcostN s₀ / (4 * lanesN s₀) :=
  Proof.Argon2.segmentLen_eq _ hp.lanes_pos

theorem laneLen_eq : (prm s₀).laneLen = 4 * (prm s₀).segmentLen :=
  Proof.Argon2.laneLen_segments _ hp.lanes_pos

theorem blocks_eq : blocksN s₀ = lanesN s₀ * (prm s₀).laneLen := by
  rw [hp.blocks]; exact Proof.Argon2.blocks_lanes _ hp.lanes_pos

/-- The memory, with the scratch beside it, fits below 2³² with room to spare. -/
theorem blocks_lt : blocksN s₀ * 1024 + 16384 ≤ 2 ^ 32 := by
  have hm := hp.mem_fits
  have hs := hp.scr_fits
  rcases Nat.eq_zero_or_pos (blocksN s₀) with h0 | hpos
  · omega_using [h0]
  have := disjoint_total hp.mem_scr (N := 2 ^ 32)
    (by simp only [MdStream.Arm.addr_toNat]; omega_using [hm])
    (by simp only [MdStream.Arm.addr_toNat]; omega_using [hs])
    (by simp only; omega_using [hpos]) (by simp only; omega_using [])
  simpa using this

end DPre

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: the derivation's frames

`vg_argon2` pushes its register arguments, then the caller's `r4`–`r11` and
its return address (with `r3`), then allocates 144 bytes for the locals
(`Impl.Argon2.Arm.Derive.derive`). `entry s₀` is the state its body starts
in; `frames_ok` gives the callee-saved registers and the stack pointer back,
from a body that leaves the stack pointer at the locals and the saved words
alone (`BodyDone`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Argon2.Arm (stkR pushed_sp_toNat addr_toNat)
open VG.Impl.Argon2.Arm.Derive (body derive locals restoreRegs)

/-- The registers of the first frame: the register arguments. -/
abbrev argRegs : List Reg := [.r0, .r1, .r2, .r3]

/-- The registers of the second frame: `r3` (for alignment), the caller's
`r4`–`r11` and the return address. -/
abbrev savedRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

/-- The state the body starts in. -/
def entry (s₀ : State) : State := allocated 144 (pushed savedRegs (pushed argRegs s₀))

/-- The stack pointer of the body: below the frames and the locals. -/
abbrev E (s₀ : State) : BitVec 32 := E0 s₀ - BitVec.ofNat 32 200

/-- What the body must keep for the frames to restore the caller's state. -/
structure BodyDone (s₀ t : State) : Prop where
  sp : t.sp = E s₀
  saved : ∀ j < 9, t.mem.readW (State.addr (E s₀ + BitVec.ofNat 32 (148 + 4 * j))) 32 =
    s₀.gpr (savedRegs[j + 1]?.getD .r0)

section
variable {s₀ : State} (hlo : 200 ≤ (E0 s₀).toNat)
include hlo

theorem sp1 : (pushed argRegs s₀).sp.toNat = (E0 s₀).toNat - 16 := by
  have h : 200 ≤ s₀.sp.toNat := hlo
  rw [pushed_sp_toNat (by simp only [List.length_cons, List.length_nil]; omega_arith)]; rfl

theorem sp2 : (pushed savedRegs (pushed argRegs s₀)).sp.toNat = (E0 s₀).toNat - 56 := by
  rw [pushed_sp_toNat (by rw [sp1 hlo]; simp only [List.length_cons, List.length_nil]; omega_arith), sp1 hlo]; rfl

theorem E_toNat : (E s₀).toNat = (E0 s₀).toNat - 200 := sub_toNat' hlo

end

/-- Loading the registers of `l` from offsets of `sp`, then running `rest`. -/
theorem restoreSp_ok {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.2 < 4096 ∧ InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 p.2)) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 p.2)) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldrSp p.1 p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h1, h2⟩ := hl p List.mem_cons_self
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine MdStream.Arm.wp_ldrSp h1 rfl h2 fun s₁ u₁ => ?_
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr hsp => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp)
    · rw [u₁.sp, u₁.rd, u₁.wr]; exact (hl q (List.mem_cons_of_mem _ hq))
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, u₁.sp]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other _ hr.1]

/-- The frames and the locals, released: their 200 bytes below the stack
pointer on entry may hold anything once the derivation returns, so `Q` must
hold whatever they hold (`hQ`). -/
theorem frames_ok {s₀ : State} (hlo : 240 ≤ (E0 s₀).toNat) {Q : State → Prop}
    (hb : WP isa body (entry s₀) fun t => BodyDone s₀ t ∧ t.wr = (entry s₀).wr ∧ Q t)
    (hQ : ∀ t u, Q t → Frame [stkR (E0 s₀) 200] t.mem u.mem → Q u) :
    WP isa derive s₀ fun u => abiPreserved s₀ u ∧ Q u := by
  have hE := (E0 s₀).isLt
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  have h1 := sp1 (s₀ := s₀) (by omega_arith)
  have h2 := sp2 (s₀ := s₀) (by omega_arith)
  -- The three released regions are in the 200 bytes below `sp`.
  have hR1 : Region.Sub ⟨State.addr (s₀.sp - BitVec.ofNat 32 (4 * argRegs.length)), 4 * argRegs.length⟩
      (stkR (E0 s₀) 200) := by
    rw [addr_sub' (by simp only [List.length_cons, List.length_nil]; omega_arith)]
    exact Proof.Argon2.Arm.stkR_sub (by decide) (by omega_arith)
  have hR2 : Region.Sub ⟨State.addr ((pushed argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length)),
      4 * savedRegs.length⟩ (stkR (E0 s₀) 200) := by
    rw [addr_sub' (by rw [h1]; simp only [List.length_cons, List.length_nil]; omega_arith), pushed_sp]
    exact Proof.Argon2.Arm.stkR_inner (by decide) (by omega_arith)
  have hR3 : Region.Sub ⟨State.addr ((pushed savedRegs (pushed argRegs s₀)).sp - BitVec.ofNat 32 144), 144⟩
      (stkR (E0 s₀) 200) := by
    rw [addr_sub' (by rw [h2]; omega_arith), pushed_sp]
    refine fun x hx => Proof.Argon2.Arm.stkR_inner (sp := s₀.sp) (a := 184) (k := 4 * argRegs.length)
      (by decide) (by omega_arith) x ?_
    rw [pushed_sp] at hx
    exact Proof.Argon2.Arm.stkR_inner (sp := s₀.sp - BitVec.ofNat 32 (4 * argRegs.length)) (a := 144)
      (k := 4 * savedRegs.length) (by decide) (by rw [← pushed_sp, h1]; omega_arith) x hx
  unfold derive
  refine WP.frameLost (rs := argRegs) (r := .r0) (by decide) (by simp only [List.length_cons, List.length_nil]; omega_arith)
    (by decide) ?_
  refine WP.frameLost (rs := savedRegs) (r := .r3) (by decide)
    (by rw [h1]; simp only [List.length_cons, List.length_nil]; omega_arith) (by decide) ?_
  refine WP.seq (WP.allocLost (by decide) (by rw [h2]; show 144 ≤ _; omega_arith)
    (hb.mono fun t ⟨d, w, q⟩ mA uA hA => ?_))
  -- The restores.
  let S2 := pushed savedRegs (pushed argRegs s₀)
  try rewrite [show pushed savedRegs (pushed argRegs s₀) = S2 from rfl] at *
  have hS2 : S2 = pushed savedRegs (pushed argRegs s₀) := rfl
  have spS2 : (freed 144 t).sp = S2.sp := by
    simp only [freed, d.sp]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, E_toNat (by omega_arith), h2, BitVec.toNat_ofNat]
    omega_arith
  have wS2 : (freed 144 t).wr = S2.wr := by simp only [freed, w, entry, allocated, List.tail_cons, hS2]
  have S2sp : S2.sp.toNat = (E0 s₀).toNat - 56 := h2
  have hS2v : ∀ i (hi : i < 10), S2.mem.readW (State.addr (S2.sp + BitVec.ofNat 32 (4 * i))) 32 =
      s₀.gpr savedRegs[i] := fun i hi => by
    have := VG.Proof.Argon2.Arm.storeWords_readW (pushed argRegs s₀).mem
      ((pushed argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length))
      (savedRegs.map (pushed argRegs s₀).gpr) (by
        simp only [List.length_map, List.length_cons, List.length_nil]
        rw [sub_toNat' (by rw [h1]; omega_arith), h1]; omega_arith) (i := i) (by simpa using hi)
    rw [List.getElem_map] at this
    exact this
  have inS2 : ∀ d, d + 4 ≤ 40 → InRegions ((freed 144 t).rd ++ (freed 144 t).wr)
      (State.addr ((freed 144 t).sp + BitVec.ofNat 32 d)) 4 := fun d hd => by
    have hw : ⟨State.addr S2.sp, 40⟩ ∈ S2.wr := by simp [hS2, pushed]
    rw [wS2, spS2, addr_add (by rw [S2sp]; omega_arith)]
    exact ⟨⟨State.addr S2.sp, 40⟩, List.mem_append_right _ hw, Offset.contains_base _ hd (by omega_arith)⟩
  show WP isa (.block (Impl.Argon2.Arm.Derive.savedSlots.map fun p => Instr.ldrSp p.1 p.2))
    { freed 144 t with mem := mA, unknowns := uA } _
  rw [← List.append_nil (List.map _ _)]
  refine restoreSp_ok _ _ _ (by decide) (fun p hpm => ⟨?_, inS2 p.2 ?_⟩) fun u hu ho hm hrd hwr hsp => WP.block_nil ?_
  · simp only [Impl.Argon2.Arm.Derive.savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [Impl.Argon2.Arm.Derive.savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  -- The values restored.
  have key : ∀ j < 9, State.addr (S2.sp + BitVec.ofNat 32 (4 * (j + 1))) =
      State.addr (E s₀ + BitVec.ofNat 32 (148 + 4 * j)) := fun j hj => by
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, S2sp, E_toNat (by omega_arith), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 4 * (j + 1)) (by omega_arith), Nat.mod_eq_of_lt (a := 148 + 4 * j) (by omega_arith)]
    omega_arith
  have tv : ∀ j (hj : j < 9), t.mem.readW (State.addr (S2.sp + BitVec.ofNat 32 (4 * (j + 1)))) 32 =
      s₀.gpr (savedRegs[j + 1]?.getD .r0) := fun j hj => by
    rw [key j hj]; exact d.saved j hj
  have hv : ∀ p ∈ Impl.Argon2.Arm.Derive.savedSlots, u.gpr p.1 = s₀.gpr p.1 := by
    intro p hpm
    rw [hu p hpm]
    dsimp only
    rw [spS2]
    have hd : p.2 + 4 ≤ 40 := by
      simp only [Impl.Argon2.Arm.Derive.savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hpm
      rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hlc : locals = 144 := rfl
    rw [hA.readW (r := ⟨State.addr (S2.sp + BitVec.ofNat 32 p.2), 4⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr, addr_add (by rw [S2sp]; omega_arith), hlc, addr_sub' (by rw [S2sp]; omega_arith)]
      exact Offset.disjoint_below _ (by omega_arith)) (by decide)]
    simp only [Impl.Argon2.Arm.Derive.savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tv 0 (by decide)
    · exact tv 1 (by decide)
    · exact tv 2 (by decide)
    · exact tv 3 (by decide)
    · exact tv 4 (by decide)
    · exact tv 5 (by decide)
    · exact tv 6 (by decide)
    · exact tv 7 (by decide)
    · exact tv 8 (by decide)
  intro m₂ u₂ f₂ m₁ u₁ f₁
  refine ⟨⟨fun r hr => ?_, ?_⟩, hQ t _ q ?_⟩
  rotate_left 2
  · -- The memory: what the body left, but in the three released regions.
    dsimp only
    dsimp only at f₁
    rw [hm] at f₂
    exact ((hA.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact hR3⟩).trans
      (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact hR2⟩)).trans
      (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact hR1⟩)
  · have hr0 : r ≠ .r0 := by rintro rfl; simp [preserved] at hr
    have hr3 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
    dsimp only
    rw [popped_gpr hr0, popped_gpr hr3]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hv (.r4, 4) (by decide), hv (.r5, 8) (by decide), hv (.r6, 12) (by decide), hv (.r7, 16) (by decide),
      hv (.r8, 20) (by decide), hv (.r9, 24) (by decide), hv (.r10, 28) (by decide), hv (.r11, 32) (by decide),
      hv (.lr, 36) (by decide)]
  · dsimp only
    simp only [popped_sp, hsp, spS2, hS2, pushed_sp, List.length_cons, List.length_nil]
    rw [BitVec.sub_add_cancel, BitVec.sub_add_cancel]

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: the state of the derivation's body

`Inv s₀ s`: in the body, `sp` and `r11` point to the locals (`E s₀`), the
permissions are those of the body's entry, and memory has changed only in
the memory matrix, `scratch`, the output, the locals and the 40 bytes of
stack below them. The arguments, the inputs and the saved registers are
therefore kept (`Inv.arg`, `Inv.input`, `Inv.done`).

The regions all lie at 32-bit addresses, so whether they are disjoint,
contain an access or lie in one another is a question about the addresses'
values (`disj32`, `contains32`, `sub32`), for `omega`.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Argon2.Arm (stkR addr_toNat)
open VG.Proof.MdStream.Arm (Upd Mupd)
open VG.Spec.Blake2 (bytesAt)

/-! ## Regions at 32-bit addresses -/

theorem disj32 {x y : BitVec 32} {n m : Nat} (h : x.toNat + n ≤ y.toNat ∨ y.toNat + m ≤ x.toNat)
    (hn : x.toNat + n ≤ 2 ^ 32) (hm : y.toNat + m ≤ 2 ^ 32) :
    Region.Disjoint ⟨State.addr x, n⟩ ⟨State.addr y, m⟩ := by
  rcases h with h | h
  · exact Offset.disjoint_of_le (by simp only [addr_toNat]; omega_using [h]) (by simp only [addr_toNat]; omega_using [hm])
  · exact (Offset.disjoint_of_le (r₁ := ⟨State.addr y, m⟩) (by simp only [addr_toNat]; omega_using [h])
      (by simp only [addr_toNat]; omega_using [hn])).symm

theorem contains32 {x y : BitVec 32} {n m : Nat} (h₁ : y.toNat ≤ x.toNat)
    (h₂ : x.toNat + n ≤ y.toNat + m) :
    Region.Contains ⟨State.addr y, m⟩ (State.addr x) n := by
  simp only [Region.Contains]
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, addr_toNat]; exact h₁), addr_toNat, addr_toNat]
  omega_using [h₁, h₂]

theorem sub32 {x y : BitVec 32} {n m : Nat} (h₁ : y.toNat ≤ x.toNat)
    (h₂ : x.toNat + n ≤ y.toNat + m) :
    Region.Sub ⟨State.addr x, n⟩ ⟨State.addr y, m⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  have hx := addr_toNat x
  have hy := addr_toNat y
  have := x.isLt
  bv_omega

/-- `x + k`, as a number. -/
theorem add_nat {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_using [h]),
    Nat.mod_eq_of_lt h]

/-! ## The regions of the body -/

section
variable (s₀ : State)

/-- The locals. -/
abbrev locR : Region := ⟨State.addr (E s₀), 144⟩

/-- The stack below the locals: a call of `vg_argon2_hprime` and its frame. -/
abbrev callR : Region := stkR (E s₀) 40

/-- The regions the body may write. -/
abbrev bodyW : List Region := [memR s₀, scrR s₀, outR s₀, locR s₀, callR s₀]

/-- The word at `[r11, #d]`. -/
abbrev lw (s : State) (d : Nat) : BitVec 32 := s.mem.readW (State.addr (E s₀ + BitVec.ofNat 32 d)) 32

end

theorem entry_rd (s₀ : State) : (entry s₀).rd = s₀.rd := rfl

theorem entry_sp' (s₀ : State) : (entry s₀).sp = E s₀ := by
  simp only [entry, allocated, pushed_sp, List.length_cons, List.length_nil, BitVec.sub_sub,
    BitVec.ofNat_add_ofNat]

theorem loc_mem (s₀ : State) : locR s₀ ∈ (entry s₀).wr := by
  simp [entry, allocated, pushed, BitVec.sub_sub, BitVec.ofNat_add_ofNat]

theorem wr_mem (s₀ : State) {r : Region} (h : r ∈ s₀.wr) : r ∈ (entry s₀).wr := by
  simp only [entry, allocated, pushed, List.mem_cons]
  exact .inr (.inr (.inr h))

/-! ## The invariant -/

/-- The state of the body. -/
structure Inv (s₀ s : State) : Prop where
  sp : s.sp = E s₀
  r11 : s.gpr .r11 = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = (entry s₀).wr
  frame : Frame (bodyW s₀) (entry s₀).mem s.mem

/-- A step that writes registers other than `r11`, and memory within the body's regions. -/
theorem Inv.step {s₀ s t : State} (h : Inv s₀ s) (hs : t.sp = s.sp)
    (hb : t.gpr .r11 = s.gpr .r11) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame (bodyW s₀) s.mem t.mem) : Inv s₀ t :=
  ⟨hs.trans h.sp, hb.trans h.r11, hrd.trans h.rd, hwr.trans h.wr, h.frame.trans hf⟩

theorem Inv.upd {s₀ s t : State} {r : Reg} {v : BitVec 32} (h : Inv s₀ s) (u : Upd s t r v)
    (h₁ : r ≠ .r11) : Inv s₀ t :=
  h.step u.sp (u.other _ h₁.symm) u.rd u.wr (by rw [u.mem]; exact Frame.refl _ _)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem E_nat : (E s₀).toNat = (E0 s₀).toNat - 200 := sub_toNat' (by have := hp.sp_lo; omega_using [this])

theorem E_hi : (E s₀).toNat + 256 ≤ 2 ^ 32 := by
  have := hp.sp_hi; have := hp.sp_lo; rw [E_nat hp]; omega_arith

theorem loc_nat {d : Nat} (hd : d < 256) : (E s₀ + BitVec.ofNat 32 d).toNat = (E s₀).toNat + d :=
  add_nat (by have := E_hi hp; omega_using [hd, this])

/-- A range above the stack the body's calls use, within the frames and locals. -/
theorem frame_stk {d n : Nat} (h : d + n ≤ 200) :
    Region.Sub ⟨State.addr (E s₀ + BitVec.ofNat 32 d), n⟩ (stkR0 s₀) := by
  have := hp.sp_lo; have := hp.sp_hi
  have h2 : (E0 s₀ - BitVec.ofNat 32 240).toNat = (E0 s₀).toNat - 240 := sub_toNat' (by omega_arith)
  have e := E_nat hp
  have hh : State.addr (E0 s₀) - BitVec.ofNat 64 240 = State.addr (E0 s₀ - BitVec.ofNat 32 240) :=
    (addr_sub' (by omega_arith)).symm
  have tL : (E s₀ + BitVec.ofNat 32 d).toNat = (E s₀).toNat + d := loc_nat hp (by omega_using [h])
  show Region.Sub _ ⟨State.addr (E0 s₀) - BitVec.ofNat 64 240, 240⟩
  rw [hh]
  exact sub32 (by rw [tL, h2]; omega_using [e]) (by rw [tL, h2]; omega_using [h, e])

theorem call_stk : Region.Sub (callR s₀) (stkR0 s₀) := by
  have := hp.sp_lo; have := hp.sp_hi
  have e := E_nat hp
  have h1 : State.addr (E s₀) - BitVec.ofNat 64 40 = State.addr (E s₀ - BitVec.ofNat 32 40) :=
    (addr_sub' (by omega_arith)).symm
  have h2 : State.addr (E0 s₀) - BitVec.ofNat 64 240 = State.addr (E0 s₀ - BitVec.ofNat 32 240) :=
    (addr_sub' (by omega_arith)).symm
  show Region.Sub ⟨State.addr (E s₀) - BitVec.ofNat 64 40, 40⟩ ⟨State.addr (E0 s₀) - BitVec.ofNat 64 240, 240⟩
  have t1 : (E s₀ - BitVec.ofNat 32 40).toNat = (E0 s₀).toNat - 240 := by rw [sub_toNat' (by omega_arith), e]; omega_using []
  have t2 : (E0 s₀ - BitVec.ofNat 32 240).toNat = (E0 s₀).toNat - 240 := sub_toNat' (by omega_arith)
  rw [h1, h2]
  exact sub32 (by rw [t1, t2]) (by rw [t1, t2]; omega_using [])

/-- A word of the locals. -/
theorem loc_in {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions s.wr (State.addr (E s₀ + BitVec.ofNat 32 d)) 4 := by
  rw [h.wr]
  exact ⟨locR s₀, loc_mem s₀, contains32 (by rw [loc_nat hp (d := d) (by omega_using [hd])]; omega_using [])
    (by rw [loc_nat hp (d := d) (by omega_using [hd])]; omega_using [hd])⟩

theorem loc_in' {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions (s.rd ++ s.wr) (State.addr (E s₀ + BitVec.ofNat 32 d)) 4 :=
  let ⟨r, hr, hc⟩ := loc_in hp h hd
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- What lies above the locals is outside the body's regions. -/
theorem above_disj {a : BitVec 32} {n : Nat} (ha : (E s₀).toNat + 144 ≤ a.toNat)
    (ha' : a.toNat + n ≤ (E0 s₀).toNat + 56)
    (hm : Region.Disjoint ⟨State.addr a, n⟩ (memR s₀)) (hs : Region.Disjoint ⟨State.addr a, n⟩ (scrR s₀))
    (ho : Region.Disjoint ⟨State.addr a, n⟩ (outR s₀)) :
    ∀ r ∈ bodyW s₀, Region.Disjoint ⟨State.addr a, n⟩ r := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := E_nat hp
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hm
  · exact hs
  · exact ho
  · exact disj32 (.inr (by omega_using [ha])) (by omega_arith) (by omega_using [hE])
  · show Region.Disjoint _ ⟨State.addr (E s₀) - BitVec.ofNat 64 40, 40⟩
    rw [← addr_sub' (by omega_arith)]
    exact disj32 (.inr (by rw [sub_toNat' (by omega_arith)]; omega_using [ha])) (by omega_arith)
      (by rw [sub_toNat' (by omega_arith)]; omega_using [])

/-! ## The frames' words -/

theorem S1_nat : (pushed argRegs s₀).sp.toNat = (E0 s₀).toNat - 16 := sp1 (by have := hp.sp_lo; omega_using [this])

/-- What the first push leaves above `E0 - 16`, and the memory above it. -/
theorem entry_frame : Frame [stkR (E0 s₀) 56] s₀.mem (entry s₀).mem := by
  have := hp.sp_lo
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  have s1 := S1_nat hp
  have f₁ := VG.Proof.Argon2.Arm.pushed_stk (rs := argRegs) (s := s₀) (by simp only [List.length_cons, List.length_nil]; omega_using [this, e0])
  have f₂ := VG.Proof.Argon2.Arm.pushed_stk (rs := savedRegs) (s := pushed argRegs s₀) (by simp only [List.length_cons, List.length_nil]; omega_using [this, s1])
  refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, VG.Proof.Argon2.Arm.stkR_sub (by simp) (by omega_using [this, e0])⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    have := VG.Proof.Argon2.Arm.stkR_inner (sp := E0 s₀) (a := 4 * savedRegs.length) (k := 16) (b := 56)
      (by simp) (by omega_using [this])
    simpa [pushed_sp] using this

/-- Word `j` of the second frame: `savedRegs[j]`. -/
theorem entry_saved {j : Nat} (hj : j < 10) :
    (entry s₀).mem.readW (State.addr (E s₀ + BitVec.ofNat 32 (144 + 4 * j))) 32 =
      s₀.gpr (savedRegs[j]?.getD .r0) := by
  have := hp.sp_lo; have := hp.sp_hi
  have s1 := S1_nat hp
  have e := E_nat hp
  have := VG.Proof.Argon2.Arm.storeWords_readW (pushed argRegs s₀).mem
    ((pushed argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length))
    (savedRegs.map (pushed argRegs s₀).gpr) (by
      simp only [List.length_map, List.length_cons, List.length_nil]
      rw [sub_toNat' (by rw [s1]; omega_arith), s1]; omega_using []) (i := j) (by simpa using hj)
  rw [List.getElem_map] at this
  have ea : (pushed argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length) + BitVec.ofNat 32 (4 * j) =
      E s₀ + BitVec.ofNat 32 (144 + 4 * j) := by
    apply BitVec.eq_of_toNat_eq
    rw [loc_nat hp (d := 144 + 4 * j) (by omega_using [hj]), BitVec.toNat_add, sub_toNat' (by simp only [List.length_cons, List.length_nil]; rw [s1]; omega_arith), s1, BitVec.toNat_ofNat]
    simp only [List.length_cons, List.length_nil]
    rw [Nat.mod_eq_of_lt (a := 4 * j) (by omega_using [hj]), Nat.mod_eq_of_lt (by omega_using [hj])]
    omega_arith
  rw [ea] at this
  refine this.trans ?_
  simp only [pushed_gpr, List.getElem?_eq_getElem (show j < savedRegs.length by simpa using hj),
    Option.getD_some]

/-- Word `i` of the first frame: register argument `i`. -/
theorem entry_regArg {i : Nat} (hi : i < 4) :
    (entry s₀).mem.readW (State.addr (E s₀ + BitVec.ofNat 32 (184 + 4 * i))) 32 = arg s₀ i := by
  have := hp.sp_lo; have := hp.sp_hi
  have s1 := S1_nat hp
  have e := E_nat hp
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  have := VG.Proof.Argon2.Arm.storeWords_readW s₀.mem (s₀.sp - BitVec.ofNat 32 (4 * argRegs.length))
    (argRegs.map s₀.gpr) (by
      simp only [List.length_map, List.length_cons, List.length_nil]
      rw [sub_toNat' (by omega_arith)]; omega_using []) (i := i) (by simpa using hi)
  rw [List.getElem_map] at this
  have ea : s₀.sp - BitVec.ofNat 32 (4 * argRegs.length) + BitVec.ofNat 32 (4 * i) =
      E s₀ + BitVec.ofNat 32 (184 + 4 * i) := by
    apply BitVec.eq_of_toNat_eq
    rw [loc_nat hp (d := 184 + 4 * i) (by omega_using [hi]), BitVec.toNat_add, sub_toNat' (by simp only [List.length_cons, List.length_nil]; omega_arith), BitVec.toNat_ofNat]
    simp only [List.length_cons, List.length_nil]
    rw [Nat.mod_eq_of_lt (a := 4 * i) (by omega_using [hi]), Nat.mod_eq_of_lt (by omega_using [hi])]
    omega_arith
  rw [ea] at this
  -- The second push and the allocation keep the first frame.
  have keep : (entry s₀).mem.readW (State.addr (E s₀ + BitVec.ofNat 32 (184 + 4 * i))) 32 =
      (pushed argRegs s₀).mem.readW (State.addr (E s₀ + BitVec.ofNat 32 (184 + 4 * i))) 32 := by
    refine (VG.Proof.Argon2.Arm.pushed_stk (rs := savedRegs) (s := pushed argRegs s₀) (by simp only [List.length_cons, List.length_nil]; omega_arith)).readW
      (r := ⟨_, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    have tS : ((pushed argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length)).toNat = (E0 s₀).toNat - 56 := by
      rw [sub_toNat' (by simp only [List.length_cons, List.length_nil]; omega_arith), s1]
      simp only [List.length_cons, List.length_nil]; omega_using []
    have tL : (E s₀ + BitVec.ofNat 32 (184 + 4 * i)).toNat = (E s₀).toNat + (184 + 4 * i) := loc_nat hp (by omega_using [hi])
    show Region.Disjoint _ ⟨State.addr (pushed argRegs s₀).sp - BitVec.ofNat 64 (4 * savedRegs.length), _⟩
    rw [← addr_sub' (by simp only [List.length_cons, List.length_nil]; omega_arith)]
    have hc : savedRegs.length = 10 := rfl
    exact disj32 (.inr (by rw [tS, tL]; omega_using [e, hc])) (by rw [tL]; omega_using [hi, e]) (by rw [tS]; omega_using [hc])
  refine keep.trans (this.trans ?_)
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The stack arguments, above the frames, are as on entry. -/
theorem entry_stackArg {i : Nat} (hi : 4 ≤ i) (hi' : i < 18) :
    (entry s₀).mem.readW (State.addr (E s₀ + BitVec.ofNat 32 (184 + 4 * i))) 32 = arg s₀ i := by
  have := hp.sp_lo; have := hp.sp_hi
  have e := E_nat hp
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 4 := ⟨i - 4, by omega_using [hi]⟩
  have ea : E s₀ + BitVec.ofNat 32 (184 + 4 * (k + 4)) = s₀.sp + BitVec.ofNat 32 (4 * k) := by
    apply BitVec.eq_of_toNat_eq
    rw [loc_nat hp (d := 184 + 4 * (k + 4)) (by omega_using [hi']), add_nat (x := s₀.sp) (k := 4 * k) (by omega_arith)]; omega_arith
  rw [ea, (entry_frame hp).readW (r := ⟨_, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
  · rfl
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  show Region.Disjoint _ ⟨State.addr (E0 s₀) - BitVec.ofNat 64 56, 56⟩
  rw [← addr_sub' (by omega_arith)]
  exact disj32 (.inr (by rw [sub_toNat' (by omega_arith), add_nat (x := s₀.sp) (k := 4 * k) (by omega_arith)]; omega_arith)) (by rw [add_nat (x := s₀.sp) (k := 4 * k) (by omega_arith)]; omega_arith)
    (by rw [sub_toNat' (by omega_arith)]; omega_using [])

/-! ## What the body keeps -/

theorem Inv.done {s : State} (h : Inv s₀ s) : BodyDone s₀ s := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := E_nat hp
  refine ⟨h.sp, fun j hj => ?_⟩
  have st := frame_stk hp (d := 148 + 4 * j) (n := 4) (by omega_using [hj])
  rw [h.frame.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
  · rw [show 148 + 4 * j = 144 + 4 * (j + 1) by omega_using [], entry_saved hp (by omega_using [hj])]
  refine above_disj hp (by rw [loc_nat hp (d := 148 + 4 * j) (by omega_using [hj])]; omega_using []) (by rw [loc_nat hp (d := 148 + 4 * j) (by omega_using [hj])]; omega_arith) ?_ ?_ ?_
  · exact ((hp.stk_all _ (by simp)).sub_left st)
  · exact ((hp.stk_all _ (by simp)).sub_left st)
  · exact ((hp.stk_all _ (by simp)).sub_left st)

/-- The word of argument `i`, above the locals. -/
theorem arg_disj {i : Nat} (hi : i < 18) :
    ∀ r ∈ bodyW s₀, Region.Disjoint
      ⟨State.addr (E s₀ + BitVec.ofNat 32 (Impl.Argon2.Arm.Derive.argOff i)), 4⟩ r := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := E_nat hp
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]
  refine above_disj hp (by rw [loc_nat hp (d := 144 + 40 + 4 * i) (by omega_using [hi])]; omega_using []) (by rw [loc_nat hp (d := 144 + 40 + 4 * i) (by omega_using [hi])]; omega_arith) ?_ ?_ ?_
    <;> by_cases h4 : i < 4
  all_goals first
    | (have st := frame_stk hp (d := 184 + 4 * i) (n := 4) (by omega_using [h4])
       exact (hp.stk_all _ (by simp)).sub_left st)
    | (have sa : Region.Sub ⟨State.addr (E s₀ + BitVec.ofNat 32 (144 + 40 + 4 * i)), 4⟩ (argR s₀) := by
         show Region.Sub _ ⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 56⟩
         exact sub32 (by rw [loc_nat hp (d := 144 + 40 + 4 * i) (by omega_using [hi]), add_nat (x := s₀.sp) (k := 4 * 0) (by omega_using [])]; omega_using [hE, e0, h4])
           (by rw [loc_nat hp (d := 144 + 40 + 4 * i) (by omega_using [hi]), add_nat (x := s₀.sp) (k := 4 * 0) (by omega_using [])]; omega_arith)
       exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sa)

theorem Inv.arg {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    lw s₀ s (Impl.Argon2.Arm.Derive.argOff i) = arg s₀ i := by
  rw [lw, h.frame.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) (arg_disj hp hi) (by decide)]
  simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]
  rw [show 144 + 40 + 4 * i = 184 + 4 * i by omega_using []]
  by_cases h4 : i < 4
  · exact entry_regArg hp h4
  · exact entry_stackArg hp (by omega_using [h4]) hi

theorem Inv.arg_in {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    InRegions (s.rd ++ s.wr) (State.addr (E s₀ + BitVec.ofNat 32 (Impl.Argon2.Arm.Derive.argOff i))) 4 := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := E_nat hp
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  have s1 := S1_nat hp
  simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]
  rw [h.rd, h.wr]
  by_cases h4 : i < 4
  · -- The first frame, writable.
    refine ⟨⟨State.addr (s₀.sp - BitVec.ofNat 32 (4 * argRegs.length)), 4 * argRegs.length⟩,
      List.mem_append_right _ (by simp [entry, allocated, pushed]), ?_⟩
    have tA : (s₀.sp - BitVec.ofNat 32 (4 * argRegs.length)).toNat = (E0 s₀).toNat - 16 := by
      rw [sub_toNat' (by simp only [List.length_cons, List.length_nil]; omega_arith)]
      simp only [List.length_cons, List.length_nil]
    have tL : (E s₀ + BitVec.ofNat 32 (144 + 40 + 4 * i)).toNat = (E s₀).toNat + (144 + 40 + 4 * i) :=
      loc_nat hp (by omega_using [h4])
    exact contains32 (by rw [tL, tA]; omega_using [hE]) (by rw [tL, tA]; simp only [List.length_cons, List.length_nil]; omega_arith)
  · refine ⟨argR s₀, List.mem_append_left _ (by rw [hp.rd]; simp), ?_⟩
    show Region.Contains ⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 56⟩ _ _
    exact contains32 (by rw [loc_nat hp (d := 144 + 40 + 4 * i) (by omega_using [hi]), add_nat (x := s₀.sp) (k := 4 * 0) (by omega_using [])]; omega_using [hE, e0, h4])
      (by rw [loc_nat hp (d := 144 + 40 + 4 * i) (by omega_using [hi]), add_nat (x := s₀.sp) (k := 4 * 0) (by omega_using [])]; omega_arith)

/-- The inputs are kept. -/
theorem Inv.input {s : State} (h : Inv s₀ s) {R : Region}
    (hR : R ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀]) :
    bytesAt s.mem R.base R.len = bytesAt s₀.mem R.base R.len := by
  have hR' : R ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> simp
  have hS : R ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> simp
  have stk := (hp.stk_all R hS).symm
  have hl : R.len ≤ 2 ^ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> exact Nat.le_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))
  have hlo := hp.sp_lo
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  rw [h.frame.bytes (R := R) (fun r hr => ?_) hl hi]
  · exact (entry_frame hp).bytes (R := R) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact stk.sub_right (VG.Proof.Argon2.Arm.stkR_sub (by decide) (by omega_using [hlo]))) hl hi
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact stk.sub_right (by simpa using frame_stk hp (d := 0) (n := 144) (by decide))
  · exact stk.sub_right (call_stk hp)

end

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: the derivation's locals

`lw s₀ s d`: the word at `[r11, #d]` in the body. A store to the locals keeps
the invariant and every other word (`Inv.store_loc`); writes to the memory
matrix, `scratch`, the output or the stack below the locals keep all of them
(`lw_keep`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Argon2.Arm (stkR addr_toNat)
open VG.Proof.MdStream.Arm (Upd Mupd wp_ldr wp_str)
open VG.Impl.Argon2.Arm.Derive (ld st)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem loc_addr {d : Nat} (hd : d < 256) :
    State.addr (E s₀ + BitVec.ofNat 32 d) = State.addr (E s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := E_hi hp; omega_using [hd, this])

/-- Another word of the frame, after a store to the locals. -/
theorem lw_store {m : Mem} {d e : Nat} (hd : d + 4 ≤ 256) (he : e + 4 ≤ 256) (hde : d + 4 ≤ e ∨ e + 4 ≤ d)
    (v : BitVec 32) :
    (m.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v).readW (State.addr (E s₀ + BitVec.ofNat 32 e)) 32 =
      m.readW (State.addr (E s₀ + BitVec.ofNat 32 e)) 32 := by
  rw [loc_addr hp (by omega_using [hd]), loc_addr hp (by omega_using [he])]
  exact MdStream.Arm.readW_writeW_save m _ v (by omega_using [he]) (by omega_using [hd]) (by omega_using [hde])

theorem Inv.store_loc {s t : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {v : BitVec 32}
    (u : Mupd s t (s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v)) :
    Inv s₀ t ∧ lw s₀ t d = v ∧ ∀ e, e + 4 ≤ 256 → (d + 4 ≤ e ∨ e + 4 ≤ d) → lw s₀ t e = lw s₀ s e := by
  refine ⟨h.step u.sp (by rw [u.gpr]) u.rd u.wr ?_, ?_, fun e he hde => ?_⟩
  · rw [u.mem]
    exact (Frame.refl _ _).writeW (r := locR s₀) (by simp) v
      (contains32 (by rw [loc_nat hp (d := d) (by omega_using [hd])]; omega_using []) (by rw [loc_nat hp (d := d) (by omega_using [hd])]; omega_using [hd]))
  · show t.mem.readW _ 32 = v
    rw [u.mem, Mem.readW_writeW_self32]
  · show t.mem.readW _ 32 = _
    rw [u.mem, lw_store hp (by omega_using [hd]) he hde]

/-- `str r, [r11, #d]` -/
theorem wp_stloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → lw s₀ t d = s.gpr r → (∀ e, e + 4 ≤ 256 → (d + 4 ≤ e ∨ e + 4 ≤ d) →
      lw s₀ t e = lw s₀ s e) → t.gpr = s.gpr → t.mem = s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 d))
      (s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (st d r :: is)) s Q :=
  wp_str (by omega_using [hd]) (by rw [h.r11]) (loc_in hp h hd) fun t u =>
    let ⟨i, v, o⟩ := h.store_loc hp hd u
    k t i v o u.gpr u.mem

/-- `ldr r, [r11, #d]` -/
theorem wp_ldloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (lw s₀ s d) → WP isa (.block is) t Q) :
    WP isa (.block (ld r d :: is)) s Q :=
  wp_ldr (by omega_using [hd]) (by rw [h.r11]) (loc_in' hp h hd) k

/-- `ldr r, [r11, #argOff i]` -/
theorem wp_ldarg {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (ld r (Impl.Argon2.Arm.Derive.argOff i) :: is)) s Q :=
  wp_ldr (by simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]; omega_using [hi]) (by rw [h.r11])
    (h.arg_in hp hi) fun t u => k t (by have := h.arg hp hi; simp only [lw] at this; rw [this] at u; exact u)

/-- The locals are outside the memory matrix, `scratch`, the output and the stack below them. -/
theorem loc_disj {d : Nat} (hd : d + 4 ≤ 144) :
    ∀ r ∈ [memR s₀, scrR s₀, outR s₀, callR s₀],
      Region.Disjoint ⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩ r := by
  have := hp.sp_lo
  have hE := E_nat hp
  have sub := frame_stk hp (d := d) (n := 4) (by omega_using [hd])
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · show Region.Disjoint _ ⟨State.addr (E s₀) - BitVec.ofNat 64 40, 40⟩
    rw [← addr_sub' (by omega_using [this, hE])]
    exact disj32 (.inr (by rw [sub_toNat' (by omega_using [this, hE]), loc_nat hp (d := d) (by omega_using [hd])]; omega_using [this, hE]))
      (by rw [loc_nat hp (d := d) (by omega_using [hd])]; have := E_hi hp; omega_using [hd, hE]) (by rw [sub_toNat' (by omega_using [this, hE])]; omega_using [])

/-- The locals are kept by writes outside them. -/
theorem lw_keep {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r') {d : Nat}
    (hd : d + 4 ≤ 144) : lw s₀ t d = lw s₀ s d :=
  (f.sub hs).readW (Region.contains_self _ _) (loc_disj hp hd) (by decide)

end

/-- The body's first instruction points `r11` to the locals. -/
theorem inv_start {s₀ : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = (entry s₀).mem → (∀ r, r ≠ .r11 → t.gpr r = (entry s₀).gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (.addSp .r11 0 :: is)) (entry s₀) Q := by
  refine MdStream.Arm.WP.cons (s' := (entry s₀).setReg .r11 ((entry s₀).sp + BitVec.ofNat 32 0)) (by
    simp [exec]) ?_
  have u := MdStream.Arm.Upd.setReg (entry s₀) .r11 ((entry s₀).sp + BitVec.ofNat 32 0)
  have esp : (entry s₀).sp = E s₀ := entry_sp' s₀
  refine k _ ⟨by rw [u.sp, esp], by rw [u.gpr, esp]; simp, by rw [u.rd, entry_rd], by rw [u.wr],
    by rw [u.mem]; exact Frame.refl _ _⟩ u.mem u.other

end VG.Proof.Argon2.Arm.Derive
