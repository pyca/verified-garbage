module

public import VerifiedGarbage.Proof.Argon2.Initial
public import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Finish
import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Blake2.Arm.Stream.Update
import VerifiedGarbage.Proof.Argon2.Divide
public import VerifiedGarbage.Impl.Argon2.Arm.Divide
public import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Blake2.Stream
public import VerifiedGarbage.Impl.Argon2.Arm.Derive
public import VerifiedGarbage.Proof.Argon2.Arm.Push
public import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Argon2.Arm.CompressLit
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Frame

/-! ### `Argon2.Arm.Derive.Scratch`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.Derive.Locals`, which this module and modules that import it used -/

section

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
  refine WP.frame (rs := argRegs) (r := .r0) (by decide) (by simp only [List.length_cons, List.length_nil]; omega_arith)
    (by decide) ?_
  refine WP.frame (rs := savedRegs) (r := .r3) (by decide)
    (by rw [h1]; simp only [List.length_cons, List.length_nil]; omega_arith) (by decide) ?_
  refine WP.seq (WP.alloc (by decide) (by rw [h2]; show 144 ≤ _; omega_arith)
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

end

end

/-!
# Argon2 on ARMv7: the derivation's use of H′'s hash macros

The H₀ code calls the BLAKE2b functions through H′'s macros
(`Impl.Argon2.Arm.HPrime`), with `r4` pointing to `scratch` and the stack
below the locals: `ctx` gives their context (`HPrime.Ctx`), and `Inv.keeps`
the body's invariant and locals after them.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Argon2.Arm (stkR)
open VG.Proof.MdStream.Arm (Upd Mupd)
open VG.Proof.Argon2.Arm.HPrime (Ctx Keeps)

/-- `n` bytes of `scratch` at offset `d`. -/
theorem scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 16384) :
    Region.Sub ⟨State.addr (scrP s₀) + BitVec.ofNat 64 d, n⟩ (scrR s₀) := Offset.sub_base _ h

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_mem : scrR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)
theorem mem_mem : memR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)
theorem out_mem : outR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)

/-- The 32 bytes below the locals that H′'s macros use are within the stack below them. -/
theorem stk32_call : Region.Sub (stkR (E s₀) 32) (callR s₀) :=
  VG.Proof.Argon2.Arm.stkR_sub (by decide) (by rw [E_nat hp]; have := hp.sp_lo; omega_using [this])

theorem ctx {s : State} (h : Inv s₀ s) (hb : s.gpr .r4 = scrP s₀) : Ctx (scrP s₀) (E s₀) s := by
  have := hp.scr_fits
  refine ⟨hb, h.sp, by omega_using [this], by rw [E_nat hp]; have := hp.sp_lo; omega_using [this], ?_, ?_⟩
  · rw [h.wr]
    exact (Covers.of_sub (rs' := [scrR s₀]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
      (fun a n ⟨r, hr, hc⟩ => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact scr_mem hp, hc⟩)
  · exact ((hp.stk_all (scrR s₀) (by simp)).sub_left fun a ha => call_stk hp a (stk32_call hp a ha)).sub_right
      (Region.sub_prefix (by decide))

/-- What H′'s macros keep keeps the body's invariant and the locals. -/
theorem Inv.keeps {s t : State} (h : Inv s₀ s) (k : Keeps (scrP s₀) (E s₀) s t) :
    Inv s₀ t ∧ ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d := by
  have sub : ∀ r ∈ [(⟨State.addr (scrP s₀), 832⟩ : Region), stkR (E s₀) 32],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨callR s₀, by simp, stk32_call hp⟩
  refine ⟨h.step k.sp (k.gpr _ (by decide)) k.rd k.wr (k.frame.sub fun r hr => ?_),
    fun d hd => lw_keep hp k.frame sub hd⟩
  obtain ⟨r', hr', hs⟩ := sub r hr
  refine ⟨r', ?_, hs⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl <;> simp

end

/-! ## The hash macros, with `Keeps` -/

section
open VG.Spec.Blake2

variable {B SP : BitVec 32} {s : State} (c : Ctx B SP s)
include c

theorem init_k {n : Nat} (hn : s.gpr .r1 = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa Impl.Argon2.Arm.HPrime.init s fun t =>
      Repr b (Spec.Blake2.init b n 0) t.mem (State.addr B) [] ∧ Keeps B SP s t :=
  (HPrime.init_ok c hn hn₁ hn₂).mono fun t ⟨r, cs, rd, wr, sp, f⟩ =>
    ⟨r, Keeps.of_call cs sp rd wr f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩⟩

theorem update_k {D : BitVec 32} {L : Nat}
    (hD : s.gpr .r9 = D) (hL : (s.gpr .r10).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨State.addr D, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨State.addr D, L⟩ ⟨State.addr B, 768⟩)
    (hDk : (stkR SP 32).Disjoint ⟨State.addr D, L⟩)
    {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (State.addr B) d)
    (hc : s.gpr .r3 ++ s.gpr .r2 = BitVec.ofNat 64 d.length) (hlen : d.length + L < 2 ^ 64) :
    WP isa Impl.Argon2.Arm.HPrime.update s fun t =>
      Repr b h0 t.mem (State.addr B) (d ++ bytesAt s.mem (State.addr D) L) ∧ Keeps B SP s t :=
  (HPrime.update_ok c hD hL hDfit hDc hDs hDk repr hc hlen).mono fun t ⟨r, cs, rd, wr, sp, f⟩ =>
    ⟨r, Keeps.of_call cs sp rd wr f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩⟩

theorem finalize_k {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (State.addr B) d)
    (hc : s.gpr .r3 ++ s.gpr .r2 = BitVec.ofNat 64 d.length) (hlen : d.length < 2 ^ 64) :
    WP isa Impl.Argon2.Arm.HPrime.finalize s fun t =>
      bytesAt t.mem (State.addr B + 768) 64 = finalHash b h0 d ∧ Keeps B SP s t :=
  (HPrime.finalize_ok c repr hc hlen).mono fun t ⟨dg, cs, rd, wr, sp, f⟩ =>
    ⟨dg, Keeps.of_call cs sp rd wr f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩⟩

end

end VG.Proof.Argon2.Arm.Derive

end

end

/-! ### `Argon2.Arm.Derive.Parameters`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.Divide`, which only this module used -/

section

/-!
# Fixed-time division on ARMv7

`code_ok`: `Impl.Argon2.Arm.Divide.code` leaves `n / D` in `r1` and `n mod D`
in `r0`, for the numerator `n` in `r1` and the divisor `D` in `r2`,
`0 < D < 2³¹`. After `k` bits (`bits_ok`) `r1` holds the `32 - k` bits of `n`
not yet consumed above the quotient of the `k` consumed ones, and `r0` their
remainder: each bit is one step of binary long division
(`Proof.Argon2.divide_step`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Divide

open VG VG.Arm
open VG.Impl.Argon2.Arm.Divide (bit bits code)
open VG.Proof.MdStream.Arm (Upd WP.cons wp_mov wp_add wp_sub wp_and op2_reg op2_imm)
open VG.Proof.Blake2.Arm.Stream (wp_adds wp_adc)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `subs`, and its carry: no borrow. -/
theorem wp_subsC {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.c = decide (y.toNat ≤ (s.gpr n).toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp [reduceExec, ho])
    (k _ (Upd.subs _ _ _ _ _) rfl)

end

/-- Only `r0`, `r1`, `r3` and the flags change. -/
structure Keep (s t : State) : Prop where
  other : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s t u : State} (h : Keep s t) (h' : Keep t u) : Keep s u :=
  ⟨fun r a b c => (h'.other r a b c).trans (h.other r a b c), h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem Keep.of_upd {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v)
    (hd : d = .r0 ∨ d = .r1 ∨ d = .r3) : Keep s t :=
  ⟨fun r a b c => u.other r (by rcases hd with rfl | rfl | rfl <;> with_reducible assumption), u.mem, u.rd, u.wr, u.sp⟩

/-- The numbers after `k` bits of `n`. -/
def Stage (n D k : Nat) (s : State) : Prop :=
  (s.gpr .r1).toNat = (n % 2 ^ (32 - k)) * 2 ^ k + n / 2 ^ (32 - k) / D ∧
    (s.gpr .r0).toNat = n / 2 ^ (32 - k) % D

/-- One bit. -/
theorem bit_ok {s : State} {D : BitVec 32} (hD : 0 < D.toNat) (hD2 : D.toNat < 2 ^ 31)
    (hb : s.gpr .r2 = D) {n k : Nat} (hn : n < 2 ^ 32) (hk : k < 32)
    (h : Stage n D.toNat k s) {is : List Instr} {Q : State → Prop}
    (hq : ∀ t, Stage n D.toNat (k + 1) t → Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (bit ++ is)) s Q := by
  obtain ⟨hc, ha⟩ := h
  obtain hm : k + (31 - k) = 31 := by omega_using [hk]
  obtain pos : ∀ j, 0 < 2 ^ j := fun j => Nat.two_pow_pos j
  obtain e32 : 32 - k = 31 - k + 1 := by omega_using [hk]
  obtain p31 : 2 ^ (31 - k) * 2 ^ k = 2 ^ 31 := by rw [← Nat.pow_add, Nat.add_comm, hm]
  obtain hRlt : n % 2 ^ (32 - k) < 2 ^ (32 - k) := Nat.mod_lt _ (pos _)
  obtain hRb := (Nat.div_add_mod' (n % 2 ^ (32 - k)) (2 ^ (31 - k))).symm
  obtain hb1 : n % 2 ^ (32 - k) / 2 ^ (31 - k) ≤ 1 := by
    obtain h' : 2 ^ (32 - k) = 2 ^ (31 - k) * 2 := by rw [e32, Nat.pow_succ]
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega_using [h', hRlt]))
  obtain hR'lt : n % 2 ^ (32 - k) % 2 ^ (31 - k) < 2 ^ (31 - k) := Nat.mod_lt _ (pos _)
  obtain hqlt : n / 2 ^ (32 - k) / D.toNat < 2 ^ k := by
    refine Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.div_lt_of_lt_mul ?_)
    rw [← Nat.pow_add, show 32 - k + k = 32 by omega_using [hk]]; exact hn
  obtain hrlt : n / 2 ^ (32 - k) % D.toNat < D.toNat := Nat.mod_lt _ hD
  -- Abbreviations, as numbers.
  generalize hN : n / 2 ^ (32 - k) = N at hc ha hqlt hrlt
  generalize hRR : n % 2 ^ (32 - k) = R at hc hRlt hRb hb1 hR'lt
  generalize hbb : R / 2 ^ (31 - k) = b at hRb hb1
  generalize hR' : R % 2 ^ (31 - k) = R' at hRb hR'lt
  -- The next stage's numbers.
  obtain N' : n / 2 ^ (32 - (k + 1)) = 2 * N + b := by
    rw [← hN, ← hbb, ← hRR, show 32 - (k + 1) = 31 - k by omega_using [hk], e32, Nat.pow_succ,
      Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (n / 2 ^ (31 - k)) 2
    omega_using [this]
  obtain R'' : n % 2 ^ (32 - (k + 1)) = R' := by
    rw [← hR', ← hRR, show 32 - (k + 1) = 31 - k by omega_using [hk], e32, Nat.pow_succ, Nat.mod_mul_right_mod]
  obtain step := Proof.Argon2.divide_step (n := N) (d := D.toNat) (q := N / D.toNat) (r := N % D.toNat)
    (bit := b) (Nat.div_add_mod' N _).symm hrlt hb1
  dsimp only at step
  obtain ⟨st₁, st₂⟩ := step
  obtain res := Proof.Argon2.divide_result hD st₁ st₂
  -- The instructions, with `K = 2 ^ k` and `P = R' · K`.
  obtain pk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  obtain hP : R' * 2 ^ (k + 1) = 2 * (R' * 2 ^ k) := by rw [pk, Nat.mul_left_comm]
  obtain hPb : R' * 2 ^ k + 2 ^ k ≤ 2 ^ 31 := by
    have := Nat.mul_le_mul_right (2 ^ k) (show R' + 1 ≤ 2 ^ (31 - k) by omega_using [hR'lt])
    rw [Nat.add_mul, Nat.one_mul, p31] at this
    exact this
  obtain hr1 : (s.gpr .r1).toNat = b * 2 ^ 31 + R' * 2 ^ k + N / D.toNat := by
    rw [hc, hRb, Nat.add_mul, Nat.mul_assoc, p31]
  generalize hPP : R' * 2 ^ k = P at hP hPb hr1
  generalize hKK : 2 ^ k = K at hPb hqlt pk
  simp only [bit, List.cons_append, List.nil_append]
  refine wp_adds (op2_reg _ _) fun s₁ u₁ c₁ => ?_
  obtain cb : s₁.c = decide (b = 1) := by
    rw [c₁, hr1]; rcases (by omega_using [hb1] : b = 0 ∨ b = 1) with rfl | rfl <;> simp <;> omega_using [hD, hD2, hN, ha, hrlt, hc, hPP, hP, hPb, hqlt, N', st₁, st₂, res, hr1]
  obtain v₁ : (s₁.gpr .r1).toNat = 2 * P + 2 * (N / D.toNat) := by
    rw [u₁.gpr, BitVec.toNat_add, hr1]
    rcases (by omega_using [hb1] : b = 0 ∨ b = 1) with rfl | rfl
    · rw [Nat.mod_eq_of_lt (by omega_using [hPb, hqlt])]; omega_using []
    · rw [show 1 * 2 ^ 31 + P + N / D.toNat + (1 * 2 ^ 31 + P + N / D.toNat) =
        (2 * P + 2 * (N / D.toNat)) + 2 ^ 32 by omega_using [], Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega_using [hPb, hqlt])]
  refine wp_adc (op2_reg _ _) fun s₂ u₂ _ => ?_
  obtain v₂ : (s₂.gpr .r0).toNat = 2 * (N % D.toNat) + b := by
    rw [u₂.gpr, u₁.other _ (by decide), cb, BitVec.toNat_add, BitVec.toNat_add, ha]
    rcases (by omega_using [hb1] : b = 0 ∨ b = 1) with rfl | rfl <;> simp <;> omega_using [hrlt, hD2]
  refine wp_subsC (op2_reg _ _) fun s₃ u₃ c₃ => ?_
  obtain d₂ : s₂.gpr .r2 = D := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb]
  rw [d₂] at u₃ c₃
  rw [v₂] at c₃
  refine wp_adc (op2_imm (by decide)) fun s₄ u₄ _ => ?_
  -- The quotient bit.
  generalize ht : (if 2 * (N % D.toNat) + b < D.toNat then 0 else 1) = t
  obtain ht1 : t ≤ 1 := by rw [← ht]; split <;> omega_using []
  obtain v₄ : (s₄.gpr .r1).toNat = 2 * P + 2 * (N / D.toNat) + t := by
    rw [u₄.gpr, c₃, u₃.other _ (by decide), u₂.other _ (by decide), BitVec.toNat_add, BitVec.toNat_add, v₁,
      ← ht]
    by_cases hv : 2 * (N % D.toNat) + b < D.toNat
    · simp only [hv, ite_true, show ¬ D.toNat ≤ 2 * (N % D.toNat) + b by omega_using [hv], decide_false,
        Bool.false_eq_true, ite_false]
      simp; omega_using [hPb, hqlt]
    · simp only [hv, ite_false, show D.toNat ≤ 2 * (N % D.toNat) + b by omega_using [hv], decide_true, ite_true]
      simp; omega_using [hPb, hqlt]
  refine wp_and (op2_imm (by decide)) fun s₅ u₅ => ?_
  obtain v₅ : s₅.gpr .r3 = BitVec.ofNat 32 t := by
    apply BitVec.eq_of_toNat_eq
    rw [u₅.gpr, BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, v₄,
      BitVec.toNat_ofNat]
    omega_using [ht1]
  refine wp_sub (op2_imm (by decide)) fun s₆ u₆ => ?_
  refine wp_and (op2_reg _ _) fun s₇ u₇ => ?_
  refine wp_add (op2_reg _ _) fun s₈ u₈ => hq s₈ ⟨?_, ?_⟩ ?_
  · -- `r1`: the remaining bits above the quotient.
    rw [R'', hP, N', ← res.1, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), v₄, ← ht]
    omega_using []
  · -- `r0`: the remainder.
    obtain d₆ : s₆.gpr .r2 = D := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), d₂]
    rw [N', ← res.2, u₈.gpr, u₇.gpr, u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), d₆, v₅,
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, ← ht]
    by_cases hv : 2 * (N % D.toNat) + b < D.toNat
    · simp only [hv, ite_true]
      rw [show BitVec.ofNat 32 0 - 1 = BitVec.allOnes 32 by decide, BitVec.allOnes_and, BitVec.sub_add_cancel,
        v₂]
    · simp only [hv, ite_false]
      rw [show BitVec.ofNat 32 1 - 1 = 0#32 by decide, show (0#32) &&& D = 0#32 by simp, BitVec.add_zero,
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, v₂]; omega_using [hv]), v₂]
  · exact (Keep.of_upd u₁ (by simp)).trans ((Keep.of_upd u₂ (by simp)).trans ((Keep.of_upd u₃ (by simp)).trans
      ((Keep.of_upd u₄ (by simp)).trans ((Keep.of_upd u₅ (by simp)).trans ((Keep.of_upd u₆ (by simp)).trans
        ((Keep.of_upd u₇ (by simp)).trans (Keep.of_upd u₈ (by simp))))))))

theorem bits_ok {D : BitVec 32} (hD : 0 < D.toNat) (hD2 : D.toNat < 2 ^ 31) {n : Nat}
    (hn : n < 2 ^ 32) {is : List Instr} {Q : State → Prop} :
    ∀ k ≤ 32, ∀ s : State, s.gpr .r2 = D → Stage n D.toNat 0 s →
      (∀ t, Stage n D.toNat k t → Keep s t → WP isa (.block is) t Q) →
      WP isa (.block (bits k ++ is)) s Q
  | 0, _, s, _, h, hq => hq s h (Keep.refl s)
  | k + 1, hk, s, hb, h, hq => by
    simp only [bits, List.append_assoc]
    refine bits_ok hD hD2 hn k (by omega_using [hk]) s hb h fun t ht kt => ?_
    refine bit_ok hD hD2 (by rw [kt.other _ (by decide) (by decide) (by decide), hb]) hn (by omega_using [hk]) ht
      fun u hu ku => hq u hu (kt.trans ku)

/-- The division: `r1 := n / D`, `r0 := n mod D`. -/
theorem code_ok {s : State} {D : BitVec 32} (hD : 0 < D.toNat) (hD2 : D.toNat < 2 ^ 31)
    (hb : s.gpr .r2 = D) {is : List Instr} {Q : State → Prop}
    (hq : ∀ t, (t.gpr .r1).toNat = (s.gpr .r1).toNat / D.toNat →
      (t.gpr .r0).toNat = (s.gpr .r1).toNat % D.toNat → Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (code ++ is)) s Q := by
  obtain hn := (s.gpr .r1).isLt
  simp only [code, List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine bits_ok hD hD2 hn 32 (Nat.le_refl _) s₁ (by rw [u₁.other _ (by decide), hb]) ⟨?_, ?_⟩
    fun t ⟨hc, ha⟩ kt => ?_
  · rw [u₁.other _ (by decide), Nat.mod_eq_of_lt hn, Nat.div_eq_of_lt hn, Nat.zero_div]; simp
  · rw [u₁.gpr, Nat.div_eq_of_lt hn, Nat.zero_mod]; rfl
  · refine hq t (by rw [hc]; simp [Nat.mod_one]) (by rw [ha]; simp) ((Keep.of_upd u₁ (by simp)).trans kt)

end VG.Proof.Argon2.Arm.Divide

end

end


/-!
# Argon2 on ARMv7: the parameters

`parameters_ok`: the body's first instructions point `r11` to the locals and
store there `4 · lanes` (the divisor), the segment length (by the fixed-time
division), the lane length and its size in bytes (`Prm`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov op2_lsl)
open VG.Impl.Argon2.Arm.Derive (parameters divisorOff segLenOff laneLenOff strideOff argOff)

/-- The parameters in the locals. -/
structure Prm (s₀ s : State) : Prop where
  divisor : lw s₀ s divisorOff = BitVec.ofNat 32 (4 * lanesN s₀)
  segLen : lw s₀ s segLenOff = BitVec.ofNat 32 (prm s₀).segmentLen
  laneLen : lw s₀ s laneLenOff = BitVec.ofNat 32 (prm s₀).laneLen
  stride : lw s₀ s strideOff = BitVec.ofNat 32 ((prm s₀).laneLen * 1024)

theorem lw_mem {s₀ s t : State} (h : t.mem = s.mem) (d : Nat) : lw s₀ t d = lw s₀ s d := by
  simp only [lw, h]

theorem Inv.keep {s₀ s t : State} (h : Inv s₀ s) (k : Divide.Keep s t) : Inv s₀ t :=
  h.step k.sp (k.other _ (by decide) (by decide) (by decide)) k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _)

/-- `x << n`, as a number, when it does not overflow. -/
theorem shl_nat {x : BitVec 32} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 32) : (x <<< n).toNat = x.toNat * 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem parameters_ok {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → Prm s₀ t → WP isa (.block is) t Q) :
    WP isa (.block ((.addSp .r11 0 :: parameters) ++ is)) (entry s₀) Q := by
  have hL := hp.lanes_lt
  have hL1 := hp.lanes_pos
  have hBl := hp.blocks_lt
  have hb := hp.blocks_eq
  have hseg := hp.segLen_eq
  have hlane := hp.laneLen_eq
  simp only [parameters, List.cons_append, List.append_assoc]
  refine inv_start fun s₁ i₁ _ _ => ?_
  refine wp_ldarg hp i₁ (i := Impl.Argon2.Arm.Derive.lanesArg) (by decide) fun s₂ u₂ => ?_
  obtain i₂ := i₁.upd u₂ (by decide)
  refine wp_mov (op2_lsl (by decide)) fun s₃ u₃ => ?_
  obtain i₃ := i₂.upd u₃ (by decide)
  obtain e₃ : (s₃.gpr .r2).toNat = 4 * lanesN s₀ := by
    rw [u₃.gpr, u₂.gpr, shl_nat (by have : (arg s₀ 7).toNat < 2 ^ 24 := hL; show (arg s₀ 7).toNat * 4 < _; omega_using [this])]
    show (arg s₀ 7).toNat * 4 = 4 * (arg s₀ 7).toNat
    omega_using []
  refine wp_stloc hp i₃ (d := divisorOff) (by decide) fun s₄ i₄ v₄ _ g₄ _ => ?_
  refine wp_ldarg hp i₄ (i := Impl.Argon2.Arm.Derive.memoryCostArg) (by decide) fun s₅ u₅ => ?_
  obtain i₅ := i₄.upd u₅ (by decide)
  obtain r2₅ : s₅.gpr .r2 = s₃.gpr .r2 := by rw [u₅.other _ (by decide), g₄]
  refine Divide.code_ok (D := s₃.gpr .r2) (by rw [e₃]; omega_using [hL1]) (by rw [e₃]; omega_using [hL]) r2₅ fun s₆ c₆ _ k₆ => ?_
  obtain i₆ := i₅.keep k₆
  rw [u₅.gpr, e₃] at c₆
  obtain c₆' : (s₆.gpr .r1).toNat = (prm s₀).segmentLen := by rw [c₆, hseg]; rfl
  refine wp_stloc hp i₆ (d := segLenOff) (by decide) fun s₇ i₇ v₇ o₇ g₇ _ => ?_
  obtain hll : (prm s₀).laneLen ≤ blocksN s₀ :=
    Nat.le_trans (Nat.le_mul_of_pos_left _ hL1) (Nat.le_of_eq hb.symm)
  obtain hsegL : (prm s₀).laneLen * 1024 + 16384 ≤ 2 ^ 32 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right 1024 hll) _) hBl
  refine wp_mov (op2_lsl (by decide)) fun s₈ u₈ => ?_
  obtain i₈ := i₇.upd u₈ (by decide)
  obtain e₈ : (s₈.gpr .r1).toNat = (prm s₀).laneLen := by
    rw [u₈.gpr, g₇, shl_nat (by rw [c₆']; omega), c₆', hlane]; omega_using []
  refine wp_stloc hp i₈ (d := laneLenOff) (by decide) fun s₉ i₉ v₉ o₉ g₉ _ => ?_
  refine wp_mov (op2_lsl (by decide)) fun s₁₀ u₁₀ => ?_
  obtain i₁₀ := i₉.upd u₁₀ (by decide)
  obtain e₁₀ : (s₁₀.gpr .r1).toNat = (prm s₀).laneLen * 1024 := by
    rw [u₁₀.gpr, g₉, shl_nat (by rw [e₈]; omega_using [hsegL]), e₈]
  refine wp_stloc hp i₁₀ (d := strideOff) (by decide) fun s₁₁ i₁₁ v₁₁ o₁₁ _ _ => k s₁₁ i₁₁ ⟨?_, ?_, ?_, ?_⟩
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, o₉ _ (by decide) (by decide), lw_mem u₈.mem,
      o₇ _ (by decide) (by decide), lw_mem k₆.mem, lw_mem u₅.mem, v₄]
    exact BitVec.eq_of_toNat_eq (by rw [e₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hL])])
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, o₉ _ (by decide) (by decide), lw_mem u₈.mem, v₇]
    exact BitVec.eq_of_toNat_eq (by rw [c₆', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [c₆'])])
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, v₉]
    exact BitVec.eq_of_toNat_eq (by rw [e₈, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hsegL])])
  · rw [v₁₁]
    exact BitVec.eq_of_toNat_eq (by rw [e₁₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hsegL])])

end

end VG.Proof.Argon2.Arm.Derive

end

end

/-!
# Argon2 on ARMv7: H₀

`HI s₀ data s`: the BLAKE2b state at `scratch` has absorbed `data`, whose
length is in the locals. `start_ok` absorbs the header, `absorb_ok` an
input with its length prefix, `finish_ok` writes the digest to the first 64
bytes of the locals: `code_ok`, H₀ (`Spec.Argon2.initialHash`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_ldr wp_str op2_imm op2_reg)
open VG.Proof.Blake2.Arm.Stream (wp_adds wp_adc)
open VG.Spec.Blake2 (Repr b bytesAt)
open VG.Proof.Argon2.Arm.HPrime (Ctx Keeps)
open VG.Impl.Argon2.Arm.Derive (countLoOff countHiOff argOff ld st)

/-- H₀'s streaming state at `scratch`, with `data` absorbed. -/
structure HI (s₀ : State) (data : List Byte) (s : State) : Prop where
  inv : Inv s₀ s
  prm : Prm s₀ s
  r4 : s.gpr .r4 = scrP s₀
  repr : Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (scrP s₀)) data
  lo : lw s₀ s countLoOff = BitVec.ofNat 32 data.length
  hi : lw s₀ s countHiOff = BitVec.ofNat 32 (data.length / 2 ^ 32)
  len : data.length < 2 ^ 36

theorem Prm.of_lw {s₀ s t : State} (pr : Prm s₀ s)
    (h : ∀ d ∈ [Impl.Argon2.Arm.Derive.divisorOff, Impl.Argon2.Arm.Derive.segLenOff,
      Impl.Argon2.Arm.Derive.laneLenOff, Impl.Argon2.Arm.Derive.strideOff], lw s₀ t d = lw s₀ s d) :
    Prm s₀ t :=
  ⟨by rw [h _ (by simp)]; exact pr.divisor, by rw [h _ (by simp)]; exact pr.segLen,
    by rw [h _ (by simp)]; exact pr.laneLen, by rw [h _ (by simp)]; exact pr.stride⟩

/-- The parameters are kept when the locals at the offsets of `prmOk` are. -/
theorem prm_offs : ∀ d ∈ [Impl.Argon2.Arm.Derive.divisorOff, Impl.Argon2.Arm.Derive.segLenOff,
    Impl.Argon2.Arm.Derive.laneLenOff, Impl.Argon2.Arm.Derive.strideOff],
    d + 4 ≤ 144 ∧ 72 ≤ d ∧ (d + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ d) := by decide

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_addr {o : Nat} (ho : o < 16384) :
    State.addr (scrP s₀ + BitVec.ofNat 32 o) = State.addr (scrP s₀) + BitVec.ofNat 64 o :=
  addr_add (by have := hp.scr_fits; omega_arith)

/-- `str r, [r4, #o]`, to `scratch`. -/
theorem wp_stscr {s : State} (h : Inv s₀ s) (hb : s.gpr .r4 = scrP s₀) {o : Nat} (ho : o + 4 ≤ 4096)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = s.mem.writeW (State.addr (scrP s₀) + BitVec.ofNat 64 o) (s.gpr r) →
      t.gpr = s.gpr → (∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d) →
      Frame [⟨State.addr (scrP s₀) + BitVec.ofNat 64 o, 4⟩] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.str r .r4 o :: is)) s Q := by
  obtain hc : (scrR s₀).Contains (State.addr (scrP s₀) + BitVec.ofNat 64 o) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine wp_str (by omega_arith) (by rw [hb, scr_addr hp (by omega_arith)]) (by rw [h.wr]; exact ⟨scrR s₀, scr_mem hp, hc⟩)
    fun t u => ?_
  obtain f : Frame [⟨State.addr (scrP s₀) + BitVec.ofNat 64 o, 4⟩] s.mem t.mem := by
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k t (h.step u.sp (by rw [u.gpr]) u.rd u.wr ?_) u.mem u.gpr
    (fun d hd => lw_keep hp f (fun r hr => ?_) hd) f
  · rw [u.mem]; exact (Frame.refl _ _).writeW (r := scrR s₀) (by simp) _ hc
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, scr_sub (by omega_arith)⟩

omit hp in
/-- A store to `scratch` from offset 192 on keeps the streaming state. -/
theorem repr_store {m m' : Mem} {o : Nat} (ho : 192 ≤ o) (ho' : o + 4 ≤ 16384)
    (f : Frame [⟨State.addr (scrP s₀) + BitVec.ofNat 64 o, 4⟩] m m') {data : List Byte}
    (h : Repr b (Spec.Blake2.init b 64 0) m (State.addr (scrP s₀)) data) :
    Repr b (Spec.Blake2.init b 64 0) m' (State.addr (scrP s₀)) data :=
  HPrime.repr_frame f (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.base_disjoint _ ho (by omega_arith)) h

end

/-- The bytes at `p`: a word, then the rest. -/
theorem bytes_word (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (4 + n) = Spec.Blake2.wordBytes (m.readW p 32) ++ bytesAt m (p + BitVec.ofNat 64 4) n := by
  rw [Proof.Blake2.bytesAt_add, Proof.Blake2.wordBytes_readW (w := 32) m p (.inl rfl)]

theorem variant_code {s₀ : State} (hk : (kindV s₀).toNat ≤ 2) : (prm s₀).variant.code = (kindV s₀).toNat := by
  simp only [prm]
  rcases (by omega_arith : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with h | h | h <;>
    simp [h, Spec.Argon2.Variant.code, Spec.Argon2.params]

theorem le32_arg (x : BitVec 32) : Spec.Argon2.le32 x.toNat = Spec.Blake2.wordBytes x := by
  simp only [Spec.Argon2.le32, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem header_eq : Impl.Argon2.Arm.Derive.header =
    [ld .r0 (argOff 7), .str .r0 .r4 768,
     ld .r0 (argOff 17), .str .r0 .r4 772,
     ld .r0 (argOff 6), .str .r0 .r4 776,
     ld .r0 (argOff 5), .str .r0 .r4 780,
     .mov .r0 (.imm 0x13), .str .r0 .r4 784,
     ld .r0 (argOff 0), .str .r0 .r4 788] := rfl

section
variable {s₀ : State} (hp : DPre s₀)
include hp

omit hp in
/-- A word of `scratch` is kept by a store to another one. -/
theorem scr_keep {m m' : Mem} {o o' : Nat} (ho : o + 4 ≤ 16384) (ho' : o' + 4 ≤ 16384)
    (hd : o + 4 ≤ o' ∨ o' + 4 ≤ o)
    (f : Frame [⟨State.addr (scrP s₀) + BitVec.ofNat 64 o', 4⟩] m m') :
    m'.readW (State.addr (scrP s₀) + BitVec.ofNat 64 o) 32 = m.readW (State.addr (scrP s₀) + BitVec.ofNat 64 o) 32 := by
  refine f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ hd (by omega_arith) (by omega_arith)

/-- The six header words, at `scratch + 768`. -/
theorem header_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) (hb : s.gpr .r4 = scrP s₀)
    (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (scrP s₀)) []) :
    WP isa (.block Impl.Argon2.Arm.Derive.header) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      t.gpr .r4 = scrP s₀ ∧ Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (scrP s₀)) [] ∧
      bytesAt t.mem (State.addr (scrP s₀) + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀) ∧
      ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d := by
  rw [header_eq]
  refine wp_ldarg hp h (i := 7) (by decide) fun s₁ u₁ => ?_
  obtain i₁ := h.upd u₁ (by decide)
  obtain b₁ : s₁.gpr .r4 = scrP s₀ := by rw [u₁.other _ (by decide), hb]
  refine wp_stscr hp i₁ b₁ (o := 768) (by decide) fun s₂ i₂ m₂ g₂ l₂ f₂ => ?_
  obtain b₂ : s₂.gpr .r4 = scrP s₀ := by rw [g₂, b₁]
  refine wp_ldarg hp i₂ (i := 17) (by decide) fun s₃ u₃ => ?_
  obtain i₃ := i₂.upd u₃ (by decide)
  obtain b₃ : s₃.gpr .r4 = scrP s₀ := by rw [u₃.other _ (by decide), b₂]
  refine wp_stscr hp i₃ b₃ (o := 772) (by decide) fun s₄ i₄ m₄ g₄ l₄ f₄ => ?_
  obtain b₄ : s₄.gpr .r4 = scrP s₀ := by rw [g₄, b₃]
  refine wp_ldarg hp i₄ (i := 6) (by decide) fun s₅ u₅ => ?_
  obtain i₅ := i₄.upd u₅ (by decide)
  obtain b₅ : s₅.gpr .r4 = scrP s₀ := by rw [u₅.other _ (by decide), b₄]
  refine wp_stscr hp i₅ b₅ (o := 776) (by decide) fun s₆ i₆ m₆ g₆ l₆ f₆ => ?_
  obtain b₆ : s₆.gpr .r4 = scrP s₀ := by rw [g₆, b₅]
  refine wp_ldarg hp i₆ (i := 5) (by decide) fun s₇ u₇ => ?_
  obtain i₇ := i₆.upd u₇ (by decide)
  obtain b₇ : s₇.gpr .r4 = scrP s₀ := by rw [u₇.other _ (by decide), b₆]
  refine wp_stscr hp i₇ b₇ (o := 780) (by decide) fun s₈ i₈ m₈ g₈ l₈ f₈ => ?_
  obtain b₈ : s₈.gpr .r4 = scrP s₀ := by rw [g₈, b₇]
  refine wp_mov (op2_imm (by decide)) fun s₉ u₉ => ?_
  obtain i₉ := i₈.upd u₉ (by decide)
  obtain b₉ : s₉.gpr .r4 = scrP s₀ := by rw [u₉.other _ (by decide), b₈]
  refine wp_stscr hp i₉ b₉ (o := 784) (by decide) fun s₁₀ i₁₀ m₁₀ g₁₀ l₁₀ f₁₀ => ?_
  obtain b₁₀ : s₁₀.gpr .r4 = scrP s₀ := by rw [g₁₀, b₉]
  refine wp_ldarg hp i₁₀ (i := 0) (by decide) fun s₁₁ u₁₁ => ?_
  obtain i₁₁ := i₁₀.upd u₁₁ (by decide)
  obtain b₁₁ : s₁₁.gpr .r4 = scrP s₀ := by rw [u₁₁.other _ (by decide), b₁₀]
  refine wp_stscr hp i₁₁ b₁₁ (o := 788) (by decide) fun t it mt gt lt ft => WP.block_nil ?_
  -- The locals.
  obtain L : ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d := fun d hd => by
    rw [lt d hd, lw_mem u₁₁.mem, l₁₀ d hd, lw_mem u₉.mem, l₈ d hd, lw_mem u₇.mem, l₆ d hd, lw_mem u₅.mem,
      l₄ d hd, lw_mem u₃.mem, l₂ d hd, lw_mem u₁.mem]
  -- The streaming state.
  obtain R : Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (scrP s₀)) [] := by
    refine repr_store (by decide) (by decide) ft ?_
    rw [u₁₁.mem]; refine repr_store (by decide) (by decide) f₁₀ ?_
    rw [u₉.mem]; refine repr_store (by decide) (by decide) f₈ ?_
    rw [u₇.mem]; refine repr_store (by decide) (by decide) f₆ ?_
    rw [u₅.mem]; refine repr_store (by decide) (by decide) f₄ ?_
    rw [u₃.mem]; refine repr_store (by decide) (by decide) f₂ ?_
    rw [u₁.mem]; exact repr
  refine ⟨it, ⟨?_, ?_, ?_, ?_⟩, by rw [gt, b₁₁], R, ?_, L⟩
  · rw [L _ (by decide)]; exact pr.divisor
  · rw [L _ (by decide)]; exact pr.segLen
  · rw [L _ (by decide)]; exact pr.laneLen
  · rw [L _ (by decide)]; exact pr.stride
  -- The words.
  obtain w0 : t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 768) 32 = arg s₀ 7 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      scr_keep (by decide) (by decide) (by decide) f₈, u₇.mem,
      scr_keep (by decide) (by decide) (by decide) f₆, u₅.mem,
      scr_keep (by decide) (by decide) (by decide) f₄, u₃.mem, m₂, Mem.readW_writeW_self32, u₁.gpr]
  obtain w1 : t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 772) 32 = arg s₀ 17 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      scr_keep (by decide) (by decide) (by decide) f₈, u₇.mem,
      scr_keep (by decide) (by decide) (by decide) f₆, u₅.mem, m₄, Mem.readW_writeW_self32, u₃.gpr]
  obtain w2 : t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 776) 32 = arg s₀ 6 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      scr_keep (by decide) (by decide) (by decide) f₈, u₇.mem, m₆, Mem.readW_writeW_self32, u₅.gpr]
  obtain w3 : t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 780) 32 = arg s₀ 5 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem, m₈, Mem.readW_writeW_self32, u₇.gpr]
  obtain w4 : t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 784) 32 = 0x13 := by
    rw [scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem, m₁₀, Mem.readW_writeW_self32, u₉.gpr]
  obtain w5 : t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 788) 32 = arg s₀ 0 := by
    rw [mt, Mem.readW_writeW_self32, u₁₁.gpr]
  obtain step : ∀ o, State.addr (scrP s₀) + BitVec.ofNat 64 o + BitVec.ofNat 64 4 =
      State.addr (scrP s₀) + BitVec.ofNat 64 (o + 4) := fun o => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show (24 : Nat) = 4 + 20 from rfl, bytes_word, step, show (20 : Nat) = 4 + 16 from rfl, bytes_word, step,
    show (16 : Nat) = 4 + 12 from rfl, bytes_word, step, show (12 : Nat) = 4 + 8 from rfl, bytes_word, step,
    show (8 : Nat) = 4 + 4 from rfl, bytes_word, step, show (4 : Nat) = 4 + 0 from rfl, bytes_word]
  simp only [Nat.reduceAdd]
  rw [w0, w1, w2, w3, w4, w5]
  simp only [Proof.Argon2.initialHeader, prm, ← le32_arg, List.append_assoc,
    bytesAt, List.range_zero, List.map_nil, List.append_nil]
  obtain vc := variant_code hp.kind_le
  simp only [prm] at vc
  rw [vc]
  rfl

/-- `n` bytes of `scratch` at offset `d` are writable. -/
theorem scr_cov {s : State} (h : Inv s₀ s) {d n : Nat} (hd : d + n ≤ 16384) :
    Covers [⟨State.addr (scrP s₀) + BitVec.ofNat 64 d, n⟩] s.wr := by
  rw [h.wr]
  exact Covers.of_sub (rs' := [scrR s₀]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, List.mem_singleton_self _, d, rfl, hd⟩) |>.trans
    fun a n ⟨r, hr, hc⟩ => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact scr_mem hp, hc⟩

/-- The stack below the locals is outside `scratch`. -/
theorem stk_scr {d n k : Nat} (hd : d + n ≤ 16384) (hk : k ≤ 40) :
    (stkR (E s₀) k).Disjoint ⟨State.addr (scrP s₀) + BitVec.ofNat 64 d, n⟩ :=
  ((hp.stk_all (scrR s₀) (by simp)).sub_left fun a ha =>
    call_stk hp a (VG.Proof.Argon2.Arm.stkR_sub hk (by rw [E_nat hp]; have := hp.sp_lo; omega_arith) a ha)).sub_right
    (scr_sub hd)

/-- A store to the locals keeps the streaming state at `scratch`. -/
theorem repr_loc {m : Mem} {d : Nat} (hd : d + 4 ≤ 144) (v : BitVec 32) {h0 : Spec.Blake2.HashValue 64}
    {data : List Byte} (h : Repr b h0 m (State.addr (scrP s₀)) data) :
    Repr b h0 (m.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v) (State.addr (scrP s₀)) data :=
  HPrime.repr_frame ((Frame.refl [⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩] m).writeW
    (List.mem_singleton_self _) v (Region.contains_self _ _)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((loc_disj hp hd (scrR s₀) (by simp)).symm).sub_left (scr_sub (d := 0) (n := 192) (by decide) |>
        fun hs => by simpa using hs)) h

/-- `start`'s first block: `r4 :=` `scratch`, and the digest length. -/
theorem stA_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) :
    WP isa (.block [ld .r4 (argOff 15), .mov .r1 (.imm 64)]) s fun t =>
      Inv s₀ t ∧ Prm s₀ t ∧ t.gpr .r4 = scrP s₀ ∧ t.gpr .r1 = BitVec.ofNat 32 64 := by
  refine wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    WP.block_nil ?_
  obtain e : ∀ d, lw s₀ s₂ d = lw s₀ s d := fun d => by rw [lw_mem u₂.mem, lw_mem u₁.mem]
  exact ⟨(h.upd u₁ (by decide)).upd u₂ (by decide),
    ⟨by rw [e]; exact pr.divisor, by rw [e]; exact pr.segLen, by rw [e]; exact pr.laneLen, by rw [e]; exact pr.stride⟩,
    by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr]; rfl⟩

/-- `start`'s `init`. -/
theorem stInit_ok {s : State}
    (h : Inv s₀ s ∧ Prm s₀ s ∧ s.gpr .r4 = scrP s₀ ∧ s.gpr .r1 = BitVec.ofNat 32 64) :
    WP isa Impl.Argon2.Arm.HPrime.init s fun t => Inv s₀ t ∧ Prm s₀ t ∧ t.gpr .r4 = scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (scrP s₀)) [] :=
  (init_k (ctx hp h.1 h.2.2.1) (n := 64) h.2.2.2 (by decide) (by decide)).mono fun _ ⟨r, k⟩ =>
    let ⟨i, l⟩ := h.1.keeps hp k
    ⟨i, Prm.of_lw h.2.1 fun d hd => l d (prm_offs d hd).1, (k.gpr _ (by decide)).trans h.2.2.1, r⟩

/-- `start`'s hash of the header. -/
theorem stFix_ok {s : State}
    (h : Inv s₀ s ∧ Prm s₀ s ∧ s.gpr .r4 = scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (scrP s₀)) [] ∧
      bytesAt s.mem (State.addr (scrP s₀) + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (prm s₀)) :
    WP isa (Impl.Argon2.Arm.HPrime.absorbFixed 768 24) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      t.gpr .r4 = scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (scrP s₀)) (Proof.Argon2.initialHeader (prm s₀)) := by
  have hs := hp.scr_fits
  obtain ⟨i₄, pr₄, b₄, r₄, hd₄⟩ := h
  refine (HPrime.absorbFixed_ok (ctx hp i₄ b₄) (offset := 768) (size := 24) (by decide) (by decide) (by omega_arith)
    (by decide) (by decide) (by decide) (scr_cov hp i₄ (by decide)) (stk_scr hp (by decide) (by decide)) r₄).mono
    fun s₅ ⟨r₅, k₅⟩ => ?_
  rw [hd₄] at r₅
  obtain ⟨i₅, l₅⟩ := i₄.keeps hp k₅
  exact ⟨i₅, Prm.of_lw pr₄ fun d hd => l₅ d (prm_offs d hd).1, (k₅.gpr _ (by decide)).trans b₄, r₅⟩

/-- `start`'s count of the header's bytes. -/
theorem stCnt_ok {s : State}
    (h : Inv s₀ s ∧ Prm s₀ s ∧ s.gpr .r4 = scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (scrP s₀)) (Proof.Argon2.initialHeader (prm s₀))) :
    WP isa (.block [.mov .r0 (.imm 24), st countLoOff .r0, .mov .r0 (.imm 0), st countHiOff .r0]) s
      (HI s₀ (Proof.Argon2.initialHeader (prm s₀))) := by
  obtain ⟨i₅, pr₄, b₅, r₅⟩ := h
  refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => ?_
  obtain i₆ := i₅.upd u₆ (by decide)
  refine wp_stloc hp i₆ (d := countLoOff) (by decide) fun s₇ i₇ v₇ o₇ g₇ m₇ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₈ u₈ => ?_
  obtain i₈ := i₇.upd u₈ (by decide)
  refine wp_stloc hp i₈ (d := countHiOff) (by decide) fun t it vt ot gt mt => WP.block_nil ?_
  obtain L : ∀ d, d + 4 ≤ 144 → (d + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ d) → lw s₀ t d = lw s₀ s d :=
    fun d hd hd' => by
      rw [ot d (by omega_arith) (by simp only [countHiOff, countLoOff] at hd' ⊢; omega_arith), lw_mem u₈.mem,
        o₇ d (by omega_arith) (by simp only [countHiOff, countLoOff] at hd' ⊢; omega_arith), lw_mem u₆.mem]
  refine ⟨it, Prm.of_lw pr₄ fun d hd => L d (prm_offs d hd).1 (prm_offs d hd).2.2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gt, u₈.other _ (by decide), g₇, u₆.other _ (by decide), b₅]
  · rw [mt, u₈.mem, m₇, u₆.mem]
    exact repr_loc hp (by decide) _ (repr_loc hp (by decide) _ r₅)
  · rw [ot _ (by decide) (by decide), lw_mem u₈.mem, v₇, u₆.gpr, Proof.Argon2.initialHeader_length]; rfl
  · rw [vt, u₈.gpr, Proof.Argon2.initialHeader_length]; rfl
  · rw [Proof.Argon2.initialHeader_length]; decide

theorem start_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) :
    WP isa Impl.Argon2.Arm.Derive.start s (HI s₀ (Proof.Argon2.initialHeader (prm s₀))) := by
  unfold Impl.Argon2.Arm.Derive.start
  refine WP.seq ((stA_ok hp h pr).mono fun s₂ h₂ => WP.seq ((stInit_ok hp h₂).mono fun s₃ ⟨i₃, pr₃, b₃, r₃⟩ =>
    WP.seq ((header_ok hp i₃ pr₃ b₃ r₃).mono fun s₄ ⟨i₄, pr₄, b₄, r₄, hd₄, _⟩ =>
      WP.seq ((stFix_ok hp ⟨i₄, pr₄, b₄, r₄, hd₄⟩).mono fun s₅ h₅ => stCnt_ok hp h₅))))

end

/-- The carry into the high word of a count. -/
theorem carry_pair {c x : Nat} (_hc : c < 2 ^ 36) (hx : x < 2 ^ 32) :
    BitVec.ofNat 32 (c / 2 ^ 32) + 0 +
      (if decide (2 ^ 32 ≤ (BitVec.ofNat 32 c).toNat + (BitVec.ofNat 32 x).toNat) = true then 1 else 0) =
    BitVec.ofNat 32 ((c + x) / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat (w := 32) (x := c), BitVec.toNat_ofNat (w := 32) (x := x), Nat.mod_eq_of_lt hx]
  by_cases h : 2 ^ 32 ≤ c % 2 ^ 32 + x
  · simp [h, BitVec.toNat_add] <;> omega_arith
  · simp [h] <;> omega_arith

theorem count64 {n : Nat} (h : n < 2 ^ 64) :
    BitVec.ofNat 32 (n / 2 ^ 32) ++ BitVec.ofNat 32 n = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [Proof.Blake2.Arm.Stream.toNat_append32, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `addCount`: the 64-bit count in the locals, `c`, plus `x`. -/
theorem count_ok {s : State} (h : Inv s₀ s) {c x : Nat} (hc : c < 2 ^ 36) (hx : x < 2 ^ 32)
    (lo : lw s₀ s countLoOff = BitVec.ofNat 32 c) (hi : lw s₀ s countHiOff = BitVec.ofNat 32 (c / 2 ^ 32))
    {y : Op2} (hy : ∀ t : State, (∀ r, r ≠ .r2 → r ≠ .r3 → t.gpr r = s.gpr r) →
      y.eval t = some (BitVec.ofNat 32 x))
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → lw s₀ t countLoOff = BitVec.ofNat 32 (c + x) →
      lw s₀ t countHiOff = BitVec.ofNat 32 ((c + x) / 2 ^ 32) →
      (∀ e, e + 4 ≤ 256 → (e + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ e) → lw s₀ t e = lw s₀ s e) →
      (∀ r, r ≠ .r2 → r ≠ .r3 → t.gpr r = s.gpr r) →
      t.mem = (s.mem.writeW (State.addr (E s₀ + BitVec.ofNat 32 countLoOff)) (BitVec.ofNat 32 (c + x))).writeW
        (State.addr (E s₀ + BitVec.ofNat 32 countHiOff)) (BitVec.ofNat 32 ((c + x) / 2 ^ 32)) →
      t.gpr .r2 = BitVec.ofNat 32 (c + x) → t.gpr .r3 = BitVec.ofNat 32 ((c + x) / 2 ^ 32) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.addCount y ++ is)) s Q := by
  simp only [Impl.Argon2.Arm.Derive.addCount, List.cons_append, List.nil_append]
  refine wp_ldloc hp h (d := countLoOff) (by decide) fun s₁ u₁ => ?_
  obtain i₁ := h.upd u₁ (by decide)
  refine wp_ldloc hp i₁ (d := countHiOff) (by decide) fun s₂ u₂ => ?_
  obtain i₂ := i₁.upd u₂ (by decide)
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  obtain o₂ : ∀ r, r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s.gpr r := fun r a b => by rw [u₂.other _ b, u₁.other _ a]
  refine wp_adds (hy s₂ o₂) fun s₃ u₃ c₃ => ?_
  obtain i₃ := i₂.upd u₃ (by decide)
  refine wp_adc (op2_imm (by decide)) fun s₄ u₄ _ => ?_
  obtain i₄ := i₃.upd u₄ (by decide)
  obtain e₁ : s₂.gpr .r2 = BitVec.ofNat 32 c := by rw [u₂.other _ (by decide), u₁.gpr, lo]
  obtain vlo : s₄.gpr .r2 = BitVec.ofNat 32 (c + x) := by
    rw [u₄.other _ (by decide), u₃.gpr, e₁, BitVec.ofNat_add]
  obtain vhi : s₄.gpr .r3 = BitVec.ofNat 32 ((c + x) / 2 ^ 32) := by
    rw [u₄.gpr, c₃, u₃.other _ (by decide), u₂.gpr, lw_mem u₁.mem, hi, e₁]
    exact carry_pair hc hx
  refine wp_stloc hp i₄ (d := countLoOff) (by decide) fun s₅ i₅ v₅ o₅ g₅ m₅ => ?_
  refine wp_stloc hp i₅ (d := countHiOff) (by decide) fun t it vt ot gt mt => k t it ?_ ?_ ?_ ?_ ?_
    (by rw [gt, g₅, vlo]) (by rw [gt, g₅, vhi])
  · rw [ot _ (by decide) (by decide), v₅, vlo]
  · rw [vt, g₅, vhi]
  · intro e he hd
    rw [ot e he (by simp only [countHiOff, countLoOff] at hd ⊢; omega_arith),
      o₅ e he (by simp only [countHiOff, countLoOff] at hd ⊢; omega_arith), lw_mem u₄.mem, lw_mem u₃.mem,
      lw_mem m₂]
  · intro r h1 h2
    rw [gt, g₅, u₄.other _ h2, u₃.other _ h1, o₂ r h1 h2]
  · rw [mt, m₅, g₅, vhi, vlo, u₄.mem, u₃.mem, m₂]

end

/-- H₀'s streaming state at `scratch`, with `data` absorbed and the count `c` in
the locals. -/
structure HC (s₀ : State) (data : List Byte) (c : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  prm : Prm s₀ s
  r4 : s.gpr .r4 = scrP s₀
  repr : Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (scrP s₀)) data
  lo : lw s₀ s countLoOff = BitVec.ofNat 32 c
  hi : lw s₀ s countHiOff = BitVec.ofNat 32 (c / 2 ^ 32)

theorem HI.hc {s₀ s : State} {data : List Byte} (h : HI s₀ data s) : HC s₀ data data.length s :=
  ⟨h.inv, h.prm, h.r4, h.repr, h.lo, h.hi⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `absorb`'s first block: LE32 of the length at `scratch + 792`, and `update`'s arguments. -/
theorem absA_ok {len : Nat} (hlen : len < 18) {data : List Byte} {c : Nat} {s : State} (h : HC s₀ data c s) :
    WP isa (.block [ld .r0 (argOff len), .str .r0 .r4 792, ld .r2 countLoOff, ld .r3 countHiOff,
      .dp .add .r9 .r4 (.imm 792), .mov .r10 (.imm 4)]) s fun t =>
      HC s₀ data c t ∧ t.gpr .r9 = scrP s₀ + 792 ∧ (t.gpr .r10).toNat = 4 ∧ t.gpr .r2 = BitVec.ofNat 32 c ∧
      t.gpr .r3 = BitVec.ofNat 32 (c / 2 ^ 32) ∧
      bytesAt t.mem (State.addr (scrP s₀ + 792)) 4 = Spec.Argon2.le32 (arg s₀ len).toNat := by
  have hs := hp.scr_fits
  refine wp_ldarg hp h.inv (i := len) hlen fun s₁ u₁ => ?_
  obtain i₁ := h.inv.upd u₁ (by decide)
  obtain b₁ : s₁.gpr .r4 = scrP s₀ := by rw [u₁.other _ (by decide), h.r4]
  refine wp_stscr hp i₁ b₁ (o := 792) (by decide) fun s₂ i₂ m₂ g₂ l₂ f₂ => ?_
  refine wp_ldloc hp i₂ (d := countLoOff) (by decide) fun s₃ u₃ => ?_
  refine wp_ldloc hp (i₂.upd u₃ (by decide)) (d := countHiOff) (by decide) fun s₄ u₄ => ?_
  refine wp_add (op2_imm (by decide)) fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  obtain i₆ := (((i₂.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)
  obtain m₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain L₂ : ∀ d, d + 4 ≤ 144 → lw s₀ s₂ d = lw s₀ s d := fun d hd => by rw [l₂ d hd, lw_mem u₁.mem]
  obtain L₆ : ∀ d, d + 4 ≤ 144 → lw s₀ s₆ d = lw s₀ s d := fun d hd => by rw [lw_mem m₆, L₂ d hd]
  obtain e792 : State.addr (scrP s₀ + 792) = State.addr (scrP s₀) + BitVec.ofNat 64 792 :=
    scr_addr hp (o := 792) (by decide)
  obtain r4₄ : s₄.gpr .r4 = scrP s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, b₁]
  refine ⟨⟨i₆, Prm.of_lw h.prm fun d hd => L₆ d (prm_offs d hd).1,
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), r4₄],
    by rw [m₆]; exact repr_store (by decide) (by decide) f₂ (by rw [u₁.mem]; exact h.repr),
    by rw [L₆ _ (by decide)]; exact h.lo, by rw [L₆ _ (by decide)]; exact h.hi⟩, ?_, by rw [u₆.gpr]; rfl, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.gpr, r4₄]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, L₂ _ (by decide), h.lo]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, lw_mem u₃.mem, L₂ _ (by decide), h.hi]
  · rw [e792, show (4 : Nat) = 4 + 0 from rfl, bytes_word, m₆, m₂, Mem.readW_writeW_self32, u₁.gpr, le32_arg]
    rfl

/-- `absorb`'s first `update`: LE32 of the length. -/
theorem absU1_ok {len : Nat} {data : List Byte} {c : Nat} {s : State} (h : HC s₀ data c s)
    (hd : data.length = c) (hc : c + 4 < 2 ^ 36) (r9 : s.gpr .r9 = scrP s₀ + 792) (r10 : (s.gpr .r10).toNat = 4)
    (r2 : s.gpr .r2 = BitVec.ofNat 32 c) (r3 : s.gpr .r3 = BitVec.ofNat 32 (c / 2 ^ 32))
    (w : bytesAt s.mem (State.addr (scrP s₀ + 792)) 4 = Spec.Argon2.le32 (arg s₀ len).toNat) :
    WP isa Impl.Argon2.Arm.HPrime.update s (HC s₀ (data ++ Spec.Argon2.le32 (arg s₀ len).toNat) c) := by
  have hs := hp.scr_fits
  obtain e792 : State.addr (scrP s₀ + 792) = State.addr (scrP s₀) + BitVec.ofNat 64 792 :=
    scr_addr hp (o := 792) (by decide)
  refine (update_k (ctx hp h.inv h.r4) (D := scrP s₀ + 792) (L := 4) r9 r10
    (by have : (scrP s₀ + 792).toNat = (scrP s₀).toNat + 792 := add_nat (k := 792) (by omega_arith)
        omega_arith)
    (by rw [e792]; exact Covers.right (scr_cov hp h.inv (by decide)))
    (by rw [e792]; exact Offset.disjoint_base _ (by decide) (by decide))
    (by rw [e792]; exact stk_scr hp (by decide) (by decide)) h.repr
    (by rw [r3, r2, hd]; exact count64 (by omega_arith)) (by omega_arith)).mono fun t ⟨r, k⟩ => ?_
  obtain ⟨i, l⟩ := h.inv.keeps hp k
  rw [w] at r
  exact ⟨i, Prm.of_lw h.prm fun d hd => l d (prm_offs d hd).1,
    (k.gpr _ (by decide)).trans h.r4, r, by rw [l _ (by decide)]; exact h.lo, by rw [l _ (by decide)]; exact h.hi⟩

/-- `absorb`'s second block: the count advanced by 4, and `update`'s arguments. -/
theorem absB_ok {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18) {data : List Byte} {c : Nat}
    (hc : c < 2 ^ 36) {s : State} (h : HC s₀ data c s) :
    WP isa (.block (Impl.Argon2.Arm.Derive.addCount (.imm 4) ++
      ([ld .r9 (argOff ptr), ld .r10 (argOff len)] : List Instr)))
      s fun t => HC s₀ data (c + 4) t ∧ t.gpr .r9 = arg s₀ ptr ∧ (t.gpr .r10).toNat = (arg s₀ len).toNat ∧
        t.gpr .r2 = BitVec.ofNat 32 (c + 4) ∧ t.gpr .r3 = BitVec.ofNat 32 ((c + 4) / 2 ^ 32) := by
  refine count_ok hp h.inv (x := 4) hc (by decide) h.lo h.hi (fun _ _ => op2_imm (by decide))
    fun s₉ i₉ lo₉ hi₉ o₉ g₉ m₉ c₉ d₉ => wp_ldarg hp i₉ (i := ptr) hptr fun s₁₀ u₁₀ =>
      wp_ldarg hp (i₉.upd u₁₀ (by decide)) (i := len) hlen fun s₁₁ u₁₁ => WP.block_nil ?_
  obtain i₁₁ := (i₉.upd u₁₀ (by decide)).upd u₁₁ (by decide)
  obtain m₁₁ : s₁₁.mem = s₉.mem := by rw [u₁₁.mem, u₁₀.mem]
  refine ⟨⟨i₁₁, Prm.of_lw h.prm fun d hd => ?_, ?_, ?_, by rw [lw_mem m₁₁]; exact lo₉, by rw [lw_mem m₁₁]; exact hi₉⟩,
    by rw [u₁₁.other _ (by decide), u₁₀.gpr], by rw [u₁₁.gpr],
    by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), c₉],
    by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), d₉]⟩
  · rw [lw_mem m₁₁, o₉ d (by have := (prm_offs d hd).1; omega_arith) (prm_offs d hd).2.2]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), g₉ _ (by decide) (by decide), h.r4]
  · rw [m₁₁, m₉]; exact repr_loc hp (by decide) _ (repr_loc hp (by decide) _ h.repr)

/-- `absorb`'s second `update`: the input. -/
theorem absU2_ok {ptr len : Nat}
    (hR : (⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀])
    (hfit : (arg s₀ ptr).toNat + (arg s₀ len).toNat ≤ 2 ^ 32) {data : List Byte} {c : Nat} {s : State}
    (h : HC s₀ data c s) (hd : data.length = c) (hc : c + 2 ^ 32 < 2 ^ 36) (r9 : s.gpr .r9 = arg s₀ ptr)
    (r10 : (s.gpr .r10).toNat = (arg s₀ len).toNat) (r2 : s.gpr .r2 = BitVec.ofNat 32 c)
    (r3 : s.gpr .r3 = BitVec.ofNat 32 (c / 2 ^ 32)) :
    WP isa Impl.Argon2.Arm.HPrime.update s
      (HC s₀ (data ++ bytesAt s₀.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat) c) := by
  obtain hlt := (arg s₀ len).isLt
  obtain hR' : (⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩ : Region) ∈
      [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h | h <;> simp [h]
  obtain hS : (⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩ : Region) ∈
      [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h | h <;> simp [h]
  obtain rin := hp.ro_w _ hR' (scrR s₀) (by simp)
  refine (update_k (ctx hp h.inv h.r4) (D := arg s₀ ptr) (L := (arg s₀ len).toNat) r9 r10 hfit
    (by rw [h.inv.rd, hp.rd]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_append_left _ hR', 0, by simp, by simp⟩)
    (rin.sub_right (Region.sub_prefix (by decide)))
    ((hp.stk_all _ hS).sub_left fun a ha => call_stk hp a (stk32_call hp a ha))
    h.repr (by rw [r3, r2, hd]; exact count64 (by omega_arith)) (by omega_arith)).mono fun t ⟨r, k⟩ => ?_
  obtain ⟨i, l⟩ := h.inv.keeps hp k
  obtain inp : bytesAt s.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat :=
    h.inv.input hp (R := ⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩) hR
  rw [inp] at r
  exact ⟨i, Prm.of_lw h.prm fun d hd => l d (prm_offs d hd).1,
    (k.gpr _ (by decide)).trans h.r4, r, by rw [l _ (by decide)]; exact h.lo, by rw [l _ (by decide)]; exact h.hi⟩

/-- `absorb`'s last block: the count advanced by the input's length. -/
theorem absC_ok {len : Nat} (hlen : len < 18) {data : List Byte} {c : Nat} (hc : c < 2 ^ 36) {s : State}
    (h : HC s₀ data c s) :
    WP isa (.block (ld .r0 (argOff len) :: Impl.Argon2.Arm.Derive.addCount (.reg .r0))) s
      (HC s₀ data (c + (arg s₀ len).toNat)) := by
  refine wp_ldarg hp h.inv (i := len) hlen fun s₁ u₁ => ?_
  obtain i₁ := h.inv.upd u₁ (by decide)
  rw [← List.append_nil (Impl.Argon2.Arm.Derive.addCount _)]
  refine count_ok hp i₁ (x := (arg s₀ len).toNat) hc (arg s₀ len).isLt (by rw [lw_mem u₁.mem]; exact h.lo)
    (by rw [lw_mem u₁.mem]; exact h.hi)
    (fun t ht => by rw [op2_reg, ht _ (by decide) (by decide), u₁.gpr, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    fun t it lo hi o g mt _ _ => WP.block_nil ⟨it, Prm.of_lw h.prm fun d hd => ?_, ?_, ?_, lo, hi⟩
  · rw [o d (by have := (prm_offs d hd).1; omega_arith) (prm_offs d hd).2.2, lw_mem u₁.mem]
  · rw [g _ (by decide) (by decide), u₁.other _ (by decide), h.r4]
  · rw [mt, u₁.mem]; exact repr_loc hp (by decide) _ (repr_loc hp (by decide) _ h.repr)

theorem absorb_ok {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18)
    (hR : (⟨State.addr (arg s₀ ptr), (arg s₀ len).toNat⟩ : Region) ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀])
    (hfit : (arg s₀ ptr).toNat + (arg s₀ len).toNat ≤ 2 ^ 32) {data : List Byte}
    (hd : data.length + 4 + 2 ^ 32 < 2 ^ 36) {s : State} (h : HI s₀ data s) :
    WP isa (Impl.Argon2.Arm.Derive.absorb ptr len) s
      (HI s₀ (Proof.Argon2.appendInput data (bytesAt s₀.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat))) := by
  obtain hlt := (arg s₀ len).isLt
  unfold Impl.Argon2.Arm.Derive.absorb
  refine WP.seq ((absA_ok hp hlen h.hc).mono fun s₁ ⟨h₁, e₁, d₁, c₁, x₁, w₁⟩ => ?_)
  refine WP.seq ((absU1_ok hp h₁ rfl (by omega_arith) e₁ d₁ c₁ x₁ w₁).mono fun s₂ h₂ => ?_)
  refine WP.seq ((absB_ok hp hptr hlen (by omega_arith) h₂).mono fun s₃ ⟨h₃, e₃, d₃, c₃, x₃⟩ => ?_)
  refine WP.seq ((absU2_ok hp hR hfit h₃ (by simp [Proof.Argon2.le32_length]) (by omega_arith) e₃ d₃ c₃ x₃).mono
    fun s₄ h₄ => ?_)
  refine (absC_ok hp hlen (by omega_arith) h₄).mono fun t ht => ?_
  obtain hd' : Proof.Argon2.appendInput data (bytesAt s₀.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat) =
      data ++ Spec.Argon2.le32 (arg s₀ len).toNat ++
        bytesAt s₀.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat := by
    simp only [Proof.Argon2.appendInput, bytesAt, List.length_map, List.length_range]
  obtain hl : (Proof.Argon2.appendInput data (bytesAt s₀.mem (State.addr (arg s₀ ptr)) (arg s₀ len).toNat)).length =
      data.length + 4 + (arg s₀ len).toNat := by
    rw [Proof.Argon2.appendInput_length]; simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨ht.inv, ht.prm, ht.r4, by rw [hd']; exact ht.repr, by rw [hl]; exact ht.lo, by rw [hl]; exact ht.hi,
    by rw [hl]; omega_arith⟩

end

/-- The bytes of `4 k` bytes, from their words. -/
theorem bytes_of_words {m m' : Mem} {p p' : Addr} {k : Nat}
    (h : ∀ j < k, m'.readW (p' + BitVec.ofNat 64 (4 * j)) 32 = m.readW (p + BitVec.ofNat 64 (4 * j)) 32) :
    bytesAt m' p' (4 * k) = bytesAt m p (4 * k) := by
  rw [Proof.Blake2.bytesAt_words (w := 32), Proof.Blake2.bytesAt_words (w := 32)]
  simp only [List.flatMap]
  refine congrArg List.flatten (List.map_congr_left fun j hj => ?_)
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (.inl rfl), ← Proof.Blake2.wordBytes_readW (w := 32) _ _ (.inl rfl)]
  exact congrArg _ (h j (List.mem_range.mp hj))

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A store to the locals keeps `scratch`. -/
theorem scr_loc {m : Mem} {d o : Nat} (hd : d + 4 ≤ 144) (ho : o + 4 ≤ 16384) (v : BitVec 32) :
    (m.writeW (State.addr (E s₀ + BitVec.ofNat 32 d)) v).readW (State.addr (scrP s₀) + BitVec.ofNat 64 o) 32 =
      m.readW (State.addr (scrP s₀) + BitVec.ofNat 64 o) 32 := by
  refine ((Frame.refl [⟨State.addr (E s₀ + BitVec.ofNat 32 d), 4⟩] m).writeW (List.mem_singleton_self _) v
    (Region.contains_self _ _)).readW (r := ⟨State.addr (scrP s₀) + BitVec.ofNat 64 o, 4⟩)
    (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ((loc_disj hp hd (scrR s₀) (by simp)).symm.sub_left (scr_sub ho))

/-- The first `k` words of the digest, copied to the locals. -/
theorem copy_ok {s : State} (h : Inv s₀ s) (hb : s.gpr .r4 = scrP s₀) :
    ∀ k ≤ 16, WP isa (.block ((List.range k).flatMap Impl.Argon2.Arm.Derive.copyWord)) s fun t =>
      Inv s₀ t ∧ t.gpr .r4 = scrP s₀ ∧
      (∀ j < k, lw s₀ t (4 * j) = s.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 (768 + 4 * j)) 32) ∧
      (∀ o, o + 4 ≤ 16384 → t.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 o) 32 =
        s.mem.readW (State.addr (scrP s₀) + BitVec.ofNat 64 o) 32) ∧
      (∀ e, e + 4 ≤ 256 → 4 * k ≤ e → lw s₀ t e = lw s₀ s e)
  | 0, _ => WP.block_nil ⟨h, hb, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, fun _ _ _ => rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((copy_ok h hb k (by omega_arith)).mono fun t ⟨it, bt, wt, st, lt⟩ => ?_)
    simp only [Impl.Argon2.Arm.Derive.copyWord]
    refine wp_ldr (by omega_arith) (by rw [bt, scr_addr hp (by omega_arith)]) (by
        rw [it.rd, it.wr]
        exact ⟨scrR s₀, List.mem_append_right _ (scr_mem hp), Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
      fun t₁ u₁ => ?_
    obtain i₁ := it.upd u₁ (by decide)
    refine wp_stloc hp i₁ (d := 4 * k) (by omega_arith) fun t₂ i₂ v₂ o₂ g₂ m₂ => WP.block_nil
      ⟨i₂, by rw [g₂, u₁.other _ (by decide), bt], fun j hj => ?_, fun o ho => ?_, fun e he hke => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [o₂ _ (by omega_arith) (by omega_arith), lw_mem u₁.mem]; exact wt j hj
      · rw [v₂, u₁.gpr, st _ (by omega_arith)]
    · rw [m₂, scr_loc hp (by omega_arith) ho, u₁.mem]; exact st o ho
    · rw [o₂ _ he (by omega_arith), lw_mem u₁.mem]; exact lt e he (by omega_arith)

/-- `finish`'s first block: the count, for `finalize`. -/
theorem fiA_ok {data : List Byte} {s : State} (h : HI s₀ data s) :
    WP isa (.block [ld .r2 countLoOff, ld .r3 countHiOff]) s fun t => HI s₀ data t ∧
      t.gpr .r2 = BitVec.ofNat 32 data.length ∧ t.gpr .r3 = BitVec.ofNat 32 (data.length / 2 ^ 32) := by
  refine wp_ldloc hp h.inv (d := countLoOff) (by decide) fun s₁ u₁ =>
    wp_ldloc hp (h.inv.upd u₁ (by decide)) (d := countHiOff) (by decide) fun s₂ u₂ =>
      WP.block_nil ?_
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨⟨(h.inv.upd u₁ (by decide)).upd u₂ (by decide), Prm.of_lw h.prm fun d _ => lw_mem m₂ d,
    by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r4], by rw [m₂]; exact h.repr,
    by rw [lw_mem m₂]; exact h.lo, by rw [lw_mem m₂]; exact h.hi, h.len⟩,
    by rw [u₂.other _ (by decide), u₁.gpr, h.lo], by rw [u₂.gpr, lw_mem u₁.mem, h.hi]⟩

/-- `finish`'s `finalize`: the digest at `scratch + 768`. -/
theorem fiFin_ok {data : List Byte} {s : State} (h : HI s₀ data s)
    (r2 : s.gpr .r2 = BitVec.ofNat 32 data.length) (r3 : s.gpr .r3 = BitVec.ofNat 32 (data.length / 2 ^ 32)) :
    WP isa Impl.Argon2.Arm.HPrime.finalize s fun t => Inv s₀ t ∧ Prm s₀ t ∧ t.gpr .r4 = scrP s₀ ∧
      bytesAt t.mem (State.addr (scrP s₀) + 768) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) data := by
  have hn := h.len
  refine (finalize_k (ctx hp h.inv h.r4) (h0 := Spec.Blake2.init b 64 0) h.repr
    (by rw [r3, r2]; exact count64 (by omega_arith)) (by omega_arith)).mono fun s₃ ⟨dg, k₃⟩ => ?_
  obtain ⟨i₃, l₃⟩ := h.inv.keeps hp k₃
  exact ⟨i₃, Prm.of_lw h.prm fun d hd => l₃ d (prm_offs d hd).1, (k₃.gpr _ (by decide)).trans h.r4, dg⟩

/-- `finish`'s copy of the digest to the locals. -/
theorem fiCopy_ok {s : State} {dg : List Byte} (h : Inv s₀ s ∧ Prm s₀ s ∧ s.gpr .r4 = scrP s₀ ∧
      bytesAt s.mem (State.addr (scrP s₀) + 768) 64 = dg) :
    WP isa (.block ((List.range 16).flatMap Impl.Argon2.Arm.Derive.copyWord)) s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (State.addr (E s₀)) 64 = dg := by
  have hs := hp.scr_fits
  obtain hE := E_hi hp
  obtain ⟨i₃, pr₃, b₃, dg₃⟩ := h
  refine (copy_ok hp i₃ b₃ 16 (Nat.le_refl _)).mono fun t ⟨it, _, wt, _, lt⟩ =>
    ⟨it, Prm.of_lw pr₃ fun d hd => ?_, ?_⟩
  · rw [lt d (by have := (prm_offs d hd).1; omega_arith) (by have := (prm_offs d hd).2.1; omega_arith)]
  · rw [← dg₃]
    refine bytes_of_words (k := 16) fun j hj => ?_
    have := wt j hj
    simp only [lw] at this
    rw [loc_addr hp (by omega_arith)] at this
    rw [this, BitVec.add_assoc, show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.ofNat_add_ofNat]

theorem finish_ok {data : List Byte} {s : State} (h : HI s₀ data s) :
    WP isa Impl.Argon2.Arm.Derive.finish s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (State.addr (E s₀)) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) data := by
  unfold Impl.Argon2.Arm.Derive.finish
  exact WP.seq ((fiA_ok hp h).mono fun s₂ ⟨h₂, c₂, d₂⟩ => WP.seq ((fiFin_ok hp h₂ c₂ d₂).mono
    fun s₃ h₃ => fiCopy_ok hp h₃))

theorem code_ok {s : State} (h : Inv s₀ s) (pr : Prm s₀ s) :
    WP isa Impl.Argon2.Arm.Derive.code s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      bytesAt t.mem (State.addr (E s₀)) 64 =
        Spec.Argon2.initialHash (prm s₀) (pwB s₀) (saltB s₀) (secB s₀) (adB s₀) := by
  obtain l1 := (arg s₀ 2).isLt
  obtain l2 := (arg s₀ 4).isLt
  obtain l3 := (arg s₀ 10).isLt
  unfold Impl.Argon2.Arm.Derive.code
  refine WP.seq ((start_ok hp h pr).mono fun s₁ h₁ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 1) (len := 2) (by decide) (by decide) (by simp) hp.pw_fits
    (by rw [Proof.Argon2.initialHeader_length]; omega_arith) h₁).mono fun s₂ h₂ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 3) (len := 4) (by decide) (by decide) (by simp) hp.salt_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega_arith) h₂).mono fun s₃ h₃ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 9) (len := 10) (by decide) (by decide) (by simp) hp.sec_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega_arith) h₃).mono fun s₄ h₄ => ?_)
  refine WP.seq ((absorb_ok hp (ptr := 11) (len := 12) (by decide) (by decide) (by simp) hp.ad_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega_arith) h₄).mono fun s₅ h₅ => ?_)
  refine (finish_ok hp h₅).mono fun t ⟨it, pt, bt⟩ => ⟨it, pt, ?_⟩
  rw [bt, Proof.Argon2.initialHash_stream, List.take_of_length_le (by rw [HPrime.finalHash_length])]
  rfl

end

end VG.Proof.Argon2.Arm.Derive
