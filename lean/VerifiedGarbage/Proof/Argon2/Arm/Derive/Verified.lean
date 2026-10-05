import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Verified
import VerifiedGarbage.Proof.Argon2.Arm.CompressVerified
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Impl.Argon2.Arm.Derive
import VerifiedGarbage.Proof.Argon2.Arm.Divide
import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Argon2.MemoryInit
import VerifiedGarbage.Proof.Argon2.References
import VerifiedGarbage.Proof.Argon2.AddressInput
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Argon2.Serialization
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.Contract`. -/
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

abbrev kindV : BitVec 32 := VG.Proof.Argon2.Arm.Derive.arg s₀ 0
abbrev pwP : BitVec 32 := VG.Proof.Argon2.Arm.Derive.arg s₀ 1
abbrev pwL : Nat := (VG.Proof.Argon2.Arm.Derive.arg s₀ 2).toNat
abbrev saltP : BitVec 32 := VG.Proof.Argon2.Arm.Derive.arg s₀ 3
abbrev saltL : Nat := (VG.Proof.Argon2.Arm.Derive.arg s₀ 4).toNat
abbrev itersN : Nat := (VG.Proof.Argon2.Arm.Derive.arg s₀ 5).toNat
abbrev mcostN : Nat := (VG.Proof.Argon2.Arm.Derive.arg s₀ 6).toNat
abbrev lanesN : Nat := (VG.Proof.Argon2.Arm.Derive.arg s₀ 7).toNat
abbrev threadsN : Nat := (VG.Proof.Argon2.Arm.Derive.arg s₀ 8).toNat
abbrev secP : BitVec 32 := VG.Proof.Argon2.Arm.Derive.arg s₀ 9
abbrev secL : Nat := (VG.Proof.Argon2.Arm.Derive.arg s₀ 10).toNat
abbrev adP : BitVec 32 := VG.Proof.Argon2.Arm.Derive.arg s₀ 11
abbrev adL : Nat := (VG.Proof.Argon2.Arm.Derive.arg s₀ 12).toNat
abbrev memP : BitVec 32 := VG.Proof.Argon2.Arm.Derive.arg s₀ 13
abbrev blocksN : Nat := (VG.Proof.Argon2.Arm.Derive.arg s₀ 14).toNat
abbrev scrP : BitVec 32 := VG.Proof.Argon2.Arm.Derive.arg s₀ 15
abbrev outP : BitVec 32 := VG.Proof.Argon2.Arm.Derive.arg s₀ 16
abbrev outL : Nat := (VG.Proof.Argon2.Arm.Derive.arg s₀ 17).toNat
abbrev E0 : BitVec 32 := s₀.sp

/-- The parameters. -/
abbrev prm : Params := VG.Spec.Argon2.params (VG.Proof.Argon2.Arm.Derive.kindV s₀).toNat (VG.Proof.Argon2.Arm.Derive.itersN s₀) (VG.Proof.Argon2.Arm.Derive.mcostN s₀) (VG.Proof.Argon2.Arm.Derive.lanesN s₀) (VG.Proof.Argon2.Arm.Derive.outL s₀)

abbrev pwR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.pwP s₀), VG.Proof.Argon2.Arm.Derive.pwL s₀⟩
abbrev saltR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.saltP s₀), VG.Proof.Argon2.Arm.Derive.saltL s₀⟩
abbrev secR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.secP s₀), VG.Proof.Argon2.Arm.Derive.secL s₀⟩
abbrev adR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.adP s₀), VG.Proof.Argon2.Arm.Derive.adL s₀⟩
abbrev memR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.memP s₀), VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024⟩
abbrev scrR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀), 16384⟩
abbrev outR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.outP s₀), VG.Proof.Argon2.Arm.Derive.outL s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 56⟩
abbrev stkR0 : Region := stkR (VG.Proof.Argon2.Arm.Derive.E0 s₀) 240

/-- The inputs, on entry. -/
abbrev pwB : List Byte := bytesAt s₀.mem (VG.Proof.Argon2.Arm.Derive.pwR s₀).base (VG.Proof.Argon2.Arm.Derive.pwL s₀)
abbrev saltB : List Byte := bytesAt s₀.mem (VG.Proof.Argon2.Arm.Derive.saltR s₀).base (VG.Proof.Argon2.Arm.Derive.saltL s₀)
abbrev secB : List Byte := bytesAt s₀.mem (VG.Proof.Argon2.Arm.Derive.secR s₀).base (VG.Proof.Argon2.Arm.Derive.secL s₀)
abbrev adB : List Byte := bytesAt s₀.mem (VG.Proof.Argon2.Arm.Derive.adR s₀).base (VG.Proof.Argon2.Arm.Derive.adL s₀)

end

/-- The facts of `deriveArm`'s precondition. -/
structure DPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Argon2.Arm.Derive.pwR s₀, VG.Proof.Argon2.Arm.Derive.saltR s₀, VG.Proof.Argon2.Arm.Derive.secR s₀, VG.Proof.Argon2.Arm.Derive.adR s₀, VG.Proof.Argon2.Arm.Derive.argR s₀]
  wr : s₀.wr = [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀]
  ro_w : ∀ r ∈ [VG.Proof.Argon2.Arm.Derive.pwR s₀, VG.Proof.Argon2.Arm.Derive.saltR s₀, VG.Proof.Argon2.Arm.Derive.secR s₀, VG.Proof.Argon2.Arm.Derive.adR s₀, VG.Proof.Argon2.Arm.Derive.argR s₀], ∀ w ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀],
    r.Disjoint w
  mem_scr : (VG.Proof.Argon2.Arm.Derive.memR s₀).Disjoint (VG.Proof.Argon2.Arm.Derive.scrR s₀)
  mem_out : (VG.Proof.Argon2.Arm.Derive.memR s₀).Disjoint (VG.Proof.Argon2.Arm.Derive.outR s₀)
  scr_out : (VG.Proof.Argon2.Arm.Derive.scrR s₀).Disjoint (VG.Proof.Argon2.Arm.Derive.outR s₀)
  stk_all : ∀ r ∈ [VG.Proof.Argon2.Arm.Derive.pwR s₀, VG.Proof.Argon2.Arm.Derive.saltR s₀, VG.Proof.Argon2.Arm.Derive.secR s₀, VG.Proof.Argon2.Arm.Derive.adR s₀, VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀], (VG.Proof.Argon2.Arm.Derive.stkR0 s₀).Disjoint r
  pw_fits : (VG.Proof.Argon2.Arm.Derive.pwP s₀).toNat + VG.Proof.Argon2.Arm.Derive.pwL s₀ ≤ 2 ^ 32
  salt_fits : (VG.Proof.Argon2.Arm.Derive.saltP s₀).toNat + VG.Proof.Argon2.Arm.Derive.saltL s₀ ≤ 2 ^ 32
  sec_fits : (VG.Proof.Argon2.Arm.Derive.secP s₀).toNat + VG.Proof.Argon2.Arm.Derive.secL s₀ ≤ 2 ^ 32
  ad_fits : (VG.Proof.Argon2.Arm.Derive.adP s₀).toNat + VG.Proof.Argon2.Arm.Derive.adL s₀ ≤ 2 ^ 32
  mem_fits : (VG.Proof.Argon2.Arm.Derive.memP s₀).toNat + VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024 ≤ 2 ^ 32
  scr_fits : (VG.Proof.Argon2.Arm.Derive.scrP s₀).toNat + 16384 ≤ 2 ^ 32
  out_fits : (VG.Proof.Argon2.Arm.Derive.outP s₀).toNat + VG.Proof.Argon2.Arm.Derive.outL s₀ ≤ 2 ^ 32
  sp_lo : 240 ≤ (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat
  sp_hi : (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat + 56 ≤ 2 ^ 32
  kind_le : (VG.Proof.Argon2.Arm.Derive.kindV s₀).toNat ≤ 2
  valid : valid (VG.Proof.Argon2.Arm.Derive.prm s₀) (VG.Proof.Argon2.Arm.Derive.pwL s₀) (VG.Proof.Argon2.Arm.Derive.saltL s₀) (VG.Proof.Argon2.Arm.Derive.secL s₀) (VG.Proof.Argon2.Arm.Derive.adL s₀)
  threads : 1 ≤ VG.Proof.Argon2.Arm.Derive.threadsN s₀ ∧ VG.Proof.Argon2.Arm.Derive.threadsN s₀ < 2 ^ 24
  blocks : VG.Proof.Argon2.Arm.Derive.blocksN s₀ = (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks

/-- `vg_argon2`, with its stack arguments only read. -/
def deriveArm : Contract Arm.isa where
  pre := VG.Proof.Argon2.Arm.Derive.DPre
  post s s' := bytesAt s'.mem (State.addr (VG.Proof.Argon2.Arm.Derive.outP s)) (VG.Proof.Argon2.Arm.Derive.outL s) =
    derive (VG.Proof.Argon2.Arm.Derive.prm s) (VG.Proof.Argon2.Arm.Derive.pwB s) (VG.Proof.Argon2.Arm.Derive.saltB s) (VG.Proof.Argon2.Arm.Derive.secB s) (VG.Proof.Argon2.Arm.Derive.adB s)
  pub s₁ s₂ := (s₁.sp = s₂.sp ∧ ∀ i < 18, VG.Proof.Argon2.Arm.Derive.arg s₁ i = VG.Proof.Argon2.Arm.Derive.arg s₂ i) ∧
    references (VG.Proof.Argon2.Arm.Derive.prm s₁) (VG.Proof.Argon2.Arm.Derive.pwB s₁) (VG.Proof.Argon2.Arm.Derive.saltB s₁) (VG.Proof.Argon2.Arm.Derive.secB s₁) (VG.Proof.Argon2.Arm.Derive.adB s₁) =
      references (VG.Proof.Argon2.Arm.Derive.prm s₂) (VG.Proof.Argon2.Arm.Derive.pwB s₂) (VG.Proof.Argon2.Arm.Derive.saltB s₂) (VG.Proof.Argon2.Arm.Derive.secB s₂) (VG.Proof.Argon2.Arm.Derive.adB s₂)

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
      omega
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  rcases Nat.le_total a.base.toNat b.base.toNat with hle | hle
  · have := key h hle hb pb; omega
  · have := key h.symm hle ha pa; omega

namespace DPre
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem lanes_pos : 1 ≤ VG.Proof.Argon2.Arm.Derive.lanesN s₀ := hp.valid.1
theorem lanes_lt : VG.Proof.Argon2.Arm.Derive.lanesN s₀ < 2 ^ 24 := hp.valid.2.1
theorem passes_pos : 1 ≤ VG.Proof.Argon2.Arm.Derive.itersN s₀ := hp.valid.2.2.1
theorem memory_ge : 8 * VG.Proof.Argon2.Arm.Derive.lanesN s₀ ≤ VG.Proof.Argon2.Arm.Derive.mcostN s₀ := hp.valid.2.2.2.2.1
theorem tag_ge : 4 ≤ VG.Proof.Argon2.Arm.Derive.outL s₀ := hp.valid.2.2.2.2.2.2.1

theorem segLen_two : 2 ≤ (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen :=
  Proof.Argon2.segmentLen_ge_two _ hp.lanes_pos hp.memory_ge

theorem segLen_eq : (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen = VG.Proof.Argon2.Arm.Derive.mcostN s₀ / (4 * VG.Proof.Argon2.Arm.Derive.lanesN s₀) :=
  Proof.Argon2.segmentLen_eq _ hp.lanes_pos

theorem laneLen_eq : (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen = 4 * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen :=
  Proof.Argon2.laneLen_segments _ hp.lanes_pos

theorem blocks_eq : VG.Proof.Argon2.Arm.Derive.blocksN s₀ = VG.Proof.Argon2.Arm.Derive.lanesN s₀ * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen := by
  rw [hp.blocks]; exact Proof.Argon2.blocks_lanes _ hp.lanes_pos

/-- The memory, with the scratch beside it, fits below 2³² with room to spare. -/
theorem blocks_lt : VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024 + 16384 ≤ 2 ^ 32 := by
  have hm := hp.mem_fits
  have hs := hp.scr_fits
  rcases Nat.eq_zero_or_pos (VG.Proof.Argon2.Arm.Derive.blocksN s₀) with h0 | hpos
  · omega
  have := VG.Proof.Argon2.Arm.Derive.disjoint_total hp.mem_scr (N := 2 ^ 32)
    (by simp only [MdStream.Arm.addr_toNat]; omega)
    (by simp only [MdStream.Arm.addr_toNat]; omega)
    (by simp only; omega) (by simp only; omega)
  simpa using this

end DPre

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.Frame`. -/
section

/-!
# Argon2 on ARMv7: the derivation's frames

`vg_argon2` pushes its register arguments, then the caller's `r4`–`r11` and
its return address (with `r3`), then allocates 144 bytes for the locals
(`Impl.Argon2.Arm.Derive.derive`). `entry s₀` is the state its body starts
in; `frames_ok` gives the callee-saved registers and the stack pointer back,
from a body that leaves the stack pointer at the locals and the saved words
alone (`BodyDone`).
-/

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
def entry (s₀ : State) : State := allocated 144 (pushed VG.Proof.Argon2.Arm.Derive.savedRegs (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀))

/-- The stack pointer of the body: below the frames and the locals. -/
abbrev E (s₀ : State) : BitVec 32 := VG.Proof.Argon2.Arm.Derive.E0 s₀ - BitVec.ofNat 32 200

/-- What the body must keep for the frames to restore the caller's state. -/
structure BodyDone (s₀ t : State) : Prop where
  sp : t.sp = VG.Proof.Argon2.Arm.Derive.E s₀
  saved : ∀ j < 9, t.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (148 + 4 * j))) 32 =
    s₀.gpr (VG.Proof.Argon2.Arm.Derive.savedRegs[j + 1]?.getD .r0)

section
variable {s₀ : State} (hlo : 200 ≤ (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat)
include hlo

theorem sp1 : (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).sp.toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 16 := by
  have h : 200 ≤ s₀.sp.toNat := hlo
  rw [pushed_sp_toNat (by simp only [List.length_cons, List.length_nil]; omega)]; rfl

theorem sp2 : (pushed VG.Proof.Argon2.Arm.Derive.savedRegs (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀)).sp.toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 56 := by
  rw [pushed_sp_toNat (by rw [VG.Proof.Argon2.Arm.Derive.sp1 hlo]; simp only [List.length_cons, List.length_nil]; omega), VG.Proof.Argon2.Arm.Derive.sp1 hlo]; rfl

theorem E_toNat : (VG.Proof.Argon2.Arm.Derive.E s₀).toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 200 := sub_toNat' hlo

theorem entry_sp : (VG.Proof.Argon2.Arm.Derive.entry s₀).sp = VG.Proof.Argon2.Arm.Derive.E s₀ := by
  apply BitVec.eq_of_toNat_eq
  simp only [VG.Proof.Argon2.Arm.Derive.entry, allocated]
  rw [sub_toNat' (by rw [VG.Proof.Argon2.Arm.Derive.sp2 hlo]; omega), VG.Proof.Argon2.Arm.Derive.sp2 hlo, VG.Proof.Argon2.Arm.Derive.E_toNat hlo]
  omega

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

theorem frames_ok {s₀ : State} (hlo : 240 ≤ (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat) {Q : State → Prop}
    (hb : WP isa body (VG.Proof.Argon2.Arm.Derive.entry s₀) fun t => VG.Proof.Argon2.Arm.Derive.BodyDone s₀ t ∧ t.wr = (VG.Proof.Argon2.Arm.Derive.entry s₀).wr ∧ Q t)
    (hQ : ∀ t u, Q t → u.mem = t.mem → Q u) :
    WP isa derive s₀ fun u => abiPreserved s₀ u ∧ Q u := by
  have hE := (VG.Proof.Argon2.Arm.Derive.E0 s₀).isLt
  have e0 : (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat = s₀.sp.toNat := rfl
  have h1 := VG.Proof.Argon2.Arm.Derive.sp1 (s₀ := s₀) (by omega)
  have h2 := VG.Proof.Argon2.Arm.Derive.sp2 (s₀ := s₀) (by omega)
  unfold derive
  refine WP.frame (rs := VG.Proof.Argon2.Arm.Derive.argRegs) (r := .r0) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
    (by decide) ?_
  refine WP.frame (rs := VG.Proof.Argon2.Arm.Derive.savedRegs) (r := .r3) (by decide)
    (by rw [h1]; simp only [List.length_cons, List.length_nil]; omega) (by decide) ?_
  refine WP.seq (WP.alloc (by decide) (by rw [h2]; show 144 ≤ _; omega) (hb.mono fun t ⟨d, w, q⟩ => ?_))
  -- The restores.
  set S2 := pushed VG.Proof.Argon2.Arm.Derive.savedRegs (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀) with hS2
  have spS2 : (freed 144 t).sp = S2.sp := by
    simp only [freed, d.sp]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, VG.Proof.Argon2.Arm.Derive.E_toNat (by omega), h2, BitVec.toNat_ofNat]
    omega
  have wS2 : (freed 144 t).wr = S2.wr := by simp only [freed, w, VG.Proof.Argon2.Arm.Derive.entry, allocated, List.tail_cons, hS2]
  have S2sp : S2.sp.toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 56 := h2
  have hS2v : ∀ i (hi : i < 10), S2.mem.readW (State.addr (S2.sp + BitVec.ofNat 32 (4 * i))) 32 =
      s₀.gpr VG.Proof.Argon2.Arm.Derive.savedRegs[i] := fun i hi => by
    have := VG.Proof.Argon2.Arm.storeWords_readW (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).mem
      ((pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length))
      (savedRegs.map (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).gpr) (by
        simp only [List.length_map, List.length_cons, List.length_nil]
        rw [sub_toNat' (by rw [h1]; omega), h1]; omega) (i := i) (by simpa using hi)
    rw [List.getElem_map] at this
    exact this
  have inS2 : ∀ d, d + 4 ≤ 40 → InRegions ((freed 144 t).rd ++ (freed 144 t).wr)
      (State.addr ((freed 144 t).sp + BitVec.ofNat 32 d)) 4 := fun d hd => by
    have hw : ⟨State.addr S2.sp, 40⟩ ∈ S2.wr := by simp [hS2, pushed]
    rw [wS2, spS2, addr_add (by rw [S2sp]; omega)]
    exact ⟨⟨State.addr S2.sp, 40⟩, List.mem_append_right _ hw, Offset.contains_base _ hd (by omega)⟩
  show WP isa (.block (Impl.Argon2.Arm.Derive.savedSlots.map fun p => Instr.ldrSp p.1 p.2)) (freed 144 t) _
  rw [← List.append_nil (List.map _ _)]
  refine VG.Proof.Argon2.Arm.Derive.restoreSp_ok _ _ _ (by decide) (fun p hpm => ⟨?_, inS2 p.2 ?_⟩) fun u hu ho hm hrd hwr hsp => WP.block_nil ?_
  · simp only [Impl.Argon2.Arm.Derive.savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [Impl.Argon2.Arm.Derive.savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  -- The values restored.
  have key : ∀ j < 9, State.addr (S2.sp + BitVec.ofNat 32 (4 * (j + 1))) =
      State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (148 + 4 * j)) := fun j hj => by
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, S2sp, VG.Proof.Argon2.Arm.Derive.E_toNat (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 4 * (j + 1)) (by omega), Nat.mod_eq_of_lt (a := 148 + 4 * j) (by omega)]
    omega
  have tv : ∀ j (hj : j < 9), t.mem.readW (State.addr (S2.sp + BitVec.ofNat 32 (4 * (j + 1)))) 32 =
      s₀.gpr (VG.Proof.Argon2.Arm.Derive.savedRegs[j + 1]?.getD .r0) := fun j hj => by
    rw [key j hj]; exact d.saved j hj
  have hv : ∀ p ∈ Impl.Argon2.Arm.Derive.savedSlots, u.gpr p.1 = s₀.gpr p.1 := by
    intro p hpm
    rw [hu p hpm, spS2]
    have hm' : (freed 144 t).mem = t.mem := rfl
    rw [hm']
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
  refine ⟨⟨fun r hr => ?_, ?_⟩, hQ t _ q (by rw [popped_mem, popped_mem, hm]; rfl)⟩
  · have hr0 : r ≠ .r0 := by rintro rfl; simp [preserved] at hr
    have hr3 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr0, popped_gpr hr3]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hv (.r4, 4) (by decide), hv (.r5, 8) (by decide), hv (.r6, 12) (by decide), hv (.r7, 16) (by decide),
      hv (.r8, 20) (by decide), hv (.r9, 24) (by decide), hv (.r10, 28) (by decide), hv (.r11, 32) (by decide),
      hv (.lr, 36) (by decide)]
  · simp only [popped_sp, hsp, spS2, hS2, pushed_sp, List.length_cons, List.length_nil]
    rw [BitVec.sub_add_cancel, BitVec.sub_add_cancel]

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.Body`. -/
section

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
  · exact Offset.disjoint_of_le (by simp only [addr_toNat]; omega) (by simp only [addr_toNat]; omega)
  · exact (Offset.disjoint_of_le (r₁ := ⟨State.addr y, m⟩) (by simp only [addr_toNat]; omega)
      (by simp only [addr_toNat]; omega)).symm

theorem contains32 {x y : BitVec 32} {n m : Nat} (h₁ : y.toNat ≤ x.toNat)
    (h₂ : x.toNat + n ≤ y.toNat + m) :
    Region.Contains ⟨State.addr y, m⟩ (State.addr x) n := by
  simp only [Region.Contains]
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, addr_toNat]; exact h₁), addr_toNat, addr_toNat]
  omega

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
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt h]

/-! ## The regions of the body -/

section
variable (s₀ : State)

/-- The locals. -/
abbrev locR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀), 144⟩

/-- The stack below the locals: a call of `vg_argon2_hprime` and its frame. -/
abbrev callR : Region := stkR (VG.Proof.Argon2.Arm.Derive.E s₀) 40

/-- The regions the body may write. -/
abbrev bodyW : List Region := [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀, VG.Proof.Argon2.Arm.Derive.locR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀]

/-- The word at `[r11, #d]`. -/
abbrev lw (s : State) (d : Nat) : BitVec 32 := s.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) 32

end

theorem entry_gpr (s₀ : State) : (VG.Proof.Argon2.Arm.Derive.entry s₀).gpr = s₀.gpr := rfl
theorem entry_rd (s₀ : State) : (VG.Proof.Argon2.Arm.Derive.entry s₀).rd = s₀.rd := rfl

theorem entry_sp' (s₀ : State) : (VG.Proof.Argon2.Arm.Derive.entry s₀).sp = VG.Proof.Argon2.Arm.Derive.E s₀ := by
  simp only [VG.Proof.Argon2.Arm.Derive.entry, allocated, pushed_sp, List.length_cons, List.length_nil, BitVec.sub_sub,
    BitVec.ofNat_add_ofNat]

theorem loc_mem (s₀ : State) : VG.Proof.Argon2.Arm.Derive.locR s₀ ∈ (VG.Proof.Argon2.Arm.Derive.entry s₀).wr := by
  simp [VG.Proof.Argon2.Arm.Derive.entry, allocated, pushed, BitVec.sub_sub, BitVec.ofNat_add_ofNat]

theorem wr_mem (s₀ : State) {r : Region} (h : r ∈ s₀.wr) : r ∈ (VG.Proof.Argon2.Arm.Derive.entry s₀).wr := by
  simp only [VG.Proof.Argon2.Arm.Derive.entry, allocated, pushed, List.mem_cons]
  exact .inr (.inr (.inr h))

/-! ## The invariant -/

/-- The state of the body. -/
structure Inv (s₀ s : State) : Prop where
  sp : s.sp = VG.Proof.Argon2.Arm.Derive.E s₀
  r11 : s.gpr .r11 = VG.Proof.Argon2.Arm.Derive.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = (VG.Proof.Argon2.Arm.Derive.entry s₀).wr
  frame : Frame (VG.Proof.Argon2.Arm.Derive.bodyW s₀) (VG.Proof.Argon2.Arm.Derive.entry s₀).mem s.mem

/-- A step that writes registers other than `r11`, and memory within the body's regions. -/
theorem Inv.step {s₀ s t : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (hs : t.sp = s.sp)
    (hb : t.gpr .r11 = s.gpr .r11) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame (VG.Proof.Argon2.Arm.Derive.bodyW s₀) s.mem t.mem) : VG.Proof.Argon2.Arm.Derive.Inv s₀ t :=
  ⟨hs.trans h.sp, hb.trans h.r11, hrd.trans h.rd, hwr.trans h.wr, h.frame.trans hf⟩

theorem Inv.upd {s₀ s t : State} {r : Reg} {v : BitVec 32} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (u : Upd s t r v)
    (h₁ : r ≠ .r11) : VG.Proof.Argon2.Arm.Derive.Inv s₀ t :=
  h.step u.sp (u.other _ h₁.symm) u.rd u.wr (by rw [u.mem]; exact Frame.refl _ _)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem E_nat : (VG.Proof.Argon2.Arm.Derive.E s₀).toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 200 := sub_toNat' (by have := hp.sp_lo; omega)

theorem E_hi : (VG.Proof.Argon2.Arm.Derive.E s₀).toNat + 256 ≤ 2 ^ 32 := by
  have := hp.sp_hi; have := hp.sp_lo; rw [VG.Proof.Argon2.Arm.Derive.E_nat hp]; omega

theorem loc_nat {d : Nat} (hd : d < 256) : (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d).toNat = (VG.Proof.Argon2.Arm.Derive.E s₀).toNat + d :=
  VG.Proof.Argon2.Arm.Derive.add_nat (by have := VG.Proof.Argon2.Arm.Derive.E_hi hp; omega)

/-- A range above the stack the body's calls use, within the frames and locals. -/
theorem frame_stk {d n : Nat} (h : d + n ≤ 200) :
    Region.Sub ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), n⟩ (VG.Proof.Argon2.Arm.Derive.stkR0 s₀) := by
  have := hp.sp_lo; have := hp.sp_hi
  have h2 : (VG.Proof.Argon2.Arm.Derive.E0 s₀ - BitVec.ofNat 32 240).toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 240 := sub_toNat' (by omega)
  have e := VG.Proof.Argon2.Arm.Derive.E_nat hp
  have hh : State.addr (VG.Proof.Argon2.Arm.Derive.E0 s₀) - BitVec.ofNat 64 240 = State.addr (VG.Proof.Argon2.Arm.Derive.E0 s₀ - BitVec.ofNat 32 240) :=
    (addr_sub' (by omega)).symm
  have tL : (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d).toNat = (VG.Proof.Argon2.Arm.Derive.E s₀).toNat + d := VG.Proof.Argon2.Arm.Derive.loc_nat hp (by omega)
  show Region.Sub _ ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E0 s₀) - BitVec.ofNat 64 240, 240⟩
  rw [hh]
  exact VG.Proof.Argon2.Arm.Derive.sub32 (by rw [tL, h2]; omega) (by rw [tL, h2]; omega)

theorem call_stk : Region.Sub (VG.Proof.Argon2.Arm.Derive.callR s₀) (VG.Proof.Argon2.Arm.Derive.stkR0 s₀) := by
  have := hp.sp_lo; have := hp.sp_hi
  have e := VG.Proof.Argon2.Arm.Derive.E_nat hp
  have h1 : State.addr (VG.Proof.Argon2.Arm.Derive.E s₀) - BitVec.ofNat 64 40 = State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ - BitVec.ofNat 32 40) :=
    (addr_sub' (by omega)).symm
  have h2 : State.addr (VG.Proof.Argon2.Arm.Derive.E0 s₀) - BitVec.ofNat 64 240 = State.addr (VG.Proof.Argon2.Arm.Derive.E0 s₀ - BitVec.ofNat 32 240) :=
    (addr_sub' (by omega)).symm
  show Region.Sub ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀) - BitVec.ofNat 64 40, 40⟩ ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E0 s₀) - BitVec.ofNat 64 240, 240⟩
  have t1 : (VG.Proof.Argon2.Arm.Derive.E s₀ - BitVec.ofNat 32 40).toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 240 := by rw [sub_toNat' (by omega), e]; omega
  have t2 : (VG.Proof.Argon2.Arm.Derive.E0 s₀ - BitVec.ofNat 32 240).toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 240 := sub_toNat' (by omega)
  rw [h1, h2]
  exact VG.Proof.Argon2.Arm.Derive.sub32 (by rw [t1, t2]) (by rw [t1, t2]; omega)

/-- A word of the locals. -/
theorem loc_in {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions s.wr (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) 4 := by
  rw [h.wr]
  exact ⟨VG.Proof.Argon2.Arm.Derive.locR s₀, VG.Proof.Argon2.Arm.Derive.loc_mem s₀, VG.Proof.Argon2.Arm.Derive.contains32 (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := d) (by omega)]; omega)
    (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := d) (by omega)]; omega)⟩

theorem loc_in' {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions (s.rd ++ s.wr) (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) 4 :=
  let ⟨r, hr, hc⟩ := VG.Proof.Argon2.Arm.Derive.loc_in hp h hd
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- What lies above the locals is outside the body's regions. -/
theorem above_disj {a : BitVec 32} {n : Nat} (ha : (VG.Proof.Argon2.Arm.Derive.E s₀).toNat + 144 ≤ a.toNat)
    (ha' : a.toNat + n ≤ (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat + 56)
    (hm : Region.Disjoint ⟨State.addr a, n⟩ (VG.Proof.Argon2.Arm.Derive.memR s₀)) (hs : Region.Disjoint ⟨State.addr a, n⟩ (VG.Proof.Argon2.Arm.Derive.scrR s₀))
    (ho : Region.Disjoint ⟨State.addr a, n⟩ (VG.Proof.Argon2.Arm.Derive.outR s₀)) :
    ∀ r ∈ VG.Proof.Argon2.Arm.Derive.bodyW s₀, Region.Disjoint ⟨State.addr a, n⟩ r := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := VG.Proof.Argon2.Arm.Derive.E_nat hp
  intro r hr
  simp only [VG.Proof.Argon2.Arm.Derive.bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hm
  · exact hs
  · exact ho
  · exact VG.Proof.Argon2.Arm.Derive.disj32 (.inr (by omega)) (by omega) (by omega)
  · show Region.Disjoint _ ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀) - BitVec.ofNat 64 40, 40⟩
    rw [← addr_sub' (by omega)]
    exact VG.Proof.Argon2.Arm.Derive.disj32 (.inr (by rw [sub_toNat' (by omega)]; omega)) (by omega)
      (by rw [sub_toNat' (by omega)]; omega)

/-! ## The frames' words -/

theorem S1_nat : (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).sp.toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 16 := VG.Proof.Argon2.Arm.Derive.sp1 (by have := hp.sp_lo; omega)

/-- What the first push leaves above `E0 - 16`, and the memory above it. -/
theorem entry_frame : Frame [stkR (VG.Proof.Argon2.Arm.Derive.E0 s₀) 56] s₀.mem (VG.Proof.Argon2.Arm.Derive.entry s₀).mem := by
  have := hp.sp_lo
  have e0 : (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat = s₀.sp.toNat := rfl
  have s1 := VG.Proof.Argon2.Arm.Derive.S1_nat hp
  have f₁ := VG.Proof.Argon2.Arm.pushed_stk (rs := VG.Proof.Argon2.Arm.Derive.argRegs) (s := s₀) (by simp only [List.length_cons, List.length_nil]; omega)
  have f₂ := VG.Proof.Argon2.Arm.pushed_stk (rs := VG.Proof.Argon2.Arm.Derive.savedRegs) (s := pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀) (by simp only [List.length_cons, List.length_nil]; omega)
  refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, VG.Proof.Argon2.Arm.stkR_sub (by simp) (by omega)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    have := VG.Proof.Argon2.Arm.stkR_inner (sp := VG.Proof.Argon2.Arm.Derive.E0 s₀) (a := 4 * savedRegs.length) (k := 16) (b := 56)
      (by simp) (by omega)
    simpa [pushed_sp] using this

/-- Word `j` of the second frame: `savedRegs[j]`. -/
theorem entry_saved {j : Nat} (hj : j < 10) :
    (VG.Proof.Argon2.Arm.Derive.entry s₀).mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (144 + 4 * j))) 32 =
      s₀.gpr (VG.Proof.Argon2.Arm.Derive.savedRegs[j]?.getD .r0) := by
  have := hp.sp_lo; have := hp.sp_hi
  have s1 := VG.Proof.Argon2.Arm.Derive.S1_nat hp
  have e := VG.Proof.Argon2.Arm.Derive.E_nat hp
  have := VG.Proof.Argon2.Arm.storeWords_readW (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).mem
    ((pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length))
    (savedRegs.map (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).gpr) (by
      simp only [List.length_map, List.length_cons, List.length_nil]
      rw [sub_toNat' (by rw [s1]; omega), s1]; omega) (i := j) (by simpa using hj)
  rw [List.getElem_map] at this
  have ea : (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length) + BitVec.ofNat 32 (4 * j) =
      VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (144 + 4 * j) := by
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := 144 + 4 * j) (by omega), BitVec.toNat_add, sub_toNat' (by simp only [List.length_cons, List.length_nil]; rw [s1]; omega), s1, BitVec.toNat_ofNat]
    simp only [List.length_cons, List.length_nil]
    rw [Nat.mod_eq_of_lt (a := 4 * j) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [ea] at this
  refine this.trans ?_
  simp only [pushed_gpr, List.getElem?_eq_getElem (show j < savedRegs.length by simpa using hj),
    Option.getD_some]

/-- Word `i` of the first frame: register argument `i`. -/
theorem entry_regArg {i : Nat} (hi : i < 4) :
    (VG.Proof.Argon2.Arm.Derive.entry s₀).mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (184 + 4 * i))) 32 = VG.Proof.Argon2.Arm.Derive.arg s₀ i := by
  have := hp.sp_lo; have := hp.sp_hi
  have s1 := VG.Proof.Argon2.Arm.Derive.S1_nat hp
  have e := VG.Proof.Argon2.Arm.Derive.E_nat hp
  have e0 : (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat = s₀.sp.toNat := rfl
  have := VG.Proof.Argon2.Arm.storeWords_readW s₀.mem (s₀.sp - BitVec.ofNat 32 (4 * argRegs.length))
    (argRegs.map s₀.gpr) (by
      simp only [List.length_map, List.length_cons, List.length_nil]
      rw [sub_toNat' (by omega)]; omega) (i := i) (by simpa using hi)
  rw [List.getElem_map] at this
  have ea : s₀.sp - BitVec.ofNat 32 (4 * argRegs.length) + BitVec.ofNat 32 (4 * i) =
      VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (184 + 4 * i) := by
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := 184 + 4 * i) (by omega), BitVec.toNat_add, sub_toNat' (by simp only [List.length_cons, List.length_nil]; omega), BitVec.toNat_ofNat]
    simp only [List.length_cons, List.length_nil]
    rw [Nat.mod_eq_of_lt (a := 4 * i) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [ea] at this
  -- The second push and the allocation keep the first frame.
  have keep : (VG.Proof.Argon2.Arm.Derive.entry s₀).mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (184 + 4 * i))) 32 =
      (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (184 + 4 * i))) 32 := by
    refine (VG.Proof.Argon2.Arm.pushed_stk (rs := VG.Proof.Argon2.Arm.Derive.savedRegs) (s := pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀) (by simp only [List.length_cons, List.length_nil]; omega)).readW
      (r := ⟨_, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    have tS : ((pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length)).toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 56 := by
      rw [sub_toNat' (by simp only [List.length_cons, List.length_nil]; omega), s1]
      simp only [List.length_cons, List.length_nil]; omega
    have tL : (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (184 + 4 * i)).toNat = (VG.Proof.Argon2.Arm.Derive.E s₀).toNat + (184 + 4 * i) := VG.Proof.Argon2.Arm.Derive.loc_nat hp (by omega)
    show Region.Disjoint _ ⟨State.addr (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).sp - BitVec.ofNat 64 (4 * savedRegs.length), _⟩
    rw [← addr_sub' (by simp only [List.length_cons, List.length_nil]; omega)]
    have hc : savedRegs.length = 10 := rfl
    exact VG.Proof.Argon2.Arm.Derive.disj32 (.inr (by rw [tS, tL]; omega)) (by rw [tL]; omega) (by rw [tS]; omega)
  refine keep.trans (this.trans ?_)
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The stack arguments, above the frames, are as on entry. -/
theorem entry_stackArg {i : Nat} (hi : 4 ≤ i) (hi' : i < 18) :
    (VG.Proof.Argon2.Arm.Derive.entry s₀).mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (184 + 4 * i))) 32 = VG.Proof.Argon2.Arm.Derive.arg s₀ i := by
  have := hp.sp_lo; have := hp.sp_hi
  have e := VG.Proof.Argon2.Arm.Derive.E_nat hp
  have e0 : (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat = s₀.sp.toNat := rfl
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 4 := ⟨i - 4, by omega⟩
  have ea : VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (184 + 4 * (k + 4)) = s₀.sp + BitVec.ofNat 32 (4 * k) := by
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := 184 + 4 * (k + 4)) (by omega), VG.Proof.Argon2.Arm.Derive.add_nat (x := s₀.sp) (k := 4 * k) (by omega)]; omega
  rw [ea, (VG.Proof.Argon2.Arm.Derive.entry_frame hp).readW (r := ⟨_, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
  · rfl
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  show Region.Disjoint _ ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E0 s₀) - BitVec.ofNat 64 56, 56⟩
  rw [← addr_sub' (by omega)]
  exact VG.Proof.Argon2.Arm.Derive.disj32 (.inr (by rw [sub_toNat' (by omega), VG.Proof.Argon2.Arm.Derive.add_nat (x := s₀.sp) (k := 4 * k) (by omega)]; omega)) (by rw [VG.Proof.Argon2.Arm.Derive.add_nat (x := s₀.sp) (k := 4 * k) (by omega)]; omega)
    (by rw [sub_toNat' (by omega)]; omega)

/-! ## What the body keeps -/

theorem Inv.done {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) : VG.Proof.Argon2.Arm.Derive.BodyDone s₀ s := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := VG.Proof.Argon2.Arm.Derive.E_nat hp
  refine ⟨h.sp, fun j hj => ?_⟩
  have st := VG.Proof.Argon2.Arm.Derive.frame_stk hp (d := 148 + 4 * j) (n := 4) (by omega)
  rw [h.frame.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
  · rw [show 148 + 4 * j = 144 + 4 * (j + 1) by omega, VG.Proof.Argon2.Arm.Derive.entry_saved hp (by omega)]
  refine VG.Proof.Argon2.Arm.Derive.above_disj hp (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := 148 + 4 * j) (by omega)]; omega) (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := 148 + 4 * j) (by omega)]; omega) ?_ ?_ ?_
  · exact ((hp.stk_all _ (by simp)).sub_left st)
  · exact ((hp.stk_all _ (by simp)).sub_left st)
  · exact ((hp.stk_all _ (by simp)).sub_left st)

/-- The word of argument `i`, above the locals. -/
theorem arg_disj {i : Nat} (hi : i < 18) :
    ∀ r ∈ VG.Proof.Argon2.Arm.Derive.bodyW s₀, Region.Disjoint
      ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (Impl.Argon2.Arm.Derive.argOff i)), 4⟩ r := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := VG.Proof.Argon2.Arm.Derive.E_nat hp
  have e0 : (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat = s₀.sp.toNat := rfl
  simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]
  refine VG.Proof.Argon2.Arm.Derive.above_disj hp (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := 144 + 40 + 4 * i) (by omega)]; omega) (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := 144 + 40 + 4 * i) (by omega)]; omega) ?_ ?_ ?_
    <;> by_cases h4 : i < 4
  all_goals first
    | (have st := VG.Proof.Argon2.Arm.Derive.frame_stk hp (d := 184 + 4 * i) (n := 4) (by omega)
       exact (hp.stk_all _ (by simp)).sub_left st)
    | (have sa : Region.Sub ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (144 + 40 + 4 * i)), 4⟩ (VG.Proof.Argon2.Arm.Derive.argR s₀) := by
         show Region.Sub _ ⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 56⟩
         exact VG.Proof.Argon2.Arm.Derive.sub32 (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := 144 + 40 + 4 * i) (by omega), VG.Proof.Argon2.Arm.Derive.add_nat (x := s₀.sp) (k := 4 * 0) (by omega)]; omega)
           (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := 144 + 40 + 4 * i) (by omega), VG.Proof.Argon2.Arm.Derive.add_nat (x := s₀.sp) (k := 4 * 0) (by omega)]; omega)
       exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sa)

theorem Inv.arg {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {i : Nat} (hi : i < 18) :
    VG.Proof.Argon2.Arm.Derive.lw s₀ s (Impl.Argon2.Arm.Derive.argOff i) = VG.Proof.Argon2.Arm.Derive.arg s₀ i := by
  rw [VG.Proof.Argon2.Arm.Derive.lw, h.frame.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) (VG.Proof.Argon2.Arm.Derive.arg_disj hp hi) (by decide)]
  simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]
  rw [show 144 + 40 + 4 * i = 184 + 4 * i by omega]
  by_cases h4 : i < 4
  · exact VG.Proof.Argon2.Arm.Derive.entry_regArg hp h4
  · exact VG.Proof.Argon2.Arm.Derive.entry_stackArg hp (by omega) hi

theorem Inv.arg_in {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {i : Nat} (hi : i < 18) :
    InRegions (s.rd ++ s.wr) (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (Impl.Argon2.Arm.Derive.argOff i))) 4 := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := VG.Proof.Argon2.Arm.Derive.E_nat hp
  have e0 : (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat = s₀.sp.toNat := rfl
  have s1 := VG.Proof.Argon2.Arm.Derive.S1_nat hp
  simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]
  rw [h.rd, h.wr]
  by_cases h4 : i < 4
  · -- The first frame, writable.
    refine ⟨⟨State.addr (s₀.sp - BitVec.ofNat 32 (4 * argRegs.length)), 4 * argRegs.length⟩,
      List.mem_append_right _ (by simp [VG.Proof.Argon2.Arm.Derive.entry, allocated, pushed]), ?_⟩
    have tA : (s₀.sp - BitVec.ofNat 32 (4 * argRegs.length)).toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 16 := by
      rw [sub_toNat' (by simp only [List.length_cons, List.length_nil]; omega)]
      simp only [List.length_cons, List.length_nil]
    have tL : (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (144 + 40 + 4 * i)).toNat = (VG.Proof.Argon2.Arm.Derive.E s₀).toNat + (144 + 40 + 4 * i) :=
      VG.Proof.Argon2.Arm.Derive.loc_nat hp (by omega)
    exact VG.Proof.Argon2.Arm.Derive.contains32 (by rw [tL, tA]; omega) (by rw [tL, tA]; simp only [List.length_cons, List.length_nil]; omega)
  · refine ⟨VG.Proof.Argon2.Arm.Derive.argR s₀, List.mem_append_left _ (by rw [hp.rd]; simp), ?_⟩
    show Region.Contains ⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 56⟩ _ _
    exact VG.Proof.Argon2.Arm.Derive.contains32 (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := 144 + 40 + 4 * i) (by omega), VG.Proof.Argon2.Arm.Derive.add_nat (x := s₀.sp) (k := 4 * 0) (by omega)]; omega)
      (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := 144 + 40 + 4 * i) (by omega), VG.Proof.Argon2.Arm.Derive.add_nat (x := s₀.sp) (k := 4 * 0) (by omega)]; omega)

/-- The inputs are kept. -/
theorem Inv.input {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {R : Region}
    (hR : R ∈ [VG.Proof.Argon2.Arm.Derive.pwR s₀, VG.Proof.Argon2.Arm.Derive.saltR s₀, VG.Proof.Argon2.Arm.Derive.secR s₀, VG.Proof.Argon2.Arm.Derive.adR s₀]) :
    bytesAt s.mem R.base R.len = bytesAt s₀.mem R.base R.len := by
  have hR' : R ∈ [VG.Proof.Argon2.Arm.Derive.pwR s₀, VG.Proof.Argon2.Arm.Derive.saltR s₀, VG.Proof.Argon2.Arm.Derive.secR s₀, VG.Proof.Argon2.Arm.Derive.adR s₀, VG.Proof.Argon2.Arm.Derive.argR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> simp
  have hS : R ∈ [VG.Proof.Argon2.Arm.Derive.pwR s₀, VG.Proof.Argon2.Arm.Derive.saltR s₀, VG.Proof.Argon2.Arm.Derive.secR s₀, VG.Proof.Argon2.Arm.Derive.adR s₀, VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀] := by
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
  · exact (VG.Proof.Argon2.Arm.Derive.entry_frame hp).bytes (R := R) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact stk.sub_right (VG.Proof.Argon2.Arm.stkR_sub (by decide) (by omega))) hl hi
  simp only [VG.Proof.Argon2.Arm.Derive.bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact stk.sub_right (by simpa using VG.Proof.Argon2.Arm.Derive.frame_stk hp (d := 0) (n := 144) (by decide))
  · exact stk.sub_right (VG.Proof.Argon2.Arm.Derive.call_stk hp)

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.Locals`. -/
section

/-!
# Argon2 on ARMv7: the derivation's locals

`lw s₀ s d`: the word at `[r11, #d]` in the body. A store to the locals keeps
the invariant and every other word (`Inv.store_loc`); writes to the memory
matrix, `scratch`, the output or the stack below the locals keep all of them
(`lw_keep`).
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Argon2.Arm (stkR addr_toNat)
open VG.Proof.MdStream.Arm (Upd Mupd wp_ldr wp_str)
open VG.Impl.Argon2.Arm.Derive (ld st)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem loc_addr {d : Nat} (hd : d < 256) :
    State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d) = State.addr (VG.Proof.Argon2.Arm.Derive.E s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := VG.Proof.Argon2.Arm.Derive.E_hi hp; omega)

/-- Another word of the frame, after a store to the locals. -/
theorem lw_store {m : Mem} {d e : Nat} (hd : d + 4 ≤ 256) (he : e + 4 ≤ 256) (hde : d + 4 ≤ e ∨ e + 4 ≤ d)
    (v : BitVec 32) :
    (m.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) v).readW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 e)) 32 =
      m.readW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 e)) 32 := by
  rw [VG.Proof.Argon2.Arm.Derive.loc_addr hp (by omega), VG.Proof.Argon2.Arm.Derive.loc_addr hp (by omega)]
  exact MdStream.Arm.readW_writeW_save m _ v (by omega) (by omega) (by omega)

theorem Inv.store_loc {s t : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {v : BitVec 32}
    (u : Mupd s t (s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) v)) :
    VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ VG.Proof.Argon2.Arm.Derive.lw s₀ t d = v ∧ ∀ e, e + 4 ≤ 256 → (d + 4 ≤ e ∨ e + 4 ≤ d) → VG.Proof.Argon2.Arm.Derive.lw s₀ t e = VG.Proof.Argon2.Arm.Derive.lw s₀ s e := by
  refine ⟨h.step u.sp (by rw [u.gpr]) u.rd u.wr ?_, ?_, fun e he hde => ?_⟩
  · rw [u.mem]
    exact (Frame.refl _ _).writeW (r := VG.Proof.Argon2.Arm.Derive.locR s₀) (by simp) v
      (VG.Proof.Argon2.Arm.Derive.contains32 (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := d) (by omega)]; omega) (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := d) (by omega)]; omega))
  · show t.mem.readW _ 32 = v
    rw [u.mem, Mem.readW_writeW_self32]
  · show t.mem.readW _ 32 = _
    rw [u.mem, VG.Proof.Argon2.Arm.Derive.lw_store hp (by omega) he hde]

/-- `str r, [r11, #d]` -/
theorem wp_stloc {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → VG.Proof.Argon2.Arm.Derive.lw s₀ t d = s.gpr r → (∀ e, e + 4 ≤ 256 → (d + 4 ≤ e ∨ e + 4 ≤ d) →
      VG.Proof.Argon2.Arm.Derive.lw s₀ t e = VG.Proof.Argon2.Arm.Derive.lw s₀ s e) → t.gpr = s.gpr → t.mem = s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d))
      (s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (VG.Impl.Argon2.Arm.Derive.st d r :: is)) s Q :=
  wp_str (by omega) (by rw [h.r11]) (VG.Proof.Argon2.Arm.Derive.loc_in hp h hd) fun t u =>
    let ⟨i, v, o⟩ := h.store_loc hp hd u
    k t i v o u.gpr u.mem

/-- `ldr r, [r11, #d]` -/
theorem wp_ldloc {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (VG.Proof.Argon2.Arm.Derive.lw s₀ s d) → WP isa (.block is) t Q) :
    WP isa (.block (ld r d :: is)) s Q :=
  wp_ldr (by omega) (by rw [h.r11]) (VG.Proof.Argon2.Arm.Derive.loc_in' hp h hd) k

/-- `ldr r, [r11, #argOff i]` -/
theorem wp_ldarg {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (VG.Proof.Argon2.Arm.Derive.arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (ld r (Impl.Argon2.Arm.Derive.argOff i) :: is)) s Q :=
  wp_ldr (by simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]; omega) (by rw [h.r11])
    (h.arg_in hp hi) fun t u => k t (by have := h.arg hp hi; simp only [VG.Proof.Argon2.Arm.Derive.lw] at this; rw [this] at u; exact u)

/-- The locals are outside the memory matrix, `scratch`, the output and the stack below them. -/
theorem loc_disj {d : Nat} (hd : d + 4 ≤ 144) :
    ∀ r ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀],
      Region.Disjoint ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), 4⟩ r := by
  have := hp.sp_lo
  have hE := VG.Proof.Argon2.Arm.Derive.E_nat hp
  have sub := VG.Proof.Argon2.Arm.Derive.frame_stk hp (d := d) (n := 4) (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · show Region.Disjoint _ ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀) - BitVec.ofNat 64 40, 40⟩
    rw [← addr_sub' (by omega)]
    exact VG.Proof.Argon2.Arm.Derive.disj32 (.inr (by rw [sub_toNat' (by omega), VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := d) (by omega)]; omega))
      (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := d) (by omega)]; have := VG.Proof.Argon2.Arm.Derive.E_hi hp; omega) (by rw [sub_toNat' (by omega)]; omega)

/-- The locals are kept by writes outside them. -/
theorem lw_keep {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀], Region.Sub r r') {d : Nat}
    (hd : d + 4 ≤ 144) : VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d :=
  (f.sub hs).readW (Region.contains_self _ _) (VG.Proof.Argon2.Arm.Derive.loc_disj hp hd) (by decide)

end

/-- The body's first instruction points `r11` to the locals. -/
theorem inv_start {s₀ : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → t.mem = (VG.Proof.Argon2.Arm.Derive.entry s₀).mem → (∀ r, r ≠ .r11 → t.gpr r = (VG.Proof.Argon2.Arm.Derive.entry s₀).gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (.addSp .r11 0 :: is)) (VG.Proof.Argon2.Arm.Derive.entry s₀) Q := by
  refine MdStream.Arm.WP.cons (s' := (VG.Proof.Argon2.Arm.Derive.entry s₀).setReg .r11 ((VG.Proof.Argon2.Arm.Derive.entry s₀).sp + BitVec.ofNat 32 0)) (by
    simp [exec]) ?_
  have u := MdStream.Arm.Upd.setReg (VG.Proof.Argon2.Arm.Derive.entry s₀) .r11 ((VG.Proof.Argon2.Arm.Derive.entry s₀).sp + BitVec.ofNat 32 0)
  have esp : (VG.Proof.Argon2.Arm.Derive.entry s₀).sp = VG.Proof.Argon2.Arm.Derive.E s₀ := VG.Proof.Argon2.Arm.Derive.entry_sp' s₀
  refine k _ ⟨by rw [u.sp, esp], by rw [u.gpr, esp]; simp, by rw [u.rd, VG.Proof.Argon2.Arm.Derive.entry_rd], by rw [u.wr],
    by rw [u.mem]; exact Frame.refl _ _⟩ u.mem u.other

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.Parameters`. -/
section

/-!
# Argon2 on ARMv7: the parameters

`parameters_ok`: the body's first instructions point `r11` to the locals and
store there `4 · lanes` (the divisor), the segment length (by the fixed-time
division), the lane length and its size in bytes (`Prm`).
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov op2_lsl)
open VG.Impl.Argon2.Arm.Derive (parameters divisorOff segLenOff laneLenOff strideOff argOff)

/-- The parameters in the locals. -/
structure Prm (s₀ s : State) : Prop where
  divisor : VG.Proof.Argon2.Arm.Derive.lw s₀ s divisorOff = BitVec.ofNat 32 (4 * VG.Proof.Argon2.Arm.Derive.lanesN s₀)
  segLen : VG.Proof.Argon2.Arm.Derive.lw s₀ s segLenOff = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen
  laneLen : VG.Proof.Argon2.Arm.Derive.lw s₀ s laneLenOff = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen
  stride : VG.Proof.Argon2.Arm.Derive.lw s₀ s strideOff = BitVec.ofNat 32 ((VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen * 1024)

theorem lw_mem {s₀ s t : State} (h : t.mem = s.mem) (d : Nat) : VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d := by
  simp only [VG.Proof.Argon2.Arm.Derive.lw, h]

theorem Inv.keep {s₀ s t : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (k : Divide.Keep s t) : VG.Proof.Argon2.Arm.Derive.Inv s₀ t :=
  h.step k.sp (k.other _ (by decide) (by decide) (by decide)) k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _)

/-- `x << n`, as a number, when it does not overflow. -/
theorem shl_nat {x : BitVec 32} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 32) : (x <<< n).toNat = x.toNat * 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem parameters_ok {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → VG.Proof.Argon2.Arm.Derive.Prm s₀ t → WP isa (.block is) t Q) :
    WP isa (.block ((.addSp .r11 0 :: parameters) ++ is)) (VG.Proof.Argon2.Arm.Derive.entry s₀) Q := by
  have hL := hp.lanes_lt
  have hL1 := hp.lanes_pos
  have hBl := hp.blocks_lt
  have hb := hp.blocks_eq
  have hseg := hp.segLen_eq
  have hlane := hp.laneLen_eq
  simp only [parameters, List.cons_append, List.append_assoc]
  refine VG.Proof.Argon2.Arm.Derive.inv_start fun s₁ i₁ _ _ => ?_
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₁ (i := Impl.Argon2.Arm.Derive.lanesArg) (by decide) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide)
  refine wp_mov (op2_lsl (by decide)) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide)
  have e₃ : (s₃.gpr .r2).toNat = 4 * VG.Proof.Argon2.Arm.Derive.lanesN s₀ := by
    rw [u₃.gpr, u₂.gpr, VG.Proof.Argon2.Arm.Derive.shl_nat (by have : (VG.Proof.Argon2.Arm.Derive.arg s₀ 7).toNat < 2 ^ 24 := hL; show (VG.Proof.Argon2.Arm.Derive.arg s₀ 7).toNat * 4 < _; omega)]
    show (VG.Proof.Argon2.Arm.Derive.arg s₀ 7).toNat * 4 = 4 * (VG.Proof.Argon2.Arm.Derive.arg s₀ 7).toNat
    omega
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₃ (d := divisorOff) (by decide) fun s₄ i₄ v₄ _ g₄ _ => ?_
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₄ (i := Impl.Argon2.Arm.Derive.memoryCostArg) (by decide) fun s₅ u₅ => ?_
  have i₅ := i₄.upd u₅ (by decide)
  have r2₅ : s₅.gpr .r2 = s₃.gpr .r2 := by rw [u₅.other _ (by decide), g₄]
  refine Divide.code_ok (D := s₃.gpr .r2) (by rw [e₃]; omega) (by rw [e₃]; omega) r2₅ fun s₆ c₆ _ k₆ => ?_
  have i₆ := i₅.keep k₆
  rw [u₅.gpr, e₃] at c₆
  have c₆' : (s₆.gpr .r1).toNat = (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen := by rw [c₆, hseg]; rfl
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₆ (d := segLenOff) (by decide) fun s₇ i₇ v₇ o₇ g₇ _ => ?_
  have hll : (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ :=
    Nat.le_trans (Nat.le_mul_of_pos_left _ hL1) (Nat.le_of_eq hb.symm)
  have hsegL : (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen * 1024 + 16384 ≤ 2 ^ 32 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right 1024 hll) _) hBl
  refine wp_mov (op2_lsl (by decide)) fun s₈ u₈ => ?_
  have i₈ := i₇.upd u₈ (by decide)
  have e₈ : (s₈.gpr .r1).toNat = (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen := by
    rw [u₈.gpr, g₇, VG.Proof.Argon2.Arm.Derive.shl_nat (by rw [c₆']; omega), c₆', hlane]; omega
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₈ (d := laneLenOff) (by decide) fun s₉ i₉ v₉ o₉ g₉ _ => ?_
  refine wp_mov (op2_lsl (by decide)) fun s₁₀ u₁₀ => ?_
  have i₁₀ := i₉.upd u₁₀ (by decide)
  have e₁₀ : (s₁₀.gpr .r1).toNat = (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen * 1024 := by
    rw [u₁₀.gpr, g₉, VG.Proof.Argon2.Arm.Derive.shl_nat (by rw [e₈]; omega), e₈]
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₁₀ (d := strideOff) (by decide) fun s₁₁ i₁₁ v₁₁ o₁₁ _ _ => k s₁₁ i₁₁ ⟨?_, ?_, ?_, ?_⟩
  · rw [o₁₁ _ (by decide) (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem u₁₀.mem, o₉ _ (by decide) (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem u₈.mem,
      o₇ _ (by decide) (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem k₆.mem, VG.Proof.Argon2.Arm.Derive.lw_mem u₅.mem, v₄]
    exact BitVec.eq_of_toNat_eq (by rw [e₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [o₁₁ _ (by decide) (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem u₁₀.mem, o₉ _ (by decide) (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem u₈.mem, v₇]
    exact BitVec.eq_of_toNat_eq (by rw [c₆', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [o₁₁ _ (by decide) (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem u₁₀.mem, v₉]
    exact BitVec.eq_of_toNat_eq (by rw [e₈, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [v₁₁]
    exact BitVec.eq_of_toNat_eq (by rw [e₁₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.Scratch`. -/
section

/-!
# Argon2 on ARMv7: the derivation's use of H′'s hash macros

The H₀ code calls the BLAKE2b functions through H′'s macros
(`Impl.Argon2.Arm.HPrime`), with `r4` pointing to `scratch` and the stack
below the locals: `ctx` gives their context (`HPrime.Ctx`), and `Inv.keeps`
the body's invariant and locals after them.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Argon2.Arm (stkR)
open VG.Proof.MdStream.Arm (Upd Mupd)
open VG.Proof.Argon2.Arm.HPrime (Ctx Keeps)

/-- `n` bytes of `scratch` at offset `d`. -/
theorem scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 16384) :
    Region.Sub ⟨State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 d, n⟩ (VG.Proof.Argon2.Arm.Derive.scrR s₀) := Offset.sub_base _ h

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem scr_mem : VG.Proof.Argon2.Arm.Derive.scrR s₀ ∈ (VG.Proof.Argon2.Arm.Derive.entry s₀).wr := VG.Proof.Argon2.Arm.Derive.wr_mem s₀ (by rw [hp.wr]; simp)
theorem mem_mem : VG.Proof.Argon2.Arm.Derive.memR s₀ ∈ (VG.Proof.Argon2.Arm.Derive.entry s₀).wr := VG.Proof.Argon2.Arm.Derive.wr_mem s₀ (by rw [hp.wr]; simp)
theorem out_mem : VG.Proof.Argon2.Arm.Derive.outR s₀ ∈ (VG.Proof.Argon2.Arm.Derive.entry s₀).wr := VG.Proof.Argon2.Arm.Derive.wr_mem s₀ (by rw [hp.wr]; simp)

/-- The 32 bytes below the locals that H′'s macros use are within the stack below them. -/
theorem stk32_call : Region.Sub (stkR (VG.Proof.Argon2.Arm.Derive.E s₀) 32) (VG.Proof.Argon2.Arm.Derive.callR s₀) :=
  VG.Proof.Argon2.Arm.stkR_sub (by decide) (by rw [VG.Proof.Argon2.Arm.Derive.E_nat hp]; have := hp.sp_lo; omega)

theorem ctx {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (hb : s.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀) : Ctx (VG.Proof.Argon2.Arm.Derive.scrP s₀) (VG.Proof.Argon2.Arm.Derive.E s₀) s := by
  have := hp.scr_fits
  refine ⟨hb, h.sp, by omega, by rw [VG.Proof.Argon2.Arm.Derive.E_nat hp]; have := hp.sp_lo; omega, ?_, ?_⟩
  · rw [h.wr]
    exact (Covers.of_sub (rs' := [VG.Proof.Argon2.Arm.Derive.scrR s₀]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
      (fun a n ⟨r, hr, hc⟩ => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Argon2.Arm.Derive.scr_mem hp, hc⟩)
  · exact ((hp.stk_all (VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp)).sub_left fun a ha => VG.Proof.Argon2.Arm.Derive.call_stk hp a (VG.Proof.Argon2.Arm.Derive.stk32_call hp a ha)).sub_right
      (Region.sub_prefix (by decide))

/-- What H′'s macros keep keeps the body's invariant and the locals. -/
theorem Inv.keeps {s t : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (k : Keeps (VG.Proof.Argon2.Arm.Derive.scrP s₀) (VG.Proof.Argon2.Arm.Derive.E s₀) s t) :
    VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d := by
  have sub : ∀ r ∈ [(⟨State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀), 832⟩ : Region), stkR (VG.Proof.Argon2.Arm.Derive.E s₀) 32],
      ∃ r' ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.Argon2.Arm.Derive.callR s₀, by simp, VG.Proof.Argon2.Arm.Derive.stk32_call hp⟩
  refine ⟨h.step k.sp (k.gpr _ (by decide)) k.rd k.wr (k.frame.sub fun r hr => ?_),
    fun d hd => VG.Proof.Argon2.Arm.Derive.lw_keep hp k.frame sub hd⟩
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

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.Initial`. -/
section

/-!
# Argon2 on ARMv7: H₀

`HI s₀ data s`: the BLAKE2b state at `scratch` has absorbed `data`, whose
length is in the locals. `start_ok` absorbs the header, `absorb_ok` an
input with its length prefix, `finish_ok` writes the digest to the first 64
bytes of the locals: `code_ok`, H₀ (`Spec.Argon2.initialHash`).
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_ldr wp_str op2_imm op2_reg)
open VG.Proof.Blake2.Arm.Stream (wp_adds wp_adc)
open VG.Spec.Blake2 (Repr b bytesAt)
open VG.Proof.Argon2.Arm.HPrime (Ctx Keeps)
open VG.Impl.Argon2.Arm.Derive (countLoOff countHiOff argOff ld st)

/-- H₀'s streaming state at `scratch`, with `data` absorbed. -/
structure HI (s₀ : State) (data : List Byte) (s : State) : Prop where
  inv : VG.Proof.Argon2.Arm.Derive.Inv s₀ s
  prm : VG.Proof.Argon2.Arm.Derive.Prm s₀ s
  r4 : s.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀
  repr : Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)) data
  lo : VG.Proof.Argon2.Arm.Derive.lw s₀ s countLoOff = BitVec.ofNat 32 data.length
  hi : VG.Proof.Argon2.Arm.Derive.lw s₀ s countHiOff = BitVec.ofNat 32 (data.length / 2 ^ 32)
  len : data.length < 2 ^ 36

theorem Prm.of_lw {s₀ s t : State} (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s)
    (h : ∀ d ∈ [Impl.Argon2.Arm.Derive.divisorOff, Impl.Argon2.Arm.Derive.segLenOff,
      Impl.Argon2.Arm.Derive.laneLenOff, Impl.Argon2.Arm.Derive.strideOff], VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d) :
    VG.Proof.Argon2.Arm.Derive.Prm s₀ t :=
  ⟨by rw [h _ (by simp)]; exact pr.divisor, by rw [h _ (by simp)]; exact pr.segLen,
    by rw [h _ (by simp)]; exact pr.laneLen, by rw [h _ (by simp)]; exact pr.stride⟩

/-- The parameters are kept when the locals at the offsets of `prmOk` are. -/
theorem prm_offs : ∀ d ∈ [Impl.Argon2.Arm.Derive.divisorOff, Impl.Argon2.Arm.Derive.segLenOff,
    Impl.Argon2.Arm.Derive.laneLenOff, Impl.Argon2.Arm.Derive.strideOff],
    d + 4 ≤ 144 ∧ 72 ≤ d ∧ (d + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ d) := by decide

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem scr_addr {o : Nat} (ho : o < 16384) :
    State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 o) = State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o :=
  addr_add (by have := hp.scr_fits; omega)

/-- `str r, [r4, #o]`, to `scratch`. -/
theorem wp_stscr {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (hb : s.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀) {o : Nat} (ho : o + 4 ≤ 4096)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → t.mem = s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o) (s.gpr r) →
      t.gpr = s.gpr → (∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d) →
      Frame [⟨State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o, 4⟩] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.str r .r4 o :: is)) s Q := by
  have hc : (VG.Proof.Argon2.Arm.Derive.scrR s₀).Contains (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  refine wp_str (by omega) (by rw [hb, VG.Proof.Argon2.Arm.Derive.scr_addr hp (by omega)]) (by rw [h.wr]; exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.scr_mem hp, hc⟩)
    fun t u => ?_
  have f : Frame [⟨State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o, 4⟩] s.mem t.mem := by
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k t (h.step u.sp (by rw [u.gpr]) u.rd u.wr ?_) u.mem u.gpr
    (fun d hd => VG.Proof.Argon2.Arm.Derive.lw_keep hp f (fun r hr => ?_) hd) f
  · rw [u.mem]; exact (Frame.refl _ _).writeW (r := VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp) _ hc
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, by simp, VG.Proof.Argon2.Arm.Derive.scr_sub (by omega)⟩

omit hp in
/-- A store to `scratch` from offset 192 on keeps the streaming state. -/
theorem repr_store {m m' : Mem} {o : Nat} (ho : 192 ≤ o) (ho' : o + 4 ≤ 16384)
    (f : Frame [⟨State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o, 4⟩] m m') {data : List Byte}
    (h : Repr b (Spec.Blake2.init b 64 0) m (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)) data) :
    Repr b (Spec.Blake2.init b 64 0) m' (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)) data :=
  HPrime.repr_frame f (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.base_disjoint _ ho (by omega)) h

end

/-- The bytes at `p`: a word, then the rest. -/
theorem bytes_word (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (4 + n) = Spec.Blake2.wordBytes (m.readW p 32) ++ bytesAt m (p + BitVec.ofNat 64 4) n := by
  rw [Proof.Blake2.bytesAt_add, Proof.Blake2.wordBytes_readW (w := 32) m p (.inl rfl)]

theorem variant_code {s₀ : State} (hk : (VG.Proof.Argon2.Arm.Derive.kindV s₀).toNat ≤ 2) : (VG.Proof.Argon2.Arm.Derive.prm s₀).variant.code = (VG.Proof.Argon2.Arm.Derive.kindV s₀).toNat := by
  simp only [VG.Proof.Argon2.Arm.Derive.prm]
  rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with h | h | h <;>
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
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

omit hp in
/-- A word of `scratch` is kept by a store to another one. -/
theorem scr_keep {m m' : Mem} {o o' : Nat} (ho : o + 4 ≤ 16384) (ho' : o' + 4 ≤ 16384)
    (hd : o + 4 ≤ o' ∨ o' + 4 ≤ o)
    (f : Frame [⟨State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o', 4⟩] m m') :
    m'.readW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o) 32 = m.readW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o) 32 := by
  refine f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ hd (by omega) (by omega)

/-- The six header words, at `scratch + 768`. -/
theorem header_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s) (hb : s.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀)
    (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)) []) :
    WP isa (.block Impl.Argon2.Arm.Derive.header) s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ t ∧
      t.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧ Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)) [] ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (VG.Proof.Argon2.Arm.Derive.prm s₀) ∧
      ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d := by
  rw [VG.Proof.Argon2.Arm.Derive.header_eq]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h (i := 7) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide)
  have b₁ : s₁.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by rw [u₁.other _ (by decide), hb]
  refine VG.Proof.Argon2.Arm.Derive.wp_stscr hp i₁ b₁ (o := 768) (by decide) fun s₂ i₂ m₂ g₂ l₂ f₂ => ?_
  have b₂ : s₂.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by rw [g₂, b₁]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₂ (i := 17) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide)
  have b₃ : s₃.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by rw [u₃.other _ (by decide), b₂]
  refine VG.Proof.Argon2.Arm.Derive.wp_stscr hp i₃ b₃ (o := 772) (by decide) fun s₄ i₄ m₄ g₄ l₄ f₄ => ?_
  have b₄ : s₄.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by rw [g₄, b₃]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₄ (i := 6) (by decide) fun s₅ u₅ => ?_
  have i₅ := i₄.upd u₅ (by decide)
  have b₅ : s₅.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by rw [u₅.other _ (by decide), b₄]
  refine VG.Proof.Argon2.Arm.Derive.wp_stscr hp i₅ b₅ (o := 776) (by decide) fun s₆ i₆ m₆ g₆ l₆ f₆ => ?_
  have b₆ : s₆.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by rw [g₆, b₅]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₆ (i := 5) (by decide) fun s₇ u₇ => ?_
  have i₇ := i₆.upd u₇ (by decide)
  have b₇ : s₇.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by rw [u₇.other _ (by decide), b₆]
  refine VG.Proof.Argon2.Arm.Derive.wp_stscr hp i₇ b₇ (o := 780) (by decide) fun s₈ i₈ m₈ g₈ l₈ f₈ => ?_
  have b₈ : s₈.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by rw [g₈, b₇]
  refine wp_mov (op2_imm (by decide)) fun s₉ u₉ => ?_
  have i₉ := i₈.upd u₉ (by decide)
  have b₉ : s₉.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by rw [u₉.other _ (by decide), b₈]
  refine VG.Proof.Argon2.Arm.Derive.wp_stscr hp i₉ b₉ (o := 784) (by decide) fun s₁₀ i₁₀ m₁₀ g₁₀ l₁₀ f₁₀ => ?_
  have b₁₀ : s₁₀.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by rw [g₁₀, b₉]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₁₀ (i := 0) (by decide) fun s₁₁ u₁₁ => ?_
  have i₁₁ := i₁₀.upd u₁₁ (by decide)
  have b₁₁ : s₁₁.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by rw [u₁₁.other _ (by decide), b₁₀]
  refine VG.Proof.Argon2.Arm.Derive.wp_stscr hp i₁₁ b₁₁ (o := 788) (by decide) fun t it mt gt lt ft => WP.block_nil ?_
  -- The locals.
  have L : ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d := fun d hd => by
    rw [lt d hd, VG.Proof.Argon2.Arm.Derive.lw_mem u₁₁.mem, l₁₀ d hd, VG.Proof.Argon2.Arm.Derive.lw_mem u₉.mem, l₈ d hd, VG.Proof.Argon2.Arm.Derive.lw_mem u₇.mem, l₆ d hd, VG.Proof.Argon2.Arm.Derive.lw_mem u₅.mem,
      l₄ d hd, VG.Proof.Argon2.Arm.Derive.lw_mem u₃.mem, l₂ d hd, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem]
  -- The streaming state.
  have R : Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)) [] := by
    refine VG.Proof.Argon2.Arm.Derive.repr_store (by decide) (by decide) ft ?_
    rw [u₁₁.mem]; refine VG.Proof.Argon2.Arm.Derive.repr_store (by decide) (by decide) f₁₀ ?_
    rw [u₉.mem]; refine VG.Proof.Argon2.Arm.Derive.repr_store (by decide) (by decide) f₈ ?_
    rw [u₇.mem]; refine VG.Proof.Argon2.Arm.Derive.repr_store (by decide) (by decide) f₆ ?_
    rw [u₅.mem]; refine VG.Proof.Argon2.Arm.Derive.repr_store (by decide) (by decide) f₄ ?_
    rw [u₃.mem]; refine VG.Proof.Argon2.Arm.Derive.repr_store (by decide) (by decide) f₂ ?_
    rw [u₁.mem]; exact repr
  refine ⟨it, ⟨?_, ?_, ?_, ?_⟩, by rw [gt, b₁₁], R, ?_, L⟩
  · rw [L _ (by decide)]; exact pr.divisor
  · rw [L _ (by decide)]; exact pr.segLen
  · rw [L _ (by decide)]; exact pr.laneLen
  · rw [L _ (by decide)]; exact pr.stride
  -- The words.
  have w0 : t.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 768) 32 = VG.Proof.Argon2.Arm.Derive.arg s₀ 7 := by
    rw [VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) f₈, u₇.mem,
      VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) f₆, u₅.mem,
      VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) f₄, u₃.mem, m₂, Mem.readW_writeW_self32, u₁.gpr]
  have w1 : t.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 772) 32 = VG.Proof.Argon2.Arm.Derive.arg s₀ 17 := by
    rw [VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) f₈, u₇.mem,
      VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) f₆, u₅.mem, m₄, Mem.readW_writeW_self32, u₃.gpr]
  have w2 : t.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 776) 32 = VG.Proof.Argon2.Arm.Derive.arg s₀ 6 := by
    rw [VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) f₈, u₇.mem, m₆, Mem.readW_writeW_self32, u₅.gpr]
  have w3 : t.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 780) 32 = VG.Proof.Argon2.Arm.Derive.arg s₀ 5 := by
    rw [VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem,
      VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) f₁₀, u₉.mem, m₈, Mem.readW_writeW_self32, u₇.gpr]
  have w4 : t.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 784) 32 = 0x13 := by
    rw [VG.Proof.Argon2.Arm.Derive.scr_keep (by decide) (by decide) (by decide) ft, u₁₁.mem, m₁₀, Mem.readW_writeW_self32, u₉.gpr]
  have w5 : t.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 788) 32 = VG.Proof.Argon2.Arm.Derive.arg s₀ 0 := by
    rw [mt, Mem.readW_writeW_self32, u₁₁.gpr]
  have step : ∀ o, State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o + BitVec.ofNat 64 4 =
      State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 (o + 4) := fun o => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show (24 : Nat) = 4 + 20 from rfl, VG.Proof.Argon2.Arm.Derive.bytes_word, step, show (20 : Nat) = 4 + 16 from rfl, VG.Proof.Argon2.Arm.Derive.bytes_word, step,
    show (16 : Nat) = 4 + 12 from rfl, VG.Proof.Argon2.Arm.Derive.bytes_word, step, show (12 : Nat) = 4 + 8 from rfl, VG.Proof.Argon2.Arm.Derive.bytes_word, step,
    show (8 : Nat) = 4 + 4 from rfl, VG.Proof.Argon2.Arm.Derive.bytes_word, step, show (4 : Nat) = 4 + 0 from rfl, VG.Proof.Argon2.Arm.Derive.bytes_word]
  simp only [Nat.reduceAdd]
  rw [w0, w1, w2, w3, w4, w5]
  simp only [Proof.Argon2.initialHeader, VG.Proof.Argon2.Arm.Derive.prm, ← VG.Proof.Argon2.Arm.Derive.le32_arg, List.append_assoc,
    bytesAt, List.range_zero, List.map_nil, List.append_nil]
  have vc := VG.Proof.Argon2.Arm.Derive.variant_code hp.kind_le
  simp only [VG.Proof.Argon2.Arm.Derive.prm] at vc
  rw [vc]
  rfl

/-- `n` bytes of `scratch` at offset `d` are writable. -/
theorem scr_cov {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {d n : Nat} (hd : d + n ≤ 16384) :
    Covers [⟨State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 d, n⟩] s.wr := by
  rw [h.wr]
  exact Covers.of_sub (rs' := [VG.Proof.Argon2.Arm.Derive.scrR s₀]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, List.mem_singleton_self _, d, rfl, hd⟩) |>.trans
    fun a n ⟨r, hr, hc⟩ => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Argon2.Arm.Derive.scr_mem hp, hc⟩

/-- The stack below the locals is outside `scratch`. -/
theorem stk_scr {d n k : Nat} (hd : d + n ≤ 16384) (hk : k ≤ 40) :
    (stkR (VG.Proof.Argon2.Arm.Derive.E s₀) k).Disjoint ⟨State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 d, n⟩ :=
  ((hp.stk_all (VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp)).sub_left fun a ha =>
    VG.Proof.Argon2.Arm.Derive.call_stk hp a (VG.Proof.Argon2.Arm.stkR_sub hk (by rw [VG.Proof.Argon2.Arm.Derive.E_nat hp]; have := hp.sp_lo; omega) a ha)).sub_right
    (VG.Proof.Argon2.Arm.Derive.scr_sub hd)

/-- A store to the locals keeps the streaming state at `scratch`. -/
theorem repr_loc {m : Mem} {d : Nat} (hd : d + 4 ≤ 144) (v : BitVec 32) {h0 : Spec.Blake2.HashValue 64}
    {data : List Byte} (h : Repr b h0 m (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)) data) :
    Repr b h0 (m.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) v) (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)) data :=
  HPrime.repr_frame ((Frame.refl [⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), 4⟩] m).writeW
    (List.mem_singleton_self _) v (Region.contains_self _ _)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((VG.Proof.Argon2.Arm.Derive.loc_disj hp hd (VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp)).symm).sub_left (VG.Proof.Argon2.Arm.Derive.scr_sub (d := 0) (n := 192) (by decide) |>
        fun hs => by simpa using hs)) h

/-- `start`'s first block: `r4 :=` `scratch`, and the digest length. -/
theorem stA_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s) :
    WP isa (.block [ld .r4 (argOff 15), .mov .r1 (.imm 64)]) s fun t =>
      VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ t ∧ t.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧ t.gpr .r1 = BitVec.ofNat 32 64 := by
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    WP.block_nil ?_
  have e : ∀ d, VG.Proof.Argon2.Arm.Derive.lw s₀ s₂ d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d := fun d => by rw [VG.Proof.Argon2.Arm.Derive.lw_mem u₂.mem, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem]
  exact ⟨(h.upd u₁ (by decide)).upd u₂ (by decide),
    ⟨by rw [e]; exact pr.divisor, by rw [e]; exact pr.segLen, by rw [e]; exact pr.laneLen, by rw [e]; exact pr.stride⟩,
    by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr]; rfl⟩

/-- `start`'s `init`. -/
theorem stInit_ok {s : State}
    (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ s ∧ s.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧ s.gpr .r1 = BitVec.ofNat 32 64) :
    WP isa Impl.Argon2.Arm.HPrime.init s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ t ∧ t.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)) [] :=
  (VG.Proof.Argon2.Arm.Derive.init_k (VG.Proof.Argon2.Arm.Derive.ctx hp h.1 h.2.2.1) (n := 64) h.2.2.2 (by decide) (by decide)).mono fun _ ⟨r, k⟩ =>
    let ⟨i, l⟩ := h.1.keeps hp k
    ⟨i, Prm.of_lw h.2.1 fun d hd => l d (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).1, (k.gpr _ (by decide)).trans h.2.2.1, r⟩

/-- `start`'s hash of the header. -/
theorem stFix_ok {s : State}
    (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ s ∧ s.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)) [] ∧
      bytesAt s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (VG.Proof.Argon2.Arm.Derive.prm s₀)) :
    WP isa (Impl.Argon2.Arm.HPrime.absorbFixed 768 24) s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ t ∧
      t.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)) (Proof.Argon2.initialHeader (VG.Proof.Argon2.Arm.Derive.prm s₀)) := by
  have hs := hp.scr_fits
  obtain ⟨i₄, pr₄, b₄, r₄, hd₄⟩ := h
  refine (HPrime.absorbFixed_ok (VG.Proof.Argon2.Arm.Derive.ctx hp i₄ b₄) (offset := 768) (size := 24) (by decide) (by decide) (by omega)
    (by decide) (by decide) (by decide) (VG.Proof.Argon2.Arm.Derive.scr_cov hp i₄ (by decide)) (VG.Proof.Argon2.Arm.Derive.stk_scr hp (by decide) (by decide)) r₄).mono
    fun s₅ ⟨r₅, k₅⟩ => ?_
  rw [hd₄] at r₅
  obtain ⟨i₅, l₅⟩ := i₄.keeps hp k₅
  exact ⟨i₅, Prm.of_lw pr₄ fun d hd => l₅ d (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).1, (k₅.gpr _ (by decide)).trans b₄, r₅⟩

/-- `start`'s count of the header's bytes. -/
theorem stCnt_ok {s : State}
    (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ s ∧ s.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)) (Proof.Argon2.initialHeader (VG.Proof.Argon2.Arm.Derive.prm s₀))) :
    WP isa (.block [.mov .r0 (.imm 24), VG.Impl.Argon2.Arm.Derive.st countLoOff .r0, .mov .r0 (.imm 0), VG.Impl.Argon2.Arm.Derive.st countHiOff .r0]) s
      (VG.Proof.Argon2.Arm.Derive.HI s₀ (Proof.Argon2.initialHeader (VG.Proof.Argon2.Arm.Derive.prm s₀))) := by
  obtain ⟨i₅, pr₄, b₅, r₅⟩ := h
  refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => ?_
  have i₆ := i₅.upd u₆ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₆ (d := countLoOff) (by decide) fun s₇ i₇ v₇ o₇ g₇ m₇ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₈ u₈ => ?_
  have i₈ := i₇.upd u₈ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₈ (d := countHiOff) (by decide) fun t it vt ot gt mt => WP.block_nil ?_
  have L : ∀ d, d + 4 ≤ 144 → (d + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ d) → VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d :=
    fun d hd hd' => by
      rw [ot d (by omega) (by simp only [countHiOff, countLoOff] at hd' ⊢; omega), VG.Proof.Argon2.Arm.Derive.lw_mem u₈.mem,
        o₇ d (by omega) (by simp only [countHiOff, countLoOff] at hd' ⊢; omega), VG.Proof.Argon2.Arm.Derive.lw_mem u₆.mem]
  refine ⟨it, Prm.of_lw pr₄ fun d hd => L d (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).1 (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).2.2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gt, u₈.other _ (by decide), g₇, u₆.other _ (by decide), b₅]
  · rw [mt, u₈.mem, m₇, u₆.mem]
    exact VG.Proof.Argon2.Arm.Derive.repr_loc hp (by decide) _ (VG.Proof.Argon2.Arm.Derive.repr_loc hp (by decide) _ r₅)
  · rw [ot _ (by decide) (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem u₈.mem, v₇, u₆.gpr, Proof.Argon2.initialHeader_length]; rfl
  · rw [vt, u₈.gpr, Proof.Argon2.initialHeader_length]; rfl
  · rw [Proof.Argon2.initialHeader_length]; decide

theorem start_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s) :
    WP isa Impl.Argon2.Arm.Derive.start s (VG.Proof.Argon2.Arm.Derive.HI s₀ (Proof.Argon2.initialHeader (VG.Proof.Argon2.Arm.Derive.prm s₀))) := by
  unfold Impl.Argon2.Arm.Derive.start
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.stA_ok hp h pr).mono fun s₂ h₂ => WP.seq ((VG.Proof.Argon2.Arm.Derive.stInit_ok hp h₂).mono fun s₃ ⟨i₃, pr₃, b₃, r₃⟩ =>
    WP.seq ((VG.Proof.Argon2.Arm.Derive.header_ok hp i₃ pr₃ b₃ r₃).mono fun s₄ ⟨i₄, pr₄, b₄, r₄, hd₄, _⟩ =>
      WP.seq ((VG.Proof.Argon2.Arm.Derive.stFix_ok hp ⟨i₄, pr₄, b₄, r₄, hd₄⟩).mono fun s₅ h₅ => VG.Proof.Argon2.Arm.Derive.stCnt_ok hp h₅))))

end

/-- The carry into the high word of a count. -/
theorem carry_pair {c x : Nat} (_hc : c < 2 ^ 36) (hx : x < 2 ^ 32) :
    BitVec.ofNat 32 (c / 2 ^ 32) + 0 +
      (if decide (2 ^ 32 ≤ (BitVec.ofNat 32 c).toNat + (BitVec.ofNat 32 x).toNat) = true then 1 else 0) =
    BitVec.ofNat 32 ((c + x) / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat (w := 32) (x := c), BitVec.toNat_ofNat (w := 32) (x := x), Nat.mod_eq_of_lt hx]
  by_cases h : 2 ^ 32 ≤ c % 2 ^ 32 + x
  · simp [h, BitVec.toNat_add] <;> omega
  · simp [h] <;> omega

theorem count64 {n : Nat} (h : n < 2 ^ 64) :
    BitVec.ofNat 32 (n / 2 ^ 32) ++ BitVec.ofNat 32 n = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [Proof.Blake2.Arm.Stream.toNat_append32, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- `addCount`: the 64-bit count in the locals, `c`, plus `x`. -/
theorem count_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {c x : Nat} (hc : c < 2 ^ 36) (hx : x < 2 ^ 32)
    (lo : VG.Proof.Argon2.Arm.Derive.lw s₀ s countLoOff = BitVec.ofNat 32 c) (hi : VG.Proof.Argon2.Arm.Derive.lw s₀ s countHiOff = BitVec.ofNat 32 (c / 2 ^ 32))
    {y : Op2} (hy : ∀ t : State, (∀ r, r ≠ .r2 → r ≠ .r3 → t.gpr r = s.gpr r) →
      y.eval t = some (BitVec.ofNat 32 x))
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → VG.Proof.Argon2.Arm.Derive.lw s₀ t countLoOff = BitVec.ofNat 32 (c + x) →
      VG.Proof.Argon2.Arm.Derive.lw s₀ t countHiOff = BitVec.ofNat 32 ((c + x) / 2 ^ 32) →
      (∀ e, e + 4 ≤ 256 → (e + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ e) → VG.Proof.Argon2.Arm.Derive.lw s₀ t e = VG.Proof.Argon2.Arm.Derive.lw s₀ s e) →
      (∀ r, r ≠ .r2 → r ≠ .r3 → t.gpr r = s.gpr r) →
      t.mem = (s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 countLoOff)) (BitVec.ofNat 32 (c + x))).writeW
        (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 countHiOff)) (BitVec.ofNat 32 ((c + x) / 2 ^ 32)) →
      t.gpr .r2 = BitVec.ofNat 32 (c + x) → t.gpr .r3 = BitVec.ofNat 32 ((c + x) / 2 ^ 32) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.addCount y ++ is)) s Q := by
  simp only [Impl.Argon2.Arm.Derive.addCount, List.cons_append, List.nil_append]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h (d := countLoOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp i₁ (d := countHiOff) (by decide) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide)
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have o₂ : ∀ r, r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s.gpr r := fun r a b => by rw [u₂.other _ b, u₁.other _ a]
  refine wp_adds (hy s₂ o₂) fun s₃ u₃ c₃ => ?_
  have i₃ := i₂.upd u₃ (by decide)
  refine wp_adc (op2_imm (by decide)) fun s₄ u₄ _ => ?_
  have i₄ := i₃.upd u₄ (by decide)
  have e₁ : s₂.gpr .r2 = BitVec.ofNat 32 c := by rw [u₂.other _ (by decide), u₁.gpr, lo]
  have vlo : s₄.gpr .r2 = BitVec.ofNat 32 (c + x) := by
    rw [u₄.other _ (by decide), u₃.gpr, e₁, BitVec.ofNat_add]
  have vhi : s₄.gpr .r3 = BitVec.ofNat 32 ((c + x) / 2 ^ 32) := by
    rw [u₄.gpr, c₃, u₃.other _ (by decide), u₂.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem, hi, e₁]
    exact VG.Proof.Argon2.Arm.Derive.carry_pair hc hx
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₄ (d := countLoOff) (by decide) fun s₅ i₅ v₅ o₅ g₅ m₅ => ?_
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₅ (d := countHiOff) (by decide) fun t it vt ot gt mt => k t it ?_ ?_ ?_ ?_ ?_
    (by rw [gt, g₅, vlo]) (by rw [gt, g₅, vhi])
  · rw [ot _ (by decide) (by decide), v₅, vlo]
  · rw [vt, g₅, vhi]
  · intro e he hd
    rw [ot e he (by simp only [countHiOff, countLoOff] at hd ⊢; omega),
      o₅ e he (by simp only [countHiOff, countLoOff] at hd ⊢; omega), VG.Proof.Argon2.Arm.Derive.lw_mem u₄.mem, VG.Proof.Argon2.Arm.Derive.lw_mem u₃.mem,
      VG.Proof.Argon2.Arm.Derive.lw_mem m₂]
  · intro r h1 h2
    rw [gt, g₅, u₄.other _ h2, u₃.other _ h1, o₂ r h1 h2]
  · rw [mt, m₅, g₅, vhi, vlo, u₄.mem, u₃.mem, m₂]

end

/-- H₀'s streaming state at `scratch`, with `data` absorbed and the count `c` in
the locals. -/
structure HC (s₀ : State) (data : List Byte) (c : Nat) (s : State) : Prop where
  inv : VG.Proof.Argon2.Arm.Derive.Inv s₀ s
  prm : VG.Proof.Argon2.Arm.Derive.Prm s₀ s
  r4 : s.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀
  repr : Repr b (Spec.Blake2.init b 64 0) s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)) data
  lo : VG.Proof.Argon2.Arm.Derive.lw s₀ s countLoOff = BitVec.ofNat 32 c
  hi : VG.Proof.Argon2.Arm.Derive.lw s₀ s countHiOff = BitVec.ofNat 32 (c / 2 ^ 32)

theorem HI.hc {s₀ s : State} {data : List Byte} (h : VG.Proof.Argon2.Arm.Derive.HI s₀ data s) : VG.Proof.Argon2.Arm.Derive.HC s₀ data data.length s :=
  ⟨h.inv, h.prm, h.r4, h.repr, h.lo, h.hi⟩

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- `absorb`'s first block: LE32 of the length at `scratch + 792`, and `update`'s arguments. -/
theorem absA_ok {len : Nat} (hlen : len < 18) {data : List Byte} {c : Nat} {s : State} (h : VG.Proof.Argon2.Arm.Derive.HC s₀ data c s) :
    WP isa (.block [ld .r0 (argOff len), .str .r0 .r4 792, ld .r2 countLoOff, ld .r3 countHiOff,
      .dp .add .r9 .r4 (.imm 792), .mov .r10 (.imm 4)]) s fun t =>
      VG.Proof.Argon2.Arm.Derive.HC s₀ data c t ∧ t.gpr .r9 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + 792 ∧ (t.gpr .r10).toNat = 4 ∧ t.gpr .r2 = BitVec.ofNat 32 c ∧
      t.gpr .r3 = BitVec.ofNat 32 (c / 2 ^ 32) ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + 792)) 4 = Spec.Argon2.le32 (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat := by
  have hs := hp.scr_fits
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h.inv (i := len) hlen fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide)
  have b₁ : s₁.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by rw [u₁.other _ (by decide), h.r4]
  refine VG.Proof.Argon2.Arm.Derive.wp_stscr hp i₁ b₁ (o := 792) (by decide) fun s₂ i₂ m₂ g₂ l₂ f₂ => ?_
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp i₂ (d := countLoOff) (by decide) fun s₃ u₃ => ?_
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp (i₂.upd u₃ (by decide)) (d := countHiOff) (by decide) fun s₄ u₄ => ?_
  refine wp_add (op2_imm (by decide)) fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have i₆ := (((i₂.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)
  have m₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have L₂ : ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.Arm.Derive.lw s₀ s₂ d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d := fun d hd => by rw [l₂ d hd, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem]
  have L₆ : ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.Arm.Derive.lw s₀ s₆ d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d := fun d hd => by rw [VG.Proof.Argon2.Arm.Derive.lw_mem m₆, L₂ d hd]
  have e792 : State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + 792) = State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 792 :=
    VG.Proof.Argon2.Arm.Derive.scr_addr hp (o := 792) (by decide)
  have r4₄ : s₄.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, b₁]
  refine ⟨⟨i₆, Prm.of_lw h.prm fun d hd => L₆ d (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).1,
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), r4₄],
    by rw [m₆]; exact VG.Proof.Argon2.Arm.Derive.repr_store (by decide) (by decide) f₂ (by rw [u₁.mem]; exact h.repr),
    by rw [L₆ _ (by decide)]; exact h.lo, by rw [L₆ _ (by decide)]; exact h.hi⟩, ?_, by rw [u₆.gpr]; rfl, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.gpr, r4₄]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, L₂ _ (by decide), h.lo]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₃.mem, L₂ _ (by decide), h.hi]
  · rw [e792, show (4 : Nat) = 4 + 0 from rfl, VG.Proof.Argon2.Arm.Derive.bytes_word, m₆, m₂, Mem.readW_writeW_self32, u₁.gpr, VG.Proof.Argon2.Arm.Derive.le32_arg]
    rfl

/-- `absorb`'s first `update`: LE32 of the length. -/
theorem absU1_ok {len : Nat} {data : List Byte} {c : Nat} {s : State} (h : VG.Proof.Argon2.Arm.Derive.HC s₀ data c s)
    (hd : data.length = c) (hc : c + 4 < 2 ^ 36) (r9 : s.gpr .r9 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + 792) (r10 : (s.gpr .r10).toNat = 4)
    (r2 : s.gpr .r2 = BitVec.ofNat 32 c) (r3 : s.gpr .r3 = BitVec.ofNat 32 (c / 2 ^ 32))
    (w : bytesAt s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + 792)) 4 = Spec.Argon2.le32 (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat) :
    WP isa Impl.Argon2.Arm.HPrime.update s (VG.Proof.Argon2.Arm.Derive.HC s₀ (data ++ Spec.Argon2.le32 (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat) c) := by
  have hs := hp.scr_fits
  have e792 : State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + 792) = State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 792 :=
    VG.Proof.Argon2.Arm.Derive.scr_addr hp (o := 792) (by decide)
  refine (VG.Proof.Argon2.Arm.Derive.update_k (VG.Proof.Argon2.Arm.Derive.ctx hp h.inv h.r4) (D := VG.Proof.Argon2.Arm.Derive.scrP s₀ + 792) (L := 4) r9 r10
    (by have : (VG.Proof.Argon2.Arm.Derive.scrP s₀ + 792).toNat = (VG.Proof.Argon2.Arm.Derive.scrP s₀).toNat + 792 := VG.Proof.Argon2.Arm.Derive.add_nat (k := 792) (by omega)
        omega)
    (by rw [e792]; exact Covers.right (VG.Proof.Argon2.Arm.Derive.scr_cov hp h.inv (by decide)))
    (by rw [e792]; exact Offset.disjoint_base _ (by decide) (by decide))
    (by rw [e792]; exact VG.Proof.Argon2.Arm.Derive.stk_scr hp (by decide) (by decide)) h.repr
    (by rw [r3, r2, hd]; exact VG.Proof.Argon2.Arm.Derive.count64 (by omega)) (by omega)).mono fun t ⟨r, k⟩ => ?_
  obtain ⟨i, l⟩ := h.inv.keeps hp k
  rw [w] at r
  exact ⟨i, Prm.of_lw h.prm fun d hd => l d (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).1,
    (k.gpr _ (by decide)).trans h.r4, r, by rw [l _ (by decide)]; exact h.lo, by rw [l _ (by decide)]; exact h.hi⟩

/-- `absorb`'s second block: the count advanced by 4, and `update`'s arguments. -/
theorem absB_ok {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18) {data : List Byte} {c : Nat}
    (hc : c < 2 ^ 36) {s : State} (h : VG.Proof.Argon2.Arm.Derive.HC s₀ data c s) :
    WP isa (.block (Impl.Argon2.Arm.Derive.addCount (.imm 4) ++
      ([ld .r9 (argOff ptr), ld .r10 (argOff len)] : List Instr)))
      s fun t => VG.Proof.Argon2.Arm.Derive.HC s₀ data (c + 4) t ∧ t.gpr .r9 = VG.Proof.Argon2.Arm.Derive.arg s₀ ptr ∧ (t.gpr .r10).toNat = (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat ∧
        t.gpr .r2 = BitVec.ofNat 32 (c + 4) ∧ t.gpr .r3 = BitVec.ofNat 32 ((c + 4) / 2 ^ 32) := by
  refine VG.Proof.Argon2.Arm.Derive.count_ok hp h.inv (x := 4) hc (by decide) h.lo h.hi (fun _ _ => op2_imm (by decide))
    fun s₉ i₉ lo₉ hi₉ o₉ g₉ m₉ c₉ d₉ => VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₉ (i := ptr) hptr fun s₁₀ u₁₀ =>
      VG.Proof.Argon2.Arm.Derive.wp_ldarg hp (i₉.upd u₁₀ (by decide)) (i := len) hlen fun s₁₁ u₁₁ => WP.block_nil ?_
  have i₁₁ := (i₉.upd u₁₀ (by decide)).upd u₁₁ (by decide)
  have m₁₁ : s₁₁.mem = s₉.mem := by rw [u₁₁.mem, u₁₀.mem]
  refine ⟨⟨i₁₁, Prm.of_lw h.prm fun d hd => ?_, ?_, ?_, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem m₁₁]; exact lo₉, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem m₁₁]; exact hi₉⟩,
    by rw [u₁₁.other _ (by decide), u₁₀.gpr], by rw [u₁₁.gpr],
    by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), c₉],
    by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), d₉]⟩
  · rw [VG.Proof.Argon2.Arm.Derive.lw_mem m₁₁, o₉ d (by have := (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).1; omega) (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).2.2]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), g₉ _ (by decide) (by decide), h.r4]
  · rw [m₁₁, m₉]; exact VG.Proof.Argon2.Arm.Derive.repr_loc hp (by decide) _ (VG.Proof.Argon2.Arm.Derive.repr_loc hp (by decide) _ h.repr)

/-- `absorb`'s second `update`: the input. -/
theorem absU2_ok {ptr len : Nat}
    (hR : (⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr), (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat⟩ : Region) ∈ [VG.Proof.Argon2.Arm.Derive.pwR s₀, VG.Proof.Argon2.Arm.Derive.saltR s₀, VG.Proof.Argon2.Arm.Derive.secR s₀, VG.Proof.Argon2.Arm.Derive.adR s₀])
    (hfit : (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr).toNat + (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat ≤ 2 ^ 32) {data : List Byte} {c : Nat} {s : State}
    (h : VG.Proof.Argon2.Arm.Derive.HC s₀ data c s) (hd : data.length = c) (hc : c + 2 ^ 32 < 2 ^ 36) (r9 : s.gpr .r9 = VG.Proof.Argon2.Arm.Derive.arg s₀ ptr)
    (r10 : (s.gpr .r10).toNat = (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat) (r2 : s.gpr .r2 = BitVec.ofNat 32 c)
    (r3 : s.gpr .r3 = BitVec.ofNat 32 (c / 2 ^ 32)) :
    WP isa Impl.Argon2.Arm.HPrime.update s
      (VG.Proof.Argon2.Arm.Derive.HC s₀ (data ++ bytesAt s₀.mem (State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr)) (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat) c) := by
  have hlt := (VG.Proof.Argon2.Arm.Derive.arg s₀ len).isLt
  have hR' : (⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr), (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat⟩ : Region) ∈
      [VG.Proof.Argon2.Arm.Derive.pwR s₀, VG.Proof.Argon2.Arm.Derive.saltR s₀, VG.Proof.Argon2.Arm.Derive.secR s₀, VG.Proof.Argon2.Arm.Derive.adR s₀, VG.Proof.Argon2.Arm.Derive.argR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h | h <;> simp [h]
  have hS : (⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr), (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat⟩ : Region) ∈
      [VG.Proof.Argon2.Arm.Derive.pwR s₀, VG.Proof.Argon2.Arm.Derive.saltR s₀, VG.Proof.Argon2.Arm.Derive.secR s₀, VG.Proof.Argon2.Arm.Derive.adR s₀, VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h | h <;> simp [h]
  have rin := hp.ro_w _ hR' (VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp)
  refine (VG.Proof.Argon2.Arm.Derive.update_k (VG.Proof.Argon2.Arm.Derive.ctx hp h.inv h.r4) (D := VG.Proof.Argon2.Arm.Derive.arg s₀ ptr) (L := (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat) r9 r10 hfit
    (by rw [h.inv.rd, hp.rd]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_append_left _ hR', 0, by simp, by simp⟩)
    (rin.sub_right (Region.sub_prefix (by decide)))
    ((hp.stk_all _ hS).sub_left fun a ha => VG.Proof.Argon2.Arm.Derive.call_stk hp a (VG.Proof.Argon2.Arm.Derive.stk32_call hp a ha))
    h.repr (by rw [r3, r2, hd]; exact VG.Proof.Argon2.Arm.Derive.count64 (by omega)) (by omega)).mono fun t ⟨r, k⟩ => ?_
  obtain ⟨i, l⟩ := h.inv.keeps hp k
  have inp : bytesAt s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr)) (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat =
      bytesAt s₀.mem (State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr)) (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat :=
    h.inv.input hp (R := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr), (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat⟩) hR
  rw [inp] at r
  exact ⟨i, Prm.of_lw h.prm fun d hd => l d (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).1,
    (k.gpr _ (by decide)).trans h.r4, r, by rw [l _ (by decide)]; exact h.lo, by rw [l _ (by decide)]; exact h.hi⟩

/-- `absorb`'s last block: the count advanced by the input's length. -/
theorem absC_ok {len : Nat} (hlen : len < 18) {data : List Byte} {c : Nat} (hc : c < 2 ^ 36) {s : State}
    (h : VG.Proof.Argon2.Arm.Derive.HC s₀ data c s) :
    WP isa (.block (ld .r0 (argOff len) :: Impl.Argon2.Arm.Derive.addCount (.reg .r0))) s
      (VG.Proof.Argon2.Arm.Derive.HC s₀ data (c + (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat)) := by
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h.inv (i := len) hlen fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide)
  rw [← List.append_nil (Impl.Argon2.Arm.Derive.addCount _)]
  refine VG.Proof.Argon2.Arm.Derive.count_ok hp i₁ (x := (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat) hc (VG.Proof.Argon2.Arm.Derive.arg s₀ len).isLt (by rw [VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem]; exact h.lo)
    (by rw [VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem]; exact h.hi)
    (fun t ht => by rw [op2_reg, ht _ (by decide) (by decide), u₁.gpr, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    fun t it lo hi o g mt _ _ => WP.block_nil ⟨it, Prm.of_lw h.prm fun d hd => ?_, ?_, ?_, lo, hi⟩
  · rw [o d (by have := (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).1; omega) (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).2.2, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem]
  · rw [g _ (by decide) (by decide), u₁.other _ (by decide), h.r4]
  · rw [mt, u₁.mem]; exact VG.Proof.Argon2.Arm.Derive.repr_loc hp (by decide) _ (VG.Proof.Argon2.Arm.Derive.repr_loc hp (by decide) _ h.repr)

theorem absorb_ok {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18)
    (hR : (⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr), (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat⟩ : Region) ∈ [VG.Proof.Argon2.Arm.Derive.pwR s₀, VG.Proof.Argon2.Arm.Derive.saltR s₀, VG.Proof.Argon2.Arm.Derive.secR s₀, VG.Proof.Argon2.Arm.Derive.adR s₀])
    (hfit : (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr).toNat + (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat ≤ 2 ^ 32) {data : List Byte}
    (hd : data.length + 4 + 2 ^ 32 < 2 ^ 36) {s : State} (h : VG.Proof.Argon2.Arm.Derive.HI s₀ data s) :
    WP isa (Impl.Argon2.Arm.Derive.absorb ptr len) s
      (VG.Proof.Argon2.Arm.Derive.HI s₀ (Proof.Argon2.appendInput data (bytesAt s₀.mem (State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr)) (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat))) := by
  have hlt := (VG.Proof.Argon2.Arm.Derive.arg s₀ len).isLt
  unfold Impl.Argon2.Arm.Derive.absorb
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.absA_ok hp hlen h.hc).mono fun s₁ ⟨h₁, e₁, d₁, c₁, x₁, w₁⟩ => ?_)
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.absU1_ok hp h₁ rfl (by omega) e₁ d₁ c₁ x₁ w₁).mono fun s₂ h₂ => ?_)
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.absB_ok hp hptr hlen (by omega) h₂).mono fun s₃ ⟨h₃, e₃, d₃, c₃, x₃⟩ => ?_)
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.absU2_ok hp hR hfit h₃ (by simp [Proof.Argon2.le32_length]) (by omega) e₃ d₃ c₃ x₃).mono
    fun s₄ h₄ => ?_)
  refine (VG.Proof.Argon2.Arm.Derive.absC_ok hp hlen (by omega) h₄).mono fun t ht => ?_
  have hd' : Proof.Argon2.appendInput data (bytesAt s₀.mem (State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr)) (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat) =
      data ++ Spec.Argon2.le32 (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat ++
        bytesAt s₀.mem (State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr)) (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat := by
    simp only [Proof.Argon2.appendInput, bytesAt, List.length_map, List.length_range]
  have hl : (Proof.Argon2.appendInput data (bytesAt s₀.mem (State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr)) (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat)).length =
      data.length + 4 + (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat := by
    rw [Proof.Argon2.appendInput_length]; simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨ht.inv, ht.prm, ht.r4, by rw [hd']; exact ht.repr, by rw [hl]; exact ht.lo, by rw [hl]; exact ht.hi,
    by rw [hl]; omega⟩

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
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- A store to the locals keeps `scratch`. -/
theorem scr_loc {m : Mem} {d o : Nat} (hd : d + 4 ≤ 144) (ho : o + 4 ≤ 16384) (v : BitVec 32) :
    (m.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) v).readW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o) 32 =
      m.readW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o) 32 := by
  refine ((Frame.refl [⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), 4⟩] m).writeW (List.mem_singleton_self _) v
    (Region.contains_self _ _)).readW (r := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o, 4⟩)
    (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ((VG.Proof.Argon2.Arm.Derive.loc_disj hp hd (VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp)).symm.sub_left (VG.Proof.Argon2.Arm.Derive.scr_sub ho))

/-- The first `k` words of the digest, copied to the locals. -/
theorem copy_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (hb : s.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀) :
    ∀ k ≤ 16, WP isa (.block ((List.range k).flatMap Impl.Argon2.Arm.Derive.copyWord)) s fun t =>
      VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ t.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧
      (∀ j < k, VG.Proof.Argon2.Arm.Derive.lw s₀ t (4 * j) = s.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 (768 + 4 * j)) 32) ∧
      (∀ o, o + 4 ≤ 16384 → t.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o) 32 =
        s.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 o) 32) ∧
      (∀ e, e + 4 ≤ 256 → 4 * k ≤ e → VG.Proof.Argon2.Arm.Derive.lw s₀ t e = VG.Proof.Argon2.Arm.Derive.lw s₀ s e)
  | 0, _ => WP.block_nil ⟨h, hb, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, fun _ _ _ => rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((VG.Proof.Argon2.Arm.Derive.copy_ok h hb k (by omega)).mono fun t ⟨it, bt, wt, st, lt⟩ => ?_)
    simp only [Impl.Argon2.Arm.Derive.copyWord]
    refine wp_ldr (by omega) (by rw [bt, VG.Proof.Argon2.Arm.Derive.scr_addr hp (by omega)]) (by
        rw [it.rd, it.wr]
        exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, List.mem_append_right _ (VG.Proof.Argon2.Arm.Derive.scr_mem hp), Offset.contains_base _ (by omega) (by omega)⟩)
      fun t₁ u₁ => ?_
    have i₁ := it.upd u₁ (by decide)
    refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₁ (d := 4 * k) (by omega) fun t₂ i₂ v₂ o₂ g₂ m₂ => WP.block_nil
      ⟨i₂, by rw [g₂, u₁.other _ (by decide), bt], fun j hj => ?_, fun o ho => ?_, fun e he hke => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [o₂ _ (by omega) (by omega), VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem]; exact wt j hj
      · rw [v₂, u₁.gpr, st _ (by omega)]
    · rw [m₂, VG.Proof.Argon2.Arm.Derive.scr_loc hp (by omega) ho, u₁.mem]; exact st o ho
    · rw [o₂ _ he (by omega), VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem]; exact lt e he (by omega)

/-- `finish`'s first block: the count, for `finalize`. -/
theorem fiA_ok {data : List Byte} {s : State} (h : VG.Proof.Argon2.Arm.Derive.HI s₀ data s) :
    WP isa (.block [ld .r2 countLoOff, ld .r3 countHiOff]) s fun t => VG.Proof.Argon2.Arm.Derive.HI s₀ data t ∧
      t.gpr .r2 = BitVec.ofNat 32 data.length ∧ t.gpr .r3 = BitVec.ofNat 32 (data.length / 2 ^ 32) := by
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h.inv (d := countLoOff) (by decide) fun s₁ u₁ =>
    VG.Proof.Argon2.Arm.Derive.wp_ldloc hp (h.inv.upd u₁ (by decide)) (d := countHiOff) (by decide) fun s₂ u₂ =>
      WP.block_nil ?_
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨⟨(h.inv.upd u₁ (by decide)).upd u₂ (by decide), Prm.of_lw h.prm fun d _ => VG.Proof.Argon2.Arm.Derive.lw_mem m₂ d,
    by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r4], by rw [m₂]; exact h.repr,
    by rw [VG.Proof.Argon2.Arm.Derive.lw_mem m₂]; exact h.lo, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem m₂]; exact h.hi, h.len⟩,
    by rw [u₂.other _ (by decide), u₁.gpr, h.lo], by rw [u₂.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem, h.hi]⟩

/-- `finish`'s `finalize`: the digest at `scratch + 768`. -/
theorem fiFin_ok {data : List Byte} {s : State} (h : VG.Proof.Argon2.Arm.Derive.HI s₀ data s)
    (r2 : s.gpr .r2 = BitVec.ofNat 32 data.length) (r3 : s.gpr .r3 = BitVec.ofNat 32 (data.length / 2 ^ 32)) :
    WP isa Impl.Argon2.Arm.HPrime.finalize s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ t ∧ t.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + 768) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) data := by
  have hn := h.len
  refine (VG.Proof.Argon2.Arm.Derive.finalize_k (VG.Proof.Argon2.Arm.Derive.ctx hp h.inv h.r4) (h0 := Spec.Blake2.init b 64 0) h.repr
    (by rw [r3, r2]; exact VG.Proof.Argon2.Arm.Derive.count64 (by omega)) (by omega)).mono fun s₃ ⟨dg, k₃⟩ => ?_
  obtain ⟨i₃, l₃⟩ := h.inv.keeps hp k₃
  exact ⟨i₃, Prm.of_lw h.prm fun d hd => l₃ d (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).1, (k₃.gpr _ (by decide)).trans h.r4, dg⟩

/-- `finish`'s copy of the digest to the locals. -/
theorem fiCopy_ok {s : State} {dg : List Byte} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ s ∧ s.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧
      bytesAt s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + 768) 64 = dg) :
    WP isa (.block ((List.range 16).flatMap Impl.Argon2.Arm.Derive.copyWord)) s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ t ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)) 64 = dg := by
  have hs := hp.scr_fits
  have hE := VG.Proof.Argon2.Arm.Derive.E_hi hp
  obtain ⟨i₃, pr₃, b₃, dg₃⟩ := h
  refine (VG.Proof.Argon2.Arm.Derive.copy_ok hp i₃ b₃ 16 (Nat.le_refl _)).mono fun t ⟨it, _, wt, _, lt⟩ =>
    ⟨it, Prm.of_lw pr₃ fun d hd => ?_, ?_⟩
  · rw [lt d (by have := (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).1; omega) (by have := (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).2.1; omega)]
  · rw [← dg₃]
    refine VG.Proof.Argon2.Arm.Derive.bytes_of_words (k := 16) fun j hj => ?_
    have := wt j hj
    simp only [VG.Proof.Argon2.Arm.Derive.lw] at this
    rw [VG.Proof.Argon2.Arm.Derive.loc_addr hp (by omega)] at this
    rw [this, BitVec.add_assoc, show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.ofNat_add_ofNat]

theorem finish_ok {data : List Byte} {s : State} (h : VG.Proof.Argon2.Arm.Derive.HI s₀ data s) :
    WP isa Impl.Argon2.Arm.Derive.finish s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ t ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) data := by
  unfold Impl.Argon2.Arm.Derive.finish
  exact WP.seq ((VG.Proof.Argon2.Arm.Derive.fiA_ok hp h).mono fun s₂ ⟨h₂, c₂, d₂⟩ => WP.seq ((VG.Proof.Argon2.Arm.Derive.fiFin_ok hp h₂ c₂ d₂).mono
    fun s₃ h₃ => VG.Proof.Argon2.Arm.Derive.fiCopy_ok hp h₃))

theorem code_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s) :
    WP isa Impl.Argon2.Arm.Derive.code s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ t ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)) 64 =
        Spec.Argon2.initialHash (VG.Proof.Argon2.Arm.Derive.prm s₀) (VG.Proof.Argon2.Arm.Derive.pwB s₀) (VG.Proof.Argon2.Arm.Derive.saltB s₀) (VG.Proof.Argon2.Arm.Derive.secB s₀) (VG.Proof.Argon2.Arm.Derive.adB s₀) := by
  have l1 := (VG.Proof.Argon2.Arm.Derive.arg s₀ 2).isLt
  have l2 := (VG.Proof.Argon2.Arm.Derive.arg s₀ 4).isLt
  have l3 := (VG.Proof.Argon2.Arm.Derive.arg s₀ 10).isLt
  unfold Impl.Argon2.Arm.Derive.code
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.start_ok hp h pr).mono fun s₁ h₁ => ?_)
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.absorb_ok hp (ptr := 1) (len := 2) (by decide) (by decide) (by simp) hp.pw_fits
    (by rw [Proof.Argon2.initialHeader_length]; omega) h₁).mono fun s₂ h₂ => ?_)
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.absorb_ok hp (ptr := 3) (len := 4) (by decide) (by decide) (by simp) hp.salt_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega) h₂).mono fun s₃ h₃ => ?_)
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.absorb_ok hp (ptr := 9) (len := 10) (by decide) (by decide) (by simp) hp.sec_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega) h₃).mono fun s₄ h₄ => ?_)
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.absorb_ok hp (ptr := 11) (len := 12) (by decide) (by decide) (by simp) hp.ad_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega) h₄).mono fun s₅ h₅ => ?_)
  refine (VG.Proof.Argon2.Arm.Derive.finish_ok hp h₅).mono fun t ⟨it, pt, bt⟩ => ⟨it, pt, ?_⟩
  rw [bt, Proof.Argon2.initialHash_stream, List.take_of_length_le (by rw [HPrime.finalHash_length])]
  rfl

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.HCall`. -/
section

/-!
# Argon2 on ARMv7: calls of H′ in the derivation

The derivation calls `vg_argon2_hprime` with its register arguments in
`r0`–`r3` and `scratch` (from `r12`) pushed with `lr`, from the body (`Inv`).
`hcall_ok` runs one: its input lies in the memory matrix or the locals, its
output in the memory matrix or `out`, and `scratch` is its working space. The
call writes only the output, `scratch` and the 40 bytes below the locals.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Argon2.Arm (stkR addr_toNat pushed_arg pushed_argAddr frameCall_ok stkR_inner stkR_sub)
open VG.Spec.Blake2 (bytesAt)

theorem hPrime_stack : armStack Impl.Argon2.Arm.HPrime.code = 32 := by lit_decide

/-- The bytes of a region a frame's regions miss are kept. -/
theorem bytes_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hR : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n :=
  Proof.Blake2.bytesAt_congr fun _ hi => f.bytes (R := ⟨p, n⟩) hd hR hi

/-- The registers `hPrimeCall` pushes. -/
abbrev hregs : List Reg := [.r12, .lr]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem call_disj {R : Region} (hR : R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀]) : (VG.Proof.Argon2.Arm.Derive.callR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left (VG.Proof.Argon2.Arm.Derive.call_stk hp)

theorem loc_call : (VG.Proof.Argon2.Arm.Derive.locR s₀).Disjoint (VG.Proof.Argon2.Arm.Derive.callR s₀) := by
  have hE := VG.Proof.Argon2.Arm.Derive.E_nat hp
  have := hp.sp_lo
  have := VG.Proof.Argon2.Arm.Derive.E_hi hp
  show Region.Disjoint _ ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀) - BitVec.ofNat 64 40, 40⟩
  rw [← addr_sub' (by omega)]
  exact VG.Proof.Argon2.Arm.Derive.disj32 (.inr (by rw [sub_toNat' (by omega)]; omega)) (by omega) (by rw [sub_toNat' (by omega)]; omega)

theorem loc_sub_stk : Region.Sub (VG.Proof.Argon2.Arm.Derive.locR s₀) (VG.Proof.Argon2.Arm.Derive.stkR0 s₀) := by
  simpa using VG.Proof.Argon2.Arm.Derive.frame_stk hp (d := 0) (n := 144) (by decide)

theorem loc_disj' {R : Region} (hR : R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀]) : (VG.Proof.Argon2.Arm.Derive.locR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left (VG.Proof.Argon2.Arm.Derive.loc_sub_stk hp)

/-- The regions H′ is given. -/
abbrev hRd (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, ⟨State.addr s.sp - BitVec.ofNat 64 (4 * hregs.length), 4⟩]
abbrev hWr (s₀ s : State) : List Region := [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩, VG.Proof.Argon2.Arm.Derive.scrR s₀]

/-- What H′ needs, from the body: `hprime(r0, r1, r2, r3, r12)`. -/
theorem hcall_pre {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (hdx : s.gpr .r12 = VG.Proof.Argon2.Arm.Derive.scrP s₀)
    (hin : ∃ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.locR s₀], ∃ off, State.addr (s.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r1).toNat ≤ R.len)
    (hinfit : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32)
    (hout : ∃ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀], ∃ off, State.addr (s.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r3).toNat ≤ R.len)
    (houtfit : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32)
    (hL : 1 ≤ (s.gpr .r3).toNat) :
    HPrime.hPrimeArm.pre ((pushed VG.Proof.Argon2.Arm.Derive.hregs s).callEntry.withRegions (VG.Proof.Argon2.Arm.Derive.hRd s) (VG.Proof.Argon2.Arm.Derive.hWr s₀ s)) ∧
      Covers (VG.Proof.Argon2.Arm.Derive.hRd s ++ VG.Proof.Argon2.Arm.Derive.hWr s₀ s) ((pushed VG.Proof.Argon2.Arm.Derive.hregs s).rd ++ (pushed VG.Proof.Argon2.Arm.Derive.hregs s).wr) ∧
      Covers (VG.Proof.Argon2.Arm.Derive.hWr s₀ s) (pushed VG.Proof.Argon2.Arm.Derive.hregs s).wr := by
  have hE := VG.Proof.Argon2.Arm.Derive.E_nat hp
  have hlo := hp.sp_lo
  have hhi := VG.Proof.Argon2.Arm.Derive.E_hi hp
  have hs := hp.scr_fits
  have sp := h.sp
  have hn : 4 * hregs.length ≤ s.sp.toNat := by simp only [List.length_cons, List.length_nil]; rw [sp]; omega
  have a0 : ∀ {rd wr}, stackArg ((pushed VG.Proof.Argon2.Arm.Derive.hregs s).callEntry.withRegions rd wr) 0 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by
    intro rd wr; rw [pushed_arg hn (by decide)]; exact hdx
  have eA : ∀ {rd wr}, stackArgAddr ((pushed VG.Proof.Argon2.Arm.Derive.hregs s).callEntry.withRegions rd wr) 0 =
      State.addr s.sp - BitVec.ofNat 64 (4 * hregs.length) := pushed_argAddr hn
  have eSp : ∀ {rd wr}, ((pushed VG.Proof.Argon2.Arm.Derive.hregs s).callEntry.withRegions rd wr).sp = s.sp - BitVec.ofNat 32 8 := by
    intro rd wr; simp [pushed_sp]
  have g : ∀ r, r ∉ linkRegs → ∀ {rd wr}, ((pushed VG.Proof.Argon2.Arm.Derive.hregs s).callEntry.withRegions rd wr).gpr r = s.gpr r :=
    fun r hr rd wr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]
  -- The input and the output.
  obtain ⟨RI, hRI, oI, bI, lI⟩ := hin
  obtain ⟨RO, hRO, oO, bO, lO⟩ := hout
  have sI : Region.Sub ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ RI := by
    rw [bI]; exact Offset.sub_base _ lI
  have sO : Region.Sub ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ RO := by
    rw [bO]; exact Offset.sub_base _ lO
  have inW : RI ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact VG.Proof.Argon2.Arm.Derive.mem_mem hp
    · exact VG.Proof.Argon2.Arm.Derive.loc_mem s₀
  have outW : RO ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact VG.Proof.Argon2.Arm.Derive.mem_mem hp
    · exact VG.Proof.Argon2.Arm.Derive.out_mem hp
  have cI : Covers [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RI, inW, oI, bI, lI⟩
  have cO : Covers [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RO, outW, oO, bO, lO⟩
  have scrW : VG.Proof.Argon2.Arm.Derive.scrR s₀ ∈ s.wr := by rw [h.wr]; exact VG.Proof.Argon2.Arm.Derive.scr_mem hp
  have I_scr : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ (VG.Proof.Argon2.Arm.Derive.scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact hp.mem_scr.sub_left sI
    · exact (VG.Proof.Argon2.Arm.Derive.loc_disj' hp (R := VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp)).sub_left sI
  have I_call : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ (VG.Proof.Argon2.Arm.Derive.callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact (VG.Proof.Argon2.Arm.Derive.call_disj hp (R := VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).symm.sub_left sI
    · exact (VG.Proof.Argon2.Arm.Derive.loc_call hp).sub_left sI
  have O_scr : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ (VG.Proof.Argon2.Arm.Derive.scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact hp.mem_scr.sub_left sO
    · exact hp.scr_out.symm.sub_left sO
  have O_call : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ (VG.Proof.Argon2.Arm.Derive.callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact (VG.Proof.Argon2.Arm.Derive.call_disj hp (R := VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).symm.sub_left sO
    · exact (VG.Proof.Argon2.Arm.Derive.call_disj hp (R := VG.Proof.Argon2.Arm.Derive.outR s₀) (by simp)).symm.sub_left sO
  have S_call : (VG.Proof.Argon2.Arm.Derive.scrR s₀).Disjoint (VG.Proof.Argon2.Arm.Derive.callR s₀) := (VG.Proof.Argon2.Arm.Derive.call_disj hp (R := VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp)).symm
  -- The callee's stack and argument.
  have cA : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 (4 * hregs.length), 4⟩ (VG.Proof.Argon2.Arm.Derive.callR s₀) := by
    rw [sp]
    show Region.Sub ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀) - BitVec.ofNat 64 8, 4⟩ ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀) - BitVec.ofNat 64 40, 40⟩
    have t8 : (VG.Proof.Argon2.Arm.Derive.E s₀ - BitVec.ofNat 32 8).toNat = (VG.Proof.Argon2.Arm.Derive.E s₀).toNat - 8 := sub_toNat' (by omega)
    have t40 : (VG.Proof.Argon2.Arm.Derive.E s₀ - BitVec.ofNat 32 40).toNat = (VG.Proof.Argon2.Arm.Derive.E s₀).toNat - 40 := sub_toNat' (by omega)
    rw [← addr_sub' (x := VG.Proof.Argon2.Arm.Derive.E s₀) (k := 8) (by omega), ← addr_sub' (x := VG.Proof.Argon2.Arm.Derive.E s₀) (k := 40) (by omega)]
    exact VG.Proof.Argon2.Arm.Derive.sub32 (by rw [t8, t40]; omega) (by rw [t8, t40]; omega)
  have cS : Region.Sub (stkR (VG.Proof.Argon2.Arm.Derive.E s₀ - BitVec.ofNat 32 8) 32) (VG.Proof.Argon2.Arm.Derive.callR s₀) :=
    stkR_inner (sp := VG.Proof.Argon2.Arm.Derive.E s₀) (a := 32) (k := 8) (b := 40) (by omega) (by omega)
  have cS' : Region.Sub (stkR (s.sp - BitVec.ofNat 32 8) 32) (VG.Proof.Argon2.Arm.Derive.callR s₀) := by rw [sp]; exact cS
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.hPrimeArm, State.withRegions_rd, State.withRegions_wr, a0, eA, eSp,
      g .r0 (by decide), g .r1 (by decide), g .r2 (by decide), g .r3 (by decide)]
    refine ⟨trivial, trivial, I_scr, O_scr, O_call.symm.sub_left cA, S_call.symm.sub_left cA,
      I_call.symm.sub_left cS', O_call.symm.sub_left cS', S_call.symm.sub_left cS', hinfit, houtfit, by omega,
      ?_, ?_, hL⟩
    · rw [sub_toNat' (by omega), sp]; omega
    · rw [sub_toNat' (by omega), sp]; omega
  · intro a n ⟨q, hq, hc⟩
    rw [pushed_rd, pushed_wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cI a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · refine InRegions_append_cons.mpr (.inl ?_)
      rw [addr_sub' hn]
      simp only [Region.Contains, List.length_cons, List.length_nil] at hc ⊢
      omega
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · exact InRegions_append_cons.mpr (.inr ⟨_, List.mem_append_right _ scrW, hc⟩)
  · intro a n ⟨q, hq, hc⟩
    rw [pushed_wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩
    · exact ⟨_, List.mem_cons_of_mem _ scrW, hc⟩

/-- A call of H′ from the body: `hprime(r0, r1, r2, r3, r12)`. -/
theorem hcall_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (hdx : s.gpr .r12 = VG.Proof.Argon2.Arm.Derive.scrP s₀)
    (hin : ∃ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.locR s₀], ∃ off, State.addr (s.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r1).toNat ≤ R.len)
    (hinfit : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32)
    (hout : ∃ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀], ∃ off, State.addr (s.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .r3).toNat ≤ R.len)
    (houtfit : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32)
    (hL : 1 ≤ (s.gpr .r3).toNat) {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → (∀ q ∈ preserved, q ≠ .lr → t.gpr q = s.gpr q) →
      Frame [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀] s.mem t.mem →
      bytesAt t.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
        Spec.Argon2.hPrime (s.gpr .r3).toNat
          (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) → Q t) :
    WP isa Impl.Argon2.Arm.Derive.hPrimeCall s Q := by
  have hE := VG.Proof.Argon2.Arm.Derive.E_nat hp
  have hlo := hp.sp_lo
  have sp := h.sp
  have hn : 4 * hregs.length ≤ s.sp.toNat := by simp only [List.length_cons, List.length_nil]; rw [sp]; omega
  obtain ⟨RI, hRI, oI, bI, lI⟩ := hin
  obtain ⟨RO, hRO, oO, bO, lO⟩ := hout
  have sI : Region.Sub ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ RI := by
    rw [bI]; exact Offset.sub_base _ lI
  have sO : Region.Sub ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ RO := by
    rw [bO]; exact Offset.sub_base _ lO
  have I_call : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ (VG.Proof.Argon2.Arm.Derive.callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact (VG.Proof.Argon2.Arm.Derive.call_disj hp (R := VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).symm.sub_left sI
    · exact (VG.Proof.Argon2.Arm.Derive.loc_call hp).sub_left sI
  obtain ⟨pre, cv, cw⟩ := VG.Proof.Argon2.Arm.Derive.hcall_pre hp h hdx ⟨RI, hRI, oI, bI, lI⟩ hinfit ⟨RO, hRO, oO, bO, lO⟩ houtfit hL
  unfold Impl.Argon2.Arm.Derive.hPrimeCall
  refine frameCall_ok (rs := VG.Proof.Argon2.Arm.Derive.hregs) (t := .r12) (by decide) (by decide) (by decide) (k := HPrime.hPrimeArm)
    HPrime.hPrime_verified.1 (K := 40) (by rw [VG.Proof.Argon2.Arm.Derive.hPrime_stack]; decide) (by rw [sp]; omega) pre cv cw
    fun t af post => ?_
  simp only [HPrime.hPrimeArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide),
    pushed_gpr] at post
  have bk : bytesAt (pushed VG.Proof.Argon2.Arm.Derive.hregs s).mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat =
      bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat :=
    VG.Proof.Argon2.Arm.Derive.bytes_keep (VG.Proof.Argon2.Arm.pushed_stk hn)
    (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact I_call.sub_right (by rw [sp]; exact stkR_sub (by decide) (by omega)))
    (Nat.le_of_lt (Nat.lt_trans (s.gpr .r1).isLt (by decide)))
  rw [bk] at post
  have f₁ : Frame [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀] s.mem
      (popped .r12 (4 * hregs.length) t).mem :=
    af.frame.sub fun q hq => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨VG.Proof.Argon2.Arm.Derive.callR s₀, by simp, by rw [sp]; exact fun _ h => h⟩
  refine k _ (h.step af.sp (af.cs .r11 (by decide) (by decide)) af.rd af.wr (f₁.sub fun q hq => ?_))
    (fun q hq hl => af.cs q hq hl) f₁ (by simpa [popped_mem] using post)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · refine ⟨RO, ?_, sO⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl <;> simp
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.Clear`. -/
section

/-!
# Argon2 on ARMv7: clearing the memory matrix

`clear_ok`: `clear` zeroes the `blocks · 1024` bytes of the memory matrix,
one word per iteration, and writes nothing else. Its loop counts the words
left in `r6` (`blocks · 256`), with `r5` the next word's address and `r7`
zero.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_subs wp_str op2_imm op2_lsl)
open VG.Spec.Blake2 (bytesAt)

/-- The memory matrix, as an address. -/
abbrev memB (s₀ : State) : Addr := State.addr (VG.Proof.Argon2.Arm.Derive.memP s₀)

/-- A byte after a zero word is stored at `a`. -/
theorem writeW_zero (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 32)) x = if (x - a).toNat < 4 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- `[x + d + k]`, at a 32-bit address that does not wrap. -/
theorem addr32 {x : BitVec 32} {d k : Nat} (h : x.toNat + d + k < 2 ^ 32) :
    State.addr (x + BitVec.ofNat 32 d + BitVec.ofNat 32 k) = State.addr x + BitVec.ofNat 64 (d + k) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact addr_add (by omega)

/-- A store to a region the body may write keeps the invariant. -/
theorem Inv.store {s₀ s t : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {R : Region} (hR : R ∈ VG.Proof.Argon2.Arm.Derive.bodyW s₀) {a : Addr}
    {v : BitVec 32} (hc : R.Contains a 4) (u : Mupd s t (s.mem.writeW a v)) : VG.Proof.Argon2.Arm.Derive.Inv s₀ t :=
  h.step u.sp (by rw [u.gpr]) u.rd u.wr (by rw [u.mem]; exact (Frame.refl _ _).writeW hR v hc)

/-- The loop's state after `j` words. -/
structure CI (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  inv : VG.Proof.Argon2.Arm.Derive.Inv s₀ s
  r5 : s.gpr .r5 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (4 * j)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 256 - j)
  r7 : s.gpr .r7 = 0
  zero : ∀ i < 4 * j, s.mem (VG.Proof.Argon2.Arm.Derive.memB s₀ + BitVec.ofNat 64 i) = 0
  frame : Frame [VG.Proof.Argon2.Arm.Derive.memR s₀] s₁.mem s.mem

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem blocks_pos : 1 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ := by
  rw [hp.blocks_eq, hp.laneLen_eq]
  have := Nat.mul_le_mul hp.lanes_pos (show 1 ≤ 4 * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen by have := hp.segLen_two; omega)
  omega

theorem clearLoop_ok {s₁ : State} (h : VG.Proof.Argon2.Arm.Derive.CI s₀ s₁ 0 s₁) :
    WP isa (.loop (.block Impl.Argon2.Arm.Derive.clearWord) .ne) s₁ (VG.Proof.Argon2.Arm.Derive.CI s₀ s₁ (VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 256)) := by
  have hm := hp.mem_fits
  have hb := hp.blocks_lt
  have b1 := VG.Proof.Argon2.Arm.Derive.blocks_pos hp
  refine WP.loop (M := isa) (fun n s => ∃ j, n = VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 256 - j ∧ j < VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 256 ∧ VG.Proof.Argon2.Arm.Derive.CI s₀ s₁ j s)
    ?_ (VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 256) s₁ ⟨0, by omega, by omega, h⟩
  rintro n s ⟨j, rfl, hj, c⟩
  have ea : State.addr (s.gpr .r5 + BitVec.ofNat 32 0) = VG.Proof.Argon2.Arm.Derive.memB s₀ + BitVec.ofNat 64 (4 * j) := by
    rw [c.r5, VG.Proof.Argon2.Arm.Derive.addr32 (by omega), Nat.add_zero]
  have hc : (VG.Proof.Argon2.Arm.Derive.memR s₀).Contains (VG.Proof.Argon2.Arm.Derive.memB s₀ + BitVec.ofNat 64 (4 * j)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  simp only [Impl.Argon2.Arm.Derive.clearWord]
  refine wp_str (by decide) ea (by rw [c.inv.wr]; exact ⟨_, VG.Proof.Argon2.Arm.Derive.mem_mem hp, hc⟩) fun t₁ u₁ => ?_
  have i₁ := c.inv.store (R := VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp) hc u₁
  refine wp_add (op2_imm (by decide)) fun t₂ u₂ => wp_subs (op2_imm (by decide)) fun t u zf => WP.block_nil ?_
  have i₃ := (i₁.upd u₂ (by decide)).upd u (by decide)
  have e₁ : t.gpr .r6 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 256 - (j + 1)) := by
    rw [u.gpr, u₂.other _ (by decide), u₁.gpr, c.r6, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.Arm.sub_ofNat (by omega), Nat.sub_sub]
  have next : VG.Proof.Argon2.Arm.Derive.CI s₀ s₁ (j + 1) t := by
    refine ⟨i₃, ?_, e₁, ?_, fun i hi => ?_, ?_⟩
    · rw [u.other _ (by decide), u₂.gpr, u₁.gpr, c.r5, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl
    · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.gpr, c.r7]
    · rw [u.mem, u₂.mem, u₁.mem, c.r7, VG.Proof.Argon2.Arm.Derive.writeW_zero]
      by_cases hi' : i < 4 * j
      · split
        · rfl
        · exact c.zero i hi'
      · rw [show VG.Proof.Argon2.Arm.Derive.memB s₀ + BitVec.ofNat 64 i = VG.Proof.Argon2.Arm.Derive.memB s₀ + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 (i - 4 * j) by
          rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' (by omega)],
          Offset.add_sub_cancel_left]
        split
        · rfl
        · rename_i hn; rw [BitVec.toNat_ofNat] at hn; omega
    · rw [u.mem, u₂.mem, u₁.mem]
      exact c.frame.writeW (List.mem_singleton_self _) _ hc
  have z : VG.Arm.eval .ne t = some (!decide (VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 256 - (j + 1) = 0)) := by
    rw [MdStream.Arm.eval_ne, zf, ← u.gpr, e₁, MdStream.Arm.ofNat_beq_zero (by omega)]
  by_cases done : j + 1 = VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 256
  · refine .inl ⟨by rw [z]; simp; omega, done ▸ next⟩
  · refine .inr ⟨by rw [z]; simp; omega, VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 256 - (j + 1), by omega, j + 1, rfl, by omega, next⟩

theorem clear_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) :
    WP isa Impl.Argon2.Arm.Derive.clear s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ Frame [VG.Proof.Argon2.Arm.Derive.memR s₀] s.mem t.mem ∧
      ∀ i < VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024, t.mem (VG.Proof.Argon2.Arm.Derive.memB s₀ + BitVec.ofNat 64 i) = 0 := by
  have hb := hp.blocks_lt
  have eb : VG.Proof.Argon2.Arm.Derive.blocksN s₀ = (VG.Proof.Argon2.Arm.Derive.arg s₀ 14).toNat := rfl
  unfold Impl.Argon2.Arm.Derive.clear Impl.Argon2.Arm.Derive.clearSetup
  refine WP.seq (VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ =>
    VG.Proof.Argon2.Arm.Derive.wp_ldarg hp (h.upd u₁ (by decide)) (i := 14) (by decide) fun s₂ u₂ => ?_)
  have i₂ := (h.upd u₁ (by decide)).upd u₂ (by decide)
  refine wp_mov (op2_lsl (by decide)) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have i₄ := (i₂.upd u₃ (by decide)).upd u₄ (by decide)
  refine (VG.Proof.Argon2.Arm.Derive.clearLoop_ok hp ⟨i₄, ?_, ?_, u₄.gpr, fun i hi => absurd hi (by omega), Frame.refl _ _⟩).mono
    fun t c => ⟨c.inv, ?_, fun i hi => c.zero i (by omega)⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    simp
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.Argon2.Arm.Derive.shl_nat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show s.mem = s₄.mem by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]]
    exact c.frame

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.MemoryInit`. -/
section

/-!
# Argon2 on ARMv7: the memory's initialization

`memoryInit_ok`: after `memoryInit`, the memory matrix represents
`initMemory` (`Proof.Argon2.Represents`). The matrix is cleared, then each
lane's first two blocks are H′ of the 72 bytes at the start of the locals
(`initBlock_ok`), H₀ followed by the column and the lane, written there just
before the call. `LI s₀ h0 l` is the state after `l` lanes (`initCell`).
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_sub wp_cmp op2_imm op2_reg)
open VG.Spec.Blake2 (bytesAt)
open VG.Spec.Argon2 (Block blockAt zeroBlock parseBlock)
open VG.Impl.Argon2.Arm.Derive (ld st)

/-! ## Blocks in memory -/

/-- A block outside a frame's regions is kept. -/
theorem blockAt_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 1024⟩ r) : blockAt m' p = blockAt m p := by
  unfold blockAt
  exact congrArg Vector.ofFn (funext fun j => f.read (r := ⟨p, 1024⟩)
    (Offset.contains_base p (by have := j.isLt; omega) (by have := j.isLt; omega)) hd (by decide))

theorem read_zero {m : Mem} {a : Addr} {n : Nat} (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = 0) :
    m.read a n = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have h0 : m a = 0 := by simpa using h 0 (by omega)
    have h1 : m.read (a + 1) n = 0 := ih fun i hi => by
      rw [BitVec.add_assoc, show (1 : Addr) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      exact h (1 + i) (by omega)
    simp only [Mem.read, h0, h1]
    exact BitVec.zero_append_zero

/-- A block of zero bytes. -/
theorem blockAt_zero {m : Mem} {p : Addr} (h : ∀ i < 1024, m (p + BitVec.ofNat 64 i) = 0) :
    blockAt m p = zeroBlock := by
  unfold blockAt zeroBlock
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, Vector.getElem_replicate]
  exact VG.Proof.Argon2.Arm.Derive.read_zero fun i hi => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact h _ (by omega)

/-! ## The initialized cells -/

/-- Cell `k` after the first two blocks of the first `l` lanes are initialized. -/
def initCell (p : Spec.Argon2.Params) (h0 : List Byte) (l k : Nat) : Block :=
  if k / p.laneLen < l ∧ k % p.laneLen < 2 then
    parseBlock (initialBytes h0 (k / p.laneLen) (k % p.laneLen))
  else zeroBlock

theorem initCell_zero (p : Spec.Argon2.Params) (h0 : List Byte) (k : Nat) : VG.Proof.Argon2.Arm.Derive.initCell p h0 0 k = zeroBlock := by
  unfold VG.Proof.Argon2.Arm.Derive.initCell
  exact ite_eq_right fun h => Nat.not_lt_zero _ h.1

theorem cell_div {L l c : Nat} (hc : c < L) : (l * L + c) / L = l := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem cell_mod {L l c : Nat} (hc : c < L) : (l * L + c) % L = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem initCell_new (p : Spec.Argon2.Params) (h0 : List Byte) {l c : Nat} (hL : 2 ≤ p.laneLen) (hc : c < 2) :
    VG.Proof.Argon2.Arm.Derive.initCell p h0 (l + 1) (l * p.laneLen + c) = parseBlock (initialBytes h0 l c) := by
  unfold VG.Proof.Argon2.Arm.Derive.initCell
  rw [VG.Proof.Argon2.Arm.Derive.cell_div (by omega), VG.Proof.Argon2.Arm.Derive.cell_mod (by omega)]
  exact ite_eq_left ⟨by omega, hc⟩

theorem initCell_old (p : Spec.Argon2.Params) (h0 : List Byte) {l k : Nat}
    (h₀ : k ≠ l * p.laneLen) (h₁ : k ≠ l * p.laneLen + 1) :
    VG.Proof.Argon2.Arm.Derive.initCell p h0 (l + 1) k = VG.Proof.Argon2.Arm.Derive.initCell p h0 l k := by
  unfold VG.Proof.Argon2.Arm.Derive.initCell
  have hdm := Nat.div_add_mod k p.laneLen
  by_cases hq : k / p.laneLen = l
  · rw [hq, Nat.mul_comm] at hdm
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · by_cases hc : k / p.laneLen < l ∧ k % p.laneLen < 2
    · rw [ite_eq_left (by omega), ite_eq_left hc]
    · rw [ite_eq_right (by omega), ite_eq_right hc]

/-- `a - b` is zero exactly when `a = b`, for 32-bit numbers. -/
theorem ofNat_sub_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : BitVec.ofNat 32 a - BitVec.ofNat 32 b ≠ 0 := by
      intro e
      have e' := congrArg BitVec.toNat e
      have z : (0 : BitVec 32).toNat = 0 := rfl
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, z] at e'
      omega
    rw [decide_eq_false h]
    exact beq_eq_false_iff_ne.mpr hne

/-! ## A lane's first blocks -/

/-- A store to the locals at `d` keeps their first `n ≤ d` bytes. -/
theorem loc_bytes_store {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀) {m : Mem} {d n : Nat} (hn : n ≤ d) (hd : d + 4 ≤ 144)
    (v : BitVec 32) :
    bytesAt (m.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) v) (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)) n =
      bytesAt m (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)) n := by
  have := VG.Proof.Argon2.Arm.Derive.E_hi hp
  refine VG.Proof.Argon2.Arm.Derive.bytes_keep
    ((Frame.refl [⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), 4⟩] m).writeW (List.mem_singleton_self _) v
      (Region.contains_self _ _))
    (fun r hr => ?_) (by omega)
  simp only [List.mem_singleton] at hr; subst hr
  exact VG.Proof.Argon2.Arm.Derive.disj32 (.inl (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := d) (by omega)]; omega)) (by omega)
    (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (d := d) (by omega)]; omega)

/-- The 72 bytes of H′'s input: H₀, then two words. -/
theorem bytes72 (m : Mem) (p : Addr) :
    bytesAt m p 72 = bytesAt m p 64 ++ Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 64) 32) ++
      Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 68) 32) := by
  rw [show (72 : Nat) = 64 + (4 + (4 + 0)) from rfl, Proof.Blake2.bytesAt_add, VG.Proof.Argon2.Arm.Derive.bytes_word, VG.Proof.Argon2.Arm.Derive.bytes_word,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  simp [bytesAt]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

omit hp in
/-- The call's frame lies in the body's regions. -/
theorem call_sub {O : Region} (hO : Region.Sub O (VG.Proof.Argon2.Arm.Derive.memR s₀) ∨ Region.Sub O (VG.Proof.Argon2.Arm.Derive.outR s₀)) :
    ∀ r ∈ [O, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀], ∃ r' ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The first 64 bytes of the locals are outside a call's frame. -/
theorem h0_call {O : Region} (hO : Region.Sub O (VG.Proof.Argon2.Arm.Derive.memR s₀) ∨ Region.Sub O (VG.Proof.Argon2.Arm.Derive.outR s₀)) :
    ∀ r ∈ [O, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀], Region.Disjoint ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀), 64⟩ r := by
  have sub : Region.Sub ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀), 64⟩ (VG.Proof.Argon2.Arm.Derive.locR s₀) := Region.sub_prefix (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ((VG.Proof.Argon2.Arm.Derive.loc_disj' hp (R := VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).sub_left sub).sub_right h
    · exact ((VG.Proof.Argon2.Arm.Derive.loc_disj' hp (R := VG.Proof.Argon2.Arm.Derive.outR s₀) (by simp)).sub_left sub).sub_right h
  · exact (VG.Proof.Argon2.Arm.Derive.loc_disj' hp (R := VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp)).sub_left sub
  · exact (VG.Proof.Argon2.Arm.Derive.loc_call hp).sub_left sub

/-- A cell of the memory matrix is outside `scratch` and the stack below the locals. -/
theorem cell_disj {k : Nat} (hk : k < VG.Proof.Argon2.Arm.Derive.blocksN s₀) :
    ∀ r ∈ [VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀], Region.Disjoint ⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k, 1024⟩ r := by
  have sub : Region.Sub ⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k, 1024⟩ (VG.Proof.Argon2.Arm.Derive.memR s₀) := matrixCell_sub _ _ _ hk
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.mem_scr.sub_left sub
  · exact (VG.Proof.Argon2.Arm.Derive.call_disj hp (R := VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).symm.sub_left sub

theorem cell_addr {k : Nat} (hk : k < VG.Proof.Argon2.Arm.Derive.blocksN s₀) :
    State.addr (VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (k * 1024)) = matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k := by
  have := hp.mem_fits
  have : k * 1024 + 1024 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024 := by omega
  exact addr_add (by omega)

omit hp in
theorem cell_in_mem {k : Nat} (hk : k < VG.Proof.Argon2.Arm.Derive.blocksN s₀) :
    Region.Sub ⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k, 1024⟩ (VG.Proof.Argon2.Arm.Derive.memR s₀) := matrixCell_sub _ _ _ hk

/-- Cells other than `k` are outside its region. -/
theorem cell_other {j k : Nat} (hj : j < VG.Proof.Argon2.Arm.Derive.blocksN s₀) (hk : k < VG.Proof.Argon2.Arm.Derive.blocksN s₀) (ne : j ≠ k) :
    Region.Disjoint ⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) j, 1024⟩ ⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k, 1024⟩ :=
  matrixCell_disjoint _ _ _ _ (by have := hp.blocks_lt; omega) hj hk ne

/-- Block `c < 2` of lane `l`: H′ of H₀, `c` and `l`. -/
theorem initBlock_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)) 64 = h0) {l c : Nat} (hl : l < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hc : c < 2)
    (r5 : s.gpr .r5 = BitVec.ofNat 32 l)
    (r6 : s.gpr .r6 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 ((l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c) * 1024)) :
    WP isa (Impl.Argon2.Arm.Derive.initBlock c) s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ t ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)) 64 = h0 ∧ t.gpr .r5 = s.gpr .r5 ∧ t.gpr .r6 = s.gpr .r6 ∧
      blockAt t.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) (l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c)) = parseBlock (initialBytes h0 l c) ∧
      ∀ k < VG.Proof.Argon2.Arm.Derive.blocksN s₀, k ≠ l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c →
        blockAt t.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k) = blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k) := by
  have hE := VG.Proof.Argon2.Arm.Derive.E_hi hp
  have hs := hp.scr_fits
  have hm := hp.mem_fits
  have hlt := hp.lanes_lt
  have L2 : 2 ≤ (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega
  have hcell : l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c < VG.Proof.Argon2.Arm.Derive.blocksN s₀ := by
    rw [hp.blocks_eq]
    have := Nat.mul_le_mul_right (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen (show l + 1 ≤ VG.Proof.Argon2.Arm.Derive.lanesN s₀ by omega)
    rw [Nat.succ_mul] at this
    omega
  have hec : encodable (BitVec.ofNat 32 c) = true := by
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> decide
  unfold Impl.Argon2.Arm.Derive.initBlock
  refine WP.seq (wp_mov (op2_imm hec) fun s₁ u₁ => ?_)
  have i₁ := h.upd u₁ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₁ (d := 64) (by decide) fun s₂ i₂ v₂ o₂ g₂ m₂ => ?_
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₂ (d := 68) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_imm (by decide)) fun s₇ u₇ => ?_
  have i₇ := (((i₃.upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₇ (i := 15) (by decide) fun s₈ u₈ => WP.block_nil ?_
  have i₈ := i₇.upd u₈ (by decide)
  have m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have g₈ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₈.gpr r = s.gpr r :=
    fun r a b d e f => by
      rw [u₈.other _ f, u₇.other _ e, u₆.other _ d, u₅.other _ b, u₄.other _ a, g₃, g₂, u₁.other _ a]
  have r0₈ : s₈.gpr .r0 = VG.Proof.Argon2.Arm.Derive.E s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      i₃.r11]
  have r1₈ : (s₈.gpr .r1).toNat = 72 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; rfl
  have r3₈ : (s₈.gpr .r3).toNat = 1024 := by rw [u₈.other _ (by decide), u₇.gpr]; rfl
  have r2₈ : s₈.gpr .r2 = s.gpr .r6 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      g₃, g₂, u₁.other _ (by decide)]
  have O : State.addr (s₈.gpr .r2) = matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) (l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c) := by
    rw [r2₈, r6, VG.Proof.Argon2.Arm.Derive.cell_addr hp hcell]
  have sO : Region.Sub ⟨State.addr (s₈.gpr .r2), (s₈.gpr .r3).toNat⟩ (VG.Proof.Argon2.Arm.Derive.memR s₀) := by
    rw [O, r3₈]; exact VG.Proof.Argon2.Arm.Derive.cell_in_mem hcell
  have hcell' : (l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c) * 1024 + 1024 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024 := by omega
  refine VG.Proof.Argon2.Arm.Derive.hcall_ok hp i₈ u₈.gpr
    ⟨VG.Proof.Argon2.Arm.Derive.locR s₀, by simp, 0, by rw [r0₈]; simp, by rw [r1₈]; show 0 + 72 ≤ 144; omega⟩ (by rw [r0₈, r1₈]; omega)
    ⟨VG.Proof.Argon2.Arm.Derive.memR s₀, by simp, (l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c) * 1024, by rw [O]; rfl, by rw [r3₈]; exact hcell'⟩
    (by rw [r2₈, r6, r3₈, VG.Proof.Argon2.Arm.Derive.add_nat (x := VG.Proof.Argon2.Arm.Derive.memP s₀) (k := (l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c) * 1024) (by omega)]; omega)
    (by rw [r3₈]; decide)
    fun t it cs fr post => ⟨it, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The parameters.
    exact Prm.of_lw pr fun d hd => by
      have hd' := VG.Proof.Argon2.Arm.Derive.prm_offs d hd
      rw [VG.Proof.Argon2.Arm.Derive.lw_keep hp fr (VG.Proof.Argon2.Arm.Derive.call_sub (.inl sO)) hd'.1, VG.Proof.Argon2.Arm.Derive.lw_mem m₈, o₃ d (by omega) (by omega),
        o₂ d (by omega) (by omega), VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem]
  · rw [VG.Proof.Argon2.Arm.Derive.bytes_keep fr (VG.Proof.Argon2.Arm.Derive.h0_call hp (.inl sO)) (by omega), m₈, m₃,
      VG.Proof.Argon2.Arm.Derive.loc_bytes_store hp (by decide) (by decide), m₂, VG.Proof.Argon2.Arm.Derive.loc_bytes_store hp (by decide) (by decide), u₁.mem, b0]
  · rw [cs .r5 (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [cs .r6 (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · refine Proof.Argon2.blockAt_of_initialBytes _ _ _ _ _ ?_
    rw [← O, ← r3₈, post, r3₈, r0₈, r1₈, VG.Proof.Argon2.Arm.Derive.bytes72, m₈]
    have w64 : s₃.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀) + BitVec.ofNat 64 64) 32 = BitVec.ofNat 32 c := by
      rw [← VG.Proof.Argon2.Arm.Derive.loc_addr hp (by omega)]
      show VG.Proof.Argon2.Arm.Derive.lw s₀ s₃ 64 = _
      rw [o₃ 64 (by decide) (by decide), v₂, u₁.gpr]
    have w68 : s₃.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀) + BitVec.ofNat 64 68) 32 = BitVec.ofNat 32 l := by
      rw [← VG.Proof.Argon2.Arm.Derive.loc_addr hp (by omega)]
      show VG.Proof.Argon2.Arm.Derive.lw s₀ s₃ 68 = _
      rw [v₃, g₂, u₁.other _ (by decide), r5]
    rw [w64, w68, m₃, VG.Proof.Argon2.Arm.Derive.loc_bytes_store hp (by decide) (by decide), m₂, VG.Proof.Argon2.Arm.Derive.loc_bytes_store hp (by decide) (by decide),
      u₁.mem, b0]
    rfl
  · intro k hk ne
    have fs : Frame [⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 64), 4⟩, ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 68), 4⟩]
        s.mem s₃.mem := by
      rw [m₃, m₂, u₁.mem]
      exact ((Frame.refl _ _).writeW (w := 32) List.mem_cons_self _ (Region.contains_self _ _)).writeW (w := 32)
        (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
    rw [VG.Proof.Argon2.Arm.Derive.blockAt_keep fr (fun r hr => ?_), m₈]
    · -- The stores to the locals.
      refine VG.Proof.Argon2.Arm.Derive.blockAt_keep fs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((VG.Proof.Argon2.Arm.Derive.loc_disj hp (d := 64) (by decide) (VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).symm.sub_left (VG.Proof.Argon2.Arm.Derive.cell_in_mem hk))
      · exact ((VG.Proof.Argon2.Arm.Derive.loc_disj hp (d := 68) (by decide) (VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).symm.sub_left (VG.Proof.Argon2.Arm.Derive.cell_in_mem hk))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [O, r3₈]; exact VG.Proof.Argon2.Arm.Derive.cell_other hp hk hcell ne
      · exact VG.Proof.Argon2.Arm.Derive.cell_disj hp hk _ (by simp)
      · exact VG.Proof.Argon2.Arm.Derive.cell_disj hp hk _ (by simp)

end

/-- The state after the first two blocks of `l` lanes. -/
structure LI (s₀ : State) (h0 : List Byte) (l : Nat) (s : State) : Prop where
  inv : VG.Proof.Argon2.Arm.Derive.Inv s₀ s
  pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s
  b0 : bytesAt s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)) 64 = h0
  r5 : s.gpr .r5 = BitVec.ofNat 32 l
  r6 : s.gpr .r6 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen * 1024)
  cells : ∀ k < VG.Proof.Argon2.Arm.Derive.blocksN s₀, blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k) = VG.Proof.Argon2.Arm.Derive.initCell (VG.Proof.Argon2.Arm.Derive.prm s₀) h0 l k

theorem Prm.of_mem {s₀ s t : State} (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s) (h : t.mem = s.mem) : VG.Proof.Argon2.Arm.Derive.Prm s₀ t :=
  Prm.of_lw pr fun d _ => VG.Proof.Argon2.Arm.Derive.lw_mem h d

theorem r6_next (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + 1024 + BitVec.ofNat 32 b - 1024 = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc (x + _) 1024, BitVec.add_comm 1024 (BitVec.ofNat 32 b), ← BitVec.add_assoc,
    BitVec.add_sub_cancel, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem lane_ok {h0 : List Byte} {l : Nat} {s : State} (hl : l < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (h : VG.Proof.Argon2.Arm.Derive.LI s₀ h0 l s) :
    WP isa Impl.Argon2.Arm.Derive.initLane s fun t =>
      VG.Proof.Argon2.Arm.Derive.LI s₀ h0 (l + 1) t ∧ VG.Arm.eval .ne t = some (!decide (l + 1 = VG.Proof.Argon2.Arm.Derive.lanesN s₀)) := by
  have L2 : 2 ≤ (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega
  have hlt := hp.lanes_lt
  unfold Impl.Argon2.Arm.Derive.initLane
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.initBlock_ok hp h.inv h.pr h.b0 hl (c := 0) (by decide) h.r5
    (by rw [h.r6, Nat.add_zero])).mono fun s₁ ⟨i₁, p₁, b₁, e₁, d₁, w₁, o₁⟩ => ?_)
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_)
  have i₂ := i₁.upd u₂ (by decide)
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.initBlock_ok hp i₂ (p₁.of_mem u₂.mem) (h0 := h0) (by rw [u₂.mem]; exact b₁) hl (c := 1)
    (by decide) (by rw [u₂.other _ (by decide), e₁, h.r5])
    (by rw [u₂.gpr, d₁, h.r6, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat, Nat.succ_mul])).mono fun s₃ ⟨i₃, p₃, b₃, e₃, d₃, w₃, o₃⟩ => ?_)
  simp only [Impl.Argon2.Arm.Derive.nextLane]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp i₃ (d := Impl.Argon2.Arm.Derive.strideOff) (by decide) fun s₄ u₄ =>
    wp_add (op2_reg _ _) fun s₅ u₅ => wp_sub (op2_imm (by decide)) fun s₆ u₆ =>
      wp_add (op2_imm (by decide)) fun s₇ u₇ => ?_
  have i₇ := (((i₃.upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₇ (i := 7) (by decide) fun s₈ u₈ => ?_
  have i₈ := i₇.upd u₈ (by decide)
  have m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have r5₈ : s₈.gpr .r5 = BitVec.ofNat 32 (l + 1) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃,
      u₂.other _ (by decide), e₁, h.r5, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_add_ofNat]
  refine wp_cmp (op2_reg _ _) fun t f z => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact i₈.step f.sp (by rw [f.gpr]) f.rd f.wr (by rw [f.mem]; exact Frame.refl _ _)
  · exact p₃.of_mem (by rw [f.mem, m₈])
  · rw [f.mem, m₈, b₃]
  · rw [f.gpr, r5₈]
  · rw [f.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₄.other _ (by decide), d₃,
      u₂.gpr, d₁, h.r6, p₃.stride, VG.Proof.Argon2.Arm.Derive.r6_next, Nat.succ_mul, Nat.add_mul]
  · intro k hk
    rw [f.mem, m₈]
    by_cases k1 : k = l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + 1
    · rw [k1, w₃]; exact (VG.Proof.Argon2.Arm.Derive.initCell_new _ _ L2 (by decide)).symm
    rw [o₃ k hk k1]
    by_cases k0 : k = l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen
    · rw [u₂.mem, k0, show l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen = l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + 0 from rfl, w₁]
      exact (VG.Proof.Argon2.Arm.Derive.initCell_new _ _ L2 (by decide)).symm
    rw [u₂.mem, o₁ k hk (by omega), h.cells k hk, VG.Proof.Argon2.Arm.Derive.initCell_old _ _ k0 k1]
  · rw [MdStream.Arm.eval_ne, z, u₈.gpr, r5₈, show VG.Proof.Argon2.Arm.Derive.arg s₀ 7 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.lanesN s₀) by simp,
      VG.Proof.Argon2.Arm.Derive.ofNat_sub_beq (by omega) (by omega)]

/-- `clear`, from the body with H₀ in the locals. -/
theorem clearW_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)) 64 = h0) :
    WP isa Impl.Argon2.Arm.Derive.clear s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ t ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)) 64 = h0 ∧ ∀ i < VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024,
        t.mem (VG.Proof.Argon2.Arm.Derive.memB s₀ + BitVec.ofNat 64 i) = 0 := by
  refine (VG.Proof.Argon2.Arm.Derive.clear_ok hp h).mono fun s₁ ⟨i₁, f₁, z₁⟩ => ⟨i₁, ?_, ?_, z₁⟩
  · have fsub : ∀ r ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀], ∃ r' ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
    exact Prm.of_lw pr fun d hd => VG.Proof.Argon2.Arm.Derive.lw_keep hp f₁ fsub (VG.Proof.Argon2.Arm.Derive.prm_offs d hd).1
  · rw [VG.Proof.Argon2.Arm.Derive.bytes_keep f₁ (fun r hr => ?_) (by omega), b0]
    simp only [List.mem_singleton] at hr; subst hr
    exact (VG.Proof.Argon2.Arm.Derive.loc_disj' hp (R := VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).sub_left (Region.sub_prefix (by decide))

/-- The first lane's first block, after `clear`. -/
theorem laneStart_ok {s : State} {h0 : List Byte} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ s ∧
      bytesAt s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)) 64 = h0 ∧ ∀ i < VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024,
        s.mem (VG.Proof.Argon2.Arm.Derive.memB s₀ + BitVec.ofNat 64 i) = 0) :
    WP isa (.block [ld .r6 (Impl.Argon2.Arm.Derive.argOff 13), .mov .r5 (.imm 0)]) s (VG.Proof.Argon2.Arm.Derive.LI s₀ h0 0) := by
  obtain ⟨i₁, p₁, b₁, z₁⟩ := h
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₁ (i := 13) (by decide) fun s₂ u₂ => wp_mov (op2_imm (by decide)) fun s₃ u₃ =>
    WP.block_nil ?_
  have i₃ := (i₁.upd u₂ (by decide)).upd u₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem]
  refine ⟨i₃, p₁.of_mem m₃, by rw [m₃]; exact b₁, u₃.gpr, ?_, fun k hk => ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr]; simp
  · rw [VG.Proof.Argon2.Arm.Derive.initCell_zero, m₃]
    refine VG.Proof.Argon2.Arm.Derive.blockAt_zero fun i hi => ?_
    rw [matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact z₁ _ (by omega)

theorem memoryInit_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)) 64 = h0) :
    WP isa Impl.Argon2.Arm.Derive.memoryInit s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ t ∧
      Represents t.mem (VG.Proof.Argon2.Arm.Derive.memB s₀) (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks (Spec.Argon2.initMemory (VG.Proof.Argon2.Arm.Derive.prm s₀) h0).memory := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  have hb := hp.blocks_lt
  unfold Impl.Argon2.Arm.Derive.memoryInit
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.clearW_ok hp h pr b0).mono fun s₁ h₁ => WP.seq ((VG.Proof.Argon2.Arm.Derive.laneStart_ok hp h₁).mono fun s₃ start => ?_))
  refine WP.loop (M := isa) (fun n t => ∃ l, n = VG.Proof.Argon2.Arm.Derive.lanesN s₀ - l ∧ l < VG.Proof.Argon2.Arm.Derive.lanesN s₀ ∧ VG.Proof.Argon2.Arm.Derive.LI s₀ h0 l t) ?_
    (VG.Proof.Argon2.Arm.Derive.lanesN s₀) s₃ ⟨0, by omega, by omega, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (VG.Proof.Argon2.Arm.Derive.lane_ok hp hl ht).mono fun u ⟨hu, cu⟩ => ?_
  by_cases done : l + 1 = VG.Proof.Argon2.Arm.Derive.lanesN s₀
  · refine .inl ⟨by show VG.Arm.eval .ne u = _; rw [cu]; simp [done], hu.inv, hu.pr, ?_⟩
    refine ⟨Proof.Argon2.initMemory_size _ _, fun k hk => ?_⟩
    have hk' : k < VG.Proof.Argon2.Arm.Derive.blocksN s₀ := by rw [hp.blocks]; exact hk
    rw [hu.cells k hk', Array.getElem?_eq_getElem (by rw [Proof.Argon2.initMemory_size]; exact hk),
      Option.getD_some, Proof.Argon2.initMemory_cell _ _ _ hk, VG.Proof.Argon2.Arm.Derive.initCell, done]
    have : k / (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen < VG.Proof.Argon2.Arm.Derive.lanesN s₀ := by
      rw [hp.blocks_eq] at hk'
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk')
    by_cases c2 : k % (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen < 2
    · rw [ite_eq_left ⟨this, c2⟩, ite_eq_left c2]
    · rw [ite_eq_right (fun h => c2 h.2), ite_eq_right c2]
  · refine .inr ⟨by show VG.Arm.eval .ne u = _; rw [cu]; simp [done], VG.Proof.Argon2.Arm.Derive.lanesN s₀ - (l + 1), by omega, l + 1, rfl, by omega, hu⟩

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillSteps`. -/
section

/-!
# Argon2 on ARMv7: the steps of the filling loops

The address computations the filling loops share: `column_ok` (the current
column), `blockAddr_ok` (a block's address from its lane and column) and
`prevPointer_ok` (the previous block's). Register-only steps are described
by `Only` (the registers they may write), which keeps the body's invariant
when `r11` is not among them (`Inv.only`).
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.Sha512.Arm (Only)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_cmp op2_imm op2_reg op2_lsl)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff ld)

theorem Inv.only {s₀ s t : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {ds : List Reg} (o : Only ds s t) (h11 : Reg.r11 ∉ ds) :
    VG.Proof.Argon2.Arm.Derive.Inv s₀ t :=
  h.step o.sp (o.gpr _ h11) o.rd o.wr (by rw [o.mem]; exact Frame.refl _ _)

theorem Only.of_fupd {s t : State} (f : Fupd s t) : Only [] s t :=
  ⟨fun _ _ => by rw [f.gpr], f.mem, f.rd, f.wr, f.sp⟩

theorem Divide.Keep.only {s t : State} (k : Divide.Keep s t) : Only [.r0, .r1, .r3] s t :=
  ⟨fun r hr => k.other r (fun h => hr (by simp [h])) (fun h => hr (by simp [h])) (fun h => hr (by simp [h])),
    k.mem, k.rd, k.wr, k.sp⟩

/-- `ofNat x << n`, without overflow. -/
theorem ofNat_shl {x n : Nat} (h : x * 2 ^ n < 2 ^ 32) :
    BitVec.ofNat 32 x <<< n = BitVec.ofNat 32 (x * 2 ^ n) := by
  have hx : x < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right x (Nat.two_pow_pos n)) h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- `ofNat a * ofNat b`, without overflow. -/
theorem ofNat_mul_ofNat {a b : Nat} : BitVec.ofNat 32 a * BitVec.ofNat 32 b = BitVec.ofNat 32 (a * b) :=
  (BitVec.ofNat_mul ..).symm

/-! ## Addresses -/

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem laneLen_ge : 8 ≤ (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega

/-- A cell of the matrix, and its bytes, fit below 2³². -/
theorem cell_fits {lane col : Nat} (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hc : col < (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen) :
    lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + col < VG.Proof.Argon2.Arm.Derive.blocksN s₀ ∧
      (VG.Proof.Argon2.Arm.Derive.memP s₀).toNat + ((lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + col) * 1024 + 1024) ≤ 2 ^ 32 := by
  have hm := hp.mem_fits
  have : lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + col < VG.Proof.Argon2.Arm.Derive.blocksN s₀ := by
    have e := hp.blocks_eq
    have := Nat.mul_le_mul_right (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen (show lane + 1 ≤ VG.Proof.Argon2.Arm.Derive.lanesN s₀ by omega)
    rw [Nat.succ_mul] at this
    omega
  have h2 : (lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + col + 1) * 1024 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024 := Nat.mul_le_mul_right 1024 this
  rw [Nat.succ_mul] at h2
  exact ⟨this, Nat.le_trans (Nat.add_le_add_left h2 _) hm⟩

/-- `blockAddr`: `r0 :=` the address of block `col` of lane `lane`. -/
theorem blockAddr_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s) {lane col : Nat} (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀)
    (hc : col < (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen) (ha : s.gpr .r0 = BitVec.ofNat 32 lane) (hcx : s.gpr .r1 = BitVec.ofNat 32 col)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r0 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 ((lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + col) * 1024) →
      Only [.r0, .r2] s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.blockAddr ++ is)) s Q := by
  obtain ⟨cl, cf⟩ := VG.Proof.Argon2.Arm.Derive.cell_fits hp hl hc
  have hb := hp.blocks_lt
  unfold Impl.Argon2.Arm.Derive.blockAddr
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h (d := laneLenOff) (by decide) fun s₁ u₁ => wp_mul fun s₂ u₂ =>
    wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  have i₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  have e₃ : s₃.gpr .r0 = BitVec.ofNat 32 (lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + col) := by
    rw [u₃.gpr, u₂.gpr, u₂.other .r1 (by decide), u₁.other .r0 (by decide), u₁.other .r1 (by decide), u₁.gpr,
      ha, hcx, pr.laneLen, VG.Proof.Argon2.Arm.Derive.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₃ (i := 13) (by decide) fun s₄ u₄ => wp_add (op2_lsl (by decide)) fun s₅ u₅ => k s₅ ?_ ?_
  · rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), e₃, VG.Proof.Argon2.Arm.Derive.ofNat_shl (by omega)]
  · exact ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans
      (Only.of_upd u₅) |>.mono (by simp)

end

/-- The loop position in the locals. -/
structure Pos (s₀ s : State) (pass slice lane index : Nat) : Prop where
  pass : VG.Proof.Argon2.Arm.Derive.lw s₀ s Impl.Argon2.Arm.Derive.passOff = BitVec.ofNat 32 pass
  slice : VG.Proof.Argon2.Arm.Derive.lw s₀ s sliceOff = BitVec.ofNat 32 slice
  lane : VG.Proof.Argon2.Arm.Derive.lw s₀ s laneOff = BitVec.ofNat 32 lane
  index : VG.Proof.Argon2.Arm.Derive.lw s₀ s indexOff = BitVec.ofNat 32 index

theorem Pos.of_mem {s₀ s t : State} {pass slice lane index : Nat} (h : VG.Proof.Argon2.Arm.Derive.Pos s₀ s pass slice lane index)
    (hm : t.mem = s.mem) : VG.Proof.Argon2.Arm.Derive.Pos s₀ t pass slice lane index :=
  ⟨by rw [VG.Proof.Argon2.Arm.Derive.lw_mem hm]; exact h.pass, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem hm]; exact h.slice, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem hm]; exact h.lane,
    by rw [VG.Proof.Argon2.Arm.Derive.lw_mem hm]; exact h.index⟩

theorem Pos.of_lw {s₀ s t : State} {pass slice lane index : Nat} (h : VG.Proof.Argon2.Arm.Derive.Pos s₀ s pass slice lane index)
    (hl : ∀ d ∈ [Impl.Argon2.Arm.Derive.passOff, sliceOff, laneOff, indexOff], VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d) :
    VG.Proof.Argon2.Arm.Derive.Pos s₀ t pass slice lane index :=
  ⟨by rw [hl _ (by simp)]; exact h.pass, by rw [hl _ (by simp)]; exact h.slice,
    by rw [hl _ (by simp)]; exact h.lane, by rw [hl _ (by simp)]; exact h.index⟩

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem segLen_lt : (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen < 2 ^ 30 := by
  have := VG.Proof.Argon2.Arm.Derive.laneLen_ge hp
  have e := hp.blocks_eq
  have l := hp.laneLen_eq
  have := Nat.le_mul_of_pos_left (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen (show 0 < VG.Proof.Argon2.Arm.Derive.lanesN s₀ from hp.lanes_pos)
  have := hp.blocks_lt
  omega

/-- `column`: `r1 :=` the current column, `slice · segLen + index`. -/
theorem column_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s) {pass slice lane index : Nat}
    (ps : VG.Proof.Argon2.Arm.Derive.Pos s₀ s pass slice lane index) (hs : slice < 4) (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r1 = BitVec.ofNat 32 (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index) → Only [.r0, .r1, .r2] s t →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.column ++ is)) s Q := by
  have sl := VG.Proof.Argon2.Arm.Derive.segLen_lt hp
  have hc := Proof.Argon2.column_lt (VG.Proof.Argon2.Arm.Derive.prm s₀) hp.lanes_pos hs hi
  have := VG.Proof.Argon2.Arm.Derive.laneLen_ge hp
  have ll := hp.laneLen_eq
  unfold Impl.Argon2.Arm.Derive.column
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h (d := sliceOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp i₁ (d := segLenOff) (by decide) fun s₂ u₂ => wp_mul fun s₃ u₃ => ?_
  have i₃ := (i₁.upd u₂ (by decide)).upd u₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp i₃ (d := indexOff) (by decide) fun s₄ u₄ => wp_add (op2_reg _ _) fun t u => k t ?_ ?_
  · rw [u.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem, ps.slice,
      pr.segLen, u₄.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem m₃, ps.index, VG.Proof.Argon2.Arm.Derive.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
  · exact ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans
      (Only.of_upd u) |>.mono (by simp)

/-- `prevColumn`: `r1 :=` the column before `r1`, cyclically. -/
theorem prevColumn_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s) {col : Nat} (hc : col < (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen)
    (hx : s.gpr .r1 = BitVec.ofNat 32 col) :
    WP isa Impl.Argon2.Arm.Derive.prevColumn s fun t =>
      t.gpr .r1 = BitVec.ofNat 32 ((col + (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) % (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen) ∧ Only [.r1] s t := by
  have sl := VG.Proof.Argon2.Arm.Derive.segLen_lt hp
  have := VG.Proof.Argon2.Arm.Derive.laneLen_ge hp
  have ll := hp.laneLen_eq
  unfold Impl.Argon2.Arm.Derive.prevColumn
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  have o₁ := Only.of_fupd f₁
  have i₁ := h.only o₁ (by decide)
  refine WP.seq (WP.ite (decide (col = 0)) ?_ ?_ ?_)
  · show VG.Arm.eval .eq s₁ = _
    have z : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
    rw [MdStream.Arm.eval_eq, z₁, hx, z, MdStream.Arm.ofNat_beq_zero (by omega)]
  · intro hz
    refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => WP.block_nil ?_
    refine wp_sub (op2_imm (by decide)) fun t u => WP.block_nil ⟨?_, ?_⟩
    · have c0 : col = 0 := of_decide_eq_true hz
      rw [u.gpr, u₂.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem f₁.mem, pr.laneLen, c0, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        MdStream.Arm.sub_ofNat (by omega), Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    · exact ((o₁.trans (Only.of_upd u₂)).trans (Only.of_upd u)).mono (by simp)
  · intro hz
    refine WP.block_nil (wp_sub (op2_imm (by decide)) fun t u => WP.block_nil ⟨?_, ?_⟩)
    · have c0 : col ≠ 0 := of_decide_eq_false hz
      rw [u.gpr, f₁.gpr, hx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.Arm.sub_ofNat (by omega)]
      congr 1
      rw [show col + (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1 = col - 1 + (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · exact (o₁.trans (Only.of_upd u)).mono (by simp)

/-- `prevPointer`: `r0 :=` the address of the previous block. -/
theorem prevPointer_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s) {pass slice lane index : Nat}
    (ps : VG.Proof.Argon2.Arm.Derive.Pos s₀ s pass slice lane index) (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hs : slice < 4)
    (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen) :
    WP isa Impl.Argon2.Arm.Derive.prevPointer s fun t =>
      t.gpr .r0 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 ((lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen +
        (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index + (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) % (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen) * 1024) ∧
      Only [.r0, .r1, .r2] s t := by
  have hc := Proof.Argon2.column_lt (VG.Proof.Argon2.Arm.Derive.prm s₀) hp.lanes_pos hs hi
  have := VG.Proof.Argon2.Arm.Derive.laneLen_ge hp
  unfold Impl.Argon2.Arm.Derive.prevPointer
  refine WP.seq ?_
  rw [← List.append_nil Impl.Argon2.Arm.Derive.column]
  refine VG.Proof.Argon2.Arm.Derive.column_ok hp h pr ps hs hi fun s₁ c₁ k₁ => WP.block_nil ?_
  have i₁ := h.only k₁ (by decide)
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.prevColumn_ok hp i₁ (pr.of_mem k₁.mem) hc c₁).mono fun s₂ ⟨c₂, k₂⟩ => ?_)
  have i₂ := i₁.only k₂ (by decide)
  have m₂ : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp i₂ (d := laneOff) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide)
  rw [← List.append_nil Impl.Argon2.Arm.Derive.blockAddr]
  refine VG.Proof.Argon2.Arm.Derive.blockAddr_ok hp i₃ (pr.of_mem (by rw [u₃.mem, m₂])) hl (Nat.mod_lt _ (by omega))
    (by rw [u₃.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem m₂, ps.lane]) (by rw [u₃.other _ (by decide), c₂]) fun t a k => WP.block_nil ⟨a, ?_⟩
  exact (((k₁.trans k₂).trans (Only.of_upd u₃)).trans k).mono (by simp)

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillState`. -/
section

/-!
# Argon2 on ARMv7: the state of the filling loops

`FS s₀ pass slice lane index ctr st`: the body at a position of the filling
loops (`Pos`), the memory matrix representing `st`'s, and the address block
cached in `scratch[6144, 7168)` that of the counter in the locals, if it is
not zero (`CacheOk`). `addressMode_ok`: `addressMode` sets Z for
data-dependent addressing.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_sub wp_orr wp_and wp_cmp op2_imm op2_reg op2_lsr)
open VG.Proof.Blake2.Arm.Stream (wp_eor)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState addressBlock independent)
open VG.Proof.Argon2.Arm (blk)
open VG.Proof.Sha512.Arm (Only rd64 A)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff)

/-- The address block cached at `scratch + 6144`, for the counter in the locals. -/
def CacheOk (s₀ : State) (pass lane slice ctr : Nat) (s : State) : Prop :=
  ctr < 2 ^ 32 ∧ VG.Proof.Argon2.Arm.Derive.lw s₀ s counterOff = BitVec.ofNat 32 ctr ∧
    (ctr = 0 ∨ 1 ≤ ctr ∧ blk s.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 6144 = addressBlock (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice ctr)

/-- The counter after a block: the index's group, for data-independent addressing. -/
def ctrNext (p : Spec.Argon2.Params) (pass slice index ctr : Nat) : Nat :=
  if independent p pass slice then index / 128 + 1 else ctr

/-- The filling loops' state at a position, the memory matrix holding `st`'s. -/
structure FS (s₀ : State) (pass slice lane index ctr : Nat) (st : FillState) (s : State) : Prop where
  inv : VG.Proof.Argon2.Arm.Derive.Inv s₀ s
  pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s
  pos : VG.Proof.Argon2.Arm.Derive.Pos s₀ s pass slice lane index
  cache : VG.Proof.Argon2.Arm.Derive.CacheOk s₀ pass lane slice ctr s
  mem : Represents s.mem (VG.Proof.Argon2.Arm.Derive.memB s₀) (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks st.memory

theorem Represents.keep {m m' : Mem} {base : Addr} {n : Nat} {b : Array Block}
    (h : Represents m base n b) (hk : ∀ k < n, blockAt m' (matrixCell base k) = blockAt m (matrixCell base k)) :
    Represents m' base n b :=
  ⟨h.size, fun k hk' => (hk k hk').trans (h.block k hk')⟩

/-- The block at `B + o`, from `B + o` as its base. -/
theorem blk_shift (m : Mem) (B : BitVec 32) (o : Nat) : blk m (B + BitVec.ofNat 32 o) 0 = blk m B o := by
  apply Vector.ext
  intro j hj
  simp only [blk, Vector.getElem_ofFn, rd64, A, Nat.zero_add, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    Nat.add_assoc]

/-- The cells of the matrix, as `blk`. -/
theorem cell_blk {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀) (m : Mem) {k : Nat} (hk : k < VG.Proof.Argon2.Arm.Derive.blocksN s₀) :
    blockAt m (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k) = blk m (VG.Proof.Argon2.Arm.Derive.memP s₀) (k * 1024) := by
  have := hp.mem_fits
  have : k * 1024 + 1024 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024 := by omega
  rw [← VG.Proof.Argon2.Arm.Derive.cell_addr hp hk, Proof.Argon2.Arm.blockAt_eq (by rw [VG.Proof.Argon2.Arm.Derive.add_nat (by omega)]; omega), VG.Proof.Argon2.Arm.Derive.blk_shift]

/-- Word `j` of a block. -/
theorem blk_get (m : Mem) (B : BitVec 32) (o j : Nat) (hj : j < 128) :
    (blk m B o)[j] = m.readW (A B (o + 8 * j + 4)) 32 ++ m.readW (A B (o + 8 * j)) 32 := by
  simp only [blk, Vector.getElem_ofFn, rd64]

/-- The first word of a block. -/
theorem blk_zero (m : Mem) (B : BitVec 32) (o : Nat) :
    (blk m B o)[0] = m.readW (A B (o + 4)) 32 ++ m.readW (A B o) 32 := by
  simp only [blk, Vector.getElem_ofFn, rd64, Nat.mul_zero, Nat.add_zero]

/-! ## The addressing mode -/

theorem independent_eq {s₀ : State} (hk : (VG.Proof.Argon2.Arm.Derive.kindV s₀).toNat ≤ 2) (pass slice : Nat) :
    independent (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice = (decide ((VG.Proof.Argon2.Arm.Derive.kindV s₀).toNat = 1) ||
      (decide ((VG.Proof.Argon2.Arm.Derive.kindV s₀).toNat = 2) && decide (pass = 0) && decide (slice < 2))) := by
  have hv : (VG.Proof.Argon2.Arm.Derive.prm s₀).variant = (if (VG.Proof.Argon2.Arm.Derive.kindV s₀).toNat = 0 then .d else if (VG.Proof.Argon2.Arm.Derive.kindV s₀).toNat = 1 then .i else .id) :=
    rfl
  have e1 : (Spec.Argon2.Variant.d == .i) = false := rfl
  have e2 : (Spec.Argon2.Variant.d == .id) = false := rfl
  have e3 : (Spec.Argon2.Variant.i == .i) = true := rfl
  have e3' : (Spec.Argon2.Variant.i == .id) = false := rfl
  have e4 : (Spec.Argon2.Variant.id == .i) = false := rfl
  have e5 : (Spec.Argon2.Variant.id == .id) = true := rfl
  rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with h | h | h
  · rw [independent, hv, ite_eq_left h, e1, e2, h]; simp
  · rw [independent, hv, ite_eq_right (by omega), ite_eq_left h, e3, e3', h]; simp
  · rw [independent, hv, ite_eq_right (by omega), ite_eq_right (by omega), e4, e5, h]; simp
    cases pass <;> rfl

/-- `((0 - x) | x) >> 31` is whether `x` is not zero. -/
theorem nz (x : BitVec 32) : ((0 - x) ||| x) >>> 31 = if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · subst hx; decide
  · simp only [hx, ite_false]
    have hn : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq h)
    have hm : ∀ y : BitVec 32, y.msb = decide (2 ^ 31 ≤ y.toNat) := fun y => by rw [BitVec.msb_eq_decide]
    have hb : 2 ^ 31 ≤ ((0 - x) ||| x).toNat := by
      have : ((0 - x) ||| x).msb = true := by
        rw [BitVec.msb_or, hm, hm, BitVec.toNat_sub, show (0 : BitVec 32).toNat = 0 from rfl]
        have := x.isLt
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega
      rw [hm] at this; exact of_decide_eq_true this
    have hl := ((0 - x) ||| x).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    show _ = 1
    omega

/-- The second test of `addressMode`: Argon2id in the first two slices of the first pass. -/
theorem id_zero {k p sl : BitVec 32} (hk : k.toNat ≤ 2) :
    ((k ^^^ (2 : BitVec 32)) ||| p ||| (sl >>> 1) = 0) ↔ (k.toNat = 2 ∧ p = 0 ∧ sl.toNat < 2) := by
  have e : sl >>> 1 = 0 ↔ sl.toNat < 2 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
      rw [show (0 : BitVec 32).toNat = 0 from rfl] at this
      omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [show (0 : BitVec 32).toNat = 0 from rfl]
      omega
  have f : k ^^^ (2 : BitVec 32) = 0 ↔ k.toNat = 2 := by
    rcases (by omega : k.toNat = 0 ∨ k.toNat = 1 ∨ k.toNat = 2) with h | h | h <;>
      · rw [show k = BitVec.ofNat 32 k.toNat by simp, h]; decide
  have orz : ∀ x y : BitVec 32, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
  rw [orz, orz, f, e, and_assoc]

theorem mode_bits (a b : Prop) [Decidable a] [Decidable b] :
    ((((if a then (0 : BitVec 32) else 1) &&& (if b then 0 else 1)) ^^^ 1) - 0 == 0) = !(decide a || decide b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- `addressMode`: Z for data-dependent addressing. -/
theorem addressMode_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {pass slice lane index : Nat}
    (ps : VG.Proof.Argon2.Arm.Derive.Pos s₀ s pass slice lane index) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block Impl.Argon2.Arm.Derive.addressMode) s fun t =>
      VG.Arm.eval .eq t = some (!independent (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice) ∧ Only [.r0, .r1, .r2, .r3, .r12] s t := by
  have hk := hp.kind_le
  unfold Impl.Argon2.Arm.Derive.addressMode
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h (i := 0) (by decide) fun s₁ u₁ => wp_eor (op2_imm (by decide)) fun s₂ u₂ =>
    wp_eor (op2_imm (by decide)) fun s₃ u₃ => ?_
  have o₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  have i₃ := h.only o₃ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp i₃ (d := passOff) (by decide) fun s₄ u₄ => wp_orr (op2_reg _ _) fun s₅ u₅ => ?_
  have o₅ := (o₃.trans (Only.of_upd u₄)).trans (Only.of_upd u₅)
  have i₅ := h.only o₅ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp i₅ (d := sliceOff) (by decide) fun s₆ u₆ => wp_orr (op2_lsr (by decide)) fun s₇ u₇ =>
    wp_mov (op2_imm (by decide)) fun s₈ u₈ => wp_sub (op2_reg _ _) fun s₉ u₉ =>
    wp_orr (op2_reg _ _) fun s₁₀ u₁₀ => wp_mov (op2_lsr (by decide)) fun s₁₁ u₁₁ =>
    wp_sub (op2_reg _ _) fun s₁₂ u₁₂ => wp_orr (op2_reg _ _) fun s₁₃ u₁₃ =>
    wp_mov (op2_lsr (by decide)) fun s₁₄ u₁₄ => wp_and (op2_reg _ _) fun s₁₅ u₁₅ =>
    wp_eor (op2_imm (by decide)) fun s₁₆ u₁₆ => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ⟨?_, ?_⟩
  · have m₅ : s₅.mem = s.mem := o₅.mem
    have v1 : s₈.gpr .r1 = VG.Proof.Argon2.Arm.Derive.kindV s₀ ^^^ 1 := by
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]
    have v2 : s₈.gpr .r2 = (VG.Proof.Argon2.Arm.Derive.kindV s₀ ^^^ (2 : BitVec 32)) ||| BitVec.ofNat 32 pass ||| (BitVec.ofNat 32 slice >>> 1) := by
      rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide),
        u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem m₅, ps.slice, VG.Proof.Argon2.Arm.Derive.lw_mem o₃.mem, ps.pass]
    have v12 : s₁₁.gpr .r12 = if VG.Proof.Argon2.Arm.Derive.kindV s₀ ^^^ 1 = 0 then 0 else 1 := by
      rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₉.other .r1 (by decide), u₈.gpr, v1, VG.Proof.Argon2.Arm.Derive.nz]
    have v0 : s₁₄.gpr .r0 = if (VG.Proof.Argon2.Arm.Derive.kindV s₀ ^^^ (2 : BitVec 32)) ||| BitVec.ofNat 32 pass ||| (BitVec.ofNat 32 slice >>> 1) = 0
        then 0 else 1 := by
      rw [u₁₄.gpr, u₁₃.gpr, u₁₂.gpr, u₁₂.other .r2 (by decide), u₁₁.other _ (by decide), u₁₁.other _ (by decide),
        u₁₀.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₉.other _ (by decide), u₈.gpr,
        v2, VG.Proof.Argon2.Arm.Derive.nz]
    have v16 : s₁₆.gpr .r12 = ((if VG.Proof.Argon2.Arm.Derive.kindV s₀ ^^^ 1 = 0 then (0 : BitVec 32) else 1) &&&
        (if (VG.Proof.Argon2.Arm.Derive.kindV s₀ ^^^ (2 : BitVec 32)) ||| BitVec.ofNat 32 pass ||| (BitVec.ofNat 32 slice >>> 1) = 0 then 0 else 1)) ^^^ 1 := by
      rw [u₁₆.gpr, u₁₅.gpr, v0, u₁₄.other _ (by decide), u₁₃.other _ (by decide),
        u₁₂.other _ (by decide), v12]
    have k1 : (VG.Proof.Argon2.Arm.Derive.kindV s₀ ^^^ 1 = 0) ↔ (VG.Proof.Argon2.Arm.Derive.kindV s₀).toNat = 1 := by
      rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with e | e | e <;>
        · rw [show VG.Proof.Argon2.Arm.Derive.kindV s₀ = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.kindV s₀).toNat by simp, e]; decide
    have ps' : (BitVec.ofNat 32 slice).toNat < 2 ↔ slice < 2 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have pp : BitVec.ofNat 32 pass = 0 ↔ pass = 0 := by
      constructor
      · intro e; have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpass] at this; exact this
      · intro e; rw [e]; rfl
    rw [MdStream.Arm.eval_eq, z, v16, VG.Proof.Argon2.Arm.Derive.mode_bits, VG.Proof.Argon2.Arm.Derive.independent_eq hk]
    simp only [k1, VG.Proof.Argon2.Arm.Derive.id_zero hk, ps', pp, Bool.decide_and, Bool.and_assoc]
  · exact ((((((((((((o₅.trans (Only.of_upd u₆)).trans (Only.of_upd u₇)).trans (Only.of_upd u₈)).trans
      (Only.of_upd u₉)).trans (Only.of_upd u₁₀)).trans (Only.of_upd u₁₁)).trans (Only.of_upd u₁₂)).trans
      (Only.of_upd u₁₃)).trans (Only.of_upd u₁₄)).trans (Only.of_upd u₁₅)).trans (Only.of_upd u₁₆)).trans
      (Only.of_fupd f)).mono (by simp)

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCall`. -/
section

/-!
# Argon2 on ARMv7: calls of G in the filling loops

The filling loops call `vg_argon2_compress` with its arguments in registers,
`compress(r0, r1, r2, r3)`: G of the blocks at `r0` and `r1`, each a cell of
the memory matrix or a block of `scratch` from offset 4096 on (`GArg`), to
`scratch + o` (`r2`), with `scratch[0, 4096)` (`r3`) as its working space
(`ccall_ok`). It uses no stack.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Spec.Argon2 (Block blockAt compress)
open VG.Proof.Argon2.Arm (blk compressArm)

/-- `scratch`, as an address. -/
abbrev scrB (s₀ : State) : Addr := State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀)

/-- A block G may read: a cell of the matrix, or a block of `scratch` from 4096
on apart from the output at offset `o`. -/
def GArg (s₀ : State) (o : Nat) (p : BitVec 32) : Prop :=
  (∃ k < VG.Proof.Argon2.Arm.Derive.blocksN s₀, p = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (k * 1024)) ∨
    ∃ d, 4096 ≤ d ∧ d + 1024 ≤ 16384 ∧ (d + 1024 ≤ o ∨ o + 1024 ≤ d) ∧ p = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 d

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- What a call needs of a block it reads. -/
theorem GArg.facts {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384) {p : BitVec 32} (h : VG.Proof.Argon2.Arm.Derive.GArg s₀ o p) :
    (∃ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀], ∃ off, State.addr p = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len) ∧
    p.toNat + 1024 ≤ 2 ^ 32 ∧
    Region.Disjoint ⟨State.addr p, 1024⟩ ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩ ∧
    Region.Disjoint ⟨State.addr p, 1024⟩ ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀, 4096⟩ := by
  have hs := hp.scr_fits
  have hm := hp.mem_fits
  rcases h with ⟨k, hk, rfl⟩ | ⟨d, hd, hd', hdo, rfl⟩
  · have hk' : k * 1024 + 1024 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024 := by omega
    have e := VG.Proof.Argon2.Arm.Derive.cell_addr hp hk
    have sub : Region.Sub ⟨State.addr (VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (k * 1024)), 1024⟩ (VG.Proof.Argon2.Arm.Derive.memR s₀) := by
      rw [e]; exact VG.Proof.Argon2.Arm.Derive.cell_in_mem hk
    refine ⟨⟨VG.Proof.Argon2.Arm.Derive.memR s₀, by simp, k * 1024, e, hk'⟩, by rw [VG.Proof.Argon2.Arm.Derive.add_nat (by omega)]; omega, ?_, ?_⟩
    · exact (hp.mem_scr.sub_left sub).sub_right (Offset.sub_base _ ho')
    · exact (hp.mem_scr.sub_left sub).sub_right (Region.sub_prefix (by decide))
  · have e : State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 d) = VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 d := VG.Proof.Argon2.Arm.Derive.scr_addr hp (by omega)
    refine ⟨⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, by simp, d, e, hd'⟩, by rw [VG.Proof.Argon2.Arm.Derive.add_nat (by omega)]; omega, ?_, ?_⟩
    · rw [e]; exact Offset.disjoint _ hdo (by omega) (by omega)
    · rw [e]; exact Offset.disjoint_base _ hd (by omega)

/-- The regions G is given. -/
abbrev cRd (s : State) : List Region := [⟨State.addr (s.gpr .r0), 1024⟩, ⟨State.addr (s.gpr .r1), 1024⟩]
abbrev cWr (s₀ : State) (o : Nat) : List Region := [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀, 4096⟩]

/-- What G needs, from the body: `compress(r0, r1, r2, r3)`, to `scratch + o`. -/
theorem ccall_pre {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (h3 : s.gpr .r3 = VG.Proof.Argon2.Arm.Derive.scrP s₀) {o : Nat} (ho : 4096 ≤ o)
    (ho' : o + 1024 ≤ 16384) (h2 : s.gpr .r2 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 o) (hx : VG.Proof.Argon2.Arm.Derive.GArg s₀ o (s.gpr .r0))
    (hy : VG.Proof.Argon2.Arm.Derive.GArg s₀ o (s.gpr .r1)) :
    compressArm.pre (s.callEntry.withRegions (VG.Proof.Argon2.Arm.Derive.cRd s) (VG.Proof.Argon2.Arm.Derive.cWr s₀ o)) ∧ Covers (VG.Proof.Argon2.Arm.Derive.cRd s ++ VG.Proof.Argon2.Arm.Derive.cWr s₀ o) (s.rd ++ s.wr) ∧
      Covers (VG.Proof.Argon2.Arm.Derive.cWr s₀ o) s.wr := by
  have hs := hp.scr_fits
  obtain ⟨⟨RX, hRX, oX, bX, lX⟩, fX, X_out, X_scr⟩ := hx.facts hp ho ho'
  obtain ⟨⟨RY, hRY, oY, bY, lY⟩, fY, Y_out, Y_scr⟩ := hy.facts hp ho ho'
  have eO : State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 o) = VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 o := VG.Proof.Argon2.Arm.Derive.scr_addr hp (by omega)
  have memW : ∀ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀], R ∈ s.wr := fun R hR => by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact VG.Proof.Argon2.Arm.Derive.mem_mem hp
    · exact VG.Proof.Argon2.Arm.Derive.scr_mem hp
  have scrW : VG.Proof.Argon2.Arm.Derive.scrR s₀ ∈ s.wr := memW _ (by simp)
  have cX : Covers [⟨State.addr (s.gpr .r0), 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RX, memW _ hRX, oX, bX, lX⟩
  have cY : Covers [⟨State.addr (s.gpr .r1), 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RY, memW _ hRY, oY, bY, lY⟩
  have cO : Covers [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, scrW, o, rfl, ho'⟩
  have cW : Covers [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀, 4096⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, scrW, 0, by simp, by simp⟩
  have O_W : Region.Disjoint ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩ ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀, 4096⟩ :=
    Offset.disjoint_base _ ho (by omega)
  refine ⟨?_, (Covers.pair cX cY).right.append_left (Covers.pair cO cW).right, Covers.pair cO cW⟩
  · simp only [VG.Proof.Argon2.Arm.compressArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide),
      h2, h3, eO]
    refine ⟨trivial, trivial, O_W, X_out, X_scr, Y_out, Y_scr, fX, fY, by rw [VG.Proof.Argon2.Arm.Derive.add_nat (by omega)]; omega, by omega⟩

/-- A call of G from the body: `compress(r0, r1, r2, r3)`, to `scratch + o`. -/
theorem ccall_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (h3 : s.gpr .r3 = VG.Proof.Argon2.Arm.Derive.scrP s₀) {o : Nat} (ho : 4096 ≤ o)
    (ho' : o + 1024 ≤ 16384) (h2 : s.gpr .r2 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 o) (hx : VG.Proof.Argon2.Arm.Derive.GArg s₀ o (s.gpr .r0))
    (hy : VG.Proof.Argon2.Arm.Derive.GArg s₀ o (s.gpr .r1)) {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → (∀ q ∈ preserved, q ≠ .lr → t.gpr q = s.gpr q) →
      Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀, 4096⟩] s.mem t.mem →
      blk t.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) o =
        compress (blockAt s.mem (State.addr (s.gpr .r0))) (blockAt s.mem (State.addr (s.gpr .r1))) → Q t) :
    WP isa Impl.Argon2.Arm.Derive.compressCall s Q := by
  have hs := hp.scr_fits
  obtain ⟨pre, cv, cw⟩ := VG.Proof.Argon2.Arm.Derive.ccall_pre hp h h3 ho ho' h2 hx hy
  refine WP.call (k := VG.Proof.Argon2.Arm.compressArm) Proof.Argon2.Arm.compress_verified'.1 pre cv cw
    (fun t hrd hwr hsp hf hcs _ hpost => ?_) (by lit_decide)
  simp only [VG.Proof.Argon2.Arm.compressArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), h2] at hpost
  rw [Proof.Argon2.Arm.blockAt_eq (by rw [VG.Proof.Argon2.Arm.Derive.add_nat (by omega)]; omega), VG.Proof.Argon2.Arm.Derive.blk_shift] at hpost
  refine k t (h.step hsp (hcs .r11 (by decide) (by decide)) hrd hwr (hf.sub fun q hq => ?_)) hcs hf hpost
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, by simp, Offset.sub_base _ ho'⟩
  · exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, by simp, Region.sub_prefix (by decide)⟩

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillDep`. -/
section

/-!
# Argon2 on ARMv7: what keeps the filling state, and data-dependent addressing

`FS.keep`: the filling state is kept by steps that keep the parameters, the
position and counter in the locals, the cached address block and the
matrix. `dependentWord_ok`: J₁ and J₂ are the first word of the previous
block.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_ldr)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Proof.Argon2.Arm (blk)
open VG.Proof.Sha512.Arm (Only A)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff j1Off j2Off)

/-- The offsets of the locals the filling state is about. -/
abbrev fsOffs : List Nat :=
  [divisorOff, segLenOff, laneLenOff, strideOff, passOff, sliceOff, laneOff, indexOff, counterOff]

theorem FS.keep {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) (it : VG.Proof.Argon2.Arm.Derive.Inv s₀ t) (hl : ∀ d ∈ VG.Proof.Argon2.Arm.Derive.fsOffs, VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d)
    (hc : blk t.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 6144 = blk s.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 6144)
    (hm : ∀ k < (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks, blockAt t.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k) = blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k)) :
    VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st t := by
  refine ⟨it, Prm.of_lw h.pr fun d hd => hl d (by simp at hd ⊢; omega),
    h.pos.of_lw fun d hd => hl d (by simp at hd ⊢; omega), ?_, Represents.keep h.mem hm⟩
  obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h.cache
  · exact ⟨c0, by rw [hl _ (by simp)]; exact c1, .inl c2⟩
  · exact ⟨c0, by rw [hl _ (by simp)]; exact c1, .inr ⟨c3, by rw [hc]; exact c4⟩⟩

/-- A step that writes only registers but `r11` keeps the filling state. -/
theorem FS.of_only {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) {ds : List Reg} (o : Only ds s t) (h11 : Reg.r11 ∉ ds) :
    VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st t :=
  h.keep (h.inv.only o h11) (fun d _ => VG.Proof.Argon2.Arm.Derive.lw_mem o.mem d) (by rw [o.mem]) fun _ _ => by rw [o.mem]

/-- `[B + o + d]` -/
theorem A_shift (B : BitVec 32) (o d : Nat) : A (B + BitVec.ofNat 32 o) d = A B (o + d) := by
  simp only [A, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- A block of `scratch`. -/
theorem scr_blk (m : Mem) {o : Nat} (ho : o + 1024 ≤ 16384) :
    blk m (VG.Proof.Argon2.Arm.Derive.scrP s₀) o = blockAt m (VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 o) := by
  have := hp.scr_fits
  have f : (VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 o).toNat + 1024 ≤ 2 ^ 32 := by rw [VG.Proof.Argon2.Arm.Derive.add_nat (by omega)]; omega
  rw [← VG.Proof.Argon2.Arm.Derive.scr_addr hp (by omega), Proof.Argon2.Arm.blockAt_eq f, VG.Proof.Argon2.Arm.Derive.blk_shift]

/-- A word of the matrix is kept by a store to the locals. -/
theorem mem_loc_store {m : Mem} {d : Nat} (hd : d + 4 ≤ 144) (v : BitVec 32) {a : Addr}
    (ha : (VG.Proof.Argon2.Arm.Derive.memR s₀).Contains a 4) :
    (m.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) v).readW a 32 = m.readW a 32 :=
  ((Frame.refl [⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), 4⟩] m).writeW (List.mem_singleton_self _) v
    (Region.contains_self _ _)).readW (r := VG.Proof.Argon2.Arm.Derive.memR s₀) ha (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Proof.Argon2.Arm.Derive.loc_disj hp hd (VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).symm) (by decide)

/-- A store to the locals keeps what the filling state is about, but at the word `d`. -/
theorem FS.store {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) (it : VG.Proof.Argon2.Arm.Derive.Inv s₀ t) {d : Nat} (hd : d + 4 ≤ 144)
    (hd' : d ∉ VG.Proof.Argon2.Arm.Derive.fsOffs) (hd'' : d % 4 = 0) {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) v) :
    VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st t := by
  have f : Frame [⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), 4⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)
  refine h.keep it (fun e he => ?_) ?_ fun k hk => ?_
  · show t.mem.readW _ 32 = s.mem.readW _ 32
    rw [hm]
    simp only [VG.Proof.Argon2.Arm.Derive.fsOffs, List.mem_cons, List.not_mem_nil, or_false] at he hd'
    have : (e + 4 ≤ d ∨ d + 4 ≤ e) ∧ e + 4 ≤ 144 := by
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [divisorOff, segLenOff, laneLenOff, strideOff, passOff, sliceOff, laneOff, indexOff,
        counterOff] at hd' ⊢ <;> omega
    exact VG.Proof.Argon2.Arm.Derive.lw_store hp (by omega) (by omega) this.1.symm v
  · rw [VG.Proof.Argon2.Arm.Derive.scr_blk hp t.mem (by decide), VG.Proof.Argon2.Arm.Derive.scr_blk hp s.mem (by decide)]
    refine VG.Proof.Argon2.Arm.Derive.blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (VG.Proof.Argon2.Arm.Derive.loc_disj hp hd (VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ (by omega))
  · refine VG.Proof.Argon2.Arm.Derive.blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hk' : k < VG.Proof.Argon2.Arm.Derive.blocksN s₀ := by rw [hp.blocks]; exact hk
    exact (VG.Proof.Argon2.Arm.Derive.loc_disj hp hd (VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).symm.sub_left (VG.Proof.Argon2.Arm.Derive.cell_in_mem hk')

/-- `dependentWord`: J₁ and J₂ are the halves of the previous block's first word. -/
theorem dependentWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hs : slice < 4)
    (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen) :
    WP isa Impl.Argon2.Arm.Derive.dependentWord s fun t => VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st t ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀ t j2Off ++ VG.Proof.Argon2.Arm.Derive.lw s₀ t j1Off = (blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) (lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen +
        (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index + (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) % (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen)))[0] := by
  have hm := hp.mem_fits
  have L8 := VG.Proof.Argon2.Arm.Derive.laneLen_ge hp
  obtain ⟨cl, cf⟩ := VG.Proof.Argon2.Arm.Derive.cell_fits hp hl (col := (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index + (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) %
    (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen) (Nat.mod_lt _ (by omega))
  unfold Impl.Argon2.Arm.Derive.dependentWord
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index + (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) %
    (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen) = c at cl cf a₁ ⊢
  have h₁ := h.of_only k₁ (by decide)
  have inP : ∀ o, o + 4 ≤ 1024 → (VG.Proof.Argon2.Arm.Derive.memR s₀).Contains (A (VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (c * 1024)) o) 4 :=
    fun o ho => by
      rw [VG.Proof.Argon2.Arm.Derive.A_shift, VG.Proof.Sha512.Arm.A_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
  have mW : ∀ t, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → VG.Proof.Argon2.Arm.Derive.memR s₀ ∈ t.wr := fun t it => by rw [it.wr]; exact VG.Proof.Argon2.Arm.Derive.mem_mem hp
  refine wp_ldr (by decide) (by rw [a₁]) ⟨_, List.mem_append_right _ (mW _ h₁.inv), inP 0 (by decide)⟩
    fun s₂ u₂ => ?_
  have h₂ := h₁.of_only (Only.of_upd u₂) (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp h₂.inv (d := j1Off) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  have h₃ := h₂.store hp i₃ (d := j1Off) (by decide) (by decide) (by decide) m₃
  refine wp_ldr (by decide) (by rw [g₃, u₂.other _ (by decide), a₁])
    ⟨_, List.mem_append_right _ (mW _ h₃.inv), inP 4 (by decide)⟩ fun s₄ u₄ => ?_
  have h₄ := h₃.of_only (Only.of_upd u₄) (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp h₄.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_⟩
  · exact h₄.store hp it (d := j2Off) (by decide) (by decide) (by decide) mt
  · rw [vt, ot j1Off (by decide) (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem u₄.mem, v₃, u₄.gpr, m₃,
      VG.Proof.Argon2.Arm.Derive.mem_loc_store hp (by decide) _ (inP 4 (by decide)), u₂.mem, u₂.gpr, k₁.mem, VG.Proof.Argon2.Arm.Derive.cell_blk hp _ cl, VG.Proof.Argon2.Arm.Derive.blk_zero,
      VG.Proof.Argon2.Arm.Derive.A_shift, VG.Proof.Argon2.Arm.Derive.A_shift, Nat.add_zero (c * 1024)]

end

/-- Regions a step of the filling loops may write without changing the filling state. -/
def Outside (s₀ : State) (r : Region) : Prop :=
  r.Disjoint (VG.Proof.Argon2.Arm.Derive.locR s₀) ∧ r.Disjoint ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 6144, 1024⟩ ∧ r.Disjoint (VG.Proof.Argon2.Arm.Derive.memR s₀)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem loc_word_sub {d : Nat} (hd : d + 4 ≤ 144) :
    Region.Sub ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), 4⟩ (VG.Proof.Argon2.Arm.Derive.locR s₀) := by
  have := VG.Proof.Argon2.Arm.Derive.E_hi hp
  exact VG.Proof.Argon2.Arm.Derive.sub32 (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (by omega)]; omega) (by rw [VG.Proof.Argon2.Arm.Derive.loc_nat hp (by omega)]; omega)

theorem FS.frame {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) (it : VG.Proof.Argon2.Arm.Derive.Inv s₀ t) {rs : List Region} (f : Frame rs s.mem t.mem)
    (ho : ∀ r ∈ rs, VG.Proof.Argon2.Arm.Derive.Outside s₀ r) : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st t := by
  refine h.keep it (fun d hd => ?_) ?_ fun k hk => ?_
  · have hd' : d + 4 ≤ 144 := by
      simp only [VG.Proof.Argon2.Arm.Derive.fsOffs, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact f.readW (r := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), 4⟩) (Region.contains_self _ _)
      (fun r hr => (ho r hr).1.symm.sub_left (VG.Proof.Argon2.Arm.Derive.loc_word_sub hp hd')) (by decide)
  · rw [VG.Proof.Argon2.Arm.Derive.scr_blk hp t.mem (by decide), VG.Proof.Argon2.Arm.Derive.scr_blk hp s.mem (by decide)]
    exact VG.Proof.Argon2.Arm.Derive.blockAt_keep f fun r hr => (ho r hr).2.1.symm
  · have hk' : k < VG.Proof.Argon2.Arm.Derive.blocksN s₀ := by rw [hp.blocks]; exact hk
    exact VG.Proof.Argon2.Arm.Derive.blockAt_keep f fun r hr => (ho r hr).2.2.symm.sub_left (VG.Proof.Argon2.Arm.Derive.cell_in_mem hk')

theorem outside_scr {o n : Nat} (h : o + n ≤ 6144 ∨ (7168 ≤ o ∧ o + n ≤ 16384)) :
    VG.Proof.Argon2.Arm.Derive.Outside s₀ ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 o, n⟩ := by
  have sub : Region.Sub ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 o, n⟩ (VG.Proof.Argon2.Arm.Derive.scrR s₀) := Offset.sub_base _ (by omega)
  refine ⟨(VG.Proof.Argon2.Arm.Derive.loc_disj' hp (R := VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp)).symm.sub_left sub, Offset.disjoint _ (by omega) (by omega)
    (by omega), hp.mem_scr.symm.sub_left sub⟩

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillInput`. -/
section

/-!
# Argon2 on ARMv7: the input of the address block

`clearAt_ok`: `clearAt d` zeroes `scratch[d, d + 1024)`. `aheader_ok`: the
seven words of the address-generation input block (§3.4.1.2), at
`scratch + 5120`. `input_ok`: after both, the block there is
`addressInput`, and the one at `scratch + 7168` is zero.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_str op2_imm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Proof.Argon2.Arm (blk ofWords blk_of_words)
open VG.Proof.Sha512.Arm (A)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff)

/-- Words of `scratch`. -/
abbrev sw (s₀ : State) (m : Mem) (o : Nat) : BitVec 32 := m.readW (A (VG.Proof.Argon2.Arm.Derive.scrP s₀) o) 32

theorem toNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- A word of `scratch` after a store to another, or the same. -/
theorem sw_store (m : Mem) {a b : Nat} (ha : a + 4 ≤ 16384) (hb : b + 4 ≤ 16384)
    (h : a = b ∨ a + 4 ≤ b ∨ b + 4 ≤ a) (v : BitVec 32) :
    VG.Proof.Argon2.Arm.Derive.sw s₀ (m.writeW (A (VG.Proof.Argon2.Arm.Derive.scrP s₀) a) v) b = if a = b then v else VG.Proof.Argon2.Arm.Derive.sw s₀ m b := by
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right e, VG.Proof.Argon2.Arm.Derive.sw, VG.Proof.Argon2.Arm.Derive.sw, A, A, VG.Proof.Argon2.Arm.Derive.scr_addr hp (by omega), VG.Proof.Argon2.Arm.Derive.scr_addr hp (by omega)]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- `n` stores of `r0 = 0` to `[r2, #4k]`, with `r2 = scratch + d`. -/
theorem zeros_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {d : Nat} (hd : d + 1024 ≤ 16384)
    (hx : s.gpr .r2 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 d) (ha : s.gpr .r0 = 0) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).map fun k => Instr.str .r0 .r2 (4 * k))) s fun t =>
      VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ t.gpr = s.gpr ∧ Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 d, 1024⟩] s.mem t.mem ∧
      ∀ i < n, VG.Proof.Argon2.Arm.Derive.sw s₀ t.mem (d + 4 * i) = 0
  | 0, _ => WP.block_nil ⟨h, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append ((VG.Proof.Argon2.Arm.Derive.zeros_ok h hd hx ha n (by omega)).mono fun t ⟨it, gt, ft, wt⟩ => ?_)
    have ea : State.addr (t.gpr .r2 + BitVec.ofNat 32 (4 * n)) = VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 (d + 4 * n) := by
      rw [gt, hx, BitVec.add_assoc, BitVec.ofNat_add_ofNat, VG.Proof.Argon2.Arm.Derive.scr_addr hp (by omega)]
    have hc : (VG.Proof.Argon2.Arm.Derive.scrR s₀).Contains (VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 (d + 4 * n)) 4 :=
      Offset.contains_base _ (by omega) (by omega)
    have hc' : (⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 d, 1024⟩ : Region).Contains (VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 (d + 4 * n)) 4 :=
      Offset.contains _ (by omega) (by omega) (by omega)
    refine wp_str (by omega) ea ⟨_, by rw [it.wr]; exact VG.Proof.Argon2.Arm.Derive.scr_mem hp, hc⟩ fun t₁ u₁ => WP.block_nil
      ⟨it.store (R := VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp) hc u₁, by rw [u₁.gpr, gt], ?_, fun i hi => ?_⟩
    · rw [u₁.mem]
      exact ft.writeW (List.mem_singleton_self _) _ hc'
    · have e : VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 (d + 4 * n) = A (VG.Proof.Argon2.Arm.Derive.scrP s₀) (d + 4 * n) := (VG.Proof.Argon2.Arm.Derive.scr_addr hp (by omega)).symm
      rw [u₁.mem, e, gt, ha, VG.Proof.Argon2.Arm.Derive.sw_store hp _ (by omega) (by omega) (by omega)]
      by_cases e : d + 4 * n = d + 4 * i
      · rw [ite_eq_left e]
      · rw [ite_eq_right e]; exact wt i (by omega)

/-- `clearAt d`: zero `scratch[d, d + 1024)`. -/
theorem clearAt_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {d : Nat} (hd : d + 1024 ≤ 16384)
    (he : encodable (BitVec.ofNat 32 d) = true) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → (∀ r, r ≠ .r0 → r ≠ .r2 → t.gpr r = s.gpr r) →
      Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 d, 1024⟩] s.mem t.mem → (∀ i < 256, VG.Proof.Argon2.Arm.Derive.sw s₀ t.mem (d + 4 * i) = 0) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.clearAt d ++ is)) s Q := by
  unfold Impl.Argon2.Arm.Derive.clearAt Impl.Argon2.Arm.Derive.scratchAt
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_add (op2_imm he) fun s₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun s₃ u₃ => ?_
  have i₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  refine WP.block_append ((VG.Proof.Argon2.Arm.Derive.zeros_ok hp i₃ hd (by rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr]) u₃.gpr 256
    (Nat.le_refl _)).mono fun t ⟨it, gt, ft, wt⟩ => k t it (fun r a b => ?_) ?_ wt)
  · rw [gt, u₃.other _ a, u₂.other _ b, u₁.other _ b]
  · rw [show s.mem = s₃.mem by rw [u₃.mem, u₂.mem, u₁.mem]]; exact ft

end

/-- The seven words of the address-generation input block. -/
def hdr (s₀ : State) (pass lane slice c : Nat) : Nat → BitVec 32
  | 0 => BitVec.ofNat 32 pass
  | 1 => BitVec.ofNat 32 lane
  | 2 => BitVec.ofNat 32 slice
  | 3 => VG.Proof.Argon2.Arm.Derive.arg s₀ 14
  | 4 => VG.Proof.Argon2.Arm.Derive.arg s₀ 5
  | 5 => VG.Proof.Argon2.Arm.Derive.arg s₀ 0
  | _ => BitVec.ofNat 32 c

/-- The words of the input block after its first `n` words are written over `m`'s. -/
def HW (s₀ : State) (m : Mem) (pass lane slice c n : Nat) (m' : Mem) : Prop :=
  ∀ i < 256, VG.Proof.Argon2.Arm.Derive.sw s₀ m' (5120 + 4 * i) =
    if i % 2 = 0 ∧ i < 2 * n then VG.Proof.Argon2.Arm.Derive.hdr s₀ pass lane slice c (i / 2) else VG.Proof.Argon2.Arm.Derive.sw s₀ m (5120 + 4 * i)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- One word of the header. -/
theorem hdr_step {m : Mem} {pass lane slice c n : Nat} (hn : n < 7) {u : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ u)
    (hx : u.gpr .r2 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 5120) (ha : u.gpr .r0 = VG.Proof.Argon2.Arm.Derive.hdr s₀ pass lane slice c n)
    (hw : VG.Proof.Argon2.Arm.Derive.HW s₀ m pass lane slice c n u.mem) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → t.gpr = u.gpr → Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] u.mem t.mem →
      VG.Proof.Argon2.Arm.Derive.HW s₀ m pass lane slice c (n + 1) t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.str .r0 .r2 (8 * n) :: is)) u Q := by
  have hs := hp.scr_fits
  have ea : State.addr (u.gpr .r2 + BitVec.ofNat 32 (8 * n)) = A (VG.Proof.Argon2.Arm.Derive.scrP s₀) (5120 + 8 * n) := by
    rw [hx, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have eb : A (VG.Proof.Argon2.Arm.Derive.scrP s₀) (5120 + 8 * n) = VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 (5120 + 8 * n) := VG.Proof.Argon2.Arm.Derive.scr_addr hp (by omega)
  have hc : (VG.Proof.Argon2.Arm.Derive.scrR s₀).Contains (A (VG.Proof.Argon2.Arm.Derive.scrP s₀) (5120 + 8 * n)) 4 := by
    rw [eb]; exact Offset.contains_base _ (by omega) (by omega)
  have hc' : (⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩ : Region).Contains (A (VG.Proof.Argon2.Arm.Derive.scrP s₀) (5120 + 8 * n)) 4 := by
    rw [eb]; exact Offset.contains _ (by omega) (by omega) (by omega)
  refine wp_str (by omega) ea ⟨_, by rw [h.wr]; exact VG.Proof.Argon2.Arm.Derive.scr_mem hp, hc⟩ fun t u₁ =>
    k t (h.store (R := VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp) hc u₁) u₁.gpr ?_ fun i hi => ?_
  · rw [u₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc'
  · rw [u₁.mem, VG.Proof.Argon2.Arm.Derive.sw_store hp _ (by omega) (by omega) (by omega), ha, hw i hi]
    by_cases e : 5120 + 8 * n = 5120 + 4 * i
    · rw [ite_eq_left e, ite_eq_left (by omega), show i / 2 = n by omega]
    · rw [ite_eq_right e]
      by_cases c₁ : i % 2 = 0 ∧ i < 2 * n
      · rw [ite_eq_left c₁, ite_eq_left (by omega)]
      · rw [ite_eq_right c₁, ite_eq_right (by omega)]

theorem aheader_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {pass slice lane index c : Nat}
    (ps : VG.Proof.Argon2.Arm.Derive.Pos s₀ s pass slice lane index) (hc : VG.Proof.Argon2.Arm.Derive.lw s₀ s counterOff = BitVec.ofNat 32 c) :
    WP isa (.block Impl.Argon2.Arm.Derive.addressHeader) s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧
      (∀ r, r ≠ .r0 → r ≠ .r2 → t.gpr r = s.gpr r) ∧
      Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.Arm.Derive.HW s₀ s.mem pass lane slice c 7 t.mem := by
  have fsub : ∀ r ∈ [(⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩ : Region)],
      ∃ r' ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  unfold Impl.Argon2.Arm.Derive.addressHeader Impl.Argon2.Arm.Derive.scratchAt
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h (i := 15) (by decide) fun s₀' u₀ => wp_add (op2_imm (by decide)) fun s₁ u₁ => ?_
  have i₁ := (h.upd u₀ (by decide)).upd u₁ (by decide)
  have x₁ : s₁.gpr .r2 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 5120 := by rw [u₁.gpr, u₀.gpr]
  have m₁ : s₁.mem = s.mem := by rw [u₁.mem, u₀.mem]
  have w₀ : VG.Proof.Argon2.Arm.Derive.HW s₀ s.mem pass lane slice c 0 s₁.mem := fun i _ => by
    rw [ite_eq_right (by omega), m₁]
  -- Word 0: the pass.
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp i₁ (d := passOff) (by decide) fun s₂ u₂ => ?_
  refine VG.Proof.Argon2.Arm.Derive.hdr_step hp (n := 0) (by decide) (i₁.upd u₂ (by decide)) (by rw [u₂.other _ (by decide), x₁])
    (by rw [u₂.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem m₁, ps.pass]; rfl) (by rw [u₂.mem]; exact w₀) fun t₂ it₂ g₂ f₂ w₂ => ?_
  -- Word 1: the lane.
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp it₂ (d := laneOff) (by decide) fun s₃ u₃ => ?_
  refine VG.Proof.Argon2.Arm.Derive.hdr_step hp (n := 1) (by decide) (it₂.upd u₃ (by decide))
    (by rw [u₃.other _ (by decide), g₂, u₂.other _ (by decide), x₁])
    (by rw [u₃.gpr, VG.Proof.Argon2.Arm.Derive.lw_keep hp f₂ fsub (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem u₂.mem, VG.Proof.Argon2.Arm.Derive.lw_mem m₁, ps.lane]; rfl)
    (by rw [u₃.mem]; exact w₂) fun t₃ it₃ g₃ f₃ w₃ => ?_
  have F₃ : Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₃.mem := by
    rw [← m₁, ← u₂.mem]; exact f₂.trans (by rw [← u₃.mem]; exact f₃)
  -- Word 2: the slice.
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp it₃ (d := sliceOff) (by decide) fun s₄ u₄ => ?_
  refine VG.Proof.Argon2.Arm.Derive.hdr_step hp (n := 2) (by decide) (it₃.upd u₄ (by decide))
    (by rw [u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂, u₂.other _ (by decide), x₁])
    (by rw [u₄.gpr, VG.Proof.Argon2.Arm.Derive.lw_keep hp F₃ fsub (by decide), ps.slice]; rfl)
    (by rw [u₄.mem]; exact w₃) fun t₄ it₄ g₄ f₄ w₄ => ?_
  have F₄ : Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₄.mem :=
    F₃.trans (by rw [← u₄.mem]; exact f₄)
  -- Words 3 to 5: the arguments.
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp it₄ (i := 14) (by decide) fun s₅ u₅ => ?_
  refine VG.Proof.Argon2.Arm.Derive.hdr_step hp (n := 3) (by decide) (it₄.upd u₅ (by decide))
    (by rw [u₅.other _ (by decide), g₄, u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂,
      u₂.other _ (by decide), x₁])
    (by rw [u₅.gpr]; rfl) (by rw [u₅.mem]; exact w₄) fun t₅ it₅ g₅ f₅ w₅ => ?_
  have F₅ : Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₅.mem :=
    F₄.trans (by rw [← u₅.mem]; exact f₅)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp it₅ (i := 5) (by decide) fun s₆ u₆ => ?_
  refine VG.Proof.Argon2.Arm.Derive.hdr_step hp (n := 4) (by decide) (it₅.upd u₆ (by decide))
    (by rw [u₆.other _ (by decide), g₅, u₅.other _ (by decide), g₄, u₄.other _ (by decide), g₃,
      u₃.other _ (by decide), g₂, u₂.other _ (by decide), x₁])
    (by rw [u₆.gpr]; rfl) (by rw [u₆.mem]; exact w₅) fun t₆ it₆ g₆ f₆ w₆ => ?_
  have F₆ : Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₆.mem :=
    F₅.trans (by rw [← u₆.mem]; exact f₆)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp it₆ (i := 0) (by decide) fun s₇ u₇ => ?_
  refine VG.Proof.Argon2.Arm.Derive.hdr_step hp (n := 5) (by decide) (it₆.upd u₇ (by decide))
    (by rw [u₇.other _ (by decide), g₆, u₆.other _ (by decide), g₅, u₅.other _ (by decide), g₄,
      u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂, u₂.other _ (by decide), x₁])
    (by rw [u₇.gpr]; rfl) (by rw [u₇.mem]; exact w₆) fun t₇ it₇ g₇ f₇ w₇ => ?_
  have F₇ : Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₇.mem :=
    F₆.trans (by rw [← u₇.mem]; exact f₇)
  -- Word 6: the counter.
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp it₇ (d := counterOff) (by decide) fun s₈ u₈ => ?_
  refine VG.Proof.Argon2.Arm.Derive.hdr_step hp (n := 6) (by decide) (it₇.upd u₈ (by decide))
    (by rw [u₈.other _ (by decide), g₇, u₇.other _ (by decide), g₆, u₆.other _ (by decide), g₅,
      u₅.other _ (by decide), g₄, u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂,
      u₂.other _ (by decide), x₁])
    (by rw [u₈.gpr, VG.Proof.Argon2.Arm.Derive.lw_keep hp F₇ fsub (by decide), hc]; rfl)
    (by rw [u₈.mem]; exact w₇) fun t it g f w => WP.block_nil ⟨it, fun r a b => ?_,
      F₇.trans (by rw [← u₈.mem]; exact f), w⟩
  rw [g, u₈.other _ a, g₇, u₇.other _ a, g₆, u₆.other _ a, g₅, u₅.other _ a, g₄, u₄.other _ a, g₃,
    u₃.other _ a, g₂, u₂.other _ a, u₁.other _ b, u₀.other _ b]

end

theorem zero_append32 (x : BitVec 32) : 0#32 ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat]
  simp
  have := x.isLt
  omega

/-- The input block's words. -/
def inWord (s₀ : State) (pass lane slice c : Nat) (i : Nat) : BitVec 32 :=
  if i % 2 = 0 ∧ i < 14 then VG.Proof.Argon2.Arm.Derive.hdr s₀ pass lane slice c (i / 2) else 0

theorem input_words {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀) {pass lane slice c : Nat} (h₁ : pass < 2 ^ 32)
    (h₂ : lane < 2 ^ 32) (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    ofWords (VG.Proof.Argon2.Arm.Derive.inWord s₀ pass lane slice c) = Proof.Argon2.addressInput (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice c := by
  have eb : (VG.Proof.Argon2.Arm.Derive.arg s₀ 14).toNat = (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks := hp.blocks
  have ep : (VG.Proof.Argon2.Arm.Derive.arg s₀ 5).toNat = (VG.Proof.Argon2.Arm.Derive.prm s₀).passes := rfl
  have ek : (VG.Proof.Argon2.Arm.Derive.arg s₀ 0).toNat = (VG.Proof.Argon2.Arm.Derive.prm s₀).variant.code := (VG.Proof.Argon2.Arm.Derive.variant_code hp.kind_le).symm
  apply Vector.ext
  intro j hj
  simp only [ofWords, Vector.getElem_ofFn, Proof.Argon2.addressInput, Vector.getElem_set, zeroBlock,
    Vector.getElem_replicate, VG.Proof.Argon2.Arm.Derive.inWord]
  rw [ite_eq_right (by omega)]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ 7 ≤ j) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | hj7
  · simp [VG.Proof.Argon2.Arm.Derive.hdr]; rw [VG.Proof.Argon2.Arm.Derive.zero_append32, VG.Proof.Argon2.Arm.Derive.toNat32 h₁]
  · simp [VG.Proof.Argon2.Arm.Derive.hdr]; rw [VG.Proof.Argon2.Arm.Derive.zero_append32, VG.Proof.Argon2.Arm.Derive.toNat32 h₂]
  · simp [VG.Proof.Argon2.Arm.Derive.hdr]; rw [VG.Proof.Argon2.Arm.Derive.zero_append32, VG.Proof.Argon2.Arm.Derive.toNat32 h₃]
  · simp [VG.Proof.Argon2.Arm.Derive.hdr]; rw [VG.Proof.Argon2.Arm.Derive.zero_append32, eb]
  · simp [VG.Proof.Argon2.Arm.Derive.hdr]; rw [VG.Proof.Argon2.Arm.Derive.zero_append32, ep]
  · simp [VG.Proof.Argon2.Arm.Derive.hdr]; rw [VG.Proof.Argon2.Arm.Derive.zero_append32, ek]
  · simp [VG.Proof.Argon2.Arm.Derive.hdr]; rw [VG.Proof.Argon2.Arm.Derive.zero_append32, VG.Proof.Argon2.Arm.Derive.toNat32 h₄]
  · rw [ite_eq_right (by omega)]
    simp (disch := omega) only [ite_eq_right]
    rfl

theorem ofWords_zero : ofWords (fun _ => 0) = zeroBlock := by
  apply Vector.ext
  intro j hj
  simp only [ofWords, Vector.getElem_ofFn, zeroBlock, Vector.getElem_replicate]
  rfl

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- A word of `scratch` outside a frame's region of `scratch`. -/
theorem sw_frame {m m' : Mem} {a n : Nat} (f : Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 a, n⟩] m m') {o : Nat}
    (h : o + 4 ≤ a ∨ a + n ≤ o) (ho : o + 4 ≤ 16384) (hn : a + n ≤ 16384) : VG.Proof.Argon2.Arm.Derive.sw s₀ m' o = VG.Proof.Argon2.Arm.Derive.sw s₀ m o := by
  rw [VG.Proof.Argon2.Arm.Derive.sw, VG.Proof.Argon2.Arm.Derive.sw, A, VG.Proof.Argon2.Arm.Derive.scr_addr hp (by omega)]
  refine f.readW (r := ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ h (by omega) (by omega)

/-- The address-generation input block at `scratch + 5120`, and a zero block at `scratch + 7168`. -/
theorem input_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {pass slice lane index c : Nat}
    (ps : VG.Proof.Argon2.Arm.Derive.Pos s₀ s pass slice lane index) (hc : VG.Proof.Argon2.Arm.Derive.lw s₀ s counterOff = BitVec.ofNat 32 c)
    (h₁ : pass < 2 ^ 32) (h₂ : lane < 2 ^ 32) (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    WP isa (.block (Impl.Argon2.Arm.Derive.clearAt 5120 ++ Impl.Argon2.Arm.Derive.clearAt 7168 ++
      Impl.Argon2.Arm.Derive.addressHeader)) s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧
      (∀ r, r ≠ .r0 → r ≠ .r2 → t.gpr r = s.gpr r) ∧
      Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩, ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 7168, 1024⟩] s.mem t.mem ∧
      blk t.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 5120 = Proof.Argon2.addressInput (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice c ∧
      blk t.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 7168 = zeroBlock := by
  have fsub : ∀ d, d + 1024 ≤ 16384 → ∀ r ∈ [(⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 d, 1024⟩ : Region)],
      ∃ r' ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀], Region.Sub r r' := fun d hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, by simp, Offset.sub_base _ hd⟩
  rw [List.append_assoc]
  refine VG.Proof.Argon2.Arm.Derive.clearAt_ok hp h (d := 5120) (by decide) (by decide) fun t₁ i₁ g₁ f₁ z₁ => ?_
  refine VG.Proof.Argon2.Arm.Derive.clearAt_ok hp i₁ (d := 7168) (by decide) (by decide) fun t₂ i₂ g₂ f₂ z₂ => ?_
  have L : ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.Arm.Derive.lw s₀ t₂ d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d := fun d hd => by
    rw [VG.Proof.Argon2.Arm.Derive.lw_keep hp f₂ (fsub _ (by decide)) hd, VG.Proof.Argon2.Arm.Derive.lw_keep hp f₁ (fsub _ (by decide)) hd]
  refine (VG.Proof.Argon2.Arm.Derive.aheader_ok hp i₂ (pass := pass) (slice := slice) (lane := lane) (index := index) (c := c)
    (ps.of_lw fun d hd => L d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide))
    (by rw [L _ (by decide)]; exact hc)).mono
    fun t ⟨it, gt, ft, wt⟩ => ⟨it, fun r a b => by rw [gt r a b, g₂ r a b, g₁ r a b], ?_, ?_, ?_⟩
  · refine (Frame.trans (f₁.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)
      (f₂.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)).trans
      (ft.sub fun r hr => ⟨⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 5120, 1024⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
  · rw [blk_of_words (f := VG.Proof.Argon2.Arm.Derive.inWord s₀ pass lane slice c) fun i hi => ?_, VG.Proof.Argon2.Arm.Derive.input_words hp h₁ h₂ h₃ h₄]
    have w := wt i hi
    simp only [VG.Proof.Argon2.Arm.Derive.sw] at w
    rw [w, VG.Proof.Argon2.Arm.Derive.inWord]
    by_cases e : i % 2 = 0 ∧ i < 2 * 7
    · rw [ite_eq_left e, ite_eq_left (by omega)]
    · rw [ite_eq_right e, ite_eq_right (by omega), ← VG.Proof.Argon2.Arm.Derive.sw, VG.Proof.Argon2.Arm.Derive.sw_frame hp f₂ (by omega) (by omega) (by decide)]
      exact z₁ i hi
  · rw [blk_of_words (f := fun _ => 0) fun i hi => ?_, VG.Proof.Argon2.Arm.Derive.ofWords_zero]
    rw [← VG.Proof.Argon2.Arm.Derive.sw, VG.Proof.Argon2.Arm.Derive.sw_frame hp ft (by omega) (by omega) (by decide)]
    exact z₂ i hi

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCache`. -/
section

/-!
# Argon2 on ARMv7: the address block and the random word

`stage_ok`: G of two blocks of `scratch` to a third. `addressCalls_ok`: the
address block for the counter, G(0, G(0, input)), at `scratch + 6144`.
`addressCache_ok`: J₁, J₂ from the cached address block, regenerated when
the index enters a new group of 128. `randomSource_ok`: J₁, J₂ are the
random word of `FillStep.random`.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_and wp_cmp wp_ldr op2_imm op2_reg op2_lsr op2_lsl)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress addressBlock)
open VG.Proof.Argon2.Arm (blk)
open VG.Proof.Sha512.Arm (Only A)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem scr_blockAt (m : Mem) {o : Nat} (ho : o + 1024 ≤ 16384) :
    blockAt m (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 o)) = blk m (VG.Proof.Argon2.Arm.Derive.scrP s₀) o := by
  have := hp.scr_fits
  rw [Proof.Argon2.Arm.blockAt_eq (by rw [VG.Proof.Argon2.Arm.Derive.add_nat (by omega)]; omega), VG.Proof.Argon2.Arm.Derive.blk_shift]

/-- `stage x y out`: G of the blocks at `scratch + x` and `scratch + y` to `scratch + out`. -/
theorem stage_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {x y o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384)
    (hx : 4096 ≤ x) (hx' : x + 1024 ≤ 16384) (hxo : x + 1024 ≤ o ∨ o + 1024 ≤ x)
    (hy : 4096 ≤ y) (hy' : y + 1024 ≤ 16384) (hyo : y + 1024 ≤ o ∨ o + 1024 ≤ y)
    (ex : encodable (BitVec.ofNat 32 x) = true) (ey : encodable (BitVec.ofNat 32 y) = true)
    (eo : encodable (BitVec.ofNat 32 o) = true) :
    WP isa (Impl.Argon2.Arm.Derive.stage x y o) s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧
      (∀ q ∈ preserved, q ≠ .lr → t.gpr q = s.gpr q) ∧
      Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀, 4096⟩] s.mem t.mem ∧
      blk t.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) o = compress (blk s.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) x) (blk s.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) y) := by
  unfold Impl.Argon2.Arm.Derive.stage
  refine WP.seq (VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_add (op2_imm ex) fun s₂ u₂ =>
    wp_add (op2_imm ey) fun s₃ u₃ => wp_add (op2_imm eo) fun s₄ u₄ => WP.block_nil ?_)
  have o₄ := (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)
  have i₄ := h.only o₄ (by decide)
  have dx : s₄.gpr .r3 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ax : s₄.gpr .r0 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 x := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]
  have sx : s₄.gpr .r1 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 y := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr]
  have cx : s₄.gpr .r2 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 o := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  refine VG.Proof.Argon2.Arm.Derive.ccall_ok hp i₄ dx ho ho' cx (by rw [ax]; exact .inr ⟨x, hx, hx', hxo, rfl⟩)
    (by rw [sx]; exact .inr ⟨y, hy, hy', hyo, rfl⟩) fun t it cs f post =>
      ⟨it, fun q hq hl => ?_, by rw [← o₄.mem]; exact f,
        by rw [post, ax, sx, VG.Proof.Argon2.Arm.Derive.scr_blockAt hp _ hx', VG.Proof.Argon2.Arm.Derive.scr_blockAt hp _ hy', o₄.mem]⟩
  rw [cs q hq hl]
  refine o₄.gpr q ?_
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A block of `scratch` at `d`, outside the regions G's call at `o` writes. -/
theorem stage_keep {m m' : Mem} {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384)
    (f : Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀, 4096⟩] m m') {d : Nat} (hd : 4096 ≤ d)
    (hd' : d + 1024 ≤ 16384) (hdo : d + 1024 ≤ o ∨ o + 1024 ≤ d) :
    blk m' (VG.Proof.Argon2.Arm.Derive.scrP s₀) d = blk m (VG.Proof.Argon2.Arm.Derive.scrP s₀) d := by
  rw [VG.Proof.Argon2.Arm.Derive.scr_blk hp m' hd', VG.Proof.Argon2.Arm.Derive.scr_blk hp m hd']
  refine VG.Proof.Argon2.Arm.Derive.blockAt_keep f fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ hdo (by omega) (by omega)
  · exact Offset.disjoint_base _ hd (by omega)

omit hp in
theorem stage_frame {m m' : Mem} {o : Nat} (ho' : o + 1024 ≤ 16384)
    (f : Frame [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀, 4096⟩] m m') :
    Frame [VG.Proof.Argon2.Arm.Derive.scrR s₀] m m' :=
  f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, by simp, Offset.sub_base _ ho'⟩
    · exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, by simp, Region.sub_prefix (by decide)⟩

/-- `addressCalls`: the address block for the counter `c` at `scratch + 6144`. -/
theorem addressCalls_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {pass slice lane index c : Nat}
    (ps : VG.Proof.Argon2.Arm.Derive.Pos s₀ s pass slice lane index) (hc : VG.Proof.Argon2.Arm.Derive.lw s₀ s counterOff = BitVec.ofNat 32 c)
    (h₁ : pass < 2 ^ 32) (h₂ : lane < 2 ^ 32) (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    WP isa Impl.Argon2.Arm.Derive.addressCalls s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧
      (∀ q ∈ preserved, q ≠ .lr → t.gpr q = s.gpr q) ∧ Frame [VG.Proof.Argon2.Arm.Derive.scrR s₀] s.mem t.mem ∧
      blk t.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 6144 = addressBlock (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice c := by
  unfold Impl.Argon2.Arm.Derive.addressCalls
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.input_ok hp h ps hc h₁ h₂ h₃ h₄).mono fun t₁ ⟨i₁, g₁, f₁, b₁, z₁⟩ => ?_)
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.stage_ok hp i₁ (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono
    fun t₂ ⟨i₂, g₂, f₂, b₂⟩ => ?_)
  refine (VG.Proof.Argon2.Arm.Derive.stage_ok hp i₂ (x := 7168) (y := 4096) (o := 6144) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono
    fun t ⟨it, gt, ft, bt⟩ => ⟨it, fun q hq hl => ?_, ?_, ?_⟩
  · rw [gt q hq hl, g₂ q hq hl]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact g₁ _ (by decide) (by decide) | exact absurd rfl hl
  · refine Frame.trans (f₁.sub fun r hr => ?_) ((VG.Proof.Argon2.Arm.Derive.stage_frame (by decide) f₂).trans (VG.Proof.Argon2.Arm.Derive.stage_frame (by decide) ft))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  · rw [bt, VG.Proof.Argon2.Arm.Derive.stage_keep hp (by decide) (by decide) f₂ (d := 7168) (by decide) (by decide) (by decide), b₂, z₁, b₁]
    rfl

end

theorem and127 {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n &&& 127 = BitVec.ofNat 32 (n % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, VG.Proof.Argon2.Arm.Derive.toNat32 h, VG.Proof.Argon2.Arm.Derive.toNat32 (by omega),
    show (127 : BitVec 32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem shr7 {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 7 = BitVec.ofNat 32 (n / 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, VG.Proof.Argon2.Arm.Derive.toNat32 h, VG.Proof.Argon2.Arm.Derive.toNat32 (by omega), Nat.shiftRight_eq_div_pow]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- `cacheWord`: J₁ and J₂ are word `index mod 128` of the cached address block. -/
theorem cacheWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) (hi : index < 2 ^ 30) :
    WP isa (.block Impl.Argon2.Arm.Derive.cacheWord) s fun t => VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st t ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀ t j2Off ++ VG.Proof.Argon2.Arm.Derive.lw s₀ t j1Off = (blk s.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 6144)[index % 128]'(Nat.mod_lt _ (by decide)) := by
  have hs := hp.scr_fits
  have e8 : 8 * (index % 128) < 1024 := by omega
  unfold Impl.Argon2.Arm.Derive.cacheWord
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_and (op2_imm (by decide)) fun s₂ u₂ => ?_
  have o₂ := (Only.of_upd u₁).trans (Only.of_upd u₂)
  have h₂ := h.of_only o₂ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h₂.inv (i := 15) (by decide) fun s₃ u₃ => wp_add (op2_lsl (by decide)) fun s₄ u₄ =>
    wp_add (op2_imm (by decide)) fun s₅ u₅ => ?_
  have h₅ := h₂.of_only (((Only.of_upd u₃).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)) (by decide)
  have a₅ : s₅.gpr .r0 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 (6144 + 8 * (index % 128)) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, h.pos.index,
      VG.Proof.Argon2.Arm.Derive.and127 (by omega), VG.Proof.Argon2.Arm.Derive.ofNat_shl (by omega), show (6144 : BitVec 32) = BitVec.ofNat 32 6144 from rfl,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; omega
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, o₂.mem]
  have inS : ∀ t : State, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → ∀ o, o + 4 ≤ 1024 →
      InRegions (t.rd ++ t.wr) (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 (6144 + 8 * (index % 128) + o))) 4 :=
    fun t it o ho => by
      rw [VG.Proof.Argon2.Arm.Derive.scr_addr hp (by omega), it.wr]
      exact ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, List.mem_append_right _ (VG.Proof.Argon2.Arm.Derive.scr_mem hp), Offset.contains_base _ (by omega) (by omega)⟩
  have ad : ∀ o, State.addr (s₅.gpr .r0 + BitVec.ofNat 32 o) =
      State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 (6144 + 8 * (index % 128) + o)) :=
    fun o => by rw [a₅, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine wp_ldr (by decide) (ad 0) (inS _ h₅.inv 0 (by decide)) fun s₆ u₆ => ?_
  have h₆ := h₅.of_only (Only.of_upd u₆) (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp h₆.inv (d := j1Off) (by decide) fun s₇ i₇ v₇ o₇ g₇ m₇ => ?_
  have h₇ := h₆.store hp i₇ (d := j1Off) (by decide) (by decide) (by decide) m₇
  refine wp_ldr (by decide) (by rw [g₇, u₆.other _ (by decide)]; exact ad 4) (inS _ h₇.inv 4 (by decide))
    fun s₈ u₈ => ?_
  have h₈ := h₇.of_only (Only.of_upd u₈) (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp h₈.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_⟩
  · exact h₈.store hp it (d := j2Off) (by decide) (by decide) (by decide) mt
  · rw [vt, ot j1Off (by decide) (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem u₈.mem, v₇, u₈.gpr, m₇,
      VG.Proof.Argon2.Arm.Derive.scr_addr hp (o := 6144 + 8 * (index % 128) + 4) (by omega), VG.Proof.Argon2.Arm.Derive.scr_loc hp (by decide) (by omega),
      ← VG.Proof.Argon2.Arm.Derive.scr_addr hp (by omega), u₆.gpr, u₆.mem, m₅, VG.Proof.Argon2.Arm.Derive.blk_get _ _ _ _ (Nat.mod_lt _ (by decide)),
      Nat.add_zero (6144 + 8 * (index % 128))]

omit hp in
/-- The cached address block is that of `c`. -/
theorem cached {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 32)
    (he : VG.Proof.Argon2.Arm.Derive.lw s₀ s counterOff = BitVec.ofNat 32 c) :
    blk s.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 6144 = addressBlock (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice c := by
  obtain ⟨c0, c1, c2 | ⟨_, c4⟩⟩ := h.cache
  · rw [he, c2] at c1
    have := congrArg BitVec.toNat c1
    rw [VG.Proof.Argon2.Arm.Derive.toNat32 hc'] at this
    exact absurd this (by simp; omega)
  · rw [c4]
    rw [he] at c1
    have := congrArg BitVec.toNat c1
    rw [VG.Proof.Argon2.Arm.Derive.toNat32 hc', VG.Proof.Argon2.Arm.Derive.toNat32 c0] at this
    rw [this]

/-- `cacheCheck`: `r0 :=` the counter of the index's group; Z if it is cached. -/
theorem cacheCheck_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen) :
    WP isa (.block Impl.Argon2.Arm.Derive.cacheCheck) s fun t => VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st t ∧
      t.gpr .r0 = BitVec.ofNat 32 (index / 128 + 1) ∧
      VG.Arm.eval .eq t = some (BitVec.ofNat 32 (index / 128 + 1) - VG.Proof.Argon2.Arm.Derive.lw s₀ t counterOff == 0) := by
  have sl := VG.Proof.Argon2.Arm.Derive.segLen_lt hp
  unfold Impl.Argon2.Arm.Derive.cacheCheck
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => ?_
  have o₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  have h₃ := h.of_only o₃ (by decide)
  have a₃ : s₃.gpr .r0 = BitVec.ofNat 32 (index / 128 + 1) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, h.pos.index, VG.Proof.Argon2.Arm.Derive.shr7 (by omega), show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_add_ofNat]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₃.inv (d := counterOff) (by decide) fun s₄ u₄ =>
    wp_cmp (op2_reg _ _) fun t f z => WP.block_nil ?_
  have o₄ := (Only.of_upd u₄).trans (Only.of_fupd f)
  refine ⟨h₃.of_only o₄ (by decide), by rw [o₄.gpr _ (by decide), a₃], ?_⟩
  rw [MdStream.Arm.eval_eq, z, u₄.other _ (by decide), a₃, u₄.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem f.mem, VG.Proof.Argon2.Arm.Derive.lw_mem u₄.mem]

/-- The address block of the index's group, regenerated unless it is cached. -/
theorem cacheFill_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h₄ : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hs : slice < 4)
    (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen) (a₃ : s.gpr .r0 = BitVec.ofNat 32 (index / 128 + 1))
    (z₄ : VG.Arm.eval .eq s = some (BitVec.ofNat 32 (index / 128 + 1) - VG.Proof.Argon2.Arm.Derive.lw s₀ s counterOff == 0)) :
    WP isa (.ite .eq (.block []) (.seq (.block [Impl.Argon2.Arm.Derive.st counterOff .r0])
      Impl.Argon2.Arm.Derive.addressCalls)) s fun t => VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      blk t.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 6144 = addressBlock (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice (index / 128 + 1) := by
  have sl := VG.Proof.Argon2.Arm.Derive.segLen_lt hp
  have hlt := hp.lanes_lt
  refine WP.ite (BitVec.ofNat 32 (index / 128 + 1) - VG.Proof.Argon2.Arm.Derive.lw s₀ s counterOff == 0) z₄
    (fun hb => ?_) fun hb => ?_
  · have ce : VG.Proof.Argon2.Arm.Derive.lw s₀ s counterOff = BitVec.ofNat 32 (index / 128 + 1) := by
      have e := beq_iff_eq.mp hb
      exact ((BitVec.sub_eq_iff_eq_add.mp e).trans (by simp)).symm
    have cb := VG.Proof.Argon2.Arm.Derive.cached h₄ (c := index / 128 + 1) (by omega) (by omega) ce
    exact WP.block_nil ⟨⟨h₄.inv, h₄.pr, h₄.pos, ⟨by omega, ce, .inr ⟨by omega, cb⟩⟩, h₄.mem⟩, cb⟩
  · refine WP.seq (VG.Proof.Argon2.Arm.Derive.wp_stloc hp h₄.inv (d := counterOff) (by decide) fun s₅ i₅ v₅ o₅ g₅ m₅ => WP.block_nil ?_)
    have L₅ : ∀ d ∈ VG.Proof.Argon2.Arm.Derive.fsOffs, d ≠ counterOff → VG.Proof.Argon2.Arm.Derive.lw s₀ s₅ d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d := fun d hd hd' => by
      simp only [VG.Proof.Argon2.Arm.Derive.fsOffs, List.mem_cons, List.not_mem_nil, or_false] at hd
      refine o₅ d ?_ ?_ <;>
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | exact absurd rfl hd'
    refine (VG.Proof.Argon2.Arm.Derive.addressCalls_ok hp i₅ (index := index) (c := index / 128 + 1)
      (h₄.pos.of_lw fun d hd => L₅ d (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl <;> decide))
      (by rw [v₅, a₃]) hpass (by omega) (by omega) (by omega)).mono
      fun t ⟨it, _, ft, bt⟩ => ⟨?_, bt⟩
    have fsub : ∀ r ∈ [VG.Proof.Argon2.Arm.Derive.scrR s₀], ∃ r' ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀, VG.Proof.Argon2.Arm.Derive.callR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
    have Lt : ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s₅ d := fun d hd => VG.Proof.Argon2.Arm.Derive.lw_keep hp ft fsub hd
    refine ⟨it, Prm.of_lw h₄.pr fun d hd => ?_, h₄.pos.of_lw fun d hd => ?_, ⟨by omega,
      by rw [Lt _ (by decide), v₅, a₃], .inr ⟨by omega, bt⟩⟩, Represents.keep h₄.mem fun k hk => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [Lt d (by rcases hd with rfl | rfl | rfl | rfl <;> decide)]
      exact L₅ d (by simp only [VG.Proof.Argon2.Arm.Derive.fsOffs]; rcases hd with rfl | rfl | rfl | rfl <;> simp)
        (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [Lt d (by rcases hd with rfl | rfl | rfl | rfl <;> decide)]
      exact L₅ d (by simp only [VG.Proof.Argon2.Arm.Derive.fsOffs]; rcases hd with rfl | rfl | rfl | rfl <;> simp)
        (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
    · have hk' : k < VG.Proof.Argon2.Arm.Derive.blocksN s₀ := by rw [hp.blocks]; exact hk
      rw [VG.Proof.Argon2.Arm.Derive.blockAt_keep ft fun r hr => ?_, m₅, VG.Proof.Argon2.Arm.Derive.blockAt_keep (rs := [⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 counterOff), 4⟩])
        ((Frame.refl _ _).writeW (w := 32) (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => ?_]
      · simp only [List.mem_singleton] at hr; subst hr
        exact (VG.Proof.Argon2.Arm.Derive.loc_disj hp (d := counterOff) (by decide) (VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).symm.sub_left (VG.Proof.Argon2.Arm.Derive.cell_in_mem hk')
      · simp only [List.mem_singleton] at hr; subst hr
        exact hp.mem_scr.sub_left (VG.Proof.Argon2.Arm.Derive.cell_in_mem hk')

/-- `addressCache`: J₁ and J₂ from the address block of the index's group of 128. -/
theorem addressCache_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hs : slice < 4)
    (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen) :
    WP isa Impl.Argon2.Arm.Derive.addressCache s fun t => VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀ t j2Off ++ VG.Proof.Argon2.Arm.Derive.lw s₀ t j1Off =
        (addressBlock (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice (index / 128 + 1))[index % 128]'(Nat.mod_lt _ (by decide)) := by
  have sl := VG.Proof.Argon2.Arm.Derive.segLen_lt hp
  unfold Impl.Argon2.Arm.Derive.addressCache
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.cacheCheck_ok hp h hi).mono fun s₄ ⟨h₄, a₄, z₄⟩ => ?_)
  have M := VG.Proof.Argon2.Arm.Derive.cacheFill_ok hp h₄ hpass hl hs hi a₄ z₄
  refine WP.seq (M.mono fun t ⟨ht, bt⟩ => (VG.Proof.Argon2.Arm.Derive.cacheWord_ok hp ht (by omega)).mono fun u ⟨hu, wu⟩ => ⟨hu, ?_⟩)
  rw [wu, bt]

/-- `randomSource`: J₁ and J₂ are the step's random word. -/
theorem randomSource_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hs : slice < 4)
    (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen) :
    WP isa Impl.Argon2.Arm.Derive.randomSource s fun t =>
      VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index (VG.Proof.Argon2.Arm.Derive.ctrNext (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice index ctr) st t ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀ t j2Off ++ VG.Proof.Argon2.Arm.Derive.lw s₀ t j1Off = Proof.Argon2.FillStep.random (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice index st.memory := by
  unfold Impl.Argon2.Arm.Derive.randomSource
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.addressMode_ok hp h.inv h.pos hpass hs).mono fun s₁ ⟨z₁, k₁⟩ => ?_)
  have h₁ := h.of_only k₁ (by decide)
  refine WP.ite (!Spec.Argon2.independent (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice) z₁ (fun hb => ?_) fun hb => ?_
  · have hind : Spec.Argon2.independent (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice = false := by simpa using hb
    refine (VG.Proof.Argon2.Arm.Derive.dependentWord_ok hp h₁ hl hs hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [VG.Proof.Argon2.Arm.Derive.ctrNext, hind]; exact ht, ?_⟩
    have cl := Proof.Argon2.previous_cell_lt (VG.Proof.Argon2.Arm.Derive.prm s₀) hp.lanes_pos hp.memory_ge
      (column := slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index) hl
    rw [wt, k₁.mem, h.mem.block _ cl]
    unfold Proof.Argon2.FillStep.random
    rw [hind]
    rfl
  · have hind : Spec.Argon2.independent (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice = true := by simpa using hb
    refine (VG.Proof.Argon2.Arm.Derive.addressCache_ok hp h₁ hpass hl hs hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [VG.Proof.Argon2.Arm.Derive.ctrNext, hind]; exact ht, ?_⟩
    rw [wt]
    unfold Proof.Argon2.FillStep.random
    rw [hind]
    rfl

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillRef`. -/
section

/-!
# Argon2 on ARMv7: the reference block's lane, start and base

`RS`: the filling state with J₁ and J₂ in the locals. `refLane_ok`: the
reference lane (RFC 9106 §3.4.2); `refStart_ok`: where the window of
eligible blocks starts; `countBase_ok`: the blocks before the current
segment that a reference may use.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_orr wp_cmp op2_imm op2_reg)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Proof.Sha512.Arm (Only)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

/-- The filling state, with J₁ and J₂ in the locals. -/
structure RS (s₀ : State) (pass slice lane index ctr : Nat) (st : FillState) (J1 J2 : BitVec 32) (s : State) :
    Prop where
  fs : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s
  j1 : VG.Proof.Argon2.Arm.Derive.lw s₀ s j1Off = J1
  j2 : VG.Proof.Argon2.Arm.Derive.lw s₀ s j2Off = J2

theorem RS.of_only {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) {ds : List Reg} (o : Only ds s t) (h11 : Reg.r11 ∉ ds) :
    VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 t :=
  ⟨h.fs.of_only o h11, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem o.mem]; exact h.j1, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem o.mem]; exact h.j2⟩

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
    rw [BitVec.toNat_or, VG.Proof.Argon2.Arm.Derive.toNat32 ha, VG.Proof.Argon2.Arm.Derive.toNat32 hb] at this
    simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

theorem sub_zero32 (y : BitVec 32) : y - 0 = y := by simp

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem RS.store {s t : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (it : VG.Proof.Argon2.Arm.Derive.Inv s₀ t) {d : Nat} (hd : d + 4 ≤ 144) (ha : d % 4 = 0)
    (hd' : d ∉ VG.Proof.Argon2.Arm.Derive.fsOffs) (h1 : d ≠ j1Off) (h2 : d ≠ j2Off) {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) v) :
    VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 t := by
  refine ⟨h.fs.store hp it hd hd' ha hm, ?_, ?_⟩
  · show t.mem.readW _ 32 = _
    rw [hm, VG.Proof.Argon2.Arm.Derive.lw_store hp (by omega) (by decide) (by simp [j1Off] at h1 ⊢; omega)]; exact h.j1
  · show t.mem.readW _ 32 = _
    rw [hm, VG.Proof.Argon2.Arm.Derive.lw_store hp (by omega) (by decide) (by simp [j2Off] at h2 ⊢; omega)]; exact h.j2

/-- The block of `refLane`: J₂ mod lanes, to the locals, and Z in the first
slice of the first pass. -/
theorem refLaneBlk_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block ([Impl.Argon2.Arm.Derive.ld .r1 j2Off, Impl.Argon2.Arm.Derive.ld .r2 (argOff 7)] ++
      Impl.Argon2.Arm.Divide.code ++
      [Impl.Argon2.Arm.Derive.st refLaneOff .r0, Impl.Argon2.Arm.Derive.ld .r0 passOff,
        Impl.Argon2.Arm.Derive.ld .r1 sliceOff, .dp .orr .r0 .r0 (.reg .r1), .cmp .r0 (.imm 0)])) s fun t =>
      VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 t ∧ VG.Arm.eval .eq t = some (decide (pass = 0 ∧ slice = 0)) ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀ t refLaneOff = BitVec.ofNat 32 (J2.toNat % VG.Proof.Argon2.Arm.Derive.lanesN s₀) := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  have e7 : VG.Proof.Argon2.Arm.Derive.lanesN s₀ = (VG.Proof.Argon2.Arm.Derive.arg s₀ 7).toNat := rfl
  rw [List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h.fs.inv (d := j2Off) (by decide) fun s₁ u₁ =>
    VG.Proof.Argon2.Arm.Derive.wp_ldarg hp (h.fs.inv.upd u₁ (by decide)) (i := 7) (by decide) fun s₂ u₂ => ?_
  have h₂ := h.of_only ((Only.of_upd u₁).trans (Only.of_upd u₂)) (by decide)
  refine Divide.code_ok (D := VG.Proof.Argon2.Arm.Derive.arg s₀ 7) (by omega) (by omega) u₂.gpr fun s₃ _ r₃ k₃ => ?_
  have h₃ := h₂.of_only (Divide.Keep.only k₃) (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp h₃.fs.inv (d := refLaneOff) (by decide) fun s₄ i₄ v₄ _ g₄ m₄ => ?_
  have h₄ := h₃.store hp i₄ (d := refLaneOff) (by decide) (by decide) (by decide) (by decide) (by decide) m₄
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₄.fs.inv (d := passOff) (by decide) fun s₅ u₅ => ?_
  have h₅ := h₄.of_only (Only.of_upd u₅) (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₅.fs.inv (d := sliceOff) (by decide) fun s₆ u₆ => wp_orr (op2_reg _ _) fun s₇ u₇ =>
    wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ?_
  have h₇ := h₅.of_only (((Only.of_upd u₆).trans (Only.of_upd u₇)).trans (Only.of_fupd f)) (by decide)
  have r : s₃.gpr .r0 = BitVec.ofNat 32 (J2.toNat % VG.Proof.Argon2.Arm.Derive.lanesN s₀) := BitVec.eq_of_toNat_eq (by
    rw [r₃, u₂.other _ (by decide), u₁.gpr, h.j2, VG.Proof.Argon2.Arm.Derive.toNat32 (by have := J2.isLt; have := Nat.mod_le J2.toNat (VG.Proof.Argon2.Arm.Derive.lanesN s₀); omega)])
  refine ⟨h₇, ?_, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem f.mem, VG.Proof.Argon2.Arm.Derive.lw_mem u₇.mem, VG.Proof.Argon2.Arm.Derive.lw_mem u₆.mem, VG.Proof.Argon2.Arm.Derive.lw_mem u₅.mem, v₄, r]⟩
  rw [MdStream.Arm.eval_eq, z, u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₆.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₅.mem, h₄.fs.pos.slice,
    h₄.fs.pos.pass, VG.Proof.Argon2.Arm.Derive.sub_zero32, VG.Proof.Argon2.Arm.Derive.or_zero hpass (by omega)]

/-- `refLane`: the reference lane, to the locals. -/
theorem refLane_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.Arm.Derive.refLane s fun t => VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 t ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀ t refLaneOff = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.refLaneV (VG.Proof.Argon2.Arm.Derive.lanesN s₀) pass slice lane J2.toNat) := by
  unfold Impl.Argon2.Arm.Derive.refLane
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.refLaneBlk_ok hp h hpass hs).mono fun s₅ ⟨h₅, z₅, e₃⟩ => ?_)
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) z₅ (fun hb => ?_) fun hb => ?_
  · have hb' : pass = 0 ∧ slice = 0 := of_decide_eq_true hb
    refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₅.fs.inv (d := laneOff) (by decide) fun s₆ u₆ => ?_
    have h₆ := h₅.of_only (Only.of_upd u₆) (by decide)
    refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp h₆.fs.inv (d := refLaneOff) (by decide) fun t it vt _ _ mt => WP.block_nil ⟨?_, ?_⟩
    · exact h₆.store hp it (d := refLaneOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt
    · rw [vt, u₆.gpr, h₅.fs.pos.lane, VG.Proof.Argon2.Arm.Derive.refLaneV, ite_eq_left hb']
  · have hb' : ¬(pass = 0 ∧ slice = 0) := of_decide_eq_false hb
    refine WP.block_nil ⟨h₅, ?_⟩
    rw [e₃, VG.Proof.Argon2.Arm.Derive.refLaneV, ite_eq_right hb']

/-- `refStart`: where the window starts, to the locals. -/
theorem refStart_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.Arm.Derive.refStart s fun t => VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 t ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀ t refLaneOff = VG.Proof.Argon2.Arm.Derive.lw s₀ s refLaneOff ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀ t startOff = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.startV (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen pass slice) := by
  have sl := VG.Proof.Argon2.Arm.Derive.segLen_lt hp
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  unfold Impl.Argon2.Arm.Derive.refStart
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_)
  have h₁ := h.of_only (Only.of_upd u₁) (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp h₁.fs.inv (d := startOff) (by decide) fun s₂ i₂ v₂ o₂ _ m₂ => ?_
  have h₂ := h₁.store hp i₂ (d := startOff) (by decide) (by decide) (by decide) (by decide) (by decide) m₂
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₂.fs.inv (d := passOff) (by decide) fun s₃ u₃ =>
    wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_
  have h₄ := h₂.of_only ((Only.of_upd u₃).trans (Only.of_fupd f₄)) (by decide)
  have m₄ : s₄.mem = s₂.mem := by rw [f₄.mem, u₃.mem]
  have r₂ : VG.Proof.Argon2.Arm.Derive.lw s₀ s₂ refLaneOff = VG.Proof.Argon2.Arm.Derive.lw s₀ s refLaneOff := by
    rw [o₂ _ (by decide) (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem]
  refine WP.ite (decide (pass = 0)) (by
    show VG.Arm.eval .eq _ = _
    rw [MdStream.Arm.eval_eq, z₄, u₃.gpr, h₂.fs.pos.pass, VG.Proof.Argon2.Arm.Derive.sub_zero32, MdStream.Arm.ofNat_beq_zero hpass])
    (fun hb => ?_) fun hb => ?_
  · refine WP.block_nil ⟨h₄, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem m₄, r₂], ?_⟩
    rw [VG.Proof.Argon2.Arm.Derive.lw_mem m₄, v₂, u₁.gpr, VG.Proof.Argon2.Arm.Derive.startV, ite_eq_left (of_decide_eq_true hb)]; rfl
  · have hp0 : pass ≠ 0 := of_decide_eq_false hb
    refine WP.seq (VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₄.fs.inv (d := sliceOff) (by decide) fun s₅ u₅ =>
      wp_cmp (op2_imm (by decide)) fun s₆ f₆ z₆ => WP.block_nil ?_)
    have h₆ := h₄.of_only ((Only.of_upd u₅).trans (Only.of_fupd f₆)) (by decide)
    have m₆ : s₆.mem = s₂.mem := by rw [f₆.mem, u₅.mem, m₄]
    refine WP.ite (decide (slice = 3)) (by
      show VG.Arm.eval .eq _ = _
      rw [MdStream.Arm.eval_eq, z₆, u₅.gpr, h₄.fs.pos.slice, show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl,
        MdStream.Arm.sub_beq (by omega) (by decide)]) (fun hb' => ?_) fun hb' => ?_
    · refine WP.block_nil ⟨h₆, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem m₆, r₂], ?_⟩
      rw [VG.Proof.Argon2.Arm.Derive.lw_mem m₆, v₂, u₁.gpr, VG.Proof.Argon2.Arm.Derive.startV, ite_eq_right hp0, of_decide_eq_true hb', ll, Nat.mod_self]; rfl
    · have hs3 : slice ≠ 3 := of_decide_eq_false hb'
      refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₆.fs.inv (d := sliceOff) (by decide) fun s₇ u₇ => wp_add (op2_imm (by decide))
        fun s₈ u₈ => ?_
      have h₈ := h₆.of_only ((Only.of_upd u₇).trans (Only.of_upd u₈)) (by decide)
      refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₈.fs.inv (d := segLenOff) (by decide) fun s₉ u₉ => wp_mul fun s₁₀ u₁₀ => ?_
      have h₁₀ := h₈.of_only ((Only.of_upd u₉).trans (Only.of_upd u₁₀)) (by decide)
      have m₁₀ : s₁₀.mem = s₂.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆]
      refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp h₁₀.fs.inv (d := startOff) (by decide) fun t it vt ot _ mt => WP.block_nil ⟨?_, ?_, ?_⟩
      · exact h₁₀.store hp it (d := startOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt
      · rw [ot _ (by decide) (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem m₁₀, r₂]
      · have : (slice + 1) * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen < (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen := by
          rw [ll]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        rw [vt, u₁₀.gpr, u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₉.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₈.mem, VG.Proof.Argon2.Arm.Derive.lw_mem u₇.mem,
          h₆.fs.pr.segLen, VG.Proof.Argon2.Arm.Derive.lw_mem (show s₆.mem = s₂.mem from m₆), h₂.fs.pos.slice,
          show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat, VG.Proof.Argon2.Arm.Derive.ofNat_mul_ofNat,
          VG.Proof.Argon2.Arm.Derive.startV, ite_eq_right hp0, Nat.mod_eq_of_lt this]

/-- `countBase`: `r0 :=` the blocks before the current segment that a reference may use. -/
theorem countBase_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) :
    WP isa Impl.Argon2.Arm.Derive.countBase s fun t => Only [.r0, .r1, .r2] s t ∧
      t.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.baseV (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen pass slice) := by
  have sl := VG.Proof.Argon2.Arm.Derive.segLen_lt hp
  have ll := hp.laneLen_eq
  unfold Impl.Argon2.Arm.Derive.countBase
  refine WP.seq (VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h.fs.inv (d := passOff) (by decide) fun s₁ u₁ =>
    wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ => WP.block_nil ?_)
  have k₂ := (Only.of_upd u₁).trans (Only.of_fupd f₂)
  have h₂ := h.of_only k₂ (by decide)
  refine WP.ite (decide (pass = 0)) (by
    show VG.Arm.eval .eq _ = _
    rw [MdStream.Arm.eval_eq, z₂, u₁.gpr, h.fs.pos.pass, VG.Proof.Argon2.Arm.Derive.sub_zero32, MdStream.Arm.ofNat_beq_zero hpass])
    (fun hb => ?_) fun hb => ?_
  · refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₂.fs.inv (d := sliceOff) (by decide) fun s₃ u₃ =>
      VG.Proof.Argon2.Arm.Derive.wp_ldloc hp (h₂.of_only (Only.of_upd u₃) (by decide)).fs.inv (d := segLenOff) (by decide) fun s₄ u₄ =>
      wp_mul fun t u => WP.block_nil ⟨(((k₂.trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans
        (Only.of_upd u)).mono (by simp), ?_⟩
    rw [u.gpr, u₄.other _ (by decide), u₃.gpr, u₄.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₃.mem, h₂.fs.pos.slice, h₂.fs.pr.segLen,
      VG.Proof.Argon2.Arm.Derive.ofNat_mul_ofNat, VG.Proof.Argon2.Arm.Derive.baseV, ite_eq_left (of_decide_eq_true hb)]
  · refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₂.fs.inv (d := laneLenOff) (by decide) fun s₃ u₃ =>
      VG.Proof.Argon2.Arm.Derive.wp_ldloc hp (h₂.of_only (Only.of_upd u₃) (by decide)).fs.inv (d := segLenOff) (by decide) fun s₄ u₄ =>
      wp_sub (op2_reg _ _) fun t u => WP.block_nil ⟨(((k₂.trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans
        (Only.of_upd u)).mono (by simp), ?_⟩
    rw [u.gpr, u₄.other _ (by decide), u₃.gpr, u₄.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₃.mem, h₂.fs.pr.laneLen, h₂.fs.pr.segLen,
      MdStream.Arm.sub_ofNat (by omega), VG.Proof.Argon2.Arm.Derive.baseV, ite_eq_right (of_decide_eq_false hb)]

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCount`. -/
section

/-!
# Argon2 on ARMv7: the reference window's size

`countSelect_ok`: the number of eligible reference blocks, chosen between
the current lane's and another lane's by a mask (`sel`), to the locals.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_orr wp_and op2_imm op2_reg op2_lsr)
open VG.Proof.Blake2.Arm.Stream (wp_eor)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Proof.Sha512.Arm (Only)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

/-- A register after an update, as an `if` on the register. -/
theorem upd_get {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v) (r : Reg) :
    t.gpr r = if r = d then v else s.gpr r := by
  by_cases h : r = d
  · subst h; rw [ite_eq_left rfl, u.gpr]
  · rw [ite_eq_right h, u.other r h]

theorem sel (a c : BitVec 32) (p : Prop) [Decidable p] :
    a ^^^ ((c ^^^ a) &&& (if p then BitVec.allOnes 32 else 0)) = if p then c else a := by
  by_cases hp : p
  · simp only [hp, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm c a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp [hp]

theorem mask_sub (p : Prop) [Decidable p] {x : BitVec 32} (hx : x = 1) :
    (if p then (0 : BitVec 32) else 1) - x = if p then BitVec.allOnes 32 else 0 := by
  subst hx
  by_cases hp : p <;> simp only [hp, ite_true, ite_false] <;> decide

theorem add_allOnes {x : Nat} (h : 1 ≤ x) (h' : x < 2 ^ 32) :
    BitVec.ofNat 32 x + BitVec.allOnes 32 = BitVec.ofNat 32 (x - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, VG.Proof.Argon2.Arm.Derive.toNat32 h', VG.Proof.Argon2.Arm.Derive.toNat32 (by omega), BitVec.toNat_allOnes]
  omega

theorem ofNat_eq_zero {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n = 0 ↔ n = 0 := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; rwa [VG.Proof.Argon2.Arm.Derive.toNat32 h] at this
  · rintro rfl; rfl

theorem xor_eq_zero {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b = 0 ↔ a = b := by
  constructor
  · intro e
    have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp e)
    rwa [VG.Proof.Argon2.Arm.Derive.toNat32 ha, VG.Proof.Argon2.Arm.Derive.toNat32 hb] at this
  · rintro rfl; simp

theorem ofNat_pred {n : Nat} (h : 1 ≤ n) {x : BitVec 32} (hx : x = 1) :
    BitVec.ofNat 32 n - x = BitVec.ofNat 32 (n - 1) := by
  rw [hx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.Arm.sub_ofNat h]

/-- The window's size. -/
def countV (base index : Nat) (same : Bool) : Nat :=
  if same then base + index - 1 else base - (if index = 0 then 1 else 0)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- `countSelect`: the window's size, to the locals and `r0`. -/
theorem countSelect_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) {base rl : Nat} (hb : base < 2 ^ 31)
    (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen) (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hrl : rl < VG.Proof.Argon2.Arm.Derive.lanesN s₀)
    (ha : s.gpr .r0 = BitVec.ofNat 32 base) (hr : VG.Proof.Argon2.Arm.Derive.lw s₀ s refLaneOff = BitVec.ofNat 32 rl)
    (hsame : rl = lane → 1 ≤ base + index) (hother : rl ≠ lane → index = 0 → 1 ≤ base)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 t →
      t.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.countV base index (rl == lane)) →
      VG.Proof.Argon2.Arm.Derive.lw s₀ t countOff = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.countV base index (rl == lane)) →
      (∀ e, e + 4 ≤ 256 → (countOff + 4 ≤ e ∨ e + 4 ≤ countOff) → VG.Proof.Argon2.Arm.Derive.lw s₀ t e = VG.Proof.Argon2.Arm.Derive.lw s₀ s e) →
      (∀ r ∉ [Reg.r0, .r1, .r2, .r3], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.countSelect ++ is)) s Q := by
  have sl := VG.Proof.Argon2.Arm.Derive.segLen_lt hp
  have lt := hp.lanes_lt
  unfold Impl.Argon2.Arm.Derive.countSelect
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h.fs.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ =>
    wp_sub (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ =>
    wp_sub (op2_reg _ _) fun s₅ u₅ => wp_orr (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_lsr (by decide)) fun s₇ u₇ =>
    wp_sub (op2_imm (by decide)) fun s₈ u₈ => wp_add (op2_reg _ _) fun s₉ u₉ => ?_
  have o₉ := ((((((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans
    (Only.of_upd u₅)).trans (Only.of_upd u₆)).trans (Only.of_upd u₇)).trans (Only.of_upd u₈)).trans (Only.of_upd u₉)
  have h₉ := h.of_only o₉ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₉.fs.inv (d := refLaneOff) (by decide) fun s₁₀ u₁₀ =>
    VG.Proof.Argon2.Arm.Derive.wp_ldloc hp (h₉.fs.inv.upd u₁₀ (by decide)) (d := laneOff) (by decide) fun s₁₁ u₁₁ =>
    wp_eor (op2_reg _ _) fun s₁₂ u₁₂ => wp_mov (op2_imm (by decide)) fun s₁₃ u₁₃ =>
    wp_sub (op2_reg _ _) fun s₁₄ u₁₄ => wp_orr (op2_reg _ _) fun s₁₅ u₁₅ => wp_mov (op2_lsr (by decide)) fun s₁₆ u₁₆ =>
    wp_sub (op2_imm (by decide)) fun s₁₇ u₁₇ => wp_eor (op2_reg _ _) fun s₁₈ u₁₈ =>
    wp_and (op2_reg _ _) fun s₁₉ u₁₉ => wp_eor (op2_reg _ _) fun s₂₀ u₂₀ => ?_
  have o₂₀ := o₉.trans (((((((((((Only.of_upd u₁₀).trans (Only.of_upd u₁₁)).trans (Only.of_upd u₁₂)).trans
    (Only.of_upd u₁₃)).trans (Only.of_upd u₁₄)).trans (Only.of_upd u₁₅)).trans (Only.of_upd u₁₆)).trans
    (Only.of_upd u₁₇)).trans (Only.of_upd u₁₈)).trans (Only.of_upd u₁₉)).trans (Only.of_upd u₂₀))
  have h₂₀ := h.of_only o₂₀ (by decide)
  -- The value.
  have m : ∀ {t : State} {ds : List Reg}, Only ds s t → ∀ d, VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d := fun k d => VG.Proof.Argon2.Arm.Derive.lw_mem k.mem d
  have mi : VG.Proof.Argon2.Arm.Derive.lw s₀ s₉ refLaneOff = BitVec.ofNat 32 rl := by rw [m o₉, hr]
  have ml : VG.Proof.Argon2.Arm.Derive.lw s₀ s₁₀ laneOff = BitVec.ofNat 32 lane := by
    rw [VG.Proof.Argon2.Arm.Derive.lw_mem u₁₀.mem, m o₉, h.fs.pos.lane]
  have v : s₂₀.gpr .r0 = (s.gpr .r0 + (((((0 : BitVec 32) - VG.Proof.Argon2.Arm.Derive.lw s₀ s indexOff) ||| lw s₀ s indexOff) >>> 31) - (1 : BitVec 32))) ^^^
      (((s.gpr .r0 + VG.Proof.Argon2.Arm.Derive.lw s₀ s indexOff - (1 : BitVec 32)) ^^^ (s.gpr .r0 + (((((0 : BitVec 32) - VG.Proof.Argon2.Arm.Derive.lw s₀ s indexOff) ||| lw s₀ s indexOff) >>> 31) - (1 : BitVec 32)))) &&&
        (((((0 : BitVec 32) - (VG.Proof.Argon2.Arm.Derive.lw s₀ s₉ refLaneOff ^^^ VG.Proof.Argon2.Arm.Derive.lw s₀ s₁₀ laneOff)) ||| (VG.Proof.Argon2.Arm.Derive.lw s₀ s₉ refLaneOff ^^^ VG.Proof.Argon2.Arm.Derive.lw s₀ s₁₀ laneOff)) >>> 31) - (1 : BitVec 32))) := by
    simp only [VG.Proof.Argon2.Arm.Derive.upd_get u₂₀, VG.Proof.Argon2.Arm.Derive.upd_get u₁₉, VG.Proof.Argon2.Arm.Derive.upd_get u₁₈, VG.Proof.Argon2.Arm.Derive.upd_get u₁₇, VG.Proof.Argon2.Arm.Derive.upd_get u₁₆, VG.Proof.Argon2.Arm.Derive.upd_get u₁₅, VG.Proof.Argon2.Arm.Derive.upd_get u₁₄, VG.Proof.Argon2.Arm.Derive.upd_get u₁₃, VG.Proof.Argon2.Arm.Derive.upd_get u₁₂, VG.Proof.Argon2.Arm.Derive.upd_get u₁₁, VG.Proof.Argon2.Arm.Derive.upd_get u₁₀,
      VG.Proof.Argon2.Arm.Derive.upd_get u₉, VG.Proof.Argon2.Arm.Derive.upd_get u₈, VG.Proof.Argon2.Arm.Derive.upd_get u₇, VG.Proof.Argon2.Arm.Derive.upd_get u₆, VG.Proof.Argon2.Arm.Derive.upd_get u₅, VG.Proof.Argon2.Arm.Derive.upd_get u₄, VG.Proof.Argon2.Arm.Derive.upd_get u₃, VG.Proof.Argon2.Arm.Derive.upd_get u₂, VG.Proof.Argon2.Arm.Derive.upd_get u₁, ↓reduceIte, reduceCtorEq]
  have val : s₂₀.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.countV base index (rl == lane)) := by
    rw [v, mi, ml, h.fs.pos.index, ha, VG.Proof.Argon2.Arm.Derive.nz, VG.Proof.Argon2.Arm.Derive.nz, VG.Proof.Argon2.Arm.Derive.mask_sub _ rfl, VG.Proof.Argon2.Arm.Derive.mask_sub _ rfl, VG.Proof.Argon2.Arm.Derive.sel, VG.Proof.Argon2.Arm.Derive.countV]
    simp only [VG.Proof.Argon2.Arm.Derive.ofNat_eq_zero (show index < 2 ^ 32 by omega), VG.Proof.Argon2.Arm.Derive.xor_eq_zero (show rl < 2 ^ 32 by omega)
      (show lane < 2 ^ 32 by omega)]
    by_cases hs : rl = lane
    · simp only [hs, ite_true, show (lane == lane) = true from beq_self_eq_true lane]
      rw [BitVec.ofNat_add_ofNat, VG.Proof.Argon2.Arm.Derive.ofNat_pred (hsame hs) rfl]
    · simp only [hs, ite_false, show (rl == lane) = false from beq_eq_false_iff_ne.mpr hs, Bool.false_eq_true]
      by_cases hi0 : index = 0
      · rw [ite_eq_left hi0, ite_eq_left hi0, VG.Proof.Argon2.Arm.Derive.add_allOnes (hother hs hi0) (by omega)]
      · rw [ite_eq_right hi0, ite_eq_right hi0, Nat.sub_zero]
        exact BitVec.add_zero _
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp h₂₀.fs.inv (d := countOff) (by decide) fun t it vt ot gt mt => k t ?_ (by rw [gt, val])
    (by rw [vt, val]) (fun e he hd => by rw [ot e he hd, m o₂₀]) (fun r hr => by rw [gt, (o₂₀.mono (es := [.r0, .r1, .r2, .r3]) (by simp)).gpr r hr])
  exact h₂₀.store hp it (d := countOff) (by decide) (by decide) (by decide) (by decide) (by decide) mt

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillPtr`. -/
section

/-!
# Argon2 on ARMv7: the reference block's column and the block pointers

`relative_ok`: the position in the window that J₁ selects (RFC 9106
§3.4.2), with the high halves of the products from `mulHi`; `wrap_ok`: its
column, from the window's start, modulo the lane length; `refPointer_ok` and
`curPointer_ok`: the reference and current blocks' addresses, to the locals.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_and op2_imm op2_reg)
open VG.Proof.Blake2.Arm.Stream (wp_adc)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Proof.Sha512.Arm (Only)
open VG.Proof.Argon2.Arm (mulHi_ok mulHiV_eq)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff)

/-- The position in the window that `j1` selects. -/
def relV (cnt j1 : Nat) : Nat := cnt - 1 - cnt * (j1 * j1 / 2 ^ 32) / 2 ^ 32

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- `relative`: `r0 :=` the position in the window. -/
theorem relative_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) {cnt : Nat} (hc : 1 ≤ cnt) (hc' : cnt < 2 ^ 32)
    (hcnt : VG.Proof.Argon2.Arm.Derive.lw s₀ s countOff = BitVec.ofNat 32 cnt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.relV cnt J1.toNat) →
      Only [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r12] s t → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.relative ++ is)) s Q := by
  have jb := J1.isLt
  have x32 := Proof.Argon2.reference_scaled_bound J1.toNat jb
  have lt := Proof.Argon2.reference_scale_lt_count cnt J1.toNat (by omega) jb
  unfold Impl.Argon2.Arm.Derive.relative
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h.fs.inv (d := j1Off) (by decide) fun s₁ u₁ =>
    mulHi_ok (by decide) (by decide) (by decide) fun s₂ o₂ p₂ => ?_
  have O₂ := (Only.of_upd u₁).trans o₂
  have h₂ := h.of_only O₂ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₂.fs.inv (d := countOff) (by decide) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    mulHi_ok (by decide) (by decide) (by decide) fun s₅ o₅ p₅ => wp_sub (op2_imm (by decide)) fun s₆ u₆ =>
    wp_sub (op2_reg _ _) fun t u => k t ?_ ?_
  · have x₄ : s₄.gpr .r6 = BitVec.ofNat 32 (J1.toNat * J1.toNat / 2 ^ 32) := by
      rw [u₄.gpr, u₃.other _ (by decide), p₂, u₁.gpr, h.j1, mulHiV_eq]
    have c₄ : s₄.gpr .r5 = BitVec.ofNat 32 cnt := by
      rw [u₄.other _ (by decide), u₃.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem O₂.mem, hcnt]
    rw [u.gpr, u₆.gpr, u₆.other .r2 (by decide), o₅.gpr .r5 (by decide), p₅, x₄, c₄, mulHiV_eq,
      VG.Proof.Argon2.Arm.Derive.toNat32 hc', VG.Proof.Argon2.Arm.Derive.toNat32 x32, VG.Proof.Argon2.Arm.Derive.ofNat_pred hc rfl, MdStream.Arm.sub_ofNat (by omega), VG.Proof.Argon2.Arm.Derive.relV]
  · exact ((((O₂.trans (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans o₅).trans
      ((Only.of_upd u₆).trans (Only.of_upd u))).mono (by simp)

/-- `wrap`: `r0 := (start + r0) mod laneLen`. -/
theorem wrap_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) {rel stt : Nat} (hr : rel < (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen)
    (hs : stt < (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen) (ha : s.gpr .r0 = BitVec.ofNat 32 rel)
    (hst : VG.Proof.Argon2.Arm.Derive.lw s₀ s startOff = BitVec.ofNat 32 stt) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r0 = BitVec.ofNat 32 ((stt + rel) % (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen) → Only [.r0, .r2, .r3] s t →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.wrap ++ is)) s Q := by
  have L22 : (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen < 2 ^ 22 := by
    have := Nat.le_mul_of_pos_left (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen (show 0 < VG.Proof.Argon2.Arm.Derive.lanesN s₀ from hp.lanes_pos)
    have e := hp.blocks_eq
    have := hp.blocks_lt
    omega
  unfold Impl.Argon2.Arm.Derive.wrap
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h.fs.inv (d := startOff) (by decide) fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ => ?_
  have O₂ := (Only.of_upd u₁).trans (Only.of_upd u₂)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp (h.of_only O₂ (by decide)).fs.inv (d := laneLenOff) (by decide) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => Divide.wp_subsC (op2_reg _ _) fun s₅ u₅ c₅ =>
    wp_adc (op2_imm (by decide)) fun s₆ u₆ _ => wp_sub (op2_imm (by decide)) fun s₇ u₇ =>
    wp_and (op2_reg _ _) fun s₈ u₈ => wp_add (op2_reg _ _) fun t u => k t ?_ ?_
  · have L₂ : VG.Proof.Argon2.Arm.Derive.lw s₀ s₂ laneLenOff = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen := by
      rw [VG.Proof.Argon2.Arm.Derive.lw_mem O₂.mem]; exact h.fs.pr.laneLen
    have x₄ : s₄.gpr .r0 = BitVec.ofNat 32 (stt + rel) := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), ha, hst,
        BitVec.ofNat_add_ofNat, Nat.add_comm]
    have l₄ : s₄.gpr .r2 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen := by
      rw [u₄.other _ (by decide), u₃.gpr, L₂]
    rw [x₄, l₄, VG.Proof.Argon2.Arm.Derive.toNat32 (by omega), VG.Proof.Argon2.Arm.Derive.toNat32 (by omega)] at c₅
    simp only [VG.Proof.Argon2.Arm.Derive.upd_get u, VG.Proof.Argon2.Arm.Derive.upd_get u₈, VG.Proof.Argon2.Arm.Derive.upd_get u₇, VG.Proof.Argon2.Arm.Derive.upd_get u₆, VG.Proof.Argon2.Arm.Derive.upd_get u₅, ↓reduceIte, reduceCtorEq, c₅, x₄, l₄,
      u₄.gpr]
    rw [Proof.Argon2.reference_wrap (stt + rel) (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen (by omega)]
    by_cases c : stt + rel < (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen
    · have c' : ¬(VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen ≤ stt + rel := by omega
      simp only [c, c', decide_false, ite_true, Bool.false_eq_true, ite_false]
      rw [show (0 : BitVec 32) + 0 + 0 - 1 = BitVec.allOnes 32 by decide, BitVec.allOnes_and,
        BitVec.sub_add_cancel]
    · have c' : (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen ≤ stt + rel := by omega
      simp only [c, c', decide_true, ite_true, ite_false]
      rw [show (0 : BitVec 32) + 0 + 1 - 1 = 0 by decide,
        show (0 : BitVec 32) &&& BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen = 0 from BitVec.zero_and]
      exact (BitVec.add_zero _).trans (MdStream.Arm.sub_ofNat c')
  · exact ((O₂.trans ((((((Only.of_upd u₃).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans
      (Only.of_upd u₆)).trans (Only.of_upd u₇)).trans (Only.of_upd u₈))).trans (Only.of_upd u)).mono (by simp)

/-- `refPointer`: the address of block `r0` of the reference lane, to the locals. -/
theorem refPointer_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) {col rl : Nat} (hc : col < (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen)
    (hrl : rl < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (ha : s.gpr .r0 = BitVec.ofNat 32 col)
    (hr : VG.Proof.Argon2.Arm.Derive.lw s₀ s refLaneOff = BitVec.ofNat 32 rl) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 t →
      VG.Proof.Argon2.Arm.Derive.lw s₀ t tmpOff = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 ((rl * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + col) * 1024) →
      (∀ e, e + 4 ≤ 256 → (tmpOff + 4 ≤ e ∨ e + 4 ≤ tmpOff) → VG.Proof.Argon2.Arm.Derive.lw s₀ t e = VG.Proof.Argon2.Arm.Derive.lw s₀ s e) →
      (∀ r ∉ [Reg.r0, .r1, .r2], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.refPointer ++ is)) s Q := by
  unfold Impl.Argon2.Arm.Derive.refPointer
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp (h.of_only (Only.of_upd u₁) (by decide)).fs.inv (d := refLaneOff) (by decide)
    fun s₂ u₂ => ?_
  have K₂ := (Only.of_upd u₁).trans (Only.of_upd u₂)
  refine VG.Proof.Argon2.Arm.Derive.blockAddr_ok hp (h.of_only K₂ (by decide)).fs.inv (h.of_only K₂ (by decide)).fs.pr hrl hc
    (by rw [u₂.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem, hr]) (by rw [u₂.other _ (by decide), u₁.gpr, ha]) fun s₃ a₃ k₃ => ?_
  have K₃ := K₂.trans k₃
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp (h.of_only K₃ (by decide)).fs.inv (d := tmpOff) (by decide) fun t it vt ot gt mt =>
    k t ?_ (by rw [vt, a₃]) (fun e he hd => by rw [ot e he hd, VG.Proof.Argon2.Arm.Derive.lw_mem K₃.mem]) (fun r hr => by
      rw [gt, (K₃.mono (es := [.r0, .r1, .r2]) (by simp)).gpr r hr])
  exact (h.of_only K₃ (by decide)).store hp it (d := tmpOff) (by decide) (by decide) (by decide) (by decide)
    (by decide) mt

/-- `curPointer`: the address of the current block, to the locals. -/
theorem curPointer_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hs : slice < 4)
    (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 t →
      VG.Proof.Argon2.Arm.Derive.lw s₀ t curOff = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32
        ((lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index)) * 1024) →
      (∀ e, e + 4 ≤ 256 → (curOff + 4 ≤ e ∨ e + 4 ≤ curOff) → VG.Proof.Argon2.Arm.Derive.lw s₀ t e = VG.Proof.Argon2.Arm.Derive.lw s₀ s e) →
      (∀ r ∉ [Reg.r0, .r1, .r2], t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.curPointer ++ is)) s Q := by
  have hc := Proof.Argon2.column_lt (VG.Proof.Argon2.Arm.Derive.prm s₀) hp.lanes_pos hs hi
  unfold Impl.Argon2.Arm.Derive.curPointer
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine VG.Proof.Argon2.Arm.Derive.column_ok hp h.fs.inv h.fs.pr h.fs.pos hs hi fun s₁ c₁ k₁ => ?_
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp (h.of_only k₁ (by decide)).fs.inv (d := laneOff) (by decide) fun s₂ u₂ => ?_
  have K₂ := k₁.trans (Only.of_upd u₂)
  refine VG.Proof.Argon2.Arm.Derive.blockAddr_ok hp (h.of_only K₂ (by decide)).fs.inv (h.of_only K₂ (by decide)).fs.pr hl hc
    (by rw [u₂.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem k₁.mem]; exact h.fs.pos.lane) (by rw [u₂.other _ (by decide), c₁])
    fun s₃ a₃ k₃ => ?_
  have K₃ := K₂.trans k₃
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp (h.of_only K₃ (by decide)).fs.inv (d := curOff) (by decide) fun t it vt ot gt mt =>
    k t ?_ (by rw [vt, a₃]) (fun e he hd => by rw [ot e he hd, VG.Proof.Argon2.Arm.Derive.lw_mem K₃.mem]) (fun r hr => by
      rw [gt, (K₃.mono (es := [.r0, .r1, .r2]) (by simp)).gpr r hr])
  exact (h.of_only K₃ (by decide)).store hp it (d := curOff) (by decide) (by decide) (by decide) (by decide)
    (by decide) mt

end

theorem j2_eq (J1 J2 : BitVec 32) : ((J2 ++ J1 : BitVec 64) >>> 32).toNat = J2.toNat := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← Proof.Sha512.Word64.hi_toNat,
    Proof.Sha512.Word64.hi_append]

theorem j1_eq (J1 J2 : BitVec 32) : ((J2 ++ J1 : BitVec 64) &&& 0xffffffff).toNat = J1.toNat := by
  rw [BitVec.toNat_and, show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    ← Proof.Sha512.Word64.lo_toNat, Proof.Sha512.Word64.lo_append]

theorem count_eq (p : Spec.Argon2.Params) (pass slice index : Nat) (same : Bool) :
    Spec.Argon2.referenceCount p pass slice index same =
      VG.Proof.Argon2.Arm.Derive.countV (VG.Proof.Argon2.Arm.Derive.baseV p.segmentLen p.laneLen pass slice) index same := by
  unfold Spec.Argon2.referenceCount VG.Proof.Argon2.Arm.Derive.countV VG.Proof.Argon2.Arm.Derive.baseV
  by_cases h : pass = 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

theorem ref_eq (p : Spec.Argon2.Params) (pass lane slice index : Nat) (J1 J2 : BitVec 32) :
    Spec.Argon2.reference p pass lane slice index (J2 ++ J1) =
      (VG.Proof.Argon2.Arm.Derive.refLaneV p.lanes pass slice lane J2.toNat,
        (VG.Proof.Argon2.Arm.Derive.startV p.segmentLen p.laneLen pass slice +
          VG.Proof.Argon2.Arm.Derive.relV (VG.Proof.Argon2.Arm.Derive.countV (VG.Proof.Argon2.Arm.Derive.baseV p.segmentLen p.laneLen pass slice) index
            (VG.Proof.Argon2.Arm.Derive.refLaneV p.lanes pass slice lane J2.toNat == lane)) J1.toNat) % p.laneLen) := by
  unfold Spec.Argon2.reference
  simp only [VG.Proof.Argon2.Arm.Derive.j1_eq, VG.Proof.Argon2.Arm.Derive.j2_eq, VG.Proof.Argon2.Arm.Derive.count_eq]
  rfl

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- `reference`: the reference and current blocks' addresses, to the locals. -/
theorem reference_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState} {J1 J2 : BitVec 32}
    (h : VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 s) (hpass : pass < 2 ^ 32) (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hs : slice < 4)
    (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.Arm.Derive.reference s fun t => VG.Proof.Argon2.Arm.Derive.RS s₀ pass slice lane index ctr st J1 J2 t ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀ t tmpOff = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32
        (((Spec.Argon2.reference (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice index (J2 ++ J1)).1 * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen +
          (Spec.Argon2.reference (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice index (J2 ++ J1)).2) * 1024) ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀ t curOff = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32
        ((lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index)) * 1024) := by
  have L22 : (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen < 2 ^ 22 := by
    have := Nat.le_mul_of_pos_left (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen (show 0 < VG.Proof.Argon2.Arm.Derive.lanesN s₀ from hp.lanes_pos)
    have e := hp.blocks_eq
    have := hp.blocks_lt
    omega
  have ll := hp.laneLen_eq
  have s2 := hp.segLen_two
  have hl1 := hp.lanes_pos
  rw [VG.Proof.Argon2.Arm.Derive.ref_eq]
  generalize hRL : VG.Proof.Argon2.Arm.Derive.refLaneV (VG.Proof.Argon2.Arm.Derive.prm s₀).lanes pass slice lane J2.toNat = RL
  have hRL' : VG.Proof.Argon2.Arm.Derive.refLaneV (VG.Proof.Argon2.Arm.Derive.lanesN s₀) pass slice lane J2.toNat = RL := hRL
  have rl_lt : RL < VG.Proof.Argon2.Arm.Derive.lanesN s₀ := by
    rw [← hRL', VG.Proof.Argon2.Arm.Derive.refLaneV]; split
    · exact hl
    · exact Nat.mod_lt _ (by omega)
  have first : pass = 0 → slice = 0 → RL = lane := fun a b => by rw [← hRL', VG.Proof.Argon2.Arm.Derive.refLaneV, ite_eq_left ⟨a, b⟩]
  generalize hB : VG.Proof.Argon2.Arm.Derive.baseV (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen pass slice = B
  have b_le : B ≤ (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen := by
    rw [← hB, VG.Proof.Argon2.Arm.Derive.baseV]; split
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (show slice ≤ 3 by omega)) (by omega))
    · omega
  generalize hST : VG.Proof.Argon2.Arm.Derive.startV (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen pass slice = ST
  have st_lt : ST < (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen := by
    rw [← hST, VG.Proof.Argon2.Arm.Derive.startV]; split
    · omega
    · exact Nat.mod_lt _ (by omega)
  have cpos := Proof.Argon2.reference_count_positive (VG.Proof.Argon2.Arm.Derive.prm s₀) hp.lanes_pos hp.memory_ge pass slice index
    (RL == lane) active fun a b => by simp [first a b]
  have clt := Proof.Argon2.reference_count_lt_lane (VG.Proof.Argon2.Arm.Derive.prm s₀) hp.lanes_pos hp.memory_ge pass slice index
    (RL == lane) hs hi
  rw [VG.Proof.Argon2.Arm.Derive.count_eq, hB] at cpos clt
  unfold Impl.Argon2.Arm.Derive.reference
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.refLane_ok hp h hpass hs).mono fun t₁ ⟨h₁, r₁⟩ => ?_)
  rw [hRL'] at r₁
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.refStart_ok hp h₁ hpass hs).mono fun t₂ ⟨h₂, r₂, st₂⟩ => ?_)
  rw [hST] at st₂
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.countBase_ok hp h₂ hpass).mono fun t₃ ⟨k₃, a₃⟩ => ?_)
  rw [hB] at a₃
  have h₃ := h₂.of_only k₃ (by decide)
  simp only [List.append_assoc]
  rw [← List.append_nil Impl.Argon2.Arm.Derive.curPointer]
  refine VG.Proof.Argon2.Arm.Derive.countSelect_ok hp h₃ (base := B) (rl := RL) (by omega) hi hl rl_lt a₃
    (by rw [VG.Proof.Argon2.Arm.Derive.lw_mem k₃.mem, r₂, r₁]) (fun e => ?_) (fun e e0 => ?_) fun t₄ h₄ a₄ c₄ o₄ g₄ => ?_
  · rw [← hB, VG.Proof.Argon2.Arm.Derive.baseV]; split
    · rename_i hp0
      by_cases hs0 : slice = 0
      · omega
      · have := Nat.mul_le_mul_right (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen (show 1 ≤ slice by omega); omega
    · omega
  · have : ¬(pass = 0 ∧ slice = 0) := fun ⟨a, b⟩ => e (first a b)
    rw [← hB, VG.Proof.Argon2.Arm.Derive.baseV]; split
    · rename_i hp0
      have := Nat.mul_le_mul_right (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen (show 1 ≤ slice by omega); omega
    · omega
  refine VG.Proof.Argon2.Arm.Derive.relative_ok hp h₄ (cnt := VG.Proof.Argon2.Arm.Derive.countV B index (RL == lane)) cpos (by omega) c₄ fun t₅ a₅ k₅ => ?_
  have h₅ := h₄.of_only k₅ (by decide)
  have rel_lt : VG.Proof.Argon2.Arm.Derive.relV (VG.Proof.Argon2.Arm.Derive.countV B index (RL == lane)) J1.toNat < (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen := by
    unfold VG.Proof.Argon2.Arm.Derive.relV; omega
  refine VG.Proof.Argon2.Arm.Derive.wrap_ok hp h₅ rel_lt st_lt a₅ (by
      rw [VG.Proof.Argon2.Arm.Derive.lw_mem k₅.mem, o₄ _ (by decide) (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem k₃.mem, st₂]) fun t₆ a₆ k₆ => ?_
  have h₆ := h₅.of_only k₆ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.refPointer_ok hp h₆ (Nat.mod_lt _ (by omega)) rl_lt a₆ (by
      rw [VG.Proof.Argon2.Arm.Derive.lw_mem k₆.mem, VG.Proof.Argon2.Arm.Derive.lw_mem k₅.mem, o₄ _ (by decide) (by decide), VG.Proof.Argon2.Arm.Derive.lw_mem k₃.mem, r₂, r₁])
    fun t₇ h₇ p₇ o₇ _ => ?_
  refine VG.Proof.Argon2.Arm.Derive.curPointer_ok hp h₇ hl hs hi fun t h' c' o' _ => WP.block_nil ⟨h', ?_, c'⟩
  rw [o' _ (by decide) (by decide), p₇]

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillWrite`. -/
section

/-!
# Argon2 on ARMv7: writing the new block

`writeWords_ok`: the words of G's output (at `r1`) to the current block (at
`r3`), XORed into the old ones after the first pass.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_ldr wp_str op2_reg)
open VG.Proof.Blake2.Arm.Stream (wp_eor)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.Arm (blk ofWords blk_of_words)
open VG.Proof.Sha512.Arm (A)
open VG.Impl.Argon2.Arm.Derive (writeWord)

/-- Words of the memory matrix. -/
abbrev mw (s₀ : State) (m : Mem) (o : Nat) : BitVec 32 := m.readW (A (VG.Proof.Argon2.Arm.Derive.memP s₀) o) 32

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem blocks22 : VG.Proof.Argon2.Arm.Derive.blocksN s₀ < 2 ^ 22 := by
  have hb := hp.blocks_lt
  omega

theorem mem_addr' {o : Nat} (ho : o < VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024) : A (VG.Proof.Argon2.Arm.Derive.memP s₀) o = VG.Proof.Argon2.Arm.Derive.memB s₀ + BitVec.ofNat 64 o :=
  addr_add (by have := hp.mem_fits; omega)

/-- A word of the matrix after a store to another, or the same. -/
theorem mw_store (m : Mem) {a b : Nat} (ha : a + 4 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024) (hb : b + 4 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024)
    (h : a = b ∨ a + 4 ≤ b ∨ b + 4 ≤ a) (v : BitVec 32) :
    VG.Proof.Argon2.Arm.Derive.mw s₀ (m.writeW (A (VG.Proof.Argon2.Arm.Derive.memP s₀) a) v) b = if a = b then v else VG.Proof.Argon2.Arm.Derive.mw s₀ m b := by
  have := VG.Proof.Argon2.Arm.Derive.blocks22 hp
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right e, VG.Proof.Argon2.Arm.Derive.mw, VG.Proof.Argon2.Arm.Derive.mw, VG.Proof.Argon2.Arm.Derive.mem_addr' hp (by omega), VG.Proof.Argon2.Arm.Derive.mem_addr' hp (by omega)]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- The words of the current block, `n` of them written. -/
theorem writeWords_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {cur : Nat} (hc : cur < VG.Proof.Argon2.Arm.Derive.blocksN s₀) (xo : Bool)
    {P : BitVec 32} (hsi : s.gpr .r1 = P) (hPfit : P.toNat + 1024 ≤ 2 ^ 32)
    (hPw : ∃ R ∈ [VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.memR s₀], ∃ off, State.addr P = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len)
    (hPC : Region.Disjoint ⟨State.addr P, 1024⟩ ⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) cur, 1024⟩)
    (hdi : s.gpr .r3 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (cur * 1024)) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).flatMap (writeWord xo))) s fun t =>
      VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ (∀ r, r ≠ .r0 → r ≠ .r2 → t.gpr r = s.gpr r) ∧
      Frame [⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) cur, 1024⟩] s.mem t.mem ∧
      ∀ i < 256, VG.Proof.Argon2.Arm.Derive.mw s₀ t.mem (cur * 1024 + 4 * i) = if i < n then
        (if xo then s.mem.readW (A P (4 * i)) 32 ^^^ VG.Proof.Argon2.Arm.Derive.mw s₀ s.mem (cur * 1024 + 4 * i) else s.mem.readW (A P (4 * i)) 32)
        else VG.Proof.Argon2.Arm.Derive.mw s₀ s.mem (cur * 1024 + 4 * i)
  | 0, _ => WP.block_nil ⟨h, fun _ _ _ => rfl, Frame.refl _ _, fun i _ => by rw [ite_eq_right (by omega)]⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    have hm := hp.mem_fits
    have hb := VG.Proof.Argon2.Arm.Derive.blocks22 hp
    have hc' : cur * 1024 + 1024 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024 := by omega
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((VG.Proof.Argon2.Arm.Derive.writeWords_ok h hc xo hsi hPfit hPw hPC hdi n (by omega)).mono
      fun t ⟨it, gt, ft, wt⟩ => ?_)
    have cell : matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) cur = VG.Proof.Argon2.Arm.Derive.memB s₀ + BitVec.ofNat 64 (cur * 1024) := rfl
    -- The source word is kept: only the current block has been written.
    have eP : A P (4 * n) = State.addr P + BitVec.ofNat 64 (4 * n) := addr_add (by omega_using [hPfit, hn])
    have sw_t : t.mem.readW (A P (4 * n)) 32 = s.mem.readW (A P (4 * n)) 32 := by
      rw [eP]
      refine ft.readW (r := ⟨State.addr P + BitVec.ofNat 64 (4 * n), 4⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hPC.sub_left (Offset.sub_base _ (by omega_using [hn]))
    have ea : State.addr (t.gpr .r1 + BitVec.ofNat 32 (4 * n)) = A P (4 * n) := by
      rw [gt _ (by decide) (by decide), hsi]
    have eb : State.addr (t.gpr .r3 + BitVec.ofNat 32 (4 * n)) = A (VG.Proof.Argon2.Arm.Derive.memP s₀) (cur * 1024 + 4 * n) := by
      rw [gt _ (by decide) (by decide), hdi, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have b1 : cur * 1024 + 4 * n + 4 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024 := by omega_using [hc', hn]
    have b2 : cur * 1024 + 1024 < 2 ^ 64 := by omega_using [hc', hb]
    have inS : InRegions (t.rd ++ t.wr) (A P (4 * n)) 4 := by
      obtain ⟨R, hR, off, bR, lR⟩ := hPw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      have RW : R ∈ t.wr ∧ R.len ≤ 2 ^ 32 := by
        rw [it.wr]
        rcases hR with rfl | rfl
        · exact ⟨VG.Proof.Argon2.Arm.Derive.scr_mem hp, by show 16384 ≤ 2 ^ 32; decide⟩
        · exact ⟨VG.Proof.Argon2.Arm.Derive.mem_mem hp, by show VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024 ≤ 2 ^ 32; omega_using [hm]⟩
      rw [eP, bR, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨R, List.mem_append_right _ RW.1, Offset.contains_base _ (by omega_using [lR, hn])
        (by have := RW.2; omega_using [lR, hn, this])⟩
    have inMc : (VG.Proof.Argon2.Arm.Derive.memR s₀).Contains (A (VG.Proof.Argon2.Arm.Derive.memP s₀) (cur * 1024 + 4 * n)) 4 := by
      rw [VG.Proof.Argon2.Arm.Derive.mem_addr' hp (by omega_using [b1])]
      exact Offset.contains_base _ b1 (by omega_using [b1, hb])
    have inC : (⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) cur, 1024⟩ : Region).Contains (A (VG.Proof.Argon2.Arm.Derive.memP s₀) (cur * 1024 + 4 * n)) 4 := by
      rw [VG.Proof.Argon2.Arm.Derive.mem_addr' hp (by omega_using [b1]), cell]
      exact Offset.contains _ (by omega_using []) (by omega_using [hn]) b2
    have inM : ∀ u : State, VG.Proof.Argon2.Arm.Derive.Inv s₀ u → InRegions u.wr (A (VG.Proof.Argon2.Arm.Derive.memP s₀) (cur * 1024 + 4 * n)) 4 :=
      fun u iu => ⟨VG.Proof.Argon2.Arm.Derive.memR s₀, by rw [iu.wr]; exact VG.Proof.Argon2.Arm.Derive.mem_mem hp, inMc⟩
    -- The word.
    have fin : ∀ (v : BitVec 32) (u : State), u.mem = t.mem.writeW (A (VG.Proof.Argon2.Arm.Derive.memP s₀) (cur * 1024 + 4 * n)) v →
        u.rd = t.rd → u.wr = t.wr → u.sp = t.sp → (∀ r, r ≠ .r0 → r ≠ .r2 → u.gpr r = s.gpr r) →
        v = (if xo then s.mem.readW (A P (4 * n)) 32 ^^^ VG.Proof.Argon2.Arm.Derive.mw s₀ s.mem (cur * 1024 + 4 * n)
          else s.mem.readW (A P (4 * n)) 32) →
        VG.Proof.Argon2.Arm.Derive.Inv s₀ u ∧ (∀ r, r ≠ .r0 → r ≠ .r2 → u.gpr r = s.gpr r) ∧
        Frame [⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) cur, 1024⟩] s.mem u.mem ∧
        ∀ i < 256, VG.Proof.Argon2.Arm.Derive.mw s₀ u.mem (cur * 1024 + 4 * i) = if i < n + 1 then
          (if xo then s.mem.readW (A P (4 * i)) 32 ^^^ VG.Proof.Argon2.Arm.Derive.mw s₀ s.mem (cur * 1024 + 4 * i)
            else s.mem.readW (A P (4 * i)) 32)
          else VG.Proof.Argon2.Arm.Derive.mw s₀ s.mem (cur * 1024 + 4 * i) := fun v u hm hrd hwr hsp gu ev => by
      have fu : Frame [⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) cur, 1024⟩] s.mem u.mem := by
        rw [hm]; exact ft.writeW (List.mem_singleton_self _) v inC
      have iu : VG.Proof.Argon2.Arm.Derive.Inv s₀ u := it.step hsp (by rw [gu _ (by decide) (by decide), gt _ (by decide) (by decide)])
        hrd hwr (by rw [hm]; exact (Frame.refl _ _).writeW (r := VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp) v inMc)
      refine ⟨iu, gu, fu, fun i hi => ?_⟩
      rw [hm, VG.Proof.Argon2.Arm.Derive.mw_store hp _ b1 (by omega_using [hi, hc', hb]) (by omega_using []), wt i hi]
      by_cases e : i = n
      · subst e
        rw [ite_eq_left rfl, ite_eq_left (show i < i + 1 by omega_using []), ev]
      · rw [ite_eq_right (show ¬cur * 1024 + 4 * n = cur * 1024 + 4 * i by omega_using [e])]
        by_cases c : i < n
        · rw [ite_eq_left c, ite_eq_left (show i < n + 1 by omega_using [c])]
        · rw [ite_eq_right c, ite_eq_right (show ¬i < n + 1 by omega_using [c, e])]
    have o4 : 4 * n < 4096 := by omega_using [hn]
    cases xo
    · simp only [writeWord, Bool.false_eq_true, ite_false, List.nil_append]
      refine wp_ldr o4 ea inS fun u₁ v₁ => ?_
      refine wp_str (a := A (VG.Proof.Argon2.Arm.Derive.memP s₀) (cur * 1024 + 4 * n)) o4 (by rw [v₁.other .r3 (by decide)]; exact eb) (by rw [v₁.wr]; exact inM _ it)
        fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₁.mem, v₁.gpr]) (by rw [mu.rd, v₁.rd]) (by rw [mu.wr, v₁.wr])
        (by rw [mu.sp, v₁.sp]) (fun r a b => by rw [mu.gpr, v₁.other r a, gt r a b]) ?_
      simp only [Bool.false_eq_true, ite_false]
      rw [sw_t]
    · simp only [writeWord, ite_true, List.cons_append, List.nil_append]
      refine wp_ldr o4 ea inS fun u₁ v₁ => ?_
      refine wp_ldr (a := A (VG.Proof.Argon2.Arm.Derive.memP s₀) (cur * 1024 + 4 * n)) o4 (by rw [v₁.other .r3 (by decide)]; exact eb)
        (by rw [v₁.rd, v₁.wr]; exact ⟨VG.Proof.Argon2.Arm.Derive.memR s₀, List.mem_append_right _ (by rw [it.wr]; exact VG.Proof.Argon2.Arm.Derive.mem_mem hp), inMc⟩)
        fun u₂ v₂ => wp_eor (op2_reg _ _) fun u₃ v₃ => ?_
      refine wp_str (a := A (VG.Proof.Argon2.Arm.Derive.memP s₀) (cur * 1024 + 4 * n)) o4 (by rw [v₃.other .r3 (by decide), v₂.other .r3 (by decide), v₁.other .r3 (by decide)]; exact eb)
        (by rw [v₃.wr, v₂.wr, v₁.wr]; exact inM _ it) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₃.mem, v₂.mem, v₁.mem, v₃.gpr]) (by rw [mu.rd, v₃.rd, v₂.rd, v₁.rd])
        (by rw [mu.wr, v₃.wr, v₂.wr, v₁.wr]) (by rw [mu.sp, v₃.sp, v₂.sp, v₁.sp])
        (fun r a b => by rw [mu.gpr, v₃.other r a, v₂.other r b, v₁.other r a, gt r a b]) ?_
      simp only [ite_true]
      rw [v₂.other .r0 (by decide), v₁.gpr, v₂.gpr, v₁.mem, sw_t, ← VG.Proof.Argon2.Arm.Derive.mw, wt n (by omega_using [hn]),
        ite_eq_right (show ¬n < n by omega_using [])]

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillBlock`. -/
section

/-!
# Argon2 on ARMv7: one block of the filling loops

`fillCompress_ok`: G of the previous and reference blocks to
`scratch + 4096`; `fillWrite_ok`: the current block, copied or XORed;
`fillBlock_ok`: the filling state after one block (`Spec.Argon2.fillBlock`).
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_cmp op2_imm op2_reg)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.Arm (blk ofWords blk_of_words xor_words)
open VG.Proof.Sha512.Arm (Only A)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff writeBlock)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem outside_work : VG.Proof.Argon2.Arm.Derive.Outside s₀ ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀, 4096⟩ := by
  have := VG.Proof.Argon2.Arm.Derive.outside_scr hp (o := 0) (n := 4096) (.inl (by decide))
  simpa using this

/-- The locals are kept by writes outside them. -/
theorem lw_outside {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem) (ho : ∀ r ∈ rs, VG.Proof.Argon2.Arm.Derive.Outside s₀ r)
    {d : Nat} (hd : d + 4 ≤ 144) : VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d :=
  f.readW (r := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), 4⟩) (Region.contains_self _ _)
    (fun r hr => (ho r hr).1.symm.sub_left (VG.Proof.Argon2.Arm.Derive.loc_word_sub hp hd)) (by decide)

/-- `fillCompress`: G of the previous and reference blocks, to `scratch + 4096`. -/
theorem fillCompress_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hs : slice < 4)
    (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen) {R : Nat} (hR : R < VG.Proof.Argon2.Arm.Derive.blocksN s₀)
    (htmp : VG.Proof.Argon2.Arm.Derive.lw s₀ s tmpOff = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (R * 1024)) :
    WP isa Impl.Argon2.Arm.Derive.fillCompress s fun t => VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st t ∧
      (∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d) ∧
      blk t.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 4096 = compress (blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) (lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen +
        (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index + (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) % (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen)))
        (blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) R)) := by
  have L8 := VG.Proof.Argon2.Arm.Derive.laneLen_ge hp
  obtain ⟨cl, _⟩ := VG.Proof.Argon2.Arm.Derive.cell_fits hp hl (col := (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index + (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) %
    (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen) (Nat.mod_lt _ (by omega))
  unfold Impl.Argon2.Arm.Derive.fillCompress
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index + (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) %
    (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen) = P at cl a₁ ⊢
  have h₁ := h.of_only k₁ (by decide)
  refine WP.seq (VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₁.inv (d := tmpOff) (by decide) fun s₂ u₂ => ?_)
  have h₂ := h₁.of_only (Only.of_upd u₂) (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h₂.inv (i := 15) (by decide) fun s₃ u₃ => ?_
  have h₃ := h₂.of_only (Only.of_upd u₃) (by decide)
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have h₄ := h₃.of_only (Only.of_upd u₄) (by decide)
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, k₁.mem]
  have ax : s₄.gpr .r0 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (P * 1024) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), a₁]
  have sx : s₄.gpr .r1 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (R * 1024) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem k₁.mem, htmp]
  have dx : s₄.gpr .r3 = VG.Proof.Argon2.Arm.Derive.scrP s₀ := by
    rw [u₄.other _ (by decide), u₃.gpr]
  have cx : s₄.gpr .r2 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 4096 := by
    rw [u₄.gpr, u₃.gpr]; rfl
  refine VG.Proof.Argon2.Arm.Derive.ccall_ok hp h₄.inv dx (o := 4096) (by decide) (by decide) cx (by rw [ax]; exact .inl ⟨P, cl, rfl⟩)
    (by rw [sx]; exact .inl ⟨R, hR, rfl⟩) fun t it _ f post => ?_
  have ho : ∀ r ∈ [⟨VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 4096, 1024⟩, ⟨VG.Proof.Argon2.Arm.Derive.scrB s₀, 4096⟩], VG.Proof.Argon2.Arm.Derive.Outside s₀ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.Argon2.Arm.Derive.outside_scr hp (.inl (by decide))
    · exact VG.Proof.Argon2.Arm.Derive.outside_work hp
  refine ⟨h₄.frame hp it f ho, fun d hd => by rw [VG.Proof.Argon2.Arm.Derive.lw_outside hp f ho hd, VG.Proof.Argon2.Arm.Derive.lw_mem m₄], ?_⟩
  rw [post, ax, sx, VG.Proof.Argon2.Arm.Derive.cell_addr hp cl, VG.Proof.Argon2.Arm.Derive.cell_addr hp hR, m₄]

/-- `fillWrite`: G's output to the current block, XORed into it after the first pass. -/
theorem fillWrite_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) {C : Nat} (hC : C < VG.Proof.Argon2.Arm.Derive.blocksN s₀)
    (hcur : VG.Proof.Argon2.Arm.Derive.lw s₀ s curOff = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (C * 1024)) :
    WP isa Impl.Argon2.Arm.Derive.fillWrite s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧
      Frame [⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) C, 1024⟩] s.mem t.mem ∧
      blockAt t.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) C) = if pass = 0 then blk s.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 4096 else
        xorBlock (blk s.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 4096) (blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) C)) := by
  unfold Impl.Argon2.Arm.Derive.fillWrite
  refine WP.seq (VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h.inv (i := 15) (by decide) fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ => ?_)
  have h₂ := h.of_only ((Only.of_upd u₁).trans (Only.of_upd u₂)) (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₂.inv (d := curOff) (by decide) fun s₃ u₃ => ?_
  have h₃ := h₂.of_only (Only.of_upd u₃) (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h₃.inv (d := passOff) (by decide) fun s₄ u₄ =>
    wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_
  have h₅ := h₃.of_only ((Only.of_upd u₄).trans (Only.of_fupd f₅)) (by decide)
  have m₅ : s₅.mem = s.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have si : s₅.gpr .r1 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 4096 := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]; rfl
  have di : s₅.gpr .r3 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (C * 1024) := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₂.mem, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem, hcur]
  have hsf := hp.scr_fits
  have eP : State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 4096) = VG.Proof.Argon2.Arm.Derive.scrB s₀ + BitVec.ofNat 64 4096 := VG.Proof.Argon2.Arm.Derive.scr_addr hp (by decide)
  have Pfit : (VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 4096).toNat + 1024 ≤ 2 ^ 32 := by rw [VG.Proof.Argon2.Arm.Derive.add_nat (by omega)]; omega
  have Pw : ∃ R ∈ [VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.memR s₀], ∃ off, State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 4096) =
      R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len :=
    ⟨VG.Proof.Argon2.Arm.Derive.scrR s₀, by simp, 4096, eP, by show 4096 + 1024 ≤ 16384; decide⟩
  have PC : Region.Disjoint ⟨State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 4096), 1024⟩ ⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) C, 1024⟩ := by
    rw [eP]
    exact (hp.mem_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (VG.Proof.Argon2.Arm.Derive.cell_in_mem hC)
  have nxt : blk s.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 4096 = ofWords fun i => VG.Proof.Argon2.Arm.Derive.sw s₀ s.mem (4096 + 4 * i) :=
    blk_of_words fun _ _ => rfl
  have old : blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) C) = ofWords fun i => VG.Proof.Argon2.Arm.Derive.mw s₀ s.mem (C * 1024 + 4 * i) := by
    rw [VG.Proof.Argon2.Arm.Derive.cell_blk hp _ hC]; exact blk_of_words fun _ _ => rfl
  have done : ∀ (xo : Bool) (t : State), (∀ i < 256, VG.Proof.Argon2.Arm.Derive.mw s₀ t.mem (C * 1024 + 4 * i) = if i < 256 then
        (if xo then s₅.mem.readW (A (VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 4096) (4 * i)) 32 ^^^ VG.Proof.Argon2.Arm.Derive.mw s₀ s₅.mem (C * 1024 + 4 * i)
          else s₅.mem.readW (A (VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 4096) (4 * i)) 32)
        else VG.Proof.Argon2.Arm.Derive.mw s₀ s₅.mem (C * 1024 + 4 * i)) →
      blockAt t.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) C) = if xo then
        xorBlock (blk s.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 4096) (blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) C)) else blk s.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 4096 :=
    fun xo t wt => by
      have e : blockAt t.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) C) = ofWords fun i => if xo then
          VG.Proof.Argon2.Arm.Derive.sw s₀ s.mem (4096 + 4 * i) ^^^ VG.Proof.Argon2.Arm.Derive.mw s₀ s.mem (C * 1024 + 4 * i) else VG.Proof.Argon2.Arm.Derive.sw s₀ s.mem (4096 + 4 * i) := by
        rw [VG.Proof.Argon2.Arm.Derive.cell_blk hp _ hC]
        exact blk_of_words fun i hi => by rw [← VG.Proof.Argon2.Arm.Derive.mw, wt i hi, ite_eq_left hi, m₅, VG.Proof.Argon2.Arm.Derive.A_shift]
      rw [e, nxt, old]
      cases xo
      · rfl
      · simp only [ite_true]; rw [xor_words]
  refine WP.ite (decide (pass = 0)) (by
    show VG.Arm.eval .eq _ = _
    rw [MdStream.Arm.eval_eq, z₅, u₄.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₃.mem, VG.Proof.Argon2.Arm.Derive.lw_mem u₂.mem, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem, h.pos.pass, VG.Proof.Argon2.Arm.Derive.sub_zero32,
      MdStream.Arm.ofNat_beq_zero hpass])
    (fun hb => ?_) fun hb => ?_
  · refine ((VG.Proof.Argon2.Arm.Derive.writeWords_ok hp h₅.inv hC false si Pfit Pw PC di 256 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₅]; exact ft, ?_⟩)
    rw [done false t wt, ite_eq_left (of_decide_eq_true hb)]; rfl
  · refine ((VG.Proof.Argon2.Arm.Derive.writeWords_ok hp h₅.inv hC true si Pfit Pw PC di 256 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₅]; exact ft, ?_⟩)
    rw [done true t wt, ite_eq_right (of_decide_eq_false hb)]; rfl

/-- `fillBlock`: one block of the filling loops. -/
theorem fillBlock_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hs : slice < 4)
    (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.Arm.Derive.fillBlock s fun t =>
      VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index (VG.Proof.Argon2.Arm.Derive.ctrNext (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice index ctr)
        (Spec.Argon2.fillBlock (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice lane index st) t := by
  have hb : VG.Proof.Argon2.Arm.Derive.blocksN s₀ = (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.Arm.Derive.fillBlock
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.randomSource_ok hp h hpass hl hs hi).mono fun t₁ ⟨h₁, w₁⟩ => ?_)
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.reference_ok hp ⟨h₁, rfl, rfl⟩ hpass hl hs hi active).mono fun t₂ ⟨h₂, tmp₂, cur₂⟩ => ?_)
  rw [w₁] at tmp₂
  have refLt := Proof.Argon2.reference_cell_lt (VG.Proof.Argon2.Arm.Derive.prm s₀) hp.lanes_pos hp.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice index st.memory) hl
  have curLt := Proof.Argon2.current_cell_lt (VG.Proof.Argon2.Arm.Derive.prm s₀) hp.lanes_pos hl hs hi
  have prevLt := Proof.Argon2.previous_cell_lt (VG.Proof.Argon2.Arm.Derive.prm s₀) hp.lanes_pos hp.memory_ge
    (column := slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index) hl
  simp only at refLt
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.fillCompress_ok hp h₂.fs hl hs hi (by rw [hb]; exact refLt) tmp₂).mono
    fun t₃ ⟨h₃, l₃, c₃⟩ => ?_)
  refine (VG.Proof.Argon2.Arm.Derive.fillWrite_ok hp h₃ hpass (C := lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index))
    (by rw [hb]; exact curLt) (by rw [l₃ _ (by decide)]; exact cur₂)).mono
    fun t ⟨it, ft, bt⟩ => ?_
  have kept : ∀ j < (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks, j ≠ lane * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen + index) →
      blockAt t.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) j) = blockAt t₃.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) j) := fun j hj ne =>
    VG.Proof.Argon2.Arm.Derive.blockAt_keep ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Argon2.Arm.Derive.cell_other hp (by rw [hb]; exact hj) (by rw [hb]; exact curLt) ne
  have lt : ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ t₃ d := fun d hd =>
    ft.readW (r := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Proof.Argon2.Arm.Derive.loc_disj hp hd (VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).sub_right (VG.Proof.Argon2.Arm.Derive.cell_in_mem (by rw [hb]; exact curLt))) (by decide)
  refine ⟨it, Prm.of_lw h₃.pr fun d hd => lt d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    h₃.pos.of_lw fun d hd => lt d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    ?_, ?_⟩
  · obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h₃.cache
    · exact ⟨c0, by rw [lt _ (by decide)]; exact c1, .inl c2⟩
    · refine ⟨c0, by rw [lt _ (by decide)]; exact c1, .inr ⟨c3, ?_⟩⟩
      rw [VG.Proof.Argon2.Arm.Derive.scr_blk hp _ (by decide), VG.Proof.Argon2.Arm.Derive.blockAt_keep ft (fun r hr => ?_), ← VG.Proof.Argon2.Arm.Derive.scr_blk hp _ (by decide), c4]
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.mem_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right
        (VG.Proof.Argon2.Arm.Derive.cell_in_mem (by rw [hb]; exact curLt))
  · rw [Proof.Argon2.FillStep.memory _ _ _ _ _ _ active]
    simp only [Proof.Argon2.FillStep.update]
    refine Represents.update h₃.mem _ curLt _ ?_ kept
    rw [bt, c₃, h₂.fs.mem.block _ prevLt, h₂.fs.mem.block _ refLt, h₃.mem.block _ curLt]

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillLoops`. -/
section

/-!
# Argon2 on ARMv7: the filling loops

`FB s₀ st`: the body with the memory matrix holding `st`'s. `segment_ok`:
a segment, from its first index (`Proof.Argon2.segmentStart`), through
`fillBlock_ok`; `lanes_ok`, `slices_ok` and `passes_ok` the loops around
it, and `passes_ok` all passes, from the initialized memory. Each loop
counts up in the locals and runs while the count differs from its bound.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_orr wp_cmp wp_ldr op2_imm op2_reg)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.Arm (blk)
open VG.Proof.Sha512.Arm (Only)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff)

/-- The body, the memory matrix holding `st`'s. -/
structure FB (s₀ : State) (st : FillState) (s : State) : Prop where
  inv : VG.Proof.Argon2.Arm.Derive.Inv s₀ s
  pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s
  mem : Represents s.mem (VG.Proof.Argon2.Arm.Derive.memB s₀) (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks st.memory

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- A store to the locals keeps their other words, the cached address block and the matrix. -/
theorem loc_store {s t : State} {d : Nat} (hd : d + 4 ≤ 144) {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) v) :
    (∀ e, e + 4 ≤ 256 → (e + 4 ≤ d ∨ d + 4 ≤ e) → VG.Proof.Argon2.Arm.Derive.lw s₀ t e = VG.Proof.Argon2.Arm.Derive.lw s₀ s e) ∧
    blk t.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 6144 = blk s.mem (VG.Proof.Argon2.Arm.Derive.scrP s₀) 6144 ∧
    ∀ k < (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks, blockAt t.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k) = blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k) := by
  have f : Frame [⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), 4⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)
  refine ⟨fun e he hde => ?_, ?_, fun k hk => ?_⟩
  · show t.mem.readW _ 32 = _
    rw [hm, VG.Proof.Argon2.Arm.Derive.lw_store hp (by omega) he hde.symm]
  · rw [VG.Proof.Argon2.Arm.Derive.scr_blk hp t.mem (by decide), VG.Proof.Argon2.Arm.Derive.scr_blk hp s.mem (by decide)]
    refine VG.Proof.Argon2.Arm.Derive.blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (VG.Proof.Argon2.Arm.Derive.loc_disj hp hd (VG.Proof.Argon2.Arm.Derive.scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ (by decide))
  · refine VG.Proof.Argon2.Arm.Derive.blockAt_keep f fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hk' : k < VG.Proof.Argon2.Arm.Derive.blocksN s₀ := by rw [hp.blocks]; exact hk
    exact (VG.Proof.Argon2.Arm.Derive.loc_disj hp hd (VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).symm.sub_left (VG.Proof.Argon2.Arm.Derive.cell_in_mem hk')

/-- A store to a word of the locals other than the parameters keeps `FB`. -/
theorem FB.store {st : FillState} {s t : State} (h : VG.Proof.Argon2.Arm.Derive.FB s₀ st s) (it : VG.Proof.Argon2.Arm.Derive.Inv s₀ t) {d : Nat} (hd : d + 4 ≤ 144)
    (hd' : ∀ e ∈ [divisorOff, segLenOff, laneLenOff, strideOff], e + 4 ≤ d ∨ d + 4 ≤ e) {v : BitVec 32}
    (hm : t.mem = s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) v) : VG.Proof.Argon2.Arm.Derive.FB s₀ st t := by
  obtain ⟨l, _, c⟩ := VG.Proof.Argon2.Arm.Derive.loc_store hp hd hm
  exact ⟨it, Prm.of_lw h.pr fun e he => l e (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl | rfl | rfl <;> decide)
    (hd' e he), Represents.keep h.mem c⟩

omit hp in
theorem FB.of_only {st : FillState} {s t : State} {ds : List Reg} (h : VG.Proof.Argon2.Arm.Derive.FB s₀ st s) (o : Only ds s t)
    (h11 : Reg.r11 ∉ ds) : VG.Proof.Argon2.Arm.Derive.FB s₀ st t :=
  ⟨h.inv.only o h11, h.pr.of_mem o.mem, by rw [o.mem]; exact h.mem⟩

/-- `[r11, #d] += 1`, compared with `r1`, loaded by `ld`. -/
theorem advanceTail_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {d n : Nat} (hd : d + 4 ≤ 144)
    (hn : VG.Proof.Argon2.Arm.Derive.lw s₀ s d = BitVec.ofNat 32 n) (hn' : n + 1 < 2 ^ 32) {B : Nat} (hB : B < 2 ^ 32)
    {tail : List Instr}
    (ht : ∀ t : State, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → t.mem = s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d))
      (BitVec.ofNat 32 (n + 1)) → t.gpr .r0 = BitVec.ofNat 32 (n + 1) →
      WP isa (.block tail) t fun u => Only [.r1] t u ∧ u.z = (BitVec.ofNat 32 (n + 1) - BitVec.ofNat 32 B == 0)) :
    WP isa (.block (Impl.Argon2.Arm.Derive.ld .r0 d :: .dp .add .r0 .r0 (.imm 1) ::
      Impl.Argon2.Arm.Derive.st d .r0 :: tail)) s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧
      t.mem = s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) (BitVec.ofNat 32 (n + 1)) ∧
      VG.Arm.eval .ne t = some (!decide (n + 1 = B)) ∧ ∀ r ∉ [Reg.r0, .r1], t.gpr r = s.gpr r := by
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h (d := d) hd fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ => ?_
  have i₂ := (h.upd u₁ (by decide)).upd u₂ (by decide)
  have a₂ : s₂.gpr .r0 = BitVec.ofNat 32 (n + 1) := by
    rw [u₂.gpr, u₁.gpr, hn, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₂ (d := d) hd fun s₃ i₃ _ _ g₃ m₃ => ?_
  have m₃' : s₃.mem = s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) (BitVec.ofNat 32 (n + 1)) := by
    rw [m₃, a₂, u₂.mem, u₁.mem]
  refine (ht s₃ i₃ m₃' (by rw [g₃, a₂])).mono fun t ⟨o, z⟩ =>
    ⟨i₃.only o (by decide), by rw [o.mem, m₃'], ?_, fun r hr => ?_⟩
  · rw [MdStream.Arm.eval_ne, z, MdStream.Arm.sub_beq hn' hB]
  · rw [o.gpr r (fun e => hr (by simp at e; simp [e])), g₃, u₂.other _ (fun e => hr (by simp [e])),
      u₁.other _ (fun e => hr (by simp [e]))]

/-- `advance d o`: `[r11, #d] += 1`, compared with `[r11, #o]`. -/
theorem advance_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {d n : Nat} (hd : d + 4 ≤ 144) (hn : VG.Proof.Argon2.Arm.Derive.lw s₀ s d = BitVec.ofNat 32 n)
    (hn' : n + 1 < 2 ^ 32) {o B : Nat} (ho : o < 4096) (hB : B < 2 ^ 32)
    (hin : ∀ t : State, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → InRegions (t.rd ++ t.wr) (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 o)) 4)
    (hsrc : ∀ t : State, VG.Proof.Argon2.Arm.Derive.Inv s₀ t → t.mem = s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d))
      (BitVec.ofNat 32 (n + 1)) → VG.Proof.Argon2.Arm.Derive.lw s₀ t o = BitVec.ofNat 32 B) :
    WP isa (.block (Impl.Argon2.Arm.Derive.advance d o)) s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧
      t.mem = s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d)) (BitVec.ofNat 32 (n + 1)) ∧
      VG.Arm.eval .ne t = some (!decide (n + 1 = B)) ∧ ∀ r ∉ [Reg.r0, .r1], t.gpr r = s.gpr r := by
  unfold Impl.Argon2.Arm.Derive.advance
  refine VG.Proof.Argon2.Arm.Derive.advanceTail_ok hp h hd hn hn' hB fun t it mt at' => ?_
  refine wp_ldr ho (by rw [it.r11]) (hin t it) fun t₁ u₁ => wp_cmp (op2_reg _ _) fun u f z => WP.block_nil
    ⟨((Only.of_upd u₁).trans (Only.of_fupd f)).mono (by simp), ?_⟩
  rw [z, u₁.other _ (by decide), at', u₁.gpr,
    show t.mem.readW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 o)) 32 = VG.Proof.Argon2.Arm.Derive.lw s₀ t o from rfl, hsrc t it mt]

end

/-- The body at a lane of the filling loops. -/
structure LS (s₀ : State) (st : FillState) (pass slice lane : Nat) (s : State) : Prop where
  fb : VG.Proof.Argon2.Arm.Derive.FB s₀ st s
  pass : VG.Proof.Argon2.Arm.Derive.lw s₀ s passOff = BitVec.ofNat 32 pass
  slice : VG.Proof.Argon2.Arm.Derive.lw s₀ s sliceOff = BitVec.ofNat 32 slice
  lane : VG.Proof.Argon2.Arm.Derive.lw s₀ s laneOff = BitVec.ofNat 32 lane

theorem FS.ls {s₀ s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) : VG.Proof.Argon2.Arm.Derive.LS s₀ st pass slice lane s :=
  ⟨⟨h.inv, h.pr, h.mem⟩, h.pos.pass, h.pos.slice, h.pos.lane⟩

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- The index advanced. -/
theorem FS.next {s t : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) (it : VG.Proof.Argon2.Arm.Derive.Inv s₀ t)
    (hm : t.mem = s.mem.writeW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 indexOff)) (BitVec.ofNat 32 (index + 1))) :
    VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane (index + 1) ctr st t := by
  obtain ⟨l, b, c⟩ := VG.Proof.Argon2.Arm.Derive.loc_store hp (d := indexOff) (by decide) hm
  refine ⟨it, Prm.of_lw h.pr fun e he => l e (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl | rfl | rfl <;> decide),
    ⟨by rw [l _ (by decide) (by decide)]; exact h.pos.pass, by rw [l _ (by decide) (by decide)]; exact h.pos.slice,
      by rw [l _ (by decide) (by decide)]; exact h.pos.lane, ?_⟩, ?_, Represents.keep h.mem c⟩
  · show t.mem.readW _ 32 = _
    rw [hm, Mem.readW_writeW_self32]
  · obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h.cache
    · exact ⟨c0, by rw [l _ (by decide) (by decide)]; exact c1, .inl c2⟩
    · exact ⟨c0, by rw [l _ (by decide) (by decide)]; exact c1, .inr ⟨c3, by rw [b]; exact c4⟩⟩

/-- `setLocal d v`. -/
theorem setLocal_ok {s : State} {st : FillState} (h : VG.Proof.Argon2.Arm.Derive.FB s₀ st s) {d : Nat} (hd : d + 4 ≤ 144)
    (hd' : ∀ e ∈ [divisorOff, segLenOff, laneLenOff, strideOff], e + 4 ≤ d ∨ d + 4 ≤ e) {v : BitVec 32}
    (hv : encodable v = true) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.Arm.Derive.FB s₀ st t → VG.Proof.Argon2.Arm.Derive.lw s₀ t d = v →
      (∀ e, e + 4 ≤ 256 → (d + 4 ≤ e ∨ e + 4 ≤ d) → VG.Proof.Argon2.Arm.Derive.lw s₀ t e = VG.Proof.Argon2.Arm.Derive.lw s₀ s e) → (∀ r ∉ [Reg.r0], t.gpr r = s.gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.Arm.Derive.setLocal d v ++ is)) s Q := by
  unfold Impl.Argon2.Arm.Derive.setLocal
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm hv) fun s₁ u₁ => ?_
  have f₁ := h.of_only (Only.of_upd u₁) (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp f₁.inv (d := d) hd fun t it vt ot gt mt =>
    k t (f₁.store hp it hd hd' mt) (by rw [vt, u₁.gpr]) (fun e he hde => by rw [ot e he hde, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem])
      fun r hr => by rw [gt, u₁.other _ (fun e => hr (by simp [e]))]

/-- The block of `segmentStart`: the counter cleared, and Z in the first slice of the first pass. -/
theorem segStartBlk_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : VG.Proof.Argon2.Arm.Derive.LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa (.block (Impl.Argon2.Arm.Derive.setLocal counterOff 0 ++
      ([Impl.Argon2.Arm.Derive.ld .r0 passOff, Impl.Argon2.Arm.Derive.ld .r1 sliceOff, .dp .orr .r0 .r0 (.reg .r1),
        .cmp .r0 (.imm 0)] : List Instr))) s
      fun t => VG.Proof.Argon2.Arm.Derive.LS s₀ st pass slice lane t ∧ VG.Proof.Argon2.Arm.Derive.lw s₀ t counterOff = 0 ∧
        VG.Arm.eval .eq t = some (decide (pass = 0 ∧ slice = 0)) := by
  refine VG.Proof.Argon2.Arm.Derive.setLocal_ok hp h.fb (d := counterOff) (by decide) (by decide) (by decide) fun s₂ f₂ v₂ o₂ _ => ?_
  have L₂ : ∀ d ∈ [passOff, sliceOff, laneOff], VG.Proof.Argon2.Arm.Derive.lw s₀ s₂ d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d := fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    exact o₂ d (by rcases hd with rfl | rfl | rfl <;> decide) (by rcases hd with rfl | rfl | rfl <;> decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp f₂.inv (d := passOff) (by decide) fun s₃ u₃ =>
    VG.Proof.Argon2.Arm.Derive.wp_ldloc hp (f₂.inv.upd u₃ (by decide)) (d := sliceOff) (by decide) fun s₄ u₄ =>
    wp_orr (op2_reg _ _) fun s₅ u₅ => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ?_
  have o := (((Only.of_upd u₃).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans (Only.of_fupd f)
  have ft := f₂.of_only o (by decide)
  have m : t.mem = s₂.mem := o.mem
  refine ⟨⟨ft, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem m, L₂ _ (by simp)]; exact h.pass, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem m, L₂ _ (by simp)]; exact h.slice,
    by rw [VG.Proof.Argon2.Arm.Derive.lw_mem m, L₂ _ (by simp)]; exact h.lane⟩, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem m, v₂], ?_⟩
  rw [MdStream.Arm.eval_eq, z, u₅.gpr, u₄.other _ (by decide), u₄.gpr, u₃.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₃.mem, L₂ _ (by simp),
    L₂ _ (by simp), h.pass, h.slice, VG.Proof.Argon2.Arm.Derive.sub_zero32, VG.Proof.Argon2.Arm.Derive.or_zero hpass (by omega)]

/-- `segmentStart`: the counter cleared, and the segment's first index. -/
theorem segmentStart_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : VG.Proof.Argon2.Arm.Derive.LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.Arm.Derive.segmentStart s
      (VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane (Proof.Argon2.segmentStart pass slice) 0 st) := by
  unfold Impl.Argon2.Arm.Derive.segmentStart
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.segStartBlk_ok hp h hpass hs).mono fun s₄ ⟨f₄, c₄, z₄⟩ => ?_)
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) z₄ (fun hb => ?_) fun hb => ?_
  all_goals
    rw [← List.append_nil (Impl.Argon2.Arm.Derive.setLocal _ _)]
    refine VG.Proof.Argon2.Arm.Derive.setLocal_ok hp f₄.fb (d := indexOff) (by decide) (by decide) (by decide) fun t ft vt ot _ => WP.block_nil ?_
    have Lt : ∀ d ∈ [passOff, sliceOff, laneOff, counterOff], VG.Proof.Argon2.Arm.Derive.lw s₀ t d = VG.Proof.Argon2.Arm.Derive.lw s₀ s₄ d := fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      exact ot d (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
    refine ⟨ft.inv, ft.pr, ⟨by rw [Lt _ (by simp)]; exact f₄.pass, by rw [Lt _ (by simp)]; exact f₄.slice,
      by rw [Lt _ (by simp)]; exact f₄.lane, ?_⟩, ⟨by decide, by rw [Lt _ (by simp), c₄]; rfl, .inl rfl⟩, ft.mem⟩
    rw [vt, Proof.Argon2.segmentStart]
  · rw [ite_eq_left (of_decide_eq_true hb)]; rfl
  · rw [ite_eq_right (of_decide_eq_false hb)]; rfl

end

theorem segment_snoc (p : Spec.Argon2.Params) (pass lane slice start k : Nat) (st : FillState) :
    Proof.Argon2.segment p pass lane slice start (k + 1) st =
      Spec.Argon2.fillBlock p pass slice lane (start + k) (Proof.Argon2.segment p pass lane slice start k st) := by
  rw [Proof.Argon2.segment_append, Proof.Argon2.segment_succ, Proof.Argon2.segment_zero]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- The comparison of the segment's first index with its length. -/
theorem segCmp_ok {s : State} {pass slice lane S ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane S ctr st s) (hS : S ≤ 2) :
    WP isa (.block [Impl.Argon2.Arm.Derive.ld .r0 indexOff, Impl.Argon2.Arm.Derive.ld .r1 segLenOff,
      .cmp .r0 (.reg .r1)]) s
      fun t => VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane S ctr st t ∧ VG.Arm.eval .eq t = some (decide (S = (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen)) := by
  have sl := VG.Proof.Argon2.Arm.Derive.segLen_lt hp
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h.inv (d := indexOff) (by decide) fun t₁ u₁ =>
    VG.Proof.Argon2.Arm.Derive.wp_ldloc hp (h.inv.upd u₁ (by decide)) (d := segLenOff) (by decide) fun t₂ u₂ =>
    wp_cmp (op2_reg _ _) fun t f z => WP.block_nil ?_
  refine ⟨h.of_only (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_fupd f)) (by decide), ?_⟩
  rw [MdStream.Arm.eval_eq, z, u₂.other _ (by decide), u₁.gpr, u₂.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem, h.pr.segLen, h.pos.index,
    MdStream.Arm.sub_beq (by omega) (by omega)]

/-- One block of a segment, and the index advanced. -/
theorem segStep_ok {t : State} {pass slice lane i c : Nat} {X : FillState}
    (ht : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane i c X t) (hpass : pass < 2 ^ 32) (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hs : slice < 4)
    (hi : i < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i) :
    WP isa (.seq Impl.Argon2.Arm.Derive.fillBlock
      (.block (Impl.Argon2.Arm.Derive.advance indexOff segLenOff))) t
      fun v => VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane (i + 1) (VG.Proof.Argon2.Arm.Derive.ctrNext (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice i c)
        (Spec.Argon2.fillBlock (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice lane i X) v ∧
        VG.Arm.eval .ne v = some (!decide (i + 1 = (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen)) := by
  have sl := VG.Proof.Argon2.Arm.Derive.segLen_lt hp
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.fillBlock_ok hp ht hpass hl hs hi active).mono fun u hu => ?_)
  refine (VG.Proof.Argon2.Arm.Derive.advance_ok hp hu.inv (d := indexOff) (n := i) (by decide) hu.pos.index (by omega)
    (o := segLenOff) (B := (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen) (by decide) (by omega)
    (fun v iv => VG.Proof.Argon2.Arm.Derive.loc_in' hp iv (d := segLenOff) (by decide)) fun v iv mv => ?_).mono
    fun v ⟨iv, mv, cv, _⟩ => ⟨hu.next hp iv mv, cv⟩
  rw [(VG.Proof.Argon2.Arm.Derive.loc_store hp (d := indexOff) (by decide) mv).1 _ (by decide) (by decide), hu.pr.segLen]

/-- `segment`: a segment of the filling loops. -/
theorem segment_ok {s : State} {pass slice lane : Nat} {st : FillState} (h : VG.Proof.Argon2.Arm.Derive.LS s₀ st pass slice lane s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀) :
    WP isa Impl.Argon2.Arm.Derive.segment s
      (VG.Proof.Argon2.Arm.Derive.LS s₀ (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice 0 (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen st) pass slice lane) := by
  have s2 := hp.segLen_two
  have sl := VG.Proof.Argon2.Arm.Derive.segLen_lt hp
  have hS : Proof.Argon2.segmentStart pass slice ≤ 2 := by unfold Proof.Argon2.segmentStart; split <;> omega
  have hS2 : pass = 0 → slice = 0 → Proof.Argon2.segmentStart pass slice = 2 := fun a b => by
    unfold Proof.Argon2.segmentStart; rw [ite_eq_left ⟨a, b⟩]
  generalize hSd : Proof.Argon2.segmentStart pass slice = S at hS hS2
  rw [Proof.Argon2.segment_start _ _ _ _ _ s2, hSd]
  unfold Impl.Argon2.Arm.Derive.segment
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.segmentStart_ok hp h hpass hs).mono fun t₁ h₁ => ?_)
  rw [hSd] at h₁
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.segCmp_ok hp h₁ hS).mono fun t₃ ⟨h₃, c₃⟩ => ?_)
  refine WP.ite (decide (S = (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen)) c₃ (fun hb => ?_) fun hb => ?_
  · have hb' : S = (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen := of_decide_eq_true hb
    refine WP.block_nil ?_
    rw [show (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen - S = 0 by omega, Proof.Argon2.segment_zero]
    exact h₃.ls
  · have hb' : S < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen := by have := of_decide_eq_false hb; omega
    refine WP.loop (M := isa) (fun n t => ∃ i, n = (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen - i ∧ S ≤ i ∧ i < (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen ∧
      ∃ c, VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane i c (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice S (i - S) st) t) ?_
      ((VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen - S) t₃ ⟨S, rfl, Nat.le_refl _, hb', 0, by rw [Nat.sub_self]; exact h₃⟩
    rintro n t ⟨i, rfl, hSi, hi, c, ht⟩
    refine (VG.Proof.Argon2.Arm.Derive.segStep_ok hp ht hpass hl hs hi (by
        by_cases a : pass = 0
        · by_cases b : slice = 0
          · have := hS2 a b; omega
          · exact .inr (.inl b)
        · exact .inl a)).mono fun v ⟨hv, cv⟩ => ?_
    have eq : Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice S (i + 1 - S) st =
        Spec.Argon2.fillBlock (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice lane i (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀) pass lane slice S (i - S) st) := by
      rw [show i + 1 - S = (i - S) + 1 by omega, VG.Proof.Argon2.Arm.Derive.segment_snoc, show S + (i - S) = i by omega]
    rw [← eq] at hv
    by_cases e : i + 1 = (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen
    · refine .inl ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], ?_⟩
      rw [show (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen - S = i + 1 - S by omega]
      exact hv.ls
    · exact .inr ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], _, by omega, i + 1, rfl, by omega, by omega, _, hv⟩

end

theorem foldl_range'_snoc {α : Type} (f : α → Nat → α) (start k : Nat) (x : α) :
    (List.range' start (k + 1)).foldl f x = f ((List.range' start k).foldl f x) (start + k) := by
  rw [List.range'_concat, List.foldl_append]
  simp

/-- The body at a slice of the filling loops. -/
structure SS (s₀ : State) (st : FillState) (pass slice : Nat) (s : State) : Prop where
  fb : VG.Proof.Argon2.Arm.Derive.FB s₀ st s
  pass : VG.Proof.Argon2.Arm.Derive.lw s₀ s passOff = BitVec.ofNat 32 pass
  slice : VG.Proof.Argon2.Arm.Derive.lw s₀ s sliceOff = BitVec.ofNat 32 slice

/-- The body at a pass of the filling loops. -/
structure PS (s₀ : State) (st : FillState) (pass : Nat) (s : State) : Prop where
  fb : VG.Proof.Argon2.Arm.Derive.FB s₀ st s
  pass : VG.Proof.Argon2.Arm.Derive.lw s₀ s passOff = BitVec.ofNat 32 pass

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- A lane's segment of a slice, and the lane advanced. -/
theorem laneStep_ok {t : State} {pass slice l : Nat} {X : FillState} (ht : VG.Proof.Argon2.Arm.Derive.LS s₀ X pass slice l t)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) (hl : l < VG.Proof.Argon2.Arm.Derive.lanesN s₀) :
    WP isa (.seq Impl.Argon2.Arm.Derive.segment
      (.block (Impl.Argon2.Arm.Derive.advance laneOff (argOff 7)))) t fun v =>
      VG.Proof.Argon2.Arm.Derive.LS s₀ (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀) pass l slice 0 (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen X) pass slice (l + 1) v ∧
      VG.Arm.eval .ne v = some (!decide (l + 1 = VG.Proof.Argon2.Arm.Derive.lanesN s₀)) := by
  have hlt := hp.lanes_lt
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.segment_ok hp ht hpass hs hl).mono fun u hu => ?_)
  refine (VG.Proof.Argon2.Arm.Derive.advance_ok hp hu.fb.inv (d := laneOff) (n := l) (by decide) hu.lane (by omega) (o := argOff 7)
    (B := VG.Proof.Argon2.Arm.Derive.lanesN s₀) (by decide) (by omega) (fun v iv => iv.arg_in hp (by decide))
    fun v iv _ => iv.arg hp (by decide) |>.trans (by simp)).mono fun v ⟨iv, mv, cv, _⟩ => ⟨?_, cv⟩
  obtain ⟨lv, _, _⟩ := VG.Proof.Argon2.Arm.Derive.loc_store hp (d := laneOff) (by decide) mv
  refine ⟨hu.fb.store hp iv (d := laneOff) (by decide) (by decide) mv, ?_, ?_, ?_⟩
  · rw [lv _ (by decide) (by decide)]; exact hu.pass
  · rw [lv _ (by decide) (by decide)]; exact hu.slice
  · show v.mem.readW _ 32 = _
    rw [mv, Mem.readW_writeW_self32]

/-- `lanesLoop`: every lane's segment of a slice. -/
theorem lanes_ok {s : State} {pass slice : Nat} {st : FillState} (h : VG.Proof.Argon2.Arm.Derive.SS s₀ st pass slice s)
    (hpass : pass < 2 ^ 32) (hs : slice < 4) :
    WP isa Impl.Argon2.Arm.Derive.lanesLoop s
      (VG.Proof.Argon2.Arm.Derive.SS s₀ (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice 0 (VG.Proof.Argon2.Arm.Derive.lanesN s₀) st) pass slice) := by
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.Arm.Derive.lanesLoop
  rw [← List.append_nil (Impl.Argon2.Arm.Derive.setLocal _ _)]
  refine WP.seq (VG.Proof.Argon2.Arm.Derive.setLocal_ok hp h.fb (d := laneOff) (by decide) (by decide) (by decide)
    fun t₁ f₁ v₁ o₁ _ => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun n t => ∃ l, n = VG.Proof.Argon2.Arm.Derive.lanesN s₀ - l ∧ l < VG.Proof.Argon2.Arm.Derive.lanesN s₀ ∧
    VG.Proof.Argon2.Arm.Derive.LS s₀ (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice 0 l st) pass slice l t) ?_ (VG.Proof.Argon2.Arm.Derive.lanesN s₀) t₁
    ⟨0, by omega, hl1, f₁, by rw [o₁ _ (by decide) (by decide)]; exact h.pass,
      by rw [o₁ _ (by decide) (by decide)]; exact h.slice, v₁⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (VG.Proof.Argon2.Arm.Derive.laneStep_ok hp ht hpass hs hl).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀) pass l slice 0 (VG.Proof.Argon2.Arm.Derive.prm s₀).segmentLen
      (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice 0 l st) = Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀) pass slice 0 (l + 1) st from by
    unfold Proof.Argon2.lanes; rw [VG.Proof.Argon2.Arm.Derive.foldl_range'_snoc, Nat.zero_add]] at hv
  by_cases e : l + 1 = VG.Proof.Argon2.Arm.Derive.lanesN s₀
  · refine .inl ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], ?_⟩
    rw [← e]
    exact ⟨hv.fb, hv.pass, hv.slice⟩
  · exact .inr ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], _, by omega, l + 1, rfl, by omega, hv⟩

/-- A slice of a pass, and the slice advanced. -/
theorem sliceStep_ok {t : State} {pass j : Nat} {X : FillState} (ht : VG.Proof.Argon2.Arm.Derive.SS s₀ X pass j t)
    (hpass : pass < 2 ^ 32) (hj : j < 4) :
    WP isa (.seq Impl.Argon2.Arm.Derive.lanesLoop
      (.block (Impl.Argon2.Arm.Derive.advanceImm sliceOff 4))) t fun v =>
      VG.Proof.Argon2.Arm.Derive.SS s₀ (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀) pass j 0 (VG.Proof.Argon2.Arm.Derive.lanesN s₀) X) pass (j + 1) v ∧
      VG.Arm.eval .ne v = some (!decide (j + 1 = 4)) := by
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.lanes_ok hp ht hpass hj).mono fun u hu => ?_)
  unfold Impl.Argon2.Arm.Derive.advanceImm
  refine (VG.Proof.Argon2.Arm.Derive.advanceTail_ok hp hu.fb.inv (d := sliceOff) (n := j) (by decide) hu.slice (by omega) (B := 4)
    (by decide) fun t it _ _ => wp_cmp (op2_imm (by decide)) fun u f z =>
      WP.block_nil ⟨(Only.of_fupd f).mono (by simp), by rw [z, ‹t.gpr .r0 = _›]; rfl⟩).mono
    fun v ⟨iv, mv, cv, _⟩ => ⟨?_, cv⟩
  obtain ⟨lv, _, _⟩ := VG.Proof.Argon2.Arm.Derive.loc_store hp (d := sliceOff) (by decide) mv
  refine ⟨hu.fb.store hp iv (d := sliceOff) (by decide) (by decide) mv, ?_, ?_⟩
  · rw [lv _ (by decide) (by decide)]; exact hu.pass
  · show v.mem.readW _ 32 = _
    rw [mv, Mem.readW_writeW_self32]

/-- `slicesLoop`: one pass. -/
theorem slices_ok {s : State} {pass : Nat} {st : FillState} (h : VG.Proof.Argon2.Arm.Derive.PS s₀ st pass s) (hpass : pass < 2 ^ 32) :
    WP isa Impl.Argon2.Arm.Derive.slicesLoop s (VG.Proof.Argon2.Arm.Derive.PS s₀ (Spec.Argon2.fillPass (VG.Proof.Argon2.Arm.Derive.prm s₀) st pass) pass) := by
  unfold Impl.Argon2.Arm.Derive.slicesLoop
  rw [← Proof.Argon2.slices_pass, ← List.append_nil (Impl.Argon2.Arm.Derive.setLocal _ _)]
  refine WP.seq (VG.Proof.Argon2.Arm.Derive.setLocal_ok hp h.fb (d := sliceOff) (by decide) (by decide) (by decide)
    fun t₁ f₁ v₁ o₁ _ => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun n t => ∃ j, n = 4 - j ∧ j < 4 ∧
    VG.Proof.Argon2.Arm.Derive.SS s₀ (Proof.Argon2.slices (VG.Proof.Argon2.Arm.Derive.prm s₀) pass 0 j st) pass j t) ?_ 4 t₁
    ⟨0, rfl, by decide, f₁, by rw [o₁ _ (by decide) (by decide)]; exact h.pass, v₁⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine (VG.Proof.Argon2.Arm.Derive.sliceStep_ok hp ht hpass hj).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀) pass j 0 (VG.Proof.Argon2.Arm.Derive.lanesN s₀) (Proof.Argon2.slices (VG.Proof.Argon2.Arm.Derive.prm s₀) pass 0 j st) =
      Proof.Argon2.slices (VG.Proof.Argon2.Arm.Derive.prm s₀) pass 0 (j + 1) st from by
    unfold Proof.Argon2.slices; rw [VG.Proof.Argon2.Arm.Derive.foldl_range'_snoc, Nat.zero_add]; rfl] at hv
  by_cases e : j + 1 = 4
  · refine .inl ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], ?_⟩
    rw [show (4 : Nat) = j + 1 by omega]
    exact ⟨hv.fb, hv.pass⟩
  · exact .inr ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], _, by omega, j + 1, rfl, by omega, hv⟩

/-- A pass, and the pass advanced. -/
theorem passStep_ok {t : State} {k : Nat} {X : FillState} (ht : VG.Proof.Argon2.Arm.Derive.PS s₀ X k t) (hk : k < VG.Proof.Argon2.Arm.Derive.itersN s₀) :
    WP isa (.seq Impl.Argon2.Arm.Derive.slicesLoop
      (.block (Impl.Argon2.Arm.Derive.advance passOff (argOff 5)))) t fun v =>
      VG.Proof.Argon2.Arm.Derive.PS s₀ (Spec.Argon2.fillPass (VG.Proof.Argon2.Arm.Derive.prm s₀) X k) (k + 1) v ∧
        VG.Arm.eval .ne v = some (!decide (k + 1 = VG.Proof.Argon2.Arm.Derive.itersN s₀)) := by
  have hpl : VG.Proof.Argon2.Arm.Derive.itersN s₀ < 2 ^ 32 := (VG.Proof.Argon2.Arm.Derive.arg s₀ 5).isLt
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.slices_ok hp ht (by omega)).mono fun u hu => ?_)
  refine (VG.Proof.Argon2.Arm.Derive.advance_ok hp hu.fb.inv (d := passOff) (n := k) (by decide) hu.pass (by omega) (o := argOff 5)
    (B := VG.Proof.Argon2.Arm.Derive.itersN s₀) (by decide) hpl (fun v iv => iv.arg_in hp (by decide))
    fun v iv _ => iv.arg hp (by decide) |>.trans (by simp)).mono fun v ⟨iv, mv, cv, _⟩ => ⟨?_, cv⟩
  refine ⟨hu.fb.store hp iv (d := passOff) (by decide) (by decide) mv, ?_⟩
  show v.mem.readW _ 32 = _
  rw [mv, Mem.readW_writeW_self32]

/-- `passesLoop`: every pass. -/
theorem passes_ok {s : State} {st : FillState} (h : VG.Proof.Argon2.Arm.Derive.FB s₀ st s) :
    WP isa Impl.Argon2.Arm.Derive.passesLoop s (VG.Proof.Argon2.Arm.Derive.FB s₀ (Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀) 0 (VG.Proof.Argon2.Arm.Derive.itersN s₀) st)) := by
  have hp1 := hp.passes_pos
  unfold Impl.Argon2.Arm.Derive.passesLoop
  rw [← List.append_nil (Impl.Argon2.Arm.Derive.setLocal _ _)]
  refine WP.seq (VG.Proof.Argon2.Arm.Derive.setLocal_ok hp h (d := passOff) (by decide) (by decide) (by decide)
    fun t₁ f₁ v₁ _ _ => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun n t => ∃ k, n = VG.Proof.Argon2.Arm.Derive.itersN s₀ - k ∧ k < VG.Proof.Argon2.Arm.Derive.itersN s₀ ∧
    VG.Proof.Argon2.Arm.Derive.PS s₀ (Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀) 0 k st) k t) ?_ (VG.Proof.Argon2.Arm.Derive.itersN s₀) t₁ ⟨0, by omega, by omega, f₁, v₁⟩
  rintro n t ⟨k, rfl, hk, ht⟩
  refine (VG.Proof.Argon2.Arm.Derive.passStep_ok hp ht hk).mono fun v ⟨hv, cv⟩ => ?_
  rw [show Spec.Argon2.fillPass (VG.Proof.Argon2.Arm.Derive.prm s₀) (Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀) 0 k st) k =
      Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀) 0 (k + 1) st from by
    unfold Proof.Argon2.iterations; rw [VG.Proof.Argon2.Arm.Derive.foldl_range'_snoc, Nat.zero_add]] at hv
  by_cases e : k + 1 = VG.Proof.Argon2.Arm.Derive.itersN s₀
  · refine .inl ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], ?_⟩
    rw [← e]
    exact hv.fb
  · exact .inr ⟨by show VG.Arm.eval .ne v = _; rw [cv]; simp [e], _, by omega, k + 1, rfl, by omega, hv⟩

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.Reduce`. -/
section

/-!
# Argon2 on ARMv7: the final block and the tag

`reduce_ok`: the memory's first block becomes the XOR of every lane's last
block (`Proof.Argon2.reduction`), the other blocks kept; `finalOutput_ok`:
H′ of it to `out`, the tag (`Proof.Argon2.finish_reduction`).
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_sub wp_str op2_imm op2_reg)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2.Arm (blk ofWords blk_of_words xor_words)
open VG.Proof.Sha512.Arm (Only A)
open VG.Impl.Argon2.Arm.Derive (laneOff laneLenOff argOff divisorOff segLenOff strideOff)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- `n` stores of `r0 = 0` to `[r3, #4k]`, `r3` the memory matrix. -/
theorem memZeros_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (hx : s.gpr .r3 = VG.Proof.Argon2.Arm.Derive.memP s₀) (ha : s.gpr .r0 = 0) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).map fun k => Instr.str .r0 .r3 (4 * k))) s fun t =>
      VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ t.gpr = s.gpr ∧ Frame [⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) 0, 1024⟩] s.mem t.mem ∧
      ∀ i < n, VG.Proof.Argon2.Arm.Derive.mw s₀ t.mem (4 * i) = 0
  | 0, _ => WP.block_nil ⟨h, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have b1 := VG.Proof.Argon2.Arm.Derive.blocks_pos hp
    have hb := VG.Proof.Argon2.Arm.Derive.blocks22 hp
    have hm := hp.mem_fits
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append ((VG.Proof.Argon2.Arm.Derive.memZeros_ok h hx ha n (by omega)).mono fun t ⟨it, gt, ft, wt⟩ => ?_)
    have ea : State.addr (t.gpr .r3 + BitVec.ofNat 32 (4 * n)) = A (VG.Proof.Argon2.Arm.Derive.memP s₀) (4 * n) := by rw [gt, hx]
    have ea' : A (VG.Proof.Argon2.Arm.Derive.memP s₀) (4 * n) = VG.Proof.Argon2.Arm.Derive.memB s₀ + BitVec.ofNat 64 (4 * n) := VG.Proof.Argon2.Arm.Derive.mem_addr' hp (by omega)
    have hc : (VG.Proof.Argon2.Arm.Derive.memR s₀).Contains (A (VG.Proof.Argon2.Arm.Derive.memP s₀) (4 * n)) 4 := by
      rw [ea']; exact Offset.contains_base _ (by omega) (by omega)
    have hc' : (⟨matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) 0, 1024⟩ : Region).Contains (A (VG.Proof.Argon2.Arm.Derive.memP s₀) (4 * n)) 4 := by
      rw [ea', show matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) 0 = VG.Proof.Argon2.Arm.Derive.memB s₀ by simp [matrixCell]]
      exact Offset.contains_base _ (by omega) (by omega)
    refine wp_str (by omega) ea ⟨_, by rw [it.wr]; exact VG.Proof.Argon2.Arm.Derive.mem_mem hp, hc⟩ fun t₁ u₁ => WP.block_nil
      ⟨it.store (R := VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp) hc u₁, by rw [u₁.gpr, gt], ?_, fun i hi => ?_⟩
    · rw [u₁.mem]
      exact ft.writeW (List.mem_singleton_self _) _ hc'
    · rw [u₁.mem, gt, show 4 * n = 0 + 4 * n by omega, show 4 * i = 0 + 4 * i by omega,
        VG.Proof.Argon2.Arm.Derive.mw_store hp _ (by omega) (by omega) (by omega), ha]
      by_cases e : 0 + 4 * n = 0 + 4 * i
      · rw [ite_eq_left e]
      · rw [ite_eq_right e, show 0 + 4 * i = 4 * i by omega]; exact wt i (by omega)

end

theorem reduction_snoc (p : Spec.Argon2.Params) (M : Array Block) (l : Nat) (acc : Block) :
    Proof.Argon2.reduction p M 0 (l + 1) acc =
      xorBlock (Proof.Argon2.reduction p M 0 l acc) (M[Proof.Argon2.lastIndex p l]?.getD zeroBlock) := by
  unfold Proof.Argon2.reduction
  rw [VG.Proof.Argon2.Arm.Derive.foldl_range'_snoc, Nat.zero_add]

/-- The state of the reduction after `l` lanes. -/
structure RI (s₀ : State) (M : Array Block) (l : Nat) (s : State) : Prop where
  inv : VG.Proof.Argon2.Arm.Derive.Inv s₀ s
  pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s
  lane : VG.Proof.Argon2.Arm.Derive.lw s₀ s laneOff = BitVec.ofNat 32 l
  first : blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) 0) = Proof.Argon2.reduction (VG.Proof.Argon2.Arm.Derive.prm s₀) M 0 l zeroBlock
  rest : ∀ k < (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks, k ≠ 0 → blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) k) = M[k]?.getD zeroBlock

theorem cell0 (s₀ : State) : matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) 0 = VG.Proof.Argon2.Arm.Derive.memB s₀ := by simp [matrixCell]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- One lane of the reduction. -/
theorem reduceLane_ok {s : State} {M : Array Block} {l : Nat} (h : VG.Proof.Argon2.Arm.Derive.RI s₀ M l s) (hl : l < VG.Proof.Argon2.Arm.Derive.lanesN s₀) :
    WP isa (.block (Impl.Argon2.Arm.Derive.reduceLane ++
      Impl.Argon2.Arm.Derive.advance laneOff (argOff Impl.Argon2.Arm.Derive.lanesArg)))
      s fun t => VG.Proof.Argon2.Arm.Derive.RI s₀ M (l + 1) t ∧ VG.Arm.eval .ne t = some (!decide (l + 1 = VG.Proof.Argon2.Arm.Derive.lanesN s₀)) := by
  have L8 := VG.Proof.Argon2.Arm.Derive.laneLen_ge hp
  have hlt := hp.lanes_lt
  have hb : VG.Proof.Argon2.Arm.Derive.blocksN s₀ = (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks := hp.blocks
  obtain ⟨cl, _⟩ := VG.Proof.Argon2.Arm.Derive.cell_fits hp hl (col := (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) (by omega)
  have last : Proof.Argon2.lastIndex (VG.Proof.Argon2.Arm.Derive.prm s₀) l = l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + ((VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) := by
    unfold Proof.Argon2.lastIndex; rw [Nat.succ_mul]; omega
  have ne0 : l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + ((VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) ≠ 0 := by omega
  unfold Impl.Argon2.Arm.Derive.reduceLane Impl.Argon2.Arm.Derive.writeBlock
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h.inv (d := laneOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => wp_sub (op2_imm (by decide)) fun s₃ u₃ => ?_
  have i₃ := (i₁.upd u₂ (by decide)).upd u₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine VG.Proof.Argon2.Arm.Derive.blockAddr_ok hp i₃ (h.pr.of_mem m₃) hl (col := (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.lane])
    (by rw [u₃.gpr, u₂.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem, h.pr.laneLen, VG.Proof.Argon2.Arm.Derive.ofNat_pred (by omega) rfl]) fun s₄ a₄ k₄ => ?_
  have i₄ := i₃.only k₄ (by decide)
  refine wp_mov (op2_reg _ _) fun s₅ u₅ => ?_
  have i₅ := i₄.upd u₅ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₅ (i := 13) (by decide) fun s₆ u₆ => ?_
  have i₆ := i₅.upd u₆ (by decide)
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, k₄.mem, m₃]
  have hm := hp.mem_fits
  have b22 := VG.Proof.Argon2.Arm.Derive.blocks22 hp
  have b1 := VG.Proof.Argon2.Arm.Derive.blocks_pos hp
  generalize hc : l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + ((VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) = c at cl a₄ ne0 last
  have hc' : c * 1024 + 1024 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024 := by omega_using [cl]
  have sx : s₆.gpr .r1 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (c * 1024) := by
    rw [u₆.other _ (by decide), u₅.gpr, a₄]
  have dx : s₆.gpr .r3 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (0 * 1024) := by
    rw [u₆.gpr]; simp
  refine WP.block_append ((VG.Proof.Argon2.Arm.Derive.writeWords_ok hp i₆ (cur := 0) b1 true sx
    (by rw [VG.Proof.Argon2.Arm.Derive.add_nat (by omega_using [hc', hm])]; omega_using [hc', hm])
    ⟨VG.Proof.Argon2.Arm.Derive.memR s₀, by simp, c * 1024, VG.Proof.Argon2.Arm.Derive.cell_addr hp cl, hc'⟩
    (by rw [VG.Proof.Argon2.Arm.Derive.cell_addr hp cl]; exact VG.Proof.Argon2.Arm.Derive.cell_other hp cl b1 ne0) dx 256 (Nat.le_refl _)).mono
    fun t₇ ⟨i₇, g₇, f₇, w₇⟩ => ?_)
  have lt₇ : ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.Arm.Derive.lw s₀ t₇ d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d := fun d hd => by
    rw [← VG.Proof.Argon2.Arm.Derive.lw_mem m₆ d]
    exact f₇.readW (r := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Proof.Argon2.Arm.Derive.loc_disj hp hd (VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).sub_right (VG.Proof.Argon2.Arm.Derive.cell_in_mem b1)) (by decide)
  refine (VG.Proof.Argon2.Arm.Derive.advance_ok hp i₇ (d := laneOff) (n := l) (by decide) (by rw [lt₇ _ (by decide)]; exact h.lane)
    (by omega) (o := argOff 7) (B := VG.Proof.Argon2.Arm.Derive.lanesN s₀) (by decide) (by omega) (fun v iv => iv.arg_in hp (by decide))
    fun v iv _ => iv.arg hp (by decide) |>.trans (by simp)).mono fun t ⟨it, mt, ct, _⟩ => ⟨?_, ct⟩
  obtain ⟨lt, _, ct⟩ := VG.Proof.Argon2.Arm.Derive.loc_store hp (d := laneOff) (by decide) mt
  have new : blockAt t₇.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) 0) =
      xorBlock (blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) c)) (blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) 0)) := by
    rw [VG.Proof.Argon2.Arm.Derive.cell_blk hp _ b1, VG.Proof.Argon2.Arm.Derive.cell_blk hp _ b1, VG.Proof.Argon2.Arm.Derive.cell_blk hp _ cl,
      blk_of_words (f := fun i => VG.Proof.Argon2.Arm.Derive.mw s₀ s.mem (c * 1024 + 4 * i) ^^^ VG.Proof.Argon2.Arm.Derive.mw s₀ s.mem (0 * 1024 + 4 * i)) fun i hi => by
        rw [← VG.Proof.Argon2.Arm.Derive.mw, w₇ i hi, ite_eq_left hi, ite_eq_left (rfl : true = true), m₆, VG.Proof.Argon2.Arm.Derive.A_shift],
      blk_of_words (m := s.mem) (B := VG.Proof.Argon2.Arm.Derive.memP s₀) (o := c * 1024) (f := fun i => VG.Proof.Argon2.Arm.Derive.mw s₀ s.mem (c * 1024 + 4 * i))
        fun _ _ => rfl,
      blk_of_words (m := s.mem) (B := VG.Proof.Argon2.Arm.Derive.memP s₀) (o := 0 * 1024) (f := fun i => VG.Proof.Argon2.Arm.Derive.mw s₀ s.mem (0 * 1024 + 4 * i))
        fun _ _ => rfl, xor_words]
  refine ⟨it, Prm.of_lw h.pr fun d hd => ?_, ?_, ?_, fun k hk k0 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    have hd4 : d + 4 ≤ 144 := by rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [lt d (by omega) (by rcases hd with rfl | rfl | rfl | rfl <;> decide), lt₇ d hd4]
  · show t.mem.readW _ 32 = _
    rw [mt, Mem.readW_writeW_self32]
  · rw [ct _ (by rw [← hb]; exact b1), new, h.first, h.rest _ (by rw [← hb]; exact cl) ne0, VG.Proof.Argon2.Arm.Derive.reduction_snoc,
      Proof.Argon2.xorBlock_comm, last]
  · rw [ct _ hk, VG.Proof.Argon2.Arm.Derive.blockAt_keep f₇ (fun r hr => ?_), m₆, h.rest k hk k0]
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.Argon2.Arm.Derive.cell_other hp (by rw [hb]; exact hk) b1 k0

/-- The first block of `reduce`: the memory's first block cleared, and the lane `0`. -/
theorem reduceStart_ok {s : State} {M : Array Block} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s)
    (hm : Represents s.mem (VG.Proof.Argon2.Arm.Derive.memB s₀) (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks M) :
    WP isa (.block (Impl.Argon2.Arm.Derive.reduceClear ++ Impl.Argon2.Arm.Derive.setLocal laneOff 0)) s
      (VG.Proof.Argon2.Arm.Derive.RI s₀ M 0) := by
  have b1 := VG.Proof.Argon2.Arm.Derive.blocks_pos hp
  have hb : VG.Proof.Argon2.Arm.Derive.blocksN s₀ = (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.Arm.Derive.reduceClear Impl.Argon2.Arm.Derive.setLocal
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have i₂ := (h.upd u₁ (by decide)).upd u₂ (by decide)
  refine WP.block_append ((VG.Proof.Argon2.Arm.Derive.memZeros_ok hp i₂ (by rw [u₂.other _ (by decide), u₁.gpr]) u₂.gpr 256
    (Nat.le_refl _)).mono fun s₃ ⟨i₃, _, f₃, z₃⟩ => ?_)
  refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₄ (d := laneOff) (by decide) fun s₅ i₅ v₅ _ _ m₅ => WP.block_nil ?_
  obtain ⟨l₅, _, c₅⟩ := VG.Proof.Argon2.Arm.Derive.loc_store hp (d := laneOff) (by decide) m₅
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have lt₃ : ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.Arm.Derive.lw s₀ s₃ d = VG.Proof.Argon2.Arm.Derive.lw s₀ s d := fun d hd => by
    rw [← VG.Proof.Argon2.Arm.Derive.lw_mem m₂ d]
    exact f₃.readW (r := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 d), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Proof.Argon2.Arm.Derive.loc_disj hp hd (VG.Proof.Argon2.Arm.Derive.memR s₀) (by simp)).sub_right (VG.Proof.Argon2.Arm.Derive.cell_in_mem b1)) (by decide)
  refine ⟨i₅, Prm.of_lw pr fun d hd => ?_, by rw [v₅, u₄.gpr]; rfl, ?_, fun k hk k0 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    have hd4 : d + 4 ≤ 144 := by rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [l₅ d (by omega) (by rcases hd with rfl | rfl | rfl | rfl <;> decide), VG.Proof.Argon2.Arm.Derive.lw_mem u₄.mem, lt₃ d hd4]
  · rw [c₅ _ (by rw [← hb]; exact b1), u₄.mem, VG.Proof.Argon2.Arm.Derive.cell_blk hp _ b1,
      blk_of_words (f := fun _ => 0) fun i hi => by rw [← VG.Proof.Argon2.Arm.Derive.mw, Nat.zero_mul, Nat.zero_add]; exact z₃ i hi,
      VG.Proof.Argon2.Arm.Derive.ofWords_zero]
    rfl
  · rw [c₅ _ hk, u₄.mem, VG.Proof.Argon2.Arm.Derive.blockAt_keep f₃ (fun r hr => ?_), m₂, hm.block k hk]
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.Argon2.Arm.Derive.cell_other hp (by rw [hb]; exact hk) b1 k0

/-- `reduce`: the XOR of every lane's last block, to the memory's first block. -/
theorem reduce_ok {s : State} {M : Array Block} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s)
    (hm : Represents s.mem (VG.Proof.Argon2.Arm.Derive.memB s₀) (VG.Proof.Argon2.Arm.Derive.prm s₀).blocks M) :
    WP isa Impl.Argon2.Arm.Derive.reduce s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ t ∧
      blockAt t.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) 0) = Proof.Argon2.reduction (VG.Proof.Argon2.Arm.Derive.prm s₀) M 0 (VG.Proof.Argon2.Arm.Derive.lanesN s₀) zeroBlock := by
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.Arm.Derive.reduce
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.reduceStart_ok hp h pr hm).mono fun s₅ start => ?_)
  refine WP.loop (M := isa) (fun n t => ∃ l, n = VG.Proof.Argon2.Arm.Derive.lanesN s₀ - l ∧ l < VG.Proof.Argon2.Arm.Derive.lanesN s₀ ∧ VG.Proof.Argon2.Arm.Derive.RI s₀ M l t) ?_ (VG.Proof.Argon2.Arm.Derive.lanesN s₀) s₅
    ⟨0, by omega, hl1, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (VG.Proof.Argon2.Arm.Derive.reduceLane_ok hp ht hl).mono fun u ⟨hu, cu⟩ => ?_
  by_cases e : l + 1 = VG.Proof.Argon2.Arm.Derive.lanesN s₀
  · refine .inl ⟨by show VG.Arm.eval .ne u = _; rw [cu]; simp [e], hu.inv, hu.pr, ?_⟩
    rw [hu.first, e]
  · exact .inr ⟨by show VG.Arm.eval .ne u = _; rw [cu]; simp [e], _, by omega, l + 1, rfl, by omega, hu⟩

/-- `finalOutput`: H′ of the memory's first block, to `out`. -/
theorem finalOutput_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) :
    WP isa Impl.Argon2.Arm.Derive.finalOutput s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.outP s₀)) (VG.Proof.Argon2.Arm.Derive.outL s₀) =
        Spec.Argon2.hPrime (VG.Proof.Argon2.Arm.Derive.outL s₀) (Spec.Argon2.serialize (blockAt s.mem (matrixCell (VG.Proof.Argon2.Arm.Derive.memB s₀) 0))) := by
  have b1 := VG.Proof.Argon2.Arm.Derive.blocks_pos hp
  have hm := hp.mem_fits
  have ho := hp.out_fits
  have tg := hp.tag_ge
  unfold Impl.Argon2.Arm.Derive.finalOutput
  refine WP.seq (VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => ?_)
  have i₁ := h.upd u₁ (by decide)
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₂ (i := 16) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₃ (i := 17) (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₄ (i := 15) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have i₅ := i₄.upd u₅ (by decide)
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have si : s₅.gpr .r0 = VG.Proof.Argon2.Arm.Derive.memP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ax : (s₅.gpr .r1).toNat = 1024 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl
  have di : s₅.gpr .r2 = VG.Proof.Argon2.Arm.Derive.outP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have cx : (s₅.gpr .r3).toNat = VG.Proof.Argon2.Arm.Derive.outL s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr]
  refine VG.Proof.Argon2.Arm.Derive.hcall_ok hp i₅ u₅.gpr
    ⟨VG.Proof.Argon2.Arm.Derive.memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024; omega⟩
    (by rw [si, ax]; omega) ⟨VG.Proof.Argon2.Arm.Derive.outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + VG.Proof.Argon2.Arm.Derive.outL s₀ ≤ VG.Proof.Argon2.Arm.Derive.outL s₀; omega⟩
    (by rw [di, cx]; exact ho) (by rw [cx]; omega) fun t it _ _ post => ⟨it, ?_⟩
  rw [← di, ← cx, post, cx, ax, si, m₅, VG.Proof.Argon2.Arm.Derive.cell0, Proof.Argon2.serialize_blockAt]

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.Correct`. -/
section

/-!
# Argon2 on ARMv7: the derivation is correct

`body_ok`: the body computes the parameters and H₀, initializes and fills
the memory, and writes the tag (`Spec.Argon2.derive`) to `out`; `correct`:
the whole function, in its frames, keeps the ABI's registers too.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Spec.Blake2 (bytesAt)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem body_ok : WP isa Impl.Argon2.Arm.Derive.body (VG.Proof.Argon2.Arm.Derive.entry s₀) fun t => VG.Proof.Argon2.Arm.Derive.BodyDone s₀ t ∧
    t.wr = (VG.Proof.Argon2.Arm.Derive.entry s₀).wr ∧ bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.outP s₀)) (VG.Proof.Argon2.Arm.Derive.outL s₀) =
      Spec.Argon2.derive (VG.Proof.Argon2.Arm.Derive.prm s₀) (VG.Proof.Argon2.Arm.Derive.pwB s₀) (VG.Proof.Argon2.Arm.Derive.saltB s₀) (VG.Proof.Argon2.Arm.Derive.secB s₀) (VG.Proof.Argon2.Arm.Derive.adB s₀) := by
  unfold Impl.Argon2.Arm.Derive.body
  refine WP.seq ?_
  rw [← List.append_nil (Instr.addSp .r11 0 :: Impl.Argon2.Arm.Derive.parameters)]
  refine VG.Proof.Argon2.Arm.Derive.parameters_ok hp fun s₁ i₁ p₁ => WP.block_nil ?_
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.code_ok hp i₁ p₁).mono fun s₂ ⟨i₂, p₂, b₂⟩ => ?_)
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.memoryInit_ok hp i₂ p₂ b₂).mono fun s₃ ⟨i₃, p₃, m₃⟩ => ?_)
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.passes_ok hp (st := Spec.Argon2.initMemory (VG.Proof.Argon2.Arm.Derive.prm s₀)
    (Spec.Argon2.initialHash (VG.Proof.Argon2.Arm.Derive.prm s₀) (VG.Proof.Argon2.Arm.Derive.pwB s₀) (VG.Proof.Argon2.Arm.Derive.saltB s₀) (VG.Proof.Argon2.Arm.Derive.secB s₀) (VG.Proof.Argon2.Arm.Derive.adB s₀))) ⟨i₃, p₃, m₃⟩).mono
    fun s₄ f₄ => ?_)
  rw [show VG.Proof.Argon2.Arm.Derive.itersN s₀ = (VG.Proof.Argon2.Arm.Derive.prm s₀).passes from rfl, Proof.Argon2.iterations_fill] at f₄
  refine WP.seq ((VG.Proof.Argon2.Arm.Derive.reduce_ok hp f₄.inv f₄.pr f₄.mem).mono fun s₅ ⟨i₅, _, b₅⟩ => ?_)
  refine (VG.Proof.Argon2.Arm.Derive.finalOutput_ok hp i₅).mono fun t ⟨it, ot⟩ => ⟨it.done hp, it.wr, ?_⟩
  rw [ot, b₅, Spec.Argon2.derive, Proof.Argon2.finish_reduction]
  rfl

theorem correct : WP isa Impl.Argon2.Arm.Derive.derive s₀ fun t => abiPreserved s₀ t ∧ deriveArm.post s₀ t :=
  VG.Proof.Argon2.Arm.Derive.frames_ok (by have := hp.sp_lo; omega) (VG.Proof.Argon2.Arm.Derive.body_ok hp) fun t u q m => by
    show bytesAt u.mem _ _ = _
    rw [m]; exact q

end

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.CTBase`. -/
section

/-!
# Argon2 on ARMv7: the derivation's taint analysis

The body reads its arguments, which the caller's frame and the first frame
hold above the locals, through `r11`. So its pieces are analysed from states
with more permissions (`RelCT.taintW`, by `Exec.widen`): the locals, the
saved registers and the arguments as one writable region of 256 bytes at `r11`,
the memory matrix, `scratch` and the output (`wide`). `τB sl rs` makes `r11`,
the registers `rs`, the arguments and the locals' slots `sl` public;
`agreeB` gives it from what two runs of the body are known to share.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Spec.Blake2 (bytesAt)

/-- Two runs leak the same trace if, from states with more permissions, the
taint analysis proves it. -/
theorem RelCT.taintW {P : State → State → Prop} {c : Prog isa} (τ : VG.Arm.Taint.T)
    (hp : ∀ s₁ s₂, P s₁ s₂ → ∃ w₁ w₂, Covers s₁.wr w₁ ∧ Covers s₂.wr w₂ ∧
      VG.Arm.Taint.Agree τ (s₁.withRegions s₁.rd w₁) (s₂.withRegions s₂.rd w₂))
    {hc : VG.Taint.Hint VG.Arm.Taint.T} (h : (VG.Taint.check taint τ c hc).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨w₁, w₂, c₁, c₂, ag⟩ := hp _ _ hP
  have e₁' := Exec.widen e₁ (Covers.append (Covers.refl _) c₁) c₁
  have e₂' := Exec.widen e₂ (Covers.append (Covers.refl _) c₂) c₂
  exact ⟨((VG.RelCT.taint (A := taint) (P := fun a b => a = s₁.withRegions s₁.rd w₁ ∧
    b = s₂.withRegions s₂.rd w₂) τ (fun _ _ ⟨h₁, h₂⟩ => by subst h₁ h₂; exact ag) h) _ _ _ _ _ _
    ⟨rfl, rfl⟩ e₁' e₂').1, trivial⟩

/-- A block of one instruction that touches no memory leaks nothing. -/
theorem RelCT.quiet {P : State → State → Prop} {i : Instr} (hi : ∀ s, addrs i s = []) :
    RelCT isa P (.block [i]) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock] at e₁ e₂
  split at e₁ <;> split at e₂ <;> simp_all [isa]

/-! ## The regions -/

/-- The regions the taint analysis of the body knows: the locals, saved
registers and arguments, the memory matrix, `scratch` and the output. -/
def wide (s₀ : State) : List Region :=
  [⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀), 256⟩, VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀]

/-- The taint state of the body, with the locals' slots `sl` and the registers
`rs` public. -/
def τB (sl : List (Nat × Nat × Nat)) (rs : List Reg := []) : VG.Arm.Taint.T :=
  { regs := .ofList (.r11 :: rs), flags := false, lens := [256, 1024, 16384, 0], bases := [(.r11, 0)],
    slots := sl ++ [(0, 184, 72)] }

/-- A region of two parts, each apart from `R`. -/
theorem disj_union {x : Addr} {n m : Nat} {R : Region} (hfit : n + m ≤ 2 ^ 64)
    (h₁ : Region.Disjoint ⟨x, n⟩ R) (h₂ : Region.Disjoint ⟨x + BitVec.ofNat 64 n, m⟩ R) :
    Region.Disjoint ⟨x, n + m⟩ R := by
  intro a ha hb
  simp only [Region.Contains] at ha
  by_cases hk : (a - x).toNat < n
  · exact h₁ a (by simp only [Region.Contains]; omega) hb
  · refine h₂ a ?_ hb
    simp only [Region.Contains]
    have := (Offset.lt_iff a x (d := n) (n := m) hfit).mpr ⟨by omega, by omega⟩
    omega

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- The 256 bytes at `E`: the locals, the saved registers and the arguments. -/
theorem big_disj {R : Region} (hR : R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀]) :
    Region.Disjoint ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀), 256⟩ R := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := VG.Proof.Argon2.Arm.Derive.E_nat hp
  have e0 : (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat = s₀.sp.toNat := rfl
  have hS : R ∈ [VG.Proof.Argon2.Arm.Derive.pwR s₀, VG.Proof.Argon2.Arm.Derive.saltR s₀, VG.Proof.Argon2.Arm.Derive.secR s₀, VG.Proof.Argon2.Arm.Derive.adR s₀, VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.scrR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl <;> simp
  have st : Region.Sub ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀), 200⟩ (VG.Proof.Argon2.Arm.Derive.stkR0 s₀) := by
    simpa using VG.Proof.Argon2.Arm.Derive.frame_stk hp (d := 0) (n := 200) (by decide)
  have sa : Region.Sub ⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀) + BitVec.ofNat 64 200, 56⟩ (VG.Proof.Argon2.Arm.Derive.argR s₀) := by
    rw [← addr_add (by have := VG.Proof.Argon2.Arm.Derive.E_hi hp; omega)]
    show Region.Sub _ ⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 56⟩
    have eE : (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 200).toNat = (VG.Proof.Argon2.Arm.Derive.E s₀).toNat + 200 := VG.Proof.Argon2.Arm.Derive.add_nat (by omega)
    have eS : (s₀.sp + BitVec.ofNat 32 (4 * 0)).toNat = s₀.sp.toNat + 4 * 0 := VG.Proof.Argon2.Arm.Derive.add_nat (by omega)
    exact VG.Proof.Argon2.Arm.Derive.sub32 (by rw [eE, eS]; omega) (by rw [eE, eS]; omega)
  exact VG.Proof.Argon2.Arm.Derive.disj_union (n := 200) (m := 56) (by decide) ((hp.stk_all R hS).sub_left st)
    ((hp.ro_w _ (by simp) R (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢; exact hR)).sub_left sa)

/-- A range of the 256 bytes at `E`, as an offset. -/
theorem in_big {x : BitVec 32} {n : Nat} (h₁ : (VG.Proof.Argon2.Arm.Derive.E s₀).toNat ≤ x.toNat) (h₂ : x.toNat + n ≤ (VG.Proof.Argon2.Arm.Derive.E s₀).toNat + 256) :
    ∃ off, State.addr x = State.addr (VG.Proof.Argon2.Arm.Derive.E s₀) + BitVec.ofNat 64 off ∧ off + n ≤ 256 := by
  have hE := VG.Proof.Argon2.Arm.Derive.E_hi hp
  refine ⟨x.toNat - (VG.Proof.Argon2.Arm.Derive.E s₀).toNat, ?_, by omega⟩
  rw [← addr_add (by omega)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.Argon2.Arm.Derive.add_nat (by omega)]; omega

theorem covers_wide : Covers (VG.Proof.Argon2.Arm.Derive.entry s₀).wr (VG.Proof.Argon2.Arm.Derive.wide s₀) := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := VG.Proof.Argon2.Arm.Derive.E_nat hp
  have e0 : (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat = s₀.sp.toNat := rfl
  have s1 := VG.Proof.Argon2.Arm.Derive.S1_nat hp
  have s2 := VG.Proof.Argon2.Arm.Derive.sp2 (s₀ := s₀) (by omega)
  refine Covers.of_sub fun r hr => ?_
  simp only [VG.Proof.Argon2.Arm.Derive.entry, allocated, pushed_wr, List.mem_cons] at hr
  have big : ∀ x : BitVec 32, ∀ n, (VG.Proof.Argon2.Arm.Derive.E s₀).toNat ≤ x.toNat → x.toNat + n ≤ (VG.Proof.Argon2.Arm.Derive.E s₀).toNat + 256 →
      ∃ r' ∈ VG.Proof.Argon2.Arm.Derive.wide s₀, ∃ off, (⟨State.addr x, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
        off + (⟨State.addr x, n⟩ : Region).len ≤ r'.len := fun x n h₁ h₂ => by
    obtain ⟨off, e, l⟩ := VG.Proof.Argon2.Arm.Derive.in_big hp h₁ h₂
    exact ⟨⟨State.addr (VG.Proof.Argon2.Arm.Derive.E s₀), 256⟩, by simp [VG.Proof.Argon2.Arm.Derive.wide], off, e, l⟩
  have f0 : ((pushed VG.Proof.Argon2.Arm.Derive.savedRegs (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀)).sp - BitVec.ofNat 32 144).toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 200 := by
    rw [VG.Arm.FrameStack.sub_toNat' (sp := (pushed VG.Proof.Argon2.Arm.Derive.savedRegs (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀)).sp) (k := 144) (by omega), s2]
    omega
  have f1 : ((pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length)).toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 56 := by
    rw [VG.Arm.FrameStack.sub_toNat' (sp := (pushed VG.Proof.Argon2.Arm.Derive.argRegs s₀).sp) (k := 4 * savedRegs.length)
      (by simp only [List.length_cons, List.length_nil]; omega), s1]
    simp only [List.length_cons, List.length_nil]; omega
  have f2 : (s₀.sp - BitVec.ofNat 32 (4 * argRegs.length)).toNat = (VG.Proof.Argon2.Arm.Derive.E0 s₀).toNat - 16 := by
    rw [VG.Arm.FrameStack.sub_toNat' (sp := s₀.sp) (k := 4 * argRegs.length)
      (by simp only [List.length_cons, List.length_nil]; omega)]
    simp only [List.length_cons, List.length_nil]
  rcases hr with rfl | rfl | rfl | hr
  · exact big _ _ (by rw [f0]; omega) (by rw [f0]; omega)
  · exact big _ _ (by rw [f1]; omega) (by rw [f1]; simp only [List.length_cons, List.length_nil]; omega)
  · exact big _ _ (by rw [f2]; omega) (by rw [f2]; simp only [List.length_cons, List.length_nil]; omega)
  · rw [hp.wr] at hr
    exact ⟨r, by simp only [VG.Proof.Argon2.Arm.Derive.wide, List.mem_cons] at hr ⊢; simp at hr; rcases hr with h | h | h <;> simp [h],
      0, by simp, by simp⟩

end

/-- What two runs share: the stack pointer and the arguments. -/
def Pub2 (s₀₁ s₀₂ : State) : Prop := VG.Proof.Argon2.Arm.Derive.E0 s₀₁ = VG.Proof.Argon2.Arm.Derive.E0 s₀₂ ∧ ∀ i < 18, VG.Proof.Argon2.Arm.Derive.arg s₀₁ i = VG.Proof.Argon2.Arm.Derive.arg s₀₂ i

theorem Pub2.E {s₀₁ s₀₂ : State} (h : VG.Proof.Argon2.Arm.Derive.Pub2 s₀₁ s₀₂) : VG.Proof.Argon2.Arm.Derive.E s₀₁ = VG.Proof.Argon2.Arm.Derive.E s₀₂ := by
  show VG.Proof.Argon2.Arm.Derive.E0 s₀₁ - BitVec.ofNat 32 200 = VG.Proof.Argon2.Arm.Derive.E0 s₀₂ - BitVec.ofNat 32 200
  rw [h.1]

theorem Pub2.wide_eq {s₀₁ s₀₂ : State} (h : VG.Proof.Argon2.Arm.Derive.Pub2 s₀₁ s₀₂) : VG.Proof.Argon2.Arm.Derive.wide s₀₁ = VG.Proof.Argon2.Arm.Derive.wide s₀₂ := by
  unfold VG.Proof.Argon2.Arm.Derive.wide
  rw [h.E, show VG.Proof.Argon2.Arm.Derive.memR s₀₁ = VG.Proof.Argon2.Arm.Derive.memR s₀₂ by simp only [VG.Proof.Argon2.Arm.Derive.memR, VG.Proof.Argon2.Arm.Derive.memP, VG.Proof.Argon2.Arm.Derive.blocksN, h.2 13 (by decide), h.2 14 (by decide)],
    show VG.Proof.Argon2.Arm.Derive.scrR s₀₁ = VG.Proof.Argon2.Arm.Derive.scrR s₀₂ by simp only [VG.Proof.Argon2.Arm.Derive.scrR, VG.Proof.Argon2.Arm.Derive.scrP, h.2 15 (by decide)],
    show VG.Proof.Argon2.Arm.Derive.outR s₀₁ = VG.Proof.Argon2.Arm.Derive.outR s₀₂ by simp only [VG.Proof.Argon2.Arm.Derive.outR, VG.Proof.Argon2.Arm.Derive.outP, VG.Proof.Argon2.Arm.Derive.outL, h.2 16 (by decide), h.2 17 (by decide)]]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem wf_wide (sl : List (Nat × Nat × Nat)) (rs : List Reg) {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) :
    VG.Arm.Taint.Wf (VG.Proof.Argon2.Arm.Derive.τB sl rs) (s.withRegions s.rd (VG.Proof.Argon2.Arm.Derive.wide s₀)) := by
  have hE := VG.Proof.Argon2.Arm.Derive.E_hi hp
  have b1 := VG.Proof.Argon2.Arm.Derive.blocks_pos hp
  have hm := hp.mem_fits
  have hs := hp.scr_fits
  have ho := hp.out_fits
  refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp' => ?_, fun h0 => absurd h0 (Nat.lt_irrefl 0),
    fun _ h' => (List.not_mem_nil h').elim⟩
  · simp only [State.withRegions_wr, VG.Proof.Argon2.Arm.Derive.wide, VG.Proof.Argon2.Arm.Derive.τB]
    refine .cons (by simp) (.cons ?_ (.cons (by simp) (.cons (by simp) .nil)))
    show 1024 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024; omega
  · simp only [State.withRegions_wr, VG.Proof.Argon2.Arm.Derive.wide]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons (fun _ h => (List.not_mem_nil h).elim) .nil)))
    · intro r hr; exact VG.Proof.Argon2.Arm.Derive.big_disj hp hr
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hp.mem_scr, hp.mem_out]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hp.scr_out
  · simp only [State.withRegions_wr, VG.Proof.Argon2.Arm.Derive.wide, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl) <;> simp only [MdStream.Arm.addr_toNat]
    · omega
    · exact hm
    · exact hs
    · exact ho
  · simp only [VG.Proof.Argon2.Arm.Derive.τB, List.mem_singleton] at hp'
    subst hp'
    show State.addr (s.gpr .r11) = State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)
    rw [h.r11]

/-- A byte of the 256 bytes at `E`, from its word. -/
theorem loc_byte (m : Mem) {k : Nat} (hk : k < 256) :
    m (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀) + BitVec.ofNat 64 k) =
      (m.readW (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀ + BitVec.ofNat 32 (4 * (k / 4)))) 32).extractLsb' (8 * (k % 4)) 8 := by
  have := VG.Proof.Argon2.Arm.Derive.E_hi hp
  rw [addr_add (by omega), ← Mem.readW_byte m _ (Nat.mod_lt _ (by decide)), BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, Nat.div_add_mod]

end

/-- The taint analysis's knowledge of the body, from what two runs share and
the values of the locals' slots `sl` in both. -/
theorem agreeB {s₀₁ s₀₂ s₁ s₂ : State} (hp₁ : VG.Proof.Argon2.Arm.Derive.DPre s₀₁) (hp₂ : VG.Proof.Argon2.Arm.Derive.DPre s₀₂) (pb : VG.Proof.Argon2.Arm.Derive.Pub2 s₀₁ s₀₂)
    (h₁ : VG.Proof.Argon2.Arm.Derive.Inv s₀₁ s₁) (h₂ : VG.Proof.Argon2.Arm.Derive.Inv s₀₂ s₂) (sl : List (Nat × Nat × Nat)) (rs : List Reg)
    (hrs : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hok : VG.Arm.Taint.SlotsOk (VG.Proof.Argon2.Arm.Derive.τB sl rs))
    (hsl : ∀ x ∈ sl, x.1 = 0 ∧ ∀ k, x.2.1 ≤ k → k < x.2.1 + x.2.2 →
      VG.Proof.Argon2.Arm.Derive.lw s₀₁ s₁ (4 * (k / 4)) = VG.Proof.Argon2.Arm.Derive.lw s₀₂ s₂ (4 * (k / 4))) :
    ∃ w₁ w₂, Covers s₁.wr w₁ ∧ Covers s₂.wr w₂ ∧
      VG.Arm.Taint.Agree (VG.Proof.Argon2.Arm.Derive.τB sl rs) (s₁.withRegions s₁.rd w₁) (s₂.withRegions s₂.rd w₂) := by
  refine ⟨VG.Proof.Argon2.Arm.Derive.wide s₀₁, VG.Proof.Argon2.Arm.Derive.wide s₀₂, by rw [h₁.wr]; exact VG.Proof.Argon2.Arm.Derive.covers_wide hp₁, by rw [h₂.wr]; exact VG.Proof.Argon2.Arm.Derive.covers_wide hp₂,
    ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => pb.wide_eq, VG.Proof.Argon2.Arm.Derive.wf_wide hp₁ sl rs h₁, VG.Proof.Argon2.Arm.Derive.wf_wide hp₂ sl rs h₂, hok,
      fun x hx k hk₁ hk₂ => ?_, fun h0 => absurd h0 (Nat.lt_irrefl 0),
      fun _ h0 => absurd h0 (Nat.not_lt_zero _)⟩⟩
  · simp only [VG.Proof.Argon2.Arm.Derive.τB, RegSet.mem_ofList, List.mem_cons] at hr
    rcases hr with rfl | hr
    · rw [State.withRegions_gpr, State.withRegions_gpr, h₁.r11, h₂.r11, pb.E]
    · rw [State.withRegions_gpr, State.withRegions_gpr]; exact hrs r hr
  · have hlen := hok x hx
    simp only [VG.Proof.Argon2.Arm.Derive.τB, List.mem_append, List.mem_singleton] at hx
    have hw : ∀ k < 256, VG.Proof.Argon2.Arm.Derive.lw s₀₁ s₁ (4 * (k / 4)) = VG.Proof.Argon2.Arm.Derive.lw s₀₂ s₂ (4 * (k / 4)) →
        (s₁.withRegions s₁.rd (VG.Proof.Argon2.Arm.Derive.wide s₀₁)).mem (VG.Arm.Taint.byteAddr (s₁.withRegions s₁.rd (VG.Proof.Argon2.Arm.Derive.wide s₀₁)) 0 k) =
        (s₂.withRegions s₂.rd (VG.Proof.Argon2.Arm.Derive.wide s₀₂)).mem (VG.Arm.Taint.byteAddr (s₂.withRegions s₂.rd (VG.Proof.Argon2.Arm.Derive.wide s₀₂)) 0 k) :=
      fun k hk e => by
        simp only [VG.Arm.Taint.byteAddr, VG.Arm.Taint.region, State.withRegions_wr, State.withRegions_mem,
          VG.Proof.Argon2.Arm.Derive.wide, List.getD_cons_zero]
        rw [VG.Proof.Argon2.Arm.Derive.loc_byte hp₁ s₁.mem hk, VG.Proof.Argon2.Arm.Derive.loc_byte hp₂ s₂.mem hk]
        exact congrArg _ e
    rcases hx with hx | rfl
    · obtain ⟨x0, hk⟩ := hsl x hx
      rw [x0] at hlen ⊢
      simp only [VG.Proof.Argon2.Arm.Derive.τB, List.getD_cons_zero] at hlen
      exact hw k (by omega) (hk k hk₁ hk₂)
    · simp only at hk₁ hk₂ ⊢
      refine hw k (by omega) ?_
      have e : 4 * (k / 4) = Impl.Argon2.Arm.Derive.argOff ((k - 184) / 4) := by
        simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]; omega
      rw [e, h₁.arg hp₁ (by omega), h₂.arg hp₂ (by omega), pb.2 _ (by omega)]

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.CTCall`. -/
section

/-!
# Argon2 on ARMv7: two runs of the body

`Two s₀₁ s₀₂`: two runs of the derivation with the same public data.
`Two.leaf` relates a piece of the body the taint analysis proves, from the
public words of the locals (`slots_of_words`), and adds what each run
satisfies by correctness; `ccall_rel` and `hcall_rel` relate the calls of G
and H′, from their preconditions in both runs and their public arguments.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.Argon2.Arm (compressArm)

/-- Two runs of the derivation, with the same public data. -/
structure Two (s₀₁ s₀₂ : State) : Prop where
  hp₁ : VG.Proof.Argon2.Arm.Derive.DPre s₀₁
  hp₂ : VG.Proof.Argon2.Arm.Derive.DPre s₀₂
  pb : VG.Proof.Argon2.Arm.Derive.Pub2 s₀₁ s₀₂

namespace Pub2
variable {s₀₁ s₀₂ : State} (h : VG.Proof.Argon2.Arm.Derive.Pub2 s₀₁ s₀₂)
include h

theorem arg_eq {i : Nat} (hi : i < 18) : VG.Proof.Argon2.Arm.Derive.arg s₀₁ i = VG.Proof.Argon2.Arm.Derive.arg s₀₂ i := h.2 i hi
theorem memP_eq : VG.Proof.Argon2.Arm.Derive.memP s₀₁ = VG.Proof.Argon2.Arm.Derive.memP s₀₂ := h.2 13 (by decide)
theorem scrP_eq : VG.Proof.Argon2.Arm.Derive.scrP s₀₁ = VG.Proof.Argon2.Arm.Derive.scrP s₀₂ := h.2 15 (by decide)
theorem outP_eq : VG.Proof.Argon2.Arm.Derive.outP s₀₁ = VG.Proof.Argon2.Arm.Derive.outP s₀₂ := h.2 16 (by decide)
theorem outL_eq : VG.Proof.Argon2.Arm.Derive.outL s₀₁ = VG.Proof.Argon2.Arm.Derive.outL s₀₂ := by simp only [VG.Proof.Argon2.Arm.Derive.outL, h.2 17 (by decide)]
theorem blocksN_eq : VG.Proof.Argon2.Arm.Derive.blocksN s₀₁ = VG.Proof.Argon2.Arm.Derive.blocksN s₀₂ := by simp only [VG.Proof.Argon2.Arm.Derive.blocksN, h.2 14 (by decide)]
theorem lanesN_eq : VG.Proof.Argon2.Arm.Derive.lanesN s₀₁ = VG.Proof.Argon2.Arm.Derive.lanesN s₀₂ := by simp only [VG.Proof.Argon2.Arm.Derive.lanesN, h.2 7 (by decide)]
theorem itersN_eq : VG.Proof.Argon2.Arm.Derive.itersN s₀₁ = VG.Proof.Argon2.Arm.Derive.itersN s₀₂ := by simp only [VG.Proof.Argon2.Arm.Derive.itersN, h.2 5 (by decide)]

theorem prm_eq : VG.Proof.Argon2.Arm.Derive.prm s₀₁ = VG.Proof.Argon2.Arm.Derive.prm s₀₂ := by
  simp only [VG.Proof.Argon2.Arm.Derive.prm, VG.Proof.Argon2.Arm.Derive.kindV, VG.Proof.Argon2.Arm.Derive.itersN, VG.Proof.Argon2.Arm.Derive.mcostN, VG.Proof.Argon2.Arm.Derive.lanesN, VG.Proof.Argon2.Arm.Derive.outL, h.2 0 (by decide), h.2 5 (by decide),
    h.2 6 (by decide), h.2 7 (by decide), h.2 17 (by decide)]

end Pub2

/-- The slots `sl` of the locals hold the words `ws`. -/
theorem slots_of_words {s₀₁ s₀₂ s₁ s₂ : State} {ws : List Nat} {sl : List (Nat × Nat × Nat)}
    (hw : ∀ d ∈ ws, VG.Proof.Argon2.Arm.Derive.lw s₀₁ s₁ d = VG.Proof.Argon2.Arm.Derive.lw s₀₂ s₂ d)
    (hc : ∀ x ∈ sl, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ ws) :
    ∀ x ∈ sl, x.1 = 0 ∧ ∀ k, x.2.1 ≤ k → k < x.2.1 + x.2.2 →
      VG.Proof.Argon2.Arm.Derive.lw s₀₁ s₁ (4 * (k / 4)) = VG.Proof.Argon2.Arm.Derive.lw s₀₂ s₂ (4 * (k / 4)) := by
  intro x hx
  obtain ⟨h0, hj⟩ := hc x hx
  refine ⟨h0, fun k h₁ h₂ => hw _ ?_⟩
  have := hj (k - x.2.1) (by omega)
  rwa [Nat.add_sub_cancel' h₁] at this

/-- A relation proved for each pair of related states. -/
theorem RelCT.of_eq {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa (fun a b => a = s₁ ∧ b = s₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

theorem execBlock_append (l₁ l₂ : List Instr) (s : State) :
    execBlock isa (l₁ ++ l₂) s = (execBlock isa l₁ s).bind fun p =>
      (execBlock isa l₂ p.1).map fun q => (q.1, p.2 ++ q.2) := by
  induction l₁ generalizing s with
  | nil => simp [execBlock]
  | cons i is ih =>
    simp only [List.cons_append, execBlock]
    split
    · rfl
    · rw [ih]
      cases execBlock isa is _ with
      | none => rfl
      | some p => simp [Function.comp_def, List.append_assoc]

/-- A block in two parts leaks as their sequence. -/
theorem RelCT.block_split {P Q : State → State → Prop} {l₁ l₂ : List Instr}
    (h : RelCT isa P (.seq (.block l₁) (.block l₂)) Q) : RelCT isa P (.block (l₁ ++ l₂)) Q := by
  have split : ∀ {s t s'}, Exec isa (.block (l₁ ++ l₂)) s t s' →
      Exec isa (.seq (.block l₁) (.block l₂)) s t s' := by
    intro s t s' e
    rw [Exec.block_iff, VG.Proof.Argon2.Arm.Derive.execBlock_append, Option.bind_eq_some_iff] at e
    obtain ⟨⟨s₁, t₁⟩, h₁, h₂⟩ := e
    rw [Option.map_eq_some_iff] at h₂
    obtain ⟨⟨s₂, t₂⟩, h₂, he⟩ := h₂
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .seq (.block h₁) (.block h₂)
  exact fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (split e₁) (split e₂)

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.Arm.Derive.Two s₀₁ s₀₂)
include T

/-- A piece of the body the taint analysis proves, from the slots `sl` of the
locals, which hold the words `ws`, public, and the registers `rs`. -/
theorem leaf {P : State → State → Prop} {c : Prog isa} (ws : List Nat) (sl : List (Nat × Nat × Nat))
    (rs : List Reg) (hok : VG.Arm.Taint.SlotsOk (VG.Proof.Argon2.Arm.Derive.τB sl rs))
    (hsl : ∀ x ∈ sl, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ ws)
    (hag : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.Argon2.Arm.Derive.Inv s₀₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.Inv s₀₂ s₂ ∧ (∀ d ∈ ws, VG.Proof.Argon2.Arm.Derive.lw s₀₁ s₁ d = VG.Proof.Argon2.Arm.Derive.lw s₀₂ s₂ d) ∧
      ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.Arm.Derive.τB sl rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  refine RelCT.taintW (VG.Proof.Argon2.Arm.Derive.τB sl rs) (fun s₁ s₂ h => ?_) hc
  obtain ⟨i₁, i₂, hw, hr⟩ := hag s₁ s₂ h
  exact VG.Proof.Argon2.Arm.Derive.agreeB T.hp₁ T.hp₂ T.pb i₁ i₂ sl rs hr hok (VG.Proof.Argon2.Arm.Derive.slots_of_words hw hsl)

/-- A call of G: `compress(r0, r1, r2, r3)` to `scratch + o`, with the same
blocks in both runs. -/
theorem ccall_rel {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ →
      (VG.Proof.Argon2.Arm.Derive.Inv s₀₁ s₁ ∧ s₁.gpr .r3 = VG.Proof.Argon2.Arm.Derive.scrP s₀₁ ∧ s₁.gpr .r2 = VG.Proof.Argon2.Arm.Derive.scrP s₀₁ + BitVec.ofNat 32 o ∧
        VG.Proof.Argon2.Arm.Derive.GArg s₀₁ o (s₁.gpr .r0) ∧ VG.Proof.Argon2.Arm.Derive.GArg s₀₁ o (s₁.gpr .r1)) ∧
      (VG.Proof.Argon2.Arm.Derive.Inv s₀₂ s₂ ∧ s₂.gpr .r3 = VG.Proof.Argon2.Arm.Derive.scrP s₀₂ ∧ s₂.gpr .r2 = VG.Proof.Argon2.Arm.Derive.scrP s₀₂ + BitVec.ofNat 32 o ∧
        VG.Proof.Argon2.Arm.Derive.GArg s₀₂ o (s₂.gpr .r0) ∧ VG.Proof.Argon2.Arm.Derive.GArg s₀₂ o (s₂.gpr .r1)) ∧
      s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1) :
    RelCT isa P Impl.Argon2.Arm.Derive.compressCall fun _ _ => True := by
  refine RelCT.of_eq fun s₁ s₂ hP => ?_
  obtain ⟨⟨i₁, d₁, c₁, x₁, y₁⟩, ⟨i₂, d₂, c₂, x₂, y₂⟩, ea, es⟩ := h s₁ s₂ hP
  obtain ⟨p₁, v₁, w₁⟩ := VG.Proof.Argon2.Arm.Derive.ccall_pre T.hp₁ i₁ d₁ ho ho' c₁ x₁ y₁
  obtain ⟨p₂, v₂, w₂⟩ := VG.Proof.Argon2.Arm.Derive.ccall_pre T.hp₂ i₂ d₂ ho ho' c₂ x₂ y₂
  have eR : VG.Proof.Argon2.Arm.Derive.cRd s₂ = VG.Proof.Argon2.Arm.Derive.cRd s₁ := by simp only [VG.Proof.Argon2.Arm.Derive.cRd, ea, es]
  have eW : VG.Proof.Argon2.Arm.Derive.cWr s₀₂ o = VG.Proof.Argon2.Arm.Derive.cWr s₀₁ o := by simp only [VG.Proof.Argon2.Arm.Derive.cWr, VG.Proof.Argon2.Arm.Derive.scrB, T.pb.scrP_eq]
  rw [eR, eW] at p₂ v₂
  rw [eW] at w₂
  unfold Impl.Argon2.Arm.Derive.compressCall
  refine RelCT.call (k := VG.Proof.Argon2.Arm.compressArm) Proof.Argon2.Arm.compress_verified'.1 Proof.Argon2.Arm.compress_ct
    (VG.Proof.Argon2.Arm.Derive.cRd s₁) (VG.Proof.Argon2.Arm.Derive.cWr s₀₁ o) fun a b ⟨ha, hb⟩ => ?_
  subst a b
  refine ⟨p₁, p₂, ?_, v₁, w₁, v₂, w₂⟩
  simp only [VG.Proof.Argon2.Arm.compressArm, State.withRegions_gpr,
    State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide)]
  exact ⟨ea, es, by rw [c₁, c₂, T.pb.scrP_eq], by rw [d₁, d₂, T.pb.scrP_eq]⟩

/-- A call of H′: `hprime(r0, r1, r2, r3, r12)`, with the same arguments in
both runs. -/
theorem hcall_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ →
      (VG.Proof.Argon2.Arm.Derive.Inv s₀₁ s₁ ∧ s₁.gpr .r12 = VG.Proof.Argon2.Arm.Derive.scrP s₀₁ ∧
        (∃ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀₁, VG.Proof.Argon2.Arm.Derive.locR s₀₁], ∃ off, State.addr (s₁.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
          off + (s₁.gpr .r1).toNat ≤ R.len) ∧ (s₁.gpr .r0).toNat + (s₁.gpr .r1).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀₁, VG.Proof.Argon2.Arm.Derive.outR s₀₁], ∃ off, State.addr (s₁.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
          off + (s₁.gpr .r3).toNat ≤ R.len) ∧ (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat ≤ 2 ^ 32 ∧
        1 ≤ (s₁.gpr .r3).toNat) ∧
      (VG.Proof.Argon2.Arm.Derive.Inv s₀₂ s₂ ∧ s₂.gpr .r12 = VG.Proof.Argon2.Arm.Derive.scrP s₀₂ ∧
        (∃ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀₂, VG.Proof.Argon2.Arm.Derive.locR s₀₂], ∃ off, State.addr (s₂.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
          off + (s₂.gpr .r1).toNat ≤ R.len) ∧ (s₂.gpr .r0).toNat + (s₂.gpr .r1).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀₂, VG.Proof.Argon2.Arm.Derive.outR s₀₂], ∃ off, State.addr (s₂.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
          off + (s₂.gpr .r3).toNat ≤ R.len) ∧ (s₂.gpr .r2).toNat + (s₂.gpr .r3).toNat ≤ 2 ^ 32 ∧
        1 ≤ (s₂.gpr .r3).toNat) ∧
      s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
        s₁.gpr .r3 = s₂.gpr .r3) :
    RelCT isa P Impl.Argon2.Arm.Derive.hPrimeCall fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.hPrimeCall
  refine RelCT.of_eq fun s₁ s₂ hP => ?_
  obtain ⟨⟨i₁, d₁, n₁, nf₁, o₁, of₁, l₁⟩, ⟨i₂, d₂, n₂, nf₂, o₂, of₂, l₂⟩, e0, e1, e2, e3⟩ := h s₁ s₂ hP
  have hsp : s₁.sp = s₂.sp := by rw [i₁.sp, i₂.sp, T.pb.E]
  obtain ⟨p₁, v₁, w₁⟩ := VG.Proof.Argon2.Arm.Derive.hcall_pre T.hp₁ i₁ d₁ n₁ nf₁ o₁ of₁ l₁
  obtain ⟨p₂, v₂, w₂⟩ := VG.Proof.Argon2.Arm.Derive.hcall_pre T.hp₂ i₂ d₂ n₂ nf₂ o₂ of₂ l₂
  have eR : VG.Proof.Argon2.Arm.Derive.hRd s₂ = VG.Proof.Argon2.Arm.Derive.hRd s₁ := by simp only [VG.Proof.Argon2.Arm.Derive.hRd, e0, e1, hsp]
  have eW : VG.Proof.Argon2.Arm.Derive.hWr s₀₂ s₂ = VG.Proof.Argon2.Arm.Derive.hWr s₀₁ s₁ := by simp only [VG.Proof.Argon2.Arm.Derive.hWr, e2, e3, VG.Proof.Argon2.Arm.Derive.scrR, VG.Proof.Argon2.Arm.Derive.scrP, T.pb.scrP_eq]
  rw [eR, eW] at p₂ v₂
  rw [eW] at w₂
  have hn₁ : 4 * hregs.length ≤ s₁.sp.toNat := by
    have := T.hp₁.sp_lo
    simp only [List.length_cons, List.length_nil]; rw [i₁.sp, VG.Proof.Argon2.Arm.Derive.E_nat T.hp₁]; omega
  have hn₂ : 4 * hregs.length ≤ s₂.sp.toNat := by rw [← hsp]; exact hn₁
  refine frameCall_rel (rs := VG.Proof.Argon2.Arm.Derive.hregs) (t := .r12) (by decide) (k := HPrime.hPrimeArm) HPrime.hPrime_verified.1
    HPrime.hPrime_verified.2.1 (VG.Proof.Argon2.Arm.Derive.hRd s₁) (VG.Proof.Argon2.Arm.Derive.hWr s₀₁ s₁) fun a b ⟨ha, hb⟩ => ?_
  subst a b
  refine ⟨hsp, p₁, p₂, ⟨by simp [hsp], ?_, ?_, ?_, ?_, ?_⟩, v₁, w₁, v₂, w₂⟩
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), pushed_gpr, e0]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide), pushed_gpr, e1]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), pushed_gpr, e2]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), pushed_gpr, e3]
  · exact VG.Proof.Argon2.Arm.pushed_arg_eq hn₁ hn₂ (i := 0) (by decide)
      (by show s₁.gpr .r12 = s₂.gpr .r12; rw [d₁, d₂, T.pb.scrP_eq])

end Two

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.InitialCT`. -/
section

/-!
# Argon2 on ARMv7: H₀, in two runs

`code_rel`: H₀'s hash leaks the same trace in two runs with the same public
data. The BLAKE2b calls are related by H′'s macros' relations
(`HPrime.init_rel`, `update_rel`, `finalize_rel`, `absorbFixed_rel`), from
the same arguments: `scratch`, the inputs' places and lengths, and the byte
count, which only the inputs' lengths fix.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Spec.Blake2 (Repr b bytesAt)
open VG.Proof.Argon2.Arm.HPrime (Ctx InitIn UpdateIn FinalizeIn FixedIn)
open VG.Impl.Argon2.Arm.Derive (countLoOff countHiOff argOff ld st)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

/-- Composition, with what each run satisfies after the first part. -/
theorem RelCT.seqW {F₁ F₂ G₁ G₂ : State → Prop} {c₁ c₂ : Prog isa} {Q : State → State → Prop}
    (h₁ : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c₁ fun _ _ => True)
    (w₁ : ∀ s, F₁ s → WP isa c₁ s G₁) (w₂ : ∀ s, F₂ s → WP isa c₁ s G₂)
    (h₂ : RelCT isa (fun s₁ s₂ => G₁ s₁ ∧ G₂ s₂) c₂ Q) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.seq c₁ c₂) Q :=
  RelCT.seq (rel_wp h₁ w₁ w₂) h₂

/-- A branch on a condition that agrees in both runs. -/
theorem RelCT.iteF {F₁ F₂ : State → Prop} {c : Cond} {th el : Prog isa} {Q : State → State → Prop}
    (hc : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) th Q) (he : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) el Q) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.ite c th el) Q :=
  RelCT.ite (fun s₁ s₂ h => hc s₁ s₂ h.1 h.2) (ht.mono (fun _ _ h => h.1) fun _ _ h => h)
    (he.mono (fun _ _ h => h.1) fun _ _ h => h)

theorem slotsOkE (rs : List Reg) : VG.Arm.Taint.SlotsOk (VG.Proof.Argon2.Arm.Derive.τB [] rs) := by
  intro x hx
  simp only [VG.Proof.Argon2.Arm.Derive.τB, List.nil_append, List.mem_singleton] at hx
  subst hx; simp [VG.Proof.Argon2.Arm.Derive.τB]

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.Arm.Derive.Two s₀₁ s₀₂)
include T

/-- A piece the taint analysis proves from the arguments and the registers
`rs`, which both runs agree on. -/
theorem leafI {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.Argon2.Arm.Derive.Inv s₀₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.Inv s₀₂ s₂ ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.Arm.Derive.τB [] rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  T.leaf [] [] rs (VG.Proof.Argon2.Arm.Derive.slotsOkE rs) (fun _ h => (List.not_mem_nil h).elim)
    (fun s₁ s₂ h => let ⟨i₁, i₂, hr⟩ := hag s₁ s₂ h; ⟨i₁, i₂, fun _ h => (List.not_mem_nil h).elim, hr⟩) hc

/-- `scratch`'s context in the second run, in the first run's terms. -/
theorem ctx₂ {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀₂ s) (hb : s.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀₂) : Ctx (VG.Proof.Argon2.Arm.Derive.scrP s₀₁) (VG.Proof.Argon2.Arm.Derive.E s₀₁) s := by
  rw [T.pb.scrP_eq, T.pb.E]; exact VG.Proof.Argon2.Arm.Derive.ctx T.hp₂ h hb

/-- `start` leaks the same trace in two runs. -/
theorem start_rel :
    RelCT isa (fun s₁ s₂ => (VG.Proof.Argon2.Arm.Derive.Inv s₀₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀₁ s₁) ∧ (VG.Proof.Argon2.Arm.Derive.Inv s₀₂ s₂ ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀₂ s₂))
      Impl.Argon2.Arm.Derive.start fun _ _ => True := by
  have hs := T.hp₁.scr_fits
  unfold Impl.Argon2.Arm.Derive.start
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.stA_ok T.hp₁ h.1 h.2) (fun s h => VG.Proof.Argon2.Arm.Derive.stA_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW ((HPrime.init_rel (B := VG.Proof.Argon2.Arm.Derive.scrP s₀₁) (SP := VG.Proof.Argon2.Arm.Derive.E s₀₁) (n := 64) (by decide) (by decide)).mono
      (fun s₁ s₂ h => ⟨⟨VG.Proof.Argon2.Arm.Derive.ctx T.hp₁ h.1.1 h.1.2.2.1, h.1.2.2.2⟩, ⟨T.ctx₂ h.2.1 h.2.2.2.1, h.2.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => VG.Proof.Argon2.Arm.Derive.stInit_ok T.hp₁ h) (fun s h => VG.Proof.Argon2.Arm.Derive.stInit_ok T.hp₂ h) ?_
  refine RelCT.seqW (T.leafI [.r4] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2.2.1, h.2.2.2.1, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀₁ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀₁ t ∧ t.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀₁ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀₁)) [] ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀₁) + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (VG.Proof.Argon2.Arm.Derive.prm s₀₁))
    (G₂ := fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀₂ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀₂ t ∧ t.gpr .r4 = VG.Proof.Argon2.Arm.Derive.scrP s₀₂ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀₂)) [] ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀₂) + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (VG.Proof.Argon2.Arm.Derive.prm s₀₂))
    (fun s h => (VG.Proof.Argon2.Arm.Derive.header_ok T.hp₁ h.1 h.2.1 h.2.2.1 h.2.2.2).mono fun t ⟨i, p, e, r, d, _⟩ => ⟨i, p, e, r, d⟩)
    (fun s h => (VG.Proof.Argon2.Arm.Derive.header_ok T.hp₂ h.1 h.2.1 h.2.2.1 h.2.2.2).mono fun t ⟨i, p, e, r, d, _⟩ => ⟨i, p, e, r, d⟩) ?_
  refine RelCT.seqW ((HPrime.absorbFixed_rel (B := VG.Proof.Argon2.Arm.Derive.scrP s₀₁) (SP := VG.Proof.Argon2.Arm.Derive.E s₀₁) (offset := 768) (size := 24)
      (by decide) (by decide) (by omega) (by decide) (by decide) (VG.Proof.Argon2.Arm.Derive.stk_scr T.hp₁ (by decide) (by decide))
      ⟨_, by taint_decide⟩).mono
      (fun s₁ s₂ h => ⟨⟨VG.Proof.Argon2.Arm.Derive.ctx T.hp₁ h.1.1 h.1.2.2.1, VG.Proof.Argon2.Arm.Derive.scr_cov T.hp₁ h.1.1 (by decide)⟩,
        ⟨T.ctx₂ h.2.1 h.2.2.2.1, by rw [T.pb.scrP_eq]; exact VG.Proof.Argon2.Arm.Derive.scr_cov T.hp₂ h.2.1 (by decide)⟩⟩) fun _ _ h => h)
    (fun s h => VG.Proof.Argon2.Arm.Derive.stFix_ok T.hp₁ h) (fun s h => VG.Proof.Argon2.Arm.Derive.stFix_ok T.hp₂ h) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩

/-- `absorb ptr len` leaks the same trace in two runs whose absorbed data have
the same length. -/
theorem absorb_rel {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18)
    (hR₁ : (⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀₁ ptr), (VG.Proof.Argon2.Arm.Derive.arg s₀₁ len).toNat⟩ : Region) ∈ [VG.Proof.Argon2.Arm.Derive.pwR s₀₁, VG.Proof.Argon2.Arm.Derive.saltR s₀₁, VG.Proof.Argon2.Arm.Derive.secR s₀₁, VG.Proof.Argon2.Arm.Derive.adR s₀₁])
    (hR₂ : (⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀₂ ptr), (VG.Proof.Argon2.Arm.Derive.arg s₀₂ len).toNat⟩ : Region) ∈ [VG.Proof.Argon2.Arm.Derive.pwR s₀₂, VG.Proof.Argon2.Arm.Derive.saltR s₀₂, VG.Proof.Argon2.Arm.Derive.secR s₀₂, VG.Proof.Argon2.Arm.Derive.adR s₀₂])
    (hfit₁ : (VG.Proof.Argon2.Arm.Derive.arg s₀₁ ptr).toNat + (VG.Proof.Argon2.Arm.Derive.arg s₀₁ len).toNat ≤ 2 ^ 32)
    (hfit₂ : (VG.Proof.Argon2.Arm.Derive.arg s₀₂ ptr).toNat + (VG.Proof.Argon2.Arm.Derive.arg s₀₂ len).toNat ≤ 2 ^ 32) {data₁ data₂ : List Byte}
    (hd : data₁.length + 4 + 2 ^ 32 < 2 ^ 36) (heq : data₁.length = data₂.length)
    (hcA : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.Arm.Derive.τB [] [.r4]) (.block [ld .r0 (argOff len), .str .r0 .r4 792,
      ld .r2 countLoOff, ld .r3 countHiOff, .dp .add .r9 .r4 (.imm 792), .mov .r10 (.imm 4)]) hc).isSome = true)
    (hcB : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.Arm.Derive.τB [] []) (.block (Impl.Argon2.Arm.Derive.addCount (.imm 4) ++
      ([ld .r9 (argOff ptr), ld .r10 (argOff len)] : List Instr))) hc).isSome = true)
    (hcC : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.Arm.Derive.τB [] [])
      (.block (ld .r0 (argOff len) :: Impl.Argon2.Arm.Derive.addCount (.reg .r0))) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.HI s₀₁ data₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.HI s₀₂ data₂ s₂) (Impl.Argon2.Arm.Derive.absorb ptr len)
      fun _ _ => True := by
  have hs := T.hp₁.scr_fits
  have ep := T.pb.arg_eq hptr
  have el := T.pb.arg_eq hlen
  have e792 : State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀₁ + 792) = State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀₁) + BitVec.ofNat 64 792 :=
    VG.Proof.Argon2.Arm.Derive.scr_addr T.hp₁ (o := 792) (by decide)
  have cov792 : ∀ {s₀ s : State}, VG.Proof.Argon2.Arm.Derive.DPre s₀ → VG.Proof.Argon2.Arm.Derive.Inv s₀ s →
      Covers [⟨State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + 792), 4⟩] (s.rd ++ s.wr) := fun {s₀ s} hp h => by
    rw [show State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀ + 792) = State.addr (VG.Proof.Argon2.Arm.Derive.scrP s₀) + BitVec.ofNat 64 792 from
      VG.Proof.Argon2.Arm.Derive.scr_addr hp (o := 792) (by decide)]
    exact Covers.right (VG.Proof.Argon2.Arm.Derive.scr_cov hp h (by decide))
  have covIn : ∀ {s₀ s : State}, VG.Proof.Argon2.Arm.Derive.DPre s₀ → VG.Proof.Argon2.Arm.Derive.Inv s₀ s →
      (⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr), (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat⟩ : Region) ∈ [VG.Proof.Argon2.Arm.Derive.pwR s₀, VG.Proof.Argon2.Arm.Derive.saltR s₀, VG.Proof.Argon2.Arm.Derive.secR s₀, VG.Proof.Argon2.Arm.Derive.adR s₀] →
      Covers [⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr), (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat⟩] (s.rd ++ s.wr) := fun {s₀ s} hp h hR => by
    have hR' : (⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀ ptr), (VG.Proof.Argon2.Arm.Derive.arg s₀ len).toNat⟩ : Region) ∈
        [VG.Proof.Argon2.Arm.Derive.pwR s₀, VG.Proof.Argon2.Arm.Derive.saltR s₀, VG.Proof.Argon2.Arm.Derive.secR s₀, VG.Proof.Argon2.Arm.Derive.adR s₀, VG.Proof.Argon2.Arm.Derive.argR s₀] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
      rcases hR with h | h | h | h <;> simp [h]
    rw [h.rd, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_left _ hR', 0, by simp, by simp⟩
  have hS : (⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀₁ ptr), (VG.Proof.Argon2.Arm.Derive.arg s₀₁ len).toNat⟩ : Region) ∈
      [VG.Proof.Argon2.Arm.Derive.pwR s₀₁, VG.Proof.Argon2.Arm.Derive.saltR s₀₁, VG.Proof.Argon2.Arm.Derive.secR s₀₁, VG.Proof.Argon2.Arm.Derive.adR s₀₁, VG.Proof.Argon2.Arm.Derive.memR s₀₁, VG.Proof.Argon2.Arm.Derive.scrR s₀₁, VG.Proof.Argon2.Arm.Derive.outR s₀₁] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR₁ ⊢
    rcases hR₁ with h | h | h | h <;> simp [h]
  have hR' : (⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s₀₁ ptr), (VG.Proof.Argon2.Arm.Derive.arg s₀₁ len).toNat⟩ : Region) ∈
      [VG.Proof.Argon2.Arm.Derive.pwR s₀₁, VG.Proof.Argon2.Arm.Derive.saltR s₀₁, VG.Proof.Argon2.Arm.Derive.secR s₀₁, VG.Proof.Argon2.Arm.Derive.adR s₀₁, VG.Proof.Argon2.Arm.Derive.argR s₀₁] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR₁ ⊢
    rcases hR₁ with h | h | h | h <;> simp [h]
  unfold Impl.Argon2.Arm.Derive.absorb
  refine RelCT.seqW (T.leafI [.r4] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.r4, h.2.r4, T.pb.scrP_eq]⟩) hcA)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absA_ok T.hp₁ hlen h.hc) (fun s h => VG.Proof.Argon2.Arm.Derive.absA_ok T.hp₂ hlen h.hc) ?_
  refine RelCT.seqW ((HPrime.update_rel (B := VG.Proof.Argon2.Arm.Derive.scrP s₀₁) (SP := VG.Proof.Argon2.Arm.Derive.E s₀₁) (D := VG.Proof.Argon2.Arm.Derive.scrP s₀₁ + 792) (L := 4)
      (lo := BitVec.ofNat 32 data₁.length) (hi := BitVec.ofNat 32 (data₁.length / 2 ^ 32))
      (by have : (VG.Proof.Argon2.Arm.Derive.scrP s₀₁ + 792).toNat = (VG.Proof.Argon2.Arm.Derive.scrP s₀₁).toNat + 792 := VG.Proof.Argon2.Arm.Derive.add_nat (k := 792) (by omega)
          omega)
      (by rw [e792]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by rw [e792]; exact VG.Proof.Argon2.Arm.Derive.stk_scr T.hp₁ (by decide) (by decide))).mono
      (fun s₁ s₂ ⟨⟨g₁, e₁, d₁, c₁, x₁, _⟩, ⟨g₂, e₂, d₂, c₂, x₂, _⟩⟩ =>
        ⟨⟨VG.Proof.Argon2.Arm.Derive.ctx T.hp₁ g₁.inv g₁.r4, e₁, d₁, c₁, x₁, cov792 T.hp₁ g₁.inv⟩,
         ⟨T.ctx₂ g₂.inv g₂.r4, by rw [e₂, T.pb.scrP_eq], d₂, by rw [c₂, heq], by rw [x₂, heq],
           by rw [T.pb.scrP_eq]; exact cov792 T.hp₂ g₂.inv⟩⟩) fun _ _ h => h)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absU1_ok T.hp₁ h.1 rfl (by omega) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absU1_ok T.hp₂ h.1 rfl (by omega) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) ?_
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) hcB)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absB_ok T.hp₁ hptr hlen (by omega) h) (fun s h => VG.Proof.Argon2.Arm.Derive.absB_ok T.hp₂ hptr hlen (by omega) h) ?_
  refine RelCT.seqW ((HPrime.update_rel (B := VG.Proof.Argon2.Arm.Derive.scrP s₀₁) (SP := VG.Proof.Argon2.Arm.Derive.E s₀₁) (D := VG.Proof.Argon2.Arm.Derive.arg s₀₁ ptr)
      (L := (VG.Proof.Argon2.Arm.Derive.arg s₀₁ len).toNat) (lo := BitVec.ofNat 32 (data₁.length + 4))
      (hi := BitVec.ofNat 32 ((data₁.length + 4) / 2 ^ 32))
      hfit₁ ((T.hp₁.ro_w _ hR' (VG.Proof.Argon2.Arm.Derive.scrR s₀₁) (by simp)).sub_right (Region.sub_prefix (by decide)))
      ((T.hp₁.stk_all _ hS).sub_left fun a ha => VG.Proof.Argon2.Arm.Derive.call_stk T.hp₁ a (VG.Proof.Argon2.Arm.Derive.stk32_call T.hp₁ a ha))).mono
      (fun s₁ s₂ ⟨⟨g₁, e₁, d₁, c₁, x₁⟩, ⟨g₂, e₂, d₂, c₂, x₂⟩⟩ =>
        ⟨⟨VG.Proof.Argon2.Arm.Derive.ctx T.hp₁ g₁.inv g₁.r4, e₁, d₁, c₁, x₁, covIn T.hp₁ g₁.inv hR₁⟩,
         ⟨T.ctx₂ g₂.inv g₂.r4, by rw [e₂, ep], by rw [d₂, el], by rw [c₂, heq], by rw [x₂, heq],
           by rw [ep, el]; exact covIn T.hp₂ g₂.inv hR₂⟩⟩) fun _ _ h => h)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absU2_ok T.hp₁ hR₁ hfit₁ h.1 (by simp [Proof.Argon2.le32_length]) (by omega)
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absU2_ok T.hp₂ hR₂ hfit₂ h.1 (by simp [Proof.Argon2.le32_length]) (by omega)
      h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) hcC

/-- `finish` leaks the same trace in two runs whose absorbed data have the same
length. -/
theorem finish_rel {data₁ data₂ : List Byte} (heq : data₁.length = data₂.length) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.HI s₀₁ data₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.HI s₀₂ data₂ s₂) Impl.Argon2.Arm.Derive.finish
      fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.finish
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.fiA_ok T.hp₁ h) (fun s h => VG.Proof.Argon2.Arm.Derive.fiA_ok T.hp₂ h) ?_
  refine RelCT.seqW ((HPrime.finalize_rel (B := VG.Proof.Argon2.Arm.Derive.scrP s₀₁) (SP := VG.Proof.Argon2.Arm.Derive.E s₀₁) (lo := BitVec.ofNat 32 data₁.length)
      (hi := BitVec.ofNat 32 (data₁.length / 2 ^ 32))).mono
      (fun s₁ s₂ ⟨⟨g₁, c₁, x₁⟩, ⟨g₂, c₂, x₂⟩⟩ =>
        ⟨⟨VG.Proof.Argon2.Arm.Derive.ctx T.hp₁ g₁.inv g₁.r4, c₁, x₁⟩, ⟨T.ctx₂ g₂.inv g₂.r4, by rw [c₂, heq], by rw [x₂, heq]⟩⟩)
      fun _ _ h => h)
    (fun s h => VG.Proof.Argon2.Arm.Derive.fiFin_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => VG.Proof.Argon2.Arm.Derive.fiFin_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  exact T.leafI [.r4] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by
    simp only [List.mem_singleton, forall_eq]; rw [h.1.2.2.1, h.2.2.2.1, T.pb.scrP_eq]⟩) ⟨_, by taint_decide⟩

/-- H₀'s code leaks the same trace in two runs. -/
theorem code_rel :
    RelCT isa (fun s₁ s₂ => (VG.Proof.Argon2.Arm.Derive.Inv s₀₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀₁ s₁) ∧ (VG.Proof.Argon2.Arm.Derive.Inv s₀₂ s₂ ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀₂ s₂))
      Impl.Argon2.Arm.Derive.code fun _ _ => True := by
  have l1 := (VG.Proof.Argon2.Arm.Derive.arg s₀₁ 2).isLt
  have l2 := (VG.Proof.Argon2.Arm.Derive.arg s₀₁ 4).isLt
  have l3 := (VG.Proof.Argon2.Arm.Derive.arg s₀₁ 10).isLt
  have hpp := T.pb
  have a2 : (VG.Proof.Argon2.Arm.Derive.arg s₀₂ 2).toNat = (VG.Proof.Argon2.Arm.Derive.arg s₀₁ 2).toNat := by rw [hpp.arg_eq (by decide)]
  have a4 : (VG.Proof.Argon2.Arm.Derive.arg s₀₂ 4).toNat = (VG.Proof.Argon2.Arm.Derive.arg s₀₁ 4).toNat := by rw [hpp.arg_eq (by decide)]
  have a10 : (VG.Proof.Argon2.Arm.Derive.arg s₀₂ 10).toNat = (VG.Proof.Argon2.Arm.Derive.arg s₀₁ 10).toNat := by rw [hpp.arg_eq (by decide)]
  have a12 : (VG.Proof.Argon2.Arm.Derive.arg s₀₂ 12).toNat = (VG.Proof.Argon2.Arm.Derive.arg s₀₁ 12).toNat := by rw [hpp.arg_eq (by decide)]
  unfold Impl.Argon2.Arm.Derive.code
  refine RelCT.seqW T.start_rel (fun s h => VG.Proof.Argon2.Arm.Derive.start_ok T.hp₁ h.1 h.2) (fun s h => VG.Proof.Argon2.Arm.Derive.start_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 1) (len := 2) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.pw_fits T.hp₂.pw_fits (by rw [Proof.Argon2.initialHeader_length]; omega)
      (by rw [Proof.Argon2.initialHeader_length, Proof.Argon2.initialHeader_length])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absorb_ok T.hp₁ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) T.hp₁.pw_fits
      (by rw [Proof.Argon2.initialHeader_length]; omega) h)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absorb_ok T.hp₂ (ptr := 1) (len := 2) (by decide) (by decide) (by simp) T.hp₂.pw_fits
      (by rw [Proof.Argon2.initialHeader_length]; omega) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 3) (len := 4) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.salt_fits T.hp₂.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.Arm.Derive.bytesAt_length]; omega)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.Arm.Derive.bytesAt_length, a2])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absorb_ok T.hp₁ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) T.hp₁.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.Arm.Derive.bytesAt_length]; omega) h)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absorb_ok T.hp₂ (ptr := 3) (len := 4) (by decide) (by decide) (by simp) T.hp₂.salt_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.Arm.Derive.bytesAt_length]
          have := (VG.Proof.Argon2.Arm.Derive.arg s₀₂ 2).isLt; omega) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 9) (len := 10) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.sec_fits T.hp₂.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.Arm.Derive.bytesAt_length]; omega)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.Arm.Derive.bytesAt_length, a2, a4])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absorb_ok T.hp₁ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) T.hp₁.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.Arm.Derive.bytesAt_length]; omega) h)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absorb_ok T.hp₂ (ptr := 9) (len := 10) (by decide) (by decide) (by simp) T.hp₂.sec_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.Arm.Derive.bytesAt_length]
          have := (VG.Proof.Argon2.Arm.Derive.arg s₀₂ 2).isLt; have := (VG.Proof.Argon2.Arm.Derive.arg s₀₂ 4).isLt; omega) h) ?_
  refine RelCT.seqW (T.absorb_rel (ptr := 11) (len := 12) (by decide) (by decide) (by simp) (by simp)
      T.hp₁.ad_fits T.hp₂.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.Arm.Derive.bytesAt_length]; omega)
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.Arm.Derive.bytesAt_length, a2, a4,
        a10])
      ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absorb_ok T.hp₁ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) T.hp₁.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.Arm.Derive.bytesAt_length]; omega) h)
    (fun s h => VG.Proof.Argon2.Arm.Derive.absorb_ok T.hp₂ (ptr := 11) (len := 12) (by decide) (by decide) (by simp) T.hp₂.ad_fits
      (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, VG.Proof.Argon2.Arm.Derive.bytesAt_length]
          have := (VG.Proof.Argon2.Arm.Derive.arg s₀₂ 2).isLt; have := (VG.Proof.Argon2.Arm.Derive.arg s₀₂ 4).isLt; have := (VG.Proof.Argon2.Arm.Derive.arg s₀₂ 10).isLt; omega) h) ?_
  exact T.finish_rel (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length,
    VG.Proof.Argon2.Arm.Derive.bytesAt_length, a2, a4, a10, a12])

end Two

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.MemCT`. -/
section

/-!
# Argon2 on ARMv7: memory initialization, in two runs

`memoryInit_rel`: clearing the matrix and the calls of H′ for the first two
blocks of every lane leak the same trace in two runs with the same public
data: the calls' arguments are H₀'s place in the locals and the blocks'
addresses, which only the lane fixes.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_imm op2_reg)
open VG.Spec.Blake2 (bytesAt)
open VG.Impl.Argon2.Arm.Derive (argOff columnOff laneWordOff ld st)

/-- The state before block `c` of lane `l`. -/
def IB (s₀ : State) (h0 : List Byte) (l c : Nat) (s : State) : Prop :=
  VG.Proof.Argon2.Arm.Derive.Inv s₀ s ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀ s ∧ bytesAt s.mem (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀)) 64 = h0 ∧ s.gpr .r5 = BitVec.ofNat 32 l ∧
    s.gpr .r6 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 ((l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c) * 1024)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

theorem initBlock_w {h0 : List Byte} {l c : Nat} (hl : l < VG.Proof.Argon2.Arm.Derive.lanesN s₀) (hc : c < 2) {s : State}
    (h : VG.Proof.Argon2.Arm.Derive.IB s₀ h0 l c s) : WP isa (Impl.Argon2.Arm.Derive.initBlock c) s (VG.Proof.Argon2.Arm.Derive.IB s₀ h0 l c) :=
  (VG.Proof.Argon2.Arm.Derive.initBlock_ok hp h.1 h.2.1 h.2.2.1 hl hc h.2.2.2.1 h.2.2.2.2).mono fun _ ⟨i, p, b, e, d, _, _⟩ =>
    ⟨i, p, b, e.trans h.2.2.2.1, d.trans h.2.2.2.2⟩

omit hp in
theorem nextBlock_w {h0 : List Byte} {l : Nat} {s : State} (h : VG.Proof.Argon2.Arm.Derive.IB s₀ h0 l 0 s) :
    WP isa (.block [.dp .add .r6 .r6 (.imm 1024)]) s (VG.Proof.Argon2.Arm.Derive.IB s₀ h0 l 1) :=
  wp_add (op2_imm (by decide)) fun t u => WP.block_nil ⟨h.1.upd u (by decide), h.2.1.of_mem u.mem,
    by rw [u.mem]; exact h.2.2.1, by rw [u.other _ (by decide)]; exact h.2.2.2.1, by
      rw [u.gpr, h.2.2.2.2, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.add_assoc,
        BitVec.ofNat_add_ofNat, show (l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + 0) * 1024 + 1024 = (l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + 1) * 1024 by
          rw [Nat.add_mul, Nat.add_mul]]⟩

/-- The instructions before `initBlock`'s call of H′. -/
theorem ibBlk_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) (c : Nat) (hc : encodable (BitVec.ofNat 32 c) = true) :
    WP isa (.block [.mov .r0 (.imm (BitVec.ofNat 32 c)), VG.Impl.Argon2.Arm.Derive.st columnOff .r0, VG.Impl.Argon2.Arm.Derive.st laneWordOff .r5,
      .mov .r0 (.reg .r11), .mov .r1 (.imm 72), .mov .r2 (.reg .r6), .mov .r3 (.imm 1024),
      ld .r12 (argOff 15)]) s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ t.gpr .r12 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧ t.gpr .r0 = VG.Proof.Argon2.Arm.Derive.E s₀ ∧
      t.gpr .r1 = 72 ∧ t.gpr .r3 = 1024 ∧ t.gpr .r2 = s.gpr .r6 := by
  refine wp_mov (op2_imm hc) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₁ (d := 64) (by decide) fun s₂ i₂ _ _ g₂ _ => ?_
  refine VG.Proof.Argon2.Arm.Derive.wp_stloc hp i₂ (d := 68) (by decide) fun s₃ i₃ _ _ g₃ _ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_imm (by decide)) fun s₇ u₇ => ?_
  have i₇ := (((i₃.upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₇ (i := 15) (by decide) fun s₈ u₈ => WP.block_nil
    ⟨i₇.upd u₈ (by decide), u₈.gpr, ?_, ?_, ?_, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      g₃, g₂, u₁.other _ (by decide), h.r11]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [u₈.other _ (by decide), u₇.gpr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      g₃, g₂, u₁.other _ (by decide)]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.Arm.Derive.Two s₀₁ s₀₂)
include T

/-- `initBlock c` leaks the same trace in two runs at the same lane. -/
theorem initBlock_rel {h₁ h₂ : List Byte} {l c : Nat} (hl : l < VG.Proof.Argon2.Arm.Derive.lanesN s₀₁) (hc : c < 2)
    (he : encodable (BitVec.ofNat 32 c) = true)
    (hchk : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.Arm.Derive.τB [] []) (.block [.mov .r0 (.imm (BitVec.ofNat 32 c)),
      VG.Impl.Argon2.Arm.Derive.st columnOff .r0, VG.Impl.Argon2.Arm.Derive.st laneWordOff .r5, .mov .r0 (.reg .r11), .mov .r1 (.imm 72), .mov .r2 (.reg .r6),
      .mov .r3 (.imm 1024), ld .r12 (argOff 15)]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.IB s₀₁ h₁ l c s₁ ∧ VG.Proof.Argon2.Arm.Derive.IB s₀₂ h₂ l c s₂) (Impl.Argon2.Arm.Derive.initBlock c)
      fun _ _ => True := by
  have pe := T.pb.prm_eq
  have cellF : ∀ {s₀ : State}, VG.Proof.Argon2.Arm.Derive.DPre s₀ → l < VG.Proof.Argon2.Arm.Derive.lanesN s₀ →
      (l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c) * 1024 + 1024 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024 ∧ l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c < VG.Proof.Argon2.Arm.Derive.blocksN s₀ :=
    fun {s₀} hp hl => by
      have L2 : 2 ≤ (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega
      have : l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c < VG.Proof.Argon2.Arm.Derive.blocksN s₀ := by
        rw [hp.blocks_eq]
        have := Nat.mul_le_mul_right (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen (show l + 1 ≤ VG.Proof.Argon2.Arm.Derive.lanesN s₀ by omega)
        rw [Nat.succ_mul] at this
        omega
      exact ⟨by omega, this⟩
  have pre : ∀ {s₀ : State}, VG.Proof.Argon2.Arm.Derive.DPre s₀ → l < VG.Proof.Argon2.Arm.Derive.lanesN s₀ → ∀ {s t : State}, VG.Proof.Argon2.Arm.Derive.IB s₀ h₁ l c s ∨ VG.Proof.Argon2.Arm.Derive.IB s₀ h₂ l c s →
      VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ t.gpr .r12 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧ t.gpr .r0 = VG.Proof.Argon2.Arm.Derive.E s₀ ∧ t.gpr .r1 = 72 ∧ t.gpr .r3 = 1024 ∧
        t.gpr .r2 = s.gpr .r6 →
      VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ t.gpr .r12 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧
        (∃ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.locR s₀], ∃ off, State.addr (t.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .r1).toNat ≤ R.len) ∧ (t.gpr .r0).toNat + (t.gpr .r1).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀], ∃ off, State.addr (t.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .r3).toNat ≤ R.len) ∧ (t.gpr .r2).toNat + (t.gpr .r3).toNat ≤ 2 ^ 32 ∧
        1 ≤ (t.gpr .r3).toNat := fun {s₀} hp hl {s t} hs ⟨i, d, a, c', f, e⟩ => by
    have hE := VG.Proof.Argon2.Arm.Derive.E_hi hp
    have hm := hp.mem_fits
    obtain ⟨hc', hk⟩ := cellF hp hl
    have ed : t.gpr .r2 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 ((l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c) * 1024) := by
      rw [e]; rcases hs with hs | hs <;> exact hs.2.2.2.2
    have an : (VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 ((l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c) * 1024)).toNat =
        (VG.Proof.Argon2.Arm.Derive.memP s₀).toNat + (l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c) * 1024 := VG.Proof.Argon2.Arm.Derive.add_nat (by omega)
    refine ⟨i, d, ⟨VG.Proof.Argon2.Arm.Derive.locR s₀, by simp, 0, by rw [a]; simp, by rw [c']; show 0 + 72 ≤ 144; decide⟩,
      by rw [a, c']; show (VG.Proof.Argon2.Arm.Derive.E s₀).toNat + 72 ≤ 2 ^ 32; omega,
      ⟨VG.Proof.Argon2.Arm.Derive.memR s₀, by simp, (l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + c) * 1024, by rw [ed, VG.Proof.Argon2.Arm.Derive.cell_addr hp hk]; rfl,
        by rw [f]; exact hc'⟩, by rw [ed, f, an]; show _ + 1024 ≤ 2 ^ 32; omega,
      by rw [f]; decide⟩
  unfold Impl.Argon2.Arm.Derive.initBlock
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) hchk)
    (G₁ := fun t => ∃ s, VG.Proof.Argon2.Arm.Derive.IB s₀₁ h₁ l c s ∧ VG.Proof.Argon2.Arm.Derive.Inv s₀₁ t ∧ t.gpr .r12 = VG.Proof.Argon2.Arm.Derive.scrP s₀₁ ∧ t.gpr .r0 = VG.Proof.Argon2.Arm.Derive.E s₀₁ ∧
      t.gpr .r1 = 72 ∧ t.gpr .r3 = 1024 ∧ t.gpr .r2 = s.gpr .r6)
    (G₂ := fun t => ∃ s, VG.Proof.Argon2.Arm.Derive.IB s₀₂ h₂ l c s ∧ VG.Proof.Argon2.Arm.Derive.Inv s₀₂ t ∧ t.gpr .r12 = VG.Proof.Argon2.Arm.Derive.scrP s₀₂ ∧ t.gpr .r0 = VG.Proof.Argon2.Arm.Derive.E s₀₂ ∧
      t.gpr .r1 = 72 ∧ t.gpr .r3 = 1024 ∧ t.gpr .r2 = s.gpr .r6)
    (fun s h => (VG.Proof.Argon2.Arm.Derive.ibBlk_ok T.hp₁ h.1 c he).mono fun t ht => ⟨s, h, ht⟩)
    (fun s h => (VG.Proof.Argon2.Arm.Derive.ibBlk_ok T.hp₂ h.1 c he).mono fun t ht => ⟨s, h, ht⟩) ?_
  refine T.hcall_rel fun s₁ s₂ ⟨⟨a₁, g₁, k₁⟩, ⟨a₂, g₂, k₂⟩⟩ =>
    ⟨pre T.hp₁ hl (.inl g₁) k₁, pre T.hp₂ (T.pb.lanesN_eq ▸ hl) (.inr g₂) k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.2.2.1, k₂.2.2.1, T.pb.E]
  · rw [k₁.2.2.2.1, k₂.2.2.2.1]
  · rw [k₁.2.2.2.2.2, k₂.2.2.2.2.2, g₁.2.2.2.2, g₂.2.2.2.2, pe, T.pb.memP_eq]
  · rw [k₁.2.2.2.2.1, k₂.2.2.2.2.1]

/-- `initLane` leaks the same trace in two runs at the same lane. -/
theorem initLane_rel {h₁ h₂ : List Byte} {l : Nat} (hl : l < VG.Proof.Argon2.Arm.Derive.lanesN s₀₁) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.LI s₀₁ h₁ l s₁ ∧ VG.Proof.Argon2.Arm.Derive.LI s₀₂ h₂ l s₂) Impl.Argon2.Arm.Derive.initLane fun _ _ => True := by
  have hl₂ : l < VG.Proof.Argon2.Arm.Derive.lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have ib : ∀ {s₀ s : State} {h0 : List Byte}, VG.Proof.Argon2.Arm.Derive.LI s₀ h0 l s → VG.Proof.Argon2.Arm.Derive.IB s₀ h0 l 0 s := fun h =>
    ⟨h.inv, h.pr, h.b0, h.r5, by rw [Nat.add_zero]; exact h.r6⟩
  unfold Impl.Argon2.Arm.Derive.initLane
  refine (RelCT.seqW (T.initBlock_rel hl (by decide) (by decide) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.initBlock_w T.hp₁ hl (by decide) h)
    (fun s h => VG.Proof.Argon2.Arm.Derive.initBlock_w T.hp₂ hl₂ (by decide) h) ?_).mono (fun _ _ h => ⟨ib h.1, ib h.2⟩) fun _ _ h => h
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.nextBlock_w h) (fun s h => VG.Proof.Argon2.Arm.Derive.nextBlock_w h) ?_
  refine RelCT.seqW (T.initBlock_rel hl (by decide) (by decide) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.initBlock_w T.hp₁ hl (by decide) h)
    (fun s h => VG.Proof.Argon2.Arm.Derive.initBlock_w T.hp₂ hl₂ (by decide) h) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩

/-- `memoryInit` leaks the same trace in two runs. -/
theorem memoryInit_rel {h₁ h₂ : List Byte} :
    RelCT isa (fun s₁ s₂ => (VG.Proof.Argon2.Arm.Derive.Inv s₀₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀₁ s₁ ∧ bytesAt s₁.mem (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀₁)) 64 = h₁) ∧
      (VG.Proof.Argon2.Arm.Derive.Inv s₀₂ s₂ ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀₂ s₂ ∧ bytesAt s₂.mem (State.addr (VG.Proof.Argon2.Arm.Derive.E s₀₂)) 64 = h₂))
      Impl.Argon2.Arm.Derive.memoryInit fun _ _ => True := by
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  unfold Impl.Argon2.Arm.Derive.memoryInit
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.clearW_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => VG.Proof.Argon2.Arm.Derive.clearW_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.laneStart_ok T.hp₁ h) (fun s h => VG.Proof.Argon2.Arm.Derive.laneStart_ok T.hp₂ h) ?_
  generalize hN : VG.Proof.Argon2.Arm.Derive.lanesN s₀₁ = N at hl1
  have hN₂ : VG.Proof.Argon2.Arm.Derive.lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      VG.Proof.Argon2.Arm.Derive.LI s₀₁ h₁ l s₁ ∧ VG.Proof.Argon2.Arm.Derive.LI s₀₂ h₂ l s₂) ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, hl1, h.1, h.2⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, g₁, g₂⟩ e₁ e₂
  obtain ⟨ht, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩ := rel_wp (T.initLane_rel (by rw [hN]; exact hl))
    (fun s h => VG.Proof.Argon2.Arm.Derive.lane_ok T.hp₁ (by rw [hN]; exact hl) h) (fun s h => VG.Proof.Argon2.Arm.Derive.lane_ok T.hp₂ (by rw [hN₂]; exact hl) h)
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨g₁, g₂⟩ e₁ e₂
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show VG.Arm.eval .ne s₁' = VG.Arm.eval .ne s₂'; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 ≠ N := by
    rw [show isa.eval .ne s₁' = VG.Arm.eval .ne s₁' from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega, l + 1, rfl, by omega, k₁, k₂⟩

end Two

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCT1`. -/
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
  inv : VG.Proof.Argon2.Arm.Derive.Inv s₀ s
  pr : VG.Proof.Argon2.Arm.Derive.Prm s₀ s
  pos : VG.Proof.Argon2.Arm.Derive.Pos s₀ s pass slice lane index
  ctr : VG.Proof.Argon2.Arm.Derive.lw s₀ s counterOff = BitVec.ofNat 32 ctr

theorem FS.w {s₀ s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : VG.Proof.Argon2.Arm.Derive.FS s₀ pass slice lane index ctr st s) : VG.Proof.Argon2.Arm.Derive.W s₀ pass slice lane index ctr s :=
  ⟨h.inv, h.pr, h.pos, h.cache.2.1⟩

theorem W.of_only {s₀ s t : State} {pass slice lane index ctr : Nat} (h : VG.Proof.Argon2.Arm.Derive.W s₀ pass slice lane index ctr s)
    {ds : List Reg} (k : Only ds s t) (h11 : Reg.r11 ∉ ds) : VG.Proof.Argon2.Arm.Derive.W s₀ pass slice lane index ctr t :=
  ⟨h.inv.only k h11, h.pr.of_mem k.mem, h.pos.of_mem k.mem, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem k.mem]; exact h.ctr⟩

/-- The words `W` is about. -/
abbrev ws0 : List Nat := [72, 76, 80, 84, 88, 92, 96, 100, 132]

/-- Their slots. -/
abbrev sl0 : List (Nat × Nat × Nat) := [(0, 72, 32), (0, 132, 4)]

theorem slotsOk0 (rs : List Reg) : VG.Arm.Taint.SlotsOk (VG.Proof.Argon2.Arm.Derive.τB VG.Proof.Argon2.Arm.Derive.sl0 rs) := by
  intro x hx
  simp only [VG.Proof.Argon2.Arm.Derive.τB, VG.Proof.Argon2.Arm.Derive.sl0, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp [VG.Proof.Argon2.Arm.Derive.τB]

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.Arm.Derive.Two s₀₁ s₀₂)
include T

theorem words {pass slice lane index ctr : Nat} {s₁ s₂ : State} (h₁ : VG.Proof.Argon2.Arm.Derive.W s₀₁ pass slice lane index ctr s₁)
    (h₂ : VG.Proof.Argon2.Arm.Derive.W s₀₂ pass slice lane index ctr s₂) : ∀ d ∈ VG.Proof.Argon2.Arm.Derive.ws0, VG.Proof.Argon2.Arm.Derive.lw s₀₁ s₁ d = VG.Proof.Argon2.Arm.Derive.lw s₀₂ s₂ d := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  intro d hd
  simp only [VG.Proof.Argon2.Arm.Derive.ws0, List.mem_cons, List.not_mem_nil, or_false] at hd
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
    (hag : ∀ s₁ s₂, P s₁ s₂ → (∃ pass slice lane index ctr, VG.Proof.Argon2.Arm.Derive.W s₀₁ pass slice lane index ctr s₁ ∧
      VG.Proof.Argon2.Arm.Derive.W s₀₂ pass slice lane index ctr s₂) ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.Arm.Derive.τB VG.Proof.Argon2.Arm.Derive.sl0 rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  T.leaf VG.Proof.Argon2.Arm.Derive.ws0 VG.Proof.Argon2.Arm.Derive.sl0 rs (VG.Proof.Argon2.Arm.Derive.slotsOk0 rs) (by decide) (fun s₁ s₂ h =>
    let ⟨⟨_, _, _, _, _, w₁, w₂⟩, hr⟩ := hag s₁ s₂ h
    ⟨w₁.inv, w₂.inv, T.words w₁ w₂, hr⟩) hc

end Two

/-! ## The address block -/

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- The instructions before G's call in `stage x y o`. -/
theorem stageBlk_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) {x y o : Nat} (ex : encodable (BitVec.ofNat 32 x) = true)
    (ey : encodable (BitVec.ofNat 32 y) = true) (eo : encodable (BitVec.ofNat 32 o) = true) :
    WP isa (.block [ld .r3 (argOff 15), .dp .add .r0 .r3 (.imm (BitVec.ofNat 32 x)),
      .dp .add .r1 .r3 (.imm (BitVec.ofNat 32 y)), .dp .add .r2 .r3 (.imm (BitVec.ofNat 32 o))]) s fun t =>
      VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ t.gpr .r3 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧ t.gpr .r0 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 x ∧
      t.gpr .r1 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 y ∧ t.gpr .r2 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 o := by
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_add (op2_imm ex) fun s₂ u₂ =>
    wp_add (op2_imm ey) fun s₃ u₃ => wp_add (op2_imm eo) fun s₄ u₄ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]

/-- The counter, stored. -/
theorem stctr_w {s : State} {pass slice lane index ctr c : Nat} (h : VG.Proof.Argon2.Arm.Derive.W s₀ pass slice lane index ctr s)
    (ha : s.gpr .r0 = BitVec.ofNat 32 c) :
    WP isa (.block [VG.Impl.Argon2.Arm.Derive.st counterOff .r0]) s (VG.Proof.Argon2.Arm.Derive.W s₀ pass slice lane index c) :=
  VG.Proof.Argon2.Arm.Derive.wp_stloc hp h.inv (d := counterOff) (by decide) fun t it vt ot _ _ => WP.block_nil
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
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.Arm.Derive.Two s₀₁ s₀₂)
include T

/-- `dependentWord` leaks the same trace in two runs at the same position. -/
theorem dependentWord_rel {pass slice lane index ctr : Nat} :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.W s₀₁ pass slice lane index ctr s₁ ∧ VG.Proof.Argon2.Arm.Derive.W s₀₂ pass slice lane index ctr s₂)
      Impl.Argon2.Arm.Derive.dependentWord fun _ _ => True :=
  T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩

/-- `stage x y o` leaks the same trace in two runs. -/
theorem stage_rel {x y o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384)
    (hx : 4096 ≤ x) (hx' : x + 1024 ≤ 16384) (hxo : x + 1024 ≤ o ∨ o + 1024 ≤ x)
    (hy : 4096 ≤ y) (hy' : y + 1024 ≤ 16384) (hyo : y + 1024 ≤ o ∨ o + 1024 ≤ y)
    (ex : encodable (BitVec.ofNat 32 x) = true) (ey : encodable (BitVec.ofNat 32 y) = true)
    (eo : encodable (BitVec.ofNat 32 o) = true)
    (hc : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.Arm.Derive.τB [] []) (.block [ld .r3 (argOff 15),
      .dp .add .r0 .r3 (.imm (BitVec.ofNat 32 x)), .dp .add .r1 .r3 (.imm (BitVec.ofNat 32 y)),
      .dp .add .r2 .r3 (.imm (BitVec.ofNat 32 o))]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.Inv s₀₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.Inv s₀₂ s₂) (Impl.Argon2.Arm.Derive.stage x y o) fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.stage
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) hc)
    (fun s h => VG.Proof.Argon2.Arm.Derive.stageBlk_ok T.hp₁ h ex ey eo) (fun s h => VG.Proof.Argon2.Arm.Derive.stageBlk_ok T.hp₂ h ex ey eo) ?_
  refine T.ccall_rel ho ho' fun s₁ s₂ ⟨⟨i₁, d₁, a₁, e₁, c₁⟩, ⟨i₂, d₂, a₂, e₂, c₂⟩⟩ =>
    ⟨⟨i₁, d₁, c₁, by rw [a₁]; exact .inr ⟨x, hx, hx', hxo, rfl⟩, by rw [e₁]; exact .inr ⟨y, hy, hy', hyo, rfl⟩⟩,
     ⟨i₂, d₂, c₂, by rw [a₂]; exact .inr ⟨x, hx, hx', hxo, rfl⟩, by rw [e₂]; exact .inr ⟨y, hy, hy', hyo, rfl⟩⟩,
     by rw [a₁, a₂, T.pb.scrP_eq], by rw [e₁, e₂, T.pb.scrP_eq]⟩

/-- `addressCalls` leaks the same trace in two runs at the same position. -/
theorem addressCalls_rel {pass slice lane index c : Nat} (h₁ : pass < 2 ^ 32) (h₂ : lane < 2 ^ 32)
    (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.W s₀₁ pass slice lane index c s₁ ∧ VG.Proof.Argon2.Arm.Derive.W s₀₂ pass slice lane index c s₂)
      Impl.Argon2.Arm.Derive.addressCalls fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.addressCalls
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1, h.2⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (VG.Proof.Argon2.Arm.Derive.input_ok T.hp₁ h.inv h.pos h.ctr h₁ h₂ h₃ h₄).mono fun t ht => ht.1)
    (fun s h => (VG.Proof.Argon2.Arm.Derive.input_ok T.hp₂ h.inv h.pos h.ctr h₁ h₂ h₃ h₄).mono fun t ht => ht.1) ?_
  refine RelCT.seqW (T.stage_rel (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩)
    (fun s h => (VG.Proof.Argon2.Arm.Derive.stage_ok T.hp₁ h (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono
      fun t ht => ht.1)
    (fun s h => (VG.Proof.Argon2.Arm.Derive.stage_ok T.hp₂ h (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono
      fun t ht => ht.1) ?_
  exact T.stage_rel (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩

/-- `addressCache` leaks the same trace in two runs at the same position. -/
theorem addressCache_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀₁) (hs : slice < 4) (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.Arm.Derive.addressCache fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (VG.Proof.Argon2.Arm.Derive.prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have sl := VG.Proof.Argon2.Arm.Derive.segLen_lt T.hp₁
  have hlt := T.hp₁.lanes_lt
  unfold Impl.Argon2.Arm.Derive.addressCache
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.cacheCheck_ok T.hp₁ h hi) (fun s h => VG.Proof.Argon2.Arm.Derive.cacheCheck_ok T.hp₂ h hi₂) ?_
  refine RelCT.seqW (RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show VG.Arm.eval .eq s₁ = VG.Arm.eval .eq s₂
      rw [h₁.2.2, h₂.2.2, h₁.1.cache.2.1, h₂.1.cache.2.1])
    (RelCT.nil fun _ _ _ => trivial) ?_)
    (fun s h => VG.Proof.Argon2.Arm.Derive.cacheFill_ok T.hp₁ h.1 hpass hl hs hi h.2.1 h.2.2)
    (fun s h => VG.Proof.Argon2.Arm.Derive.cacheFill_ok T.hp₂ h.1 hpass hl₂ hs hi₂ h.2.1 h.2.2)
    (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.2.1.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
  refine RelCT.seqW (G₁ := VG.Proof.Argon2.Arm.Derive.W s₀₁ pass slice lane index (index / 128 + 1))
    (G₂ := VG.Proof.Argon2.Arm.Derive.W s₀₂ pass slice lane index (index / 128 + 1))
    (T.leafF [.r0] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.2.1.w⟩, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2.1, h.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.stctr_w T.hp₁ h.1.w h.2.1) (fun s h => VG.Proof.Argon2.Arm.Derive.stctr_w T.hp₂ h.1.w h.2.1) ?_
  exact T.addressCalls_rel hpass (by omega) (by omega) (by omega)

/-- `randomSource` leaks the same trace in two runs at the same position. -/
theorem randomSource_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀₁) (hs : slice < 4) (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.Arm.Derive.randomSource fun _ _ => True := by
  have pe := T.pb.prm_eq
  unfold Impl.Argon2.Arm.Derive.randomSource
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => VG.Proof.Argon2.Arm.Derive.FS s₀₁ pass slice lane index ctr st₁ t ∧
      VG.Arm.eval .eq t = some (!Spec.Argon2.independent (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice))
    (G₂ := fun t => VG.Proof.Argon2.Arm.Derive.FS s₀₂ pass slice lane index ctr st₂ t ∧
      VG.Arm.eval .eq t = some (!Spec.Argon2.independent (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass slice))
    (fun s h => (VG.Proof.Argon2.Arm.Derive.addressMode_ok T.hp₁ h.inv h.pos hpass hs).mono fun t ⟨z, k⟩ => ⟨h.of_only k (by decide), z⟩)
    (fun s h => (VG.Proof.Argon2.Arm.Derive.addressMode_ok T.hp₂ h.inv h.pos hpass hs).mono fun t ⟨z, k⟩ => ⟨h.of_only k (by decide), z⟩) ?_
  refine RelCT.iteF (fun s₁ s₂ h₁ h₂ => by
      show VG.Arm.eval .eq s₁ = VG.Arm.eval .eq s₂
      rw [h₁.2, h₂.2, pe])
    (T.dependentWord_rel.mono (fun _ _ h => ⟨h.1.1.w, h.2.1.w⟩) fun _ _ h => h)
    ((T.addressCache_rel hpass hl hs hi).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)

end Two

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCT2`. -/
section

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

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_imm op2_reg)
open VG.Proof.Sha512.Arm (Only)
open VG.Spec.Argon2 (FillState)
open VG.Impl.Argon2.Arm.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  divisorOff strideOff j1Off j2Off refLaneOff tmpOff curOff ld st)

/-- The slots of the words `ws0` and `ex`. -/
abbrev slx (ex : List Nat) : List (Nat × Nat × Nat) := VG.Proof.Argon2.Arm.Derive.sl0 ++ ex.map fun d => (0, d, 4)

theorem slotsOkX {ex : List Nat} (hex : ∀ d ∈ ex, d % 4 = 0 ∧ d + 4 ≤ 144) (rs : List Reg) :
    VG.Arm.Taint.SlotsOk (VG.Proof.Argon2.Arm.Derive.τB (VG.Proof.Argon2.Arm.Derive.slx ex) rs) := by
  intro x hx
  simp only [VG.Proof.Argon2.Arm.Derive.τB, VG.Proof.Argon2.Arm.Derive.slx, List.append_assoc, List.mem_append, List.mem_map] at hx
  rcases hx with hx | ⟨d, hd, rfl⟩ | hx
  · exact VG.Proof.Argon2.Arm.Derive.slotsOk0 rs x (by simp only [VG.Proof.Argon2.Arm.Derive.τB]; exact List.mem_append_left _ hx)
  · have := hex d hd; simp [VG.Proof.Argon2.Arm.Derive.τB]; omega
  · exact VG.Proof.Argon2.Arm.Derive.slotsOk0 rs x (by simp only [VG.Proof.Argon2.Arm.Derive.τB]; exact List.mem_append_right _ hx)

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.Arm.Derive.Two s₀₁ s₀₂)
include T

/-- As `leafF`, with the words `ex` of the locals public too. -/
theorem leafX {P : State → State → Prop} {c : Prog isa} (rs : List Reg) (ex : List Nat)
    (hex : ∀ d ∈ ex, d % 4 = 0 ∧ d + 4 ≤ 144)
    (hag : ∀ s₁ s₂, P s₁ s₂ → (∃ pass slice lane index ctr, VG.Proof.Argon2.Arm.Derive.W s₀₁ pass slice lane index ctr s₁ ∧
      VG.Proof.Argon2.Arm.Derive.W s₀₂ pass slice lane index ctr s₂) ∧ (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧
      ∀ d ∈ ex, VG.Proof.Argon2.Arm.Derive.lw s₀₁ s₁ d = VG.Proof.Argon2.Arm.Derive.lw s₀₂ s₂ d)
    (hc : ∃ hc, (VG.Taint.check taint (VG.Proof.Argon2.Arm.Derive.τB (VG.Proof.Argon2.Arm.Derive.slx ex) rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  refine T.leaf (VG.Proof.Argon2.Arm.Derive.ws0 ++ ex) (VG.Proof.Argon2.Arm.Derive.slx ex) rs (VG.Proof.Argon2.Arm.Derive.slotsOkX hex rs) (fun x hx => ?_) (fun s₁ s₂ h => ?_) hc
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨h0, hj⟩ := (show ∀ x ∈ VG.Proof.Argon2.Arm.Derive.sl0, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ VG.Proof.Argon2.Arm.Derive.ws0 by decide) x hx
      exact ⟨h0, fun j hj' => List.mem_append_left _ (hj j hj')⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      refine ⟨rfl, fun j hj => List.mem_append_right _ ?_⟩
      have := (hex d hd).1
      rw [show 4 * ((d + j) / 4) = d by simp only at hj; omega]
      exact hd
  · obtain ⟨⟨_, _, _, _, _, w₁, w₂⟩, hr, he⟩ := hag s₁ s₂ h
    refine ⟨w₁.inv, w₂.inv, fun d hd => ?_, hr⟩
    rcases List.mem_append.mp hd with hd | hd
    · exact T.words w₁ w₂ d hd
    · exact he d hd

/-- `reference` leaks the same trace in two runs at the same position: it
reads the random word, but neither branches on it nor addresses memory with it. -/
theorem reference_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} {J1 J2 J1' J2' : BitVec 32} :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.RS s₀₁ pass slice lane index ctr st₁ J1 J2 s₁ ∧
      VG.Proof.Argon2.Arm.Derive.RS s₀₂ pass slice lane index ctr st₂ J1' J2' s₂) Impl.Argon2.Arm.Derive.reference fun _ _ => True :=
  T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.fs.w, h.2.fs.w⟩, by simp⟩) ⟨_, by taint_decide⟩

end Two

/-! ## G and the new block -/

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- The instructions before `fillCompress`'s call of G. -/
theorem fcBlk_ok {s : State} {pass slice lane index ctr : Nat} (h : VG.Proof.Argon2.Arm.Derive.W s₀ pass slice lane index ctr s)
    {P R : Nat} (ha : s.gpr .r0 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (P * 1024))
    (htmp : VG.Proof.Argon2.Arm.Derive.lw s₀ s tmpOff = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (R * 1024)) :
    WP isa (.block [ld .r1 tmpOff, ld .r3 (argOff 15), .dp .add .r2 .r3 (.imm 4096)]) s fun t =>
      VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ t.gpr .r3 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧ t.gpr .r2 = VG.Proof.Argon2.Arm.Derive.scrP s₀ + BitVec.ofNat 32 4096 ∧
      t.gpr .r0 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (P * 1024) ∧ t.gpr .r1 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 (R * 1024) := by
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h.inv (d := tmpOff) (by decide) fun s₂ u₂ => VG.Proof.Argon2.Arm.Derive.wp_ldarg hp (h.inv.upd u₂ (by decide))
    (i := 15) (by decide) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil
    ⟨((h.inv.upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide), ?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr]
  · rw [u₄.gpr, u₃.gpr]; rfl
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), ha]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, htmp]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.Arm.Derive.Two s₀₁ s₀₂)
include T

/-- `fillCompress` leaks the same trace in two runs at the same position and
with the same reference block. -/
theorem fillCompress_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀₁)
    (hs : slice < 4) (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen) {R : Nat} (hR : R < VG.Proof.Argon2.Arm.Derive.blocksN s₀₁) :
    RelCT isa (fun s₁ s₂ => (VG.Proof.Argon2.Arm.Derive.FS s₀₁ pass slice lane index ctr st₁ s₁ ∧
        VG.Proof.Argon2.Arm.Derive.lw s₀₁ s₁ tmpOff = VG.Proof.Argon2.Arm.Derive.memP s₀₁ + BitVec.ofNat 32 (R * 1024)) ∧
      (VG.Proof.Argon2.Arm.Derive.FS s₀₂ pass slice lane index ctr st₂ s₂ ∧ VG.Proof.Argon2.Arm.Derive.lw s₀₂ s₂ tmpOff = VG.Proof.Argon2.Arm.Derive.memP s₀₂ + BitVec.ofNat 32 (R * 1024)))
      Impl.Argon2.Arm.Derive.fillCompress fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (VG.Proof.Argon2.Arm.Derive.prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have hR₂ : R < VG.Proof.Argon2.Arm.Derive.blocksN s₀₂ := T.pb.blocksN_eq ▸ hR
  have L8 := VG.Proof.Argon2.Arm.Derive.laneLen_ge T.hp₁
  obtain ⟨cl, _⟩ := VG.Proof.Argon2.Arm.Derive.cell_fits T.hp₁ hl (col := (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen + index + (VG.Proof.Argon2.Arm.Derive.prm s₀₁).laneLen - 1) %
    (VG.Proof.Argon2.Arm.Derive.prm s₀₁).laneLen) (Nat.mod_lt _ (by omega))
  have L8₂ := VG.Proof.Argon2.Arm.Derive.laneLen_ge T.hp₂
  obtain ⟨cl₂, _⟩ := VG.Proof.Argon2.Arm.Derive.cell_fits T.hp₂ hl₂ (col := (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀₂).segmentLen + index + (VG.Proof.Argon2.Arm.Derive.prm s₀₂).laneLen - 1) %
    (VG.Proof.Argon2.Arm.Derive.prm s₀₂).laneLen) (Nat.mod_lt _ (by omega))
  unfold Impl.Argon2.Arm.Derive.fillCompress
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.2.1.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (G₁ := fun t => VG.Proof.Argon2.Arm.Derive.W s₀₁ pass slice lane index ctr t ∧ t.gpr .r0 = VG.Proof.Argon2.Arm.Derive.memP s₀₁ + BitVec.ofNat 32
      ((lane * (VG.Proof.Argon2.Arm.Derive.prm s₀₁).laneLen + (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen + index + (VG.Proof.Argon2.Arm.Derive.prm s₀₁).laneLen - 1) %
        (VG.Proof.Argon2.Arm.Derive.prm s₀₁).laneLen) * 1024) ∧ VG.Proof.Argon2.Arm.Derive.lw s₀₁ t tmpOff = VG.Proof.Argon2.Arm.Derive.memP s₀₁ + BitVec.ofNat 32 (R * 1024))
    (G₂ := fun t => VG.Proof.Argon2.Arm.Derive.W s₀₂ pass slice lane index ctr t ∧ t.gpr .r0 = VG.Proof.Argon2.Arm.Derive.memP s₀₂ + BitVec.ofNat 32
      ((lane * (VG.Proof.Argon2.Arm.Derive.prm s₀₂).laneLen + (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀₂).segmentLen + index + (VG.Proof.Argon2.Arm.Derive.prm s₀₂).laneLen - 1) %
        (VG.Proof.Argon2.Arm.Derive.prm s₀₂).laneLen) * 1024) ∧ VG.Proof.Argon2.Arm.Derive.lw s₀₂ t tmpOff = VG.Proof.Argon2.Arm.Derive.memP s₀₂ + BitVec.ofNat 32 (R * 1024))
    (fun s h => (VG.Proof.Argon2.Arm.Derive.prevPointer_ok T.hp₁ h.1.inv h.1.pr h.1.pos hl hs hi).mono fun t ⟨a, k⟩ =>
      ⟨h.1.w.of_only k (by decide), a, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem k.mem]; exact h.2⟩)
    (fun s h => (VG.Proof.Argon2.Arm.Derive.prevPointer_ok T.hp₂ h.1.inv h.1.pr h.1.pos hl₂ hs hi₂).mono fun t ⟨a, k⟩ =>
      ⟨h.1.w.of_only k (by decide), a, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem k.mem]; exact h.2⟩) ?_
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1, h.2.1⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.fcBlk_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => VG.Proof.Argon2.Arm.Derive.fcBlk_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine T.ccall_rel (o := 4096) (by decide) (by decide) fun s₁ s₂ ⟨⟨i₁, d₁, c₁, a₁, e₁⟩, ⟨i₂, d₂, c₂, a₂, e₂⟩⟩ =>
    ⟨⟨i₁, d₁, c₁, by rw [a₁]; exact .inl ⟨_, cl, rfl⟩, by rw [e₁]; exact .inl ⟨R, hR, rfl⟩⟩,
     ⟨i₂, d₂, c₂, by rw [a₂]; exact .inl ⟨_, cl₂, rfl⟩, by rw [e₂]; exact .inl ⟨R, hR₂, rfl⟩⟩,
     by rw [a₁, a₂, pe, T.pb.memP_eq], by rw [e₁, e₂, T.pb.memP_eq]⟩

/-- `fillWrite` leaks the same trace in two runs at the same position. -/
theorem fillWrite_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} :
    RelCT isa (fun s₁ s₂ => (VG.Proof.Argon2.Arm.Derive.FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.FS s₀₂ pass slice lane index ctr st₂ s₂) ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀₁ s₁ curOff = VG.Proof.Argon2.Arm.Derive.lw s₀₂ s₂ curOff) Impl.Argon2.Arm.Derive.fillWrite fun _ _ => True :=
  T.leafX [] [curOff] (by decide) (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.1.w, h.1.2.w⟩, by simp, by
    simp only [List.mem_singleton, forall_eq]; exact h.2⟩) ⟨_, by taint_decide⟩

/-- `fillBlock` leaks the same trace in two runs at the same position whose
reference blocks agree. -/
theorem fillBlock_rel {pass slice lane index ctr : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀₁) (hs : slice < 4) (hi : index < (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index)
    (href : Spec.Argon2.reference (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice index
        (Proof.Argon2.FillStep.random (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice index st₁.memory) =
      Spec.Argon2.reference (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass lane slice index
        (Proof.Argon2.FillStep.random (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass lane slice index st₂.memory)) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.FS s₀₁ pass slice lane index ctr st₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.FS s₀₂ pass slice lane index ctr st₂ s₂)
      Impl.Argon2.Arm.Derive.fillBlock fun _ _ => True := by
  have pe := T.pb.prm_eq
  have hi₂ : index < (VG.Proof.Argon2.Arm.Derive.prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have hb₁ : VG.Proof.Argon2.Arm.Derive.blocksN s₀₁ = (VG.Proof.Argon2.Arm.Derive.prm s₀₁).blocks := T.hp₁.blocks
  have refLt := Proof.Argon2.reference_cell_lt (VG.Proof.Argon2.Arm.Derive.prm s₀₁) T.hp₁.lanes_pos T.hp₁.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice index st₁.memory) hl
  simp only at refLt
  generalize hR : (Spec.Argon2.reference (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice index
      (Proof.Argon2.FillStep.random (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice index st₁.memory)).1 * (VG.Proof.Argon2.Arm.Derive.prm s₀₁).laneLen +
    (Spec.Argon2.reference (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice index
      (Proof.Argon2.FillStep.random (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice index st₁.memory)).2 = R at refLt
  have hR₂ : (Spec.Argon2.reference (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass lane slice index
      (Proof.Argon2.FillStep.random (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass lane slice index st₂.memory)).1 * (VG.Proof.Argon2.Arm.Derive.prm s₀₂).laneLen +
    (Spec.Argon2.reference (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass lane slice index
      (Proof.Argon2.FillStep.random (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass lane slice index st₂.memory)).2 = R := by
    rw [← href, ← pe]; exact hR
  generalize hC : lane * (VG.Proof.Argon2.Arm.Derive.prm s₀₁).laneLen + (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen + index) = C
  have hC₂ : lane * (VG.Proof.Argon2.Arm.Derive.prm s₀₂).laneLen + (slice * (VG.Proof.Argon2.Arm.Derive.prm s₀₂).segmentLen + index) = C := by rw [← pe]; exact hC
  unfold Impl.Argon2.Arm.Derive.fillBlock
  refine RelCT.seqW (T.randomSource_rel hpass hl hs hi)
    (fun s h => VG.Proof.Argon2.Arm.Derive.randomSource_ok T.hp₁ h hpass hl hs hi) (fun s h => VG.Proof.Argon2.Arm.Derive.randomSource_ok T.hp₂ h hpass hl₂ hs hi₂) ?_
  refine RelCT.seq (rel_wp (G := fun t =>
      VG.Proof.Argon2.Arm.Derive.FS s₀₁ pass slice lane index (VG.Proof.Argon2.Arm.Derive.ctrNext (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice index ctr) st₁ t ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀₁ t tmpOff = VG.Proof.Argon2.Arm.Derive.memP s₀₁ + BitVec.ofNat 32 (R * 1024) ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀₁ t curOff = VG.Proof.Argon2.Arm.Derive.memP s₀₁ + BitVec.ofNat 32 (C * 1024))
    (G' := fun t => VG.Proof.Argon2.Arm.Derive.FS s₀₂ pass slice lane index (VG.Proof.Argon2.Arm.Derive.ctrNext (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass slice index ctr) st₂ t ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀₂ t tmpOff = VG.Proof.Argon2.Arm.Derive.memP s₀₂ + BitVec.ofNat 32 (R * 1024) ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀₂ t curOff = VG.Proof.Argon2.Arm.Derive.memP s₀₂ + BitVec.ofNat 32 (C * 1024))
    (RelCT.of_eq fun s₁ s₂ ⟨g₁, g₂⟩ => (T.reference_rel (J1 := VG.Proof.Argon2.Arm.Derive.lw s₀₁ s₁ j1Off) (J2 := VG.Proof.Argon2.Arm.Derive.lw s₀₁ s₁ j2Off)
      (J1' := VG.Proof.Argon2.Arm.Derive.lw s₀₂ s₂ j1Off) (J2' := VG.Proof.Argon2.Arm.Derive.lw s₀₂ s₂ j2Off)).mono (fun a b ⟨ha, hb⟩ => by
        subst a b
        rw [← pe] at g₂
        exact ⟨⟨g₁.1, rfl, rfl⟩, ⟨g₂.1, rfl, rfl⟩⟩) fun _ _ h => h)
    (fun s g => (VG.Proof.Argon2.Arm.Derive.reference_ok T.hp₁ ⟨g.1, rfl, rfl⟩ hpass hl hs hi active).mono fun t ⟨r, tmp, cur⟩ =>
      ⟨r.fs, by rw [tmp, g.2, hR], by rw [cur, hC]⟩)
    (fun s g => (VG.Proof.Argon2.Arm.Derive.reference_ok T.hp₂ ⟨g.1, rfl, rfl⟩ hpass hl₂ hs hi₂ active).mono fun t ⟨r, tmp, cur⟩ =>
      ⟨r.fs, by rw [tmp, g.2, hR₂], by rw [cur, hC₂]⟩)) ?_
  rw [show VG.Proof.Argon2.Arm.Derive.ctrNext (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass slice index ctr = VG.Proof.Argon2.Arm.Derive.ctrNext (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice index ctr by rw [pe]]
  refine RelCT.seq (rel_wp (G := fun t =>
      VG.Proof.Argon2.Arm.Derive.FS s₀₁ pass slice lane index (VG.Proof.Argon2.Arm.Derive.ctrNext (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice index ctr) st₁ t ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀₁ t curOff = VG.Proof.Argon2.Arm.Derive.memP s₀₁ + BitVec.ofNat 32 (C * 1024))
    (G' := fun t => VG.Proof.Argon2.Arm.Derive.FS s₀₂ pass slice lane index (VG.Proof.Argon2.Arm.Derive.ctrNext (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice index ctr) st₂ t ∧
      VG.Proof.Argon2.Arm.Derive.lw s₀₂ t curOff = VG.Proof.Argon2.Arm.Derive.memP s₀₂ + BitVec.ofNat 32 (C * 1024))
    ((T.fillCompress_rel hl hs hi (by rw [hb₁]; exact refLt)).mono
      (fun _ _ h => ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1, h.2.2.1⟩⟩) fun _ _ h => h)
    (fun s g => (VG.Proof.Argon2.Arm.Derive.fillCompress_ok T.hp₁ g.1 hl hs hi (by rw [hb₁]; exact refLt) g.2.1).mono
      fun t ⟨f, l, _⟩ => ⟨f, by rw [l _ (by decide), g.2.2]⟩)
    (fun s g => (VG.Proof.Argon2.Arm.Derive.fillCompress_ok T.hp₂ g.1 hl₂ hs hi₂ (by rw [← T.pb.blocksN_eq, hb₁]; exact refLt) g.2.1).mono
      fun t ⟨f, l, _⟩ => ⟨f, by rw [l _ (by decide), g.2.2]⟩)) ?_
  exact T.fillWrite_rel.mono (fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, by rw [h.1.2, h.2.2, T.pb.memP_eq]⟩) fun _ _ h => h

end Two

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.FillCT3`. -/
section

/-!
# Argon2 on ARMv7: the filling loops, in two runs

The loops run in lockstep in two runs with the same public data: their
positions and counters agree, and so do the indices of the data-dependent
references still to be made (the rest of `Spec.Argon2.references`), from
which each block's reference agrees (`ref_same`). `passes_rel`: the filling
loops leak the same trace in two runs whose references agree.
-/

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

theorem slotsOkL : VG.Arm.Taint.SlotsOk (VG.Proof.Argon2.Arm.Derive.τB [(0, 72, 12), (0, 92, 12), (0, 132, 4)]) := by
  intro x hx
  simp only [VG.Proof.Argon2.Arm.Derive.τB, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [VG.Proof.Argon2.Arm.Derive.τB]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- `setLocal d v`, alone. -/
theorem setLocal_w {s : State} {st : FillState} (h : VG.Proof.Argon2.Arm.Derive.FB s₀ st s) {d : Nat} (hd : d + 4 ≤ 144)
    (hd' : ∀ e ∈ [divisorOff, segLenOff, laneLenOff, strideOff], e + 4 ≤ d ∨ d + 4 ≤ e) {v : BitVec 32}
    (hv : encodable v = true) :
    WP isa (.block (Impl.Argon2.Arm.Derive.setLocal d v)) s fun t => VG.Proof.Argon2.Arm.Derive.FB s₀ st t ∧ VG.Proof.Argon2.Arm.Derive.lw s₀ t d = v ∧
      ∀ e, e + 4 ≤ 256 → (d + 4 ≤ e ∨ e + 4 ≤ d) → VG.Proof.Argon2.Arm.Derive.lw s₀ t e = VG.Proof.Argon2.Arm.Derive.lw s₀ s e := by
  rw [← List.append_nil (Impl.Argon2.Arm.Derive.setLocal _ _)]
  exact VG.Proof.Argon2.Arm.Derive.setLocal_ok hp h hd hd' hv fun t f v o _ => WP.block_nil ⟨f, v, o⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.Arm.Derive.Two s₀₁ s₀₂)
include T

theorem wordsL {st₁ st₂ : FillState} {pass slice lane : Nat} {s₁ s₂ : State}
    (h₁ : VG.Proof.Argon2.Arm.Derive.LS s₀₁ st₁ pass slice lane s₁) (h₂ : VG.Proof.Argon2.Arm.Derive.LS s₀₂ st₂ pass slice lane s₂) :
    ∀ d ∈ VG.Proof.Argon2.Arm.Derive.wsL, VG.Proof.Argon2.Arm.Derive.lw s₀₁ s₁ d = VG.Proof.Argon2.Arm.Derive.lw s₀₂ s₂ d := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  intro d hd
  simp only [VG.Proof.Argon2.Arm.Derive.wsL, List.mem_cons, List.not_mem_nil, or_false] at hd
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
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.LS s₀₁ st₁ pass slice lane s₁ ∧ VG.Proof.Argon2.Arm.Derive.LS s₀₂ st₂ pass slice lane s₂)
      Impl.Argon2.Arm.Derive.segmentStart fun _ _ => True :=
  T.leaf VG.Proof.Argon2.Arm.Derive.wsL [(0, 72, 12), (0, 92, 12), (0, 132, 4)] [] VG.Proof.Argon2.Arm.Derive.slotsOkL (by decide)
    (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, T.wordsL h.1 h.2, by simp⟩) ⟨_, by taint_decide⟩

/-- A block of a segment and the index advanced, in two runs at the same
position whose reference blocks agree. -/
theorem segBody_rel {pass slice lane i c : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32)
    (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀₁) (hs : slice < 4) (hi : i < (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i)
    (href : Spec.Argon2.reference (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice i
        (Proof.Argon2.FillStep.random (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice i X₁.memory) =
      Spec.Argon2.reference (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass lane slice i
        (Proof.Argon2.FillStep.random (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass lane slice i X₂.memory)) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.FS s₀₁ pass slice lane i c X₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.FS s₀₂ pass slice lane i c X₂ s₂)
      (.seq Impl.Argon2.Arm.Derive.fillBlock
        (.block (Impl.Argon2.Arm.Derive.advance indexOff segLenOff)))
      fun v₁ v₂ => (VG.Proof.Argon2.Arm.Derive.FS s₀₁ pass slice lane (i + 1) (VG.Proof.Argon2.Arm.Derive.ctrNext (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice i c)
          (Spec.Argon2.fillBlock (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice lane i X₁) v₁ ∧
          VG.Arm.eval .ne v₁ = some (!decide (i + 1 = (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen))) ∧
        (VG.Proof.Argon2.Arm.Derive.FS s₀₂ pass slice lane (i + 1) (VG.Proof.Argon2.Arm.Derive.ctrNext (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass slice i c)
          (Spec.Argon2.fillBlock (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass slice lane i X₂) v₂ ∧
          VG.Arm.eval .ne v₂ = some (!decide (i + 1 = (VG.Proof.Argon2.Arm.Derive.prm s₀₂).segmentLen))) := by
  have pe := T.pb.prm_eq
  have hi₂ : i < (VG.Proof.Argon2.Arm.Derive.prm s₀₂).segmentLen := pe ▸ hi
  have hl₂ : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  refine rel_wp (RelCT.seqW (T.fillBlock_rel hpass hl hs hi active href)
    (fun s h => VG.Proof.Argon2.Arm.Derive.fillBlock_ok T.hp₁ h hpass hl hs hi active)
    (fun s h => VG.Proof.Argon2.Arm.Derive.fillBlock_ok T.hp₂ h hpass hl₂ hs hi₂ active)
    (T.leafF [] (fun s₁ s₂ h => by
      have h₂ := h.2
      rw [← pe] at h₂
      exact ⟨⟨_, _, _, _, _, h.1.w, h₂.w⟩, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => VG.Proof.Argon2.Arm.Derive.segStep_ok T.hp₁ h hpass hl hs hi active) (fun s h => VG.Proof.Argon2.Arm.Derive.segStep_ok T.hp₂ h hpass hl₂ hs hi₂ active)

/-- `segment` leaks the same trace in two runs at the same lane whose
references in it agree. -/
theorem segment_rel {pass slice lane : Nat} {st₁ st₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hl : lane < VG.Proof.Argon2.Arm.Derive.lanesN s₀₁)
    (hind : (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice 0 (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen st₁).indices =
      (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice 0 (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen st₂).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.LS s₀₁ st₁ pass slice lane s₁ ∧ VG.Proof.Argon2.Arm.Derive.LS s₀₂ st₂ pass slice lane s₂)
      Impl.Argon2.Arm.Derive.segment fun _ _ => True := by
  have pe := T.pb.prm_eq
  have s2 := T.hp₁.segLen_two
  have hS : Proof.Argon2.segmentStart pass slice ≤ 2 := by unfold Proof.Argon2.segmentStart; split <;> omega
  have hS2 : pass = 0 → slice = 0 → Proof.Argon2.segmentStart pass slice = 2 := fun a b => by
    unfold Proof.Argon2.segmentStart; rw [ite_eq_left ⟨a, b⟩]
  rw [Proof.Argon2.segment_start _ _ _ _ _ s2, Proof.Argon2.segment_start _ _ _ _ _ s2] at hind
  generalize hSd : Proof.Argon2.segmentStart pass slice = S at hS hS2 hind
  generalize hL : (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen = L at hind s2
  have hL₂ : (VG.Proof.Argon2.Arm.Derive.prm s₀₂).segmentLen = L := by rw [← pe, hL]
  unfold Impl.Argon2.Arm.Derive.segment
  refine RelCT.seq (rel_wp T.segmentStart_rel
    (fun s h => VG.Proof.Argon2.Arm.Derive.segmentStart_ok T.hp₁ h hpass hs) (fun s h => VG.Proof.Argon2.Arm.Derive.segmentStart_ok T.hp₂ h hpass hs)) ?_
  rw [hSd]
  refine RelCT.seqW (T.leafF [] (fun s₁ s₂ h => ⟨⟨_, _, _, _, _, h.1.w, h.2.w⟩, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.segCmp_ok T.hp₁ h hS) (fun s h => VG.Proof.Argon2.Arm.Derive.segCmp_ok T.hp₂ h hS) ?_
  refine RelCT.ite (fun s₁ s₂ h => by
      show VG.Arm.eval .eq s₁ = VG.Arm.eval .eq s₂
      rw [h.1.2, h.2.2, hL, hL₂]) (RelCT.nil fun _ _ _ => trivial) ?_
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ i, n = L - i ∧ S ≤ i ∧ i < L ∧ ∃ c,
      VG.Proof.Argon2.Arm.Derive.FS s₀₁ pass slice lane i c (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice S (i - S) st₁) s₁ ∧
      VG.Proof.Argon2.Arm.Derive.FS s₀₂ pass slice lane i c (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice S (i - S) st₂) s₂ ∧
      (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice i (L - i)
          (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice S (i - S) st₁)).indices =
        (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice i (L - i)
          (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice S (i - S) st₂)).indices) ?step (L - S)).mono
    (fun s₁ s₂ ⟨⟨⟨h₁, c₁⟩, ⟨h₂, _⟩⟩, e⟩ => ?init) fun _ _ h => h
  case init =>
    have hb : S < L := by
      rw [show isa.eval .eq s₁ = VG.Arm.eval .eq s₁ from rfl, c₁, hL] at e
      have := of_decide_eq_false (Option.some.inj e)
      omega
    exact ⟨S, rfl, Nat.le_refl _, hb, 0, by rw [Nat.sub_self]; exact h₁, by rw [Nat.sub_self]; exact h₂,
      by rw [Nat.sub_self]; exact hind⟩
  case step =>
    intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨i, hn, hSi, hi, c, h₁, h₂, hidx⟩ e₁ e₂
    have active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ i := by
      by_cases a : pass = 0
      · by_cases b : slice = 0
        · have := hS2 a b; omega
        · exact .inr (.inl b)
      · exact .inl a
    rw [show L - i = (L - (i + 1)) + 1 by omega] at hidx
    have href := VG.Proof.Argon2.Arm.Derive.ref_same (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice i (L - (i + 1)) _ _ active hidx
    rw [Proof.Argon2.segment_succ, Proof.Argon2.segment_succ] at hidx
    obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.segBody_rel (c := c) hpass hl hs (by rw [hL]; exact hi) active
      (by rw [← pe]; exact href) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
    rw [← pe] at g₂ c₂
    have eq₁ : ∀ X, Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice S (i + 1 - S) X =
        Spec.Argon2.fillBlock (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice lane i (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass lane slice S (i - S) X) :=
      fun X => by rw [show i + 1 - S = (i - S) + 1 by omega, VG.Proof.Argon2.Arm.Derive.segment_snoc, show S + (i - S) = i by omega]
    rw [← eq₁] at g₁ g₂ hidx
    rw [← eq₁] at hidx
    rw [hL] at c₁ c₂
    refine ⟨ht, by show VG.Arm.eval .ne s₁' = VG.Arm.eval .ne s₂'; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
    have e : i + 1 ≠ L := by
      rw [show isa.eval .ne s₁' = VG.Arm.eval .ne s₁' from rfl, c₁] at hc
      simpa using hc
    exact ⟨L - (i + 1), by omega, i + 1, rfl, by omega, by omega, _, g₁, g₂, hidx⟩

/-- A lane's segment and the lane advanced, in two runs. -/
theorem laneBody_rel {pass slice l : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hl : l < VG.Proof.Argon2.Arm.Derive.lanesN s₀₁)
    (hind : (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass l slice 0 (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen X₁).indices =
      (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass l slice 0 (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen X₂).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.LS s₀₁ X₁ pass slice l s₁ ∧ VG.Proof.Argon2.Arm.Derive.LS s₀₂ X₂ pass slice l s₂)
      (.seq Impl.Argon2.Arm.Derive.segment (.block (Impl.Argon2.Arm.Derive.advance laneOff (argOff 7))))
      fun v₁ v₂ => (VG.Proof.Argon2.Arm.Derive.LS s₀₁ (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass l slice 0 (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen X₁) pass slice
          (l + 1) v₁ ∧ VG.Arm.eval .ne v₁ = some (!decide (l + 1 = VG.Proof.Argon2.Arm.Derive.lanesN s₀₁))) ∧
        (VG.Proof.Argon2.Arm.Derive.LS s₀₂ (Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass l slice 0 (VG.Proof.Argon2.Arm.Derive.prm s₀₂).segmentLen X₂) pass slice (l + 1) v₂ ∧
          VG.Arm.eval .ne v₂ = some (!decide (l + 1 = VG.Proof.Argon2.Arm.Derive.lanesN s₀₂))) := by
  have hl₂ : l < VG.Proof.Argon2.Arm.Derive.lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  exact rel_wp (RelCT.seqW (T.segment_rel hpass hs hl hind)
    (fun s h => VG.Proof.Argon2.Arm.Derive.segment_ok T.hp₁ h hpass hs hl) (fun s h => VG.Proof.Argon2.Arm.Derive.segment_ok T.hp₂ h hpass hs hl₂)
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => VG.Proof.Argon2.Arm.Derive.laneStep_ok T.hp₁ h hpass hs hl) (fun s h => VG.Proof.Argon2.Arm.Derive.laneStep_ok T.hp₂ h hpass hs hl₂)

/-- `lanesLoop` leaks the same trace in two runs at the same slice whose
references in it agree. -/
theorem lanes_rel {pass slice : Nat} {Y₁ Y₂ : FillState} (hpass : pass < 2 ^ 32) (hs : slice < 4)
    (hind : (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice 0 (VG.Proof.Argon2.Arm.Derive.lanesN s₀₁) Y₁).indices =
      (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice 0 (VG.Proof.Argon2.Arm.Derive.lanesN s₀₁) Y₂).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.SS s₀₁ Y₁ pass slice s₁ ∧ VG.Proof.Argon2.Arm.Derive.SS s₀₂ Y₂ pass slice s₂)
      Impl.Argon2.Arm.Derive.lanesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.Arm.Derive.lanesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (VG.Proof.Argon2.Arm.Derive.setLocal_w T.hp₁ h.fb (d := laneOff) (by decide) (by decide) (by decide)).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, by rw [o _ (by decide) (by decide)]; exact h.slice,
        v⟩ : VG.Proof.Argon2.Arm.Derive.LS s₀₁ Y₁ pass slice 0 t))
    (fun s h => (VG.Proof.Argon2.Arm.Derive.setLocal_w T.hp₂ h.fb (d := laneOff) (by decide) (by decide) (by decide)).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, by rw [o _ (by decide) (by decide)]; exact h.slice,
        v⟩ : VG.Proof.Argon2.Arm.Derive.LS s₀₂ Y₂ pass slice 0 t)) ?_
  generalize hN : VG.Proof.Argon2.Arm.Derive.lanesN s₀₁ = N at hind hl1
  have hN₂ : VG.Proof.Argon2.Arm.Derive.lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      VG.Proof.Argon2.Arm.Derive.LS s₀₁ (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice 0 l Y₁) pass slice l s₁ ∧
      VG.Proof.Argon2.Arm.Derive.LS s₀₂ (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice 0 l Y₂) pass slice l s₂ ∧
      (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice l (N - l) (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice 0 l Y₁)).indices =
        (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice l (N - l) (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice 0 l Y₂)).indices)
    ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, hl1, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, h₁, h₂, hidx⟩ e₁ e₂
  rw [show N - l = (N - (l + 1)) + 1 by omega] at hidx
  have hseg := Proof.Argon2.lanes_first_segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice l (N - (l + 1)) _ _ s2 hidx
  rw [Proof.Argon2.lanes_succ, Proof.Argon2.lanes_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.laneBody_rel hpass hs (by rw [hN]; exact hl) hseg
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe] at g₂
  have eq : ∀ X, Proof.Argon2.segment (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass l slice 0 (VG.Proof.Argon2.Arm.Derive.prm s₀₁).segmentLen
      (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice 0 l X) = Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass slice 0 (l + 1) X :=
    fun X => by unfold Proof.Argon2.lanes; rw [VG.Proof.Argon2.Arm.Derive.foldl_range'_snoc, Nat.zero_add]
  rw [eq] at g₁ g₂ hidx
  rw [eq] at hidx
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show VG.Arm.eval .ne s₁' = VG.Arm.eval .ne s₂'; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 ≠ N := by
    rw [show isa.eval .ne s₁' = VG.Arm.eval .ne s₁' from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega, l + 1, rfl, by omega, g₁, g₂, hidx⟩

/-- A slice's lanes and the slice advanced, in two runs. -/
theorem sliceBody_rel {pass j : Nat} {X₁ X₂ : FillState} (hpass : pass < 2 ^ 32) (hj : j < 4)
    (hind : (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass j 0 (VG.Proof.Argon2.Arm.Derive.lanesN s₀₁) X₁).indices =
      (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass j 0 (VG.Proof.Argon2.Arm.Derive.lanesN s₀₁) X₂).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.SS s₀₁ X₁ pass j s₁ ∧ VG.Proof.Argon2.Arm.Derive.SS s₀₂ X₂ pass j s₂)
      (.seq Impl.Argon2.Arm.Derive.lanesLoop (.block (Impl.Argon2.Arm.Derive.advanceImm sliceOff 4)))
      fun v₁ v₂ => (VG.Proof.Argon2.Arm.Derive.SS s₀₁ (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass j 0 (VG.Proof.Argon2.Arm.Derive.lanesN s₀₁) X₁) pass (j + 1) v₁ ∧
          VG.Arm.eval .ne v₁ = some (!decide (j + 1 = 4))) ∧
        (VG.Proof.Argon2.Arm.Derive.SS s₀₂ (Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₂) pass j 0 (VG.Proof.Argon2.Arm.Derive.lanesN s₀₂) X₂) pass (j + 1) v₂ ∧
          VG.Arm.eval .ne v₂ = some (!decide (j + 1 = 4))) :=
  rel_wp (RelCT.seqW (T.lanes_rel hpass hj hind)
    (fun s h => VG.Proof.Argon2.Arm.Derive.lanes_ok T.hp₁ h hpass hj) (fun s h => VG.Proof.Argon2.Arm.Derive.lanes_ok T.hp₂ h hpass hj)
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => VG.Proof.Argon2.Arm.Derive.sliceStep_ok T.hp₁ h hpass hj) (fun s h => VG.Proof.Argon2.Arm.Derive.sliceStep_ok T.hp₂ h hpass hj)

/-- `slicesLoop` leaks the same trace in two runs at the same pass whose
references in it agree. -/
theorem slices_rel {pass : Nat} {Z₁ Z₂ : FillState} (hpass : pass < 2 ^ 32)
    (hind : (Proof.Argon2.slices (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass 0 4 Z₁).indices =
      (Proof.Argon2.slices (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass 0 4 Z₂).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.PS s₀₁ Z₁ pass s₁ ∧ VG.Proof.Argon2.Arm.Derive.PS s₀₂ Z₂ pass s₂)
      Impl.Argon2.Arm.Derive.slicesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.Arm.Derive.slicesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (VG.Proof.Argon2.Arm.Derive.setLocal_w T.hp₁ h.fb (d := sliceOff) (by decide) (by decide) (by decide)).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, v⟩ : VG.Proof.Argon2.Arm.Derive.SS s₀₁ Z₁ pass 0 t))
    (fun s h => (VG.Proof.Argon2.Arm.Derive.setLocal_w T.hp₂ h.fb (d := sliceOff) (by decide) (by decide) (by decide)).mono fun t ⟨f, v, o⟩ =>
      (⟨f, by rw [o _ (by decide) (by decide)]; exact h.pass, v⟩ : VG.Proof.Argon2.Arm.Derive.SS s₀₂ Z₂ pass 0 t)) ?_
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ j, n = 4 - j ∧ j < 4 ∧
      VG.Proof.Argon2.Arm.Derive.SS s₀₁ (Proof.Argon2.slices (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass 0 j Z₁) pass j s₁ ∧
      VG.Proof.Argon2.Arm.Derive.SS s₀₂ (Proof.Argon2.slices (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass 0 j Z₂) pass j s₂ ∧
      (Proof.Argon2.slices (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass j (4 - j) (Proof.Argon2.slices (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass 0 j Z₁)).indices =
        (Proof.Argon2.slices (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass j (4 - j) (Proof.Argon2.slices (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass 0 j Z₂)).indices)
    ?step 4).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, rfl, by decide, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, hn, hj, h₁, h₂, hidx⟩ e₁ e₂
  rw [show 4 - j = (3 - j) + 1 by omega] at hidx
  have hl := Proof.Argon2.slices_first_lane_fold (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass j (3 - j) _ _ s2 hidx
  rw [Proof.Argon2.slices_succ, Proof.Argon2.slices_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.sliceBody_rel hpass hj hl s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe, ← le] at g₂
  have eq : ∀ X, Proof.Argon2.lanes (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass j 0 (VG.Proof.Argon2.Arm.Derive.lanesN s₀₁) (Proof.Argon2.slices (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass 0 j X) =
      Proof.Argon2.slices (VG.Proof.Argon2.Arm.Derive.prm s₀₁) pass 0 (j + 1) X :=
    fun X => by unfold Proof.Argon2.slices; rw [VG.Proof.Argon2.Arm.Derive.foldl_range'_snoc, Nat.zero_add]; rfl
  rw [eq] at g₁ g₂
  rw [show 3 - j = 4 - (j + 1) by omega] at hidx
  refine ⟨ht, by show VG.Arm.eval .ne s₁' = VG.Arm.eval .ne s₂'; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : j + 1 ≠ 4 := by
    rw [show isa.eval .ne s₁' = VG.Arm.eval .ne s₁' from rfl, c₁] at hc
    simpa using hc
  refine ⟨4 - (j + 1), by omega, j + 1, rfl, by omega, g₁, g₂, ?_⟩
  rw [← eq, ← eq]
  exact hidx

/-- A pass and the pass advanced, in two runs. -/
theorem passBody_rel {k : Nat} {X₁ X₂ : FillState} (hk : k < VG.Proof.Argon2.Arm.Derive.itersN s₀₁)
    (hind : (Spec.Argon2.fillPass (VG.Proof.Argon2.Arm.Derive.prm s₀₁) X₁ k).indices = (Spec.Argon2.fillPass (VG.Proof.Argon2.Arm.Derive.prm s₀₁) X₂ k).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.PS s₀₁ X₁ k s₁ ∧ VG.Proof.Argon2.Arm.Derive.PS s₀₂ X₂ k s₂)
      (.seq Impl.Argon2.Arm.Derive.slicesLoop (.block (Impl.Argon2.Arm.Derive.advance passOff (argOff 5))))
      fun v₁ v₂ => (VG.Proof.Argon2.Arm.Derive.PS s₀₁ (Spec.Argon2.fillPass (VG.Proof.Argon2.Arm.Derive.prm s₀₁) X₁ k) (k + 1) v₁ ∧
          VG.Arm.eval .ne v₁ = some (!decide (k + 1 = VG.Proof.Argon2.Arm.Derive.itersN s₀₁))) ∧
        (VG.Proof.Argon2.Arm.Derive.PS s₀₂ (Spec.Argon2.fillPass (VG.Proof.Argon2.Arm.Derive.prm s₀₂) X₂ k) (k + 1) v₂ ∧
          VG.Arm.eval .ne v₂ = some (!decide (k + 1 = VG.Proof.Argon2.Arm.Derive.itersN s₀₂))) := by
  have hk₂ : k < VG.Proof.Argon2.Arm.Derive.itersN s₀₂ := T.pb.itersN_eq ▸ hk
  have hpl : VG.Proof.Argon2.Arm.Derive.itersN s₀₁ < 2 ^ 32 := (VG.Proof.Argon2.Arm.Derive.arg s₀₁ 5).isLt
  rw [← Proof.Argon2.slices_pass, ← Proof.Argon2.slices_pass] at hind
  exact rel_wp (RelCT.seqW (T.slices_rel (by omega) hind)
    (fun s h => VG.Proof.Argon2.Arm.Derive.slices_ok T.hp₁ h (by omega)) (fun s h => VG.Proof.Argon2.Arm.Derive.slices_ok T.hp₂ h (by omega))
    (T.leafI [] (fun s₁ s₂ h => ⟨h.1.fb.inv, h.2.fb.inv, by simp⟩) ⟨_, by taint_decide⟩))
    (fun s h => VG.Proof.Argon2.Arm.Derive.passStep_ok T.hp₁ h hk) (fun s h => VG.Proof.Argon2.Arm.Derive.passStep_ok T.hp₂ h hk₂)

/-- `passesLoop` leaks the same trace in two runs whose references agree. -/
theorem passes_rel {W₁ W₂ : FillState}
    (hind : (Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀₁) 0 (VG.Proof.Argon2.Arm.Derive.itersN s₀₁) W₁).indices =
      (Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀₁) 0 (VG.Proof.Argon2.Arm.Derive.itersN s₀₁) W₂).indices) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.FB s₀₁ W₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.FB s₀₂ W₂ s₂) Impl.Argon2.Arm.Derive.passesLoop fun _ _ => True := by
  have pe := T.pb.prm_eq
  have ie := T.pb.itersN_eq
  have hp1 := T.hp₁.passes_pos
  have s2 := T.hp₁.segLen_two
  unfold Impl.Argon2.Arm.Derive.passesLoop
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.inv, h.2.inv, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => (VG.Proof.Argon2.Arm.Derive.setLocal_w T.hp₁ h (d := passOff) (by decide) (by decide) (by decide)).mono fun t ⟨f, v, _⟩ =>
      (⟨f, v⟩ : VG.Proof.Argon2.Arm.Derive.PS s₀₁ W₁ 0 t))
    (fun s h => (VG.Proof.Argon2.Arm.Derive.setLocal_w T.hp₂ h (d := passOff) (by decide) (by decide) (by decide)).mono fun t ⟨f, v, _⟩ =>
      (⟨f, v⟩ : VG.Proof.Argon2.Arm.Derive.PS s₀₂ W₂ 0 t)) ?_
  generalize hN : VG.Proof.Argon2.Arm.Derive.itersN s₀₁ = N at hind hp1
  have hN₂ : VG.Proof.Argon2.Arm.Derive.itersN s₀₂ = N := by rw [← ie, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ k, n = N - k ∧ k < N ∧
      VG.Proof.Argon2.Arm.Derive.PS s₀₁ (Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀₁) 0 k W₁) k s₁ ∧
      VG.Proof.Argon2.Arm.Derive.PS s₀₂ (Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀₁) 0 k W₂) k s₂ ∧
      (Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀₁) k (N - k) (Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀₁) 0 k W₁)).indices =
        (Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀₁) k (N - k) (Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀₁) 0 k W₂)).indices)
    ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, by omega, h.1, h.2, hind⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨k, hn, hk, h₁, h₂, hidx⟩ e₁ e₂
  rw [show N - k = (N - (k + 1)) + 1 by omega] at hidx
  have hpass := Proof.Argon2.iterations_first_pass (VG.Proof.Argon2.Arm.Derive.prm s₀₁) k (N - (k + 1)) _ _ s2 hidx
  rw [Proof.Argon2.iterations_succ, Proof.Argon2.iterations_succ] at hidx
  obtain ⟨ht, ⟨g₁, c₁⟩, ⟨g₂, c₂⟩⟩ := T.passBody_rel (by rw [hN]; exact hk) hpass s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  rw [← pe] at g₂
  have eq : ∀ X, Spec.Argon2.fillPass (VG.Proof.Argon2.Arm.Derive.prm s₀₁) (Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀₁) 0 k X) k =
      Proof.Argon2.iterations (VG.Proof.Argon2.Arm.Derive.prm s₀₁) 0 (k + 1) X :=
    fun X => by unfold Proof.Argon2.iterations; rw [VG.Proof.Argon2.Arm.Derive.foldl_range'_snoc, Nat.zero_add]
  rw [eq] at g₁ g₂ hidx
  rw [eq] at hidx
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show VG.Arm.eval .ne s₁' = VG.Arm.eval .ne s₂'; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : k + 1 ≠ N := by
    rw [show isa.eval .ne s₁' = VG.Arm.eval .ne s₁' from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (k + 1), by omega, k + 1, rfl, by omega, g₁, g₂, hidx⟩

end Two

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.ReduceCT`. -/
section

/-!
# Argon2 on ARMv7: the final block and the tag, in two runs

`reduce_rel`: XORing every lane's last block into the first leaks the same
trace in two runs (the lane's last block's address is related by
correctness); `finalOutput_rel`: so does the call of H′ that writes the tag.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd wp_mov wp_sub op2_imm op2_reg)
open VG.Proof.Sha512.Arm (Only)
open VG.Spec.Argon2 (Block zeroBlock)
open VG.Impl.Argon2.Arm.Derive (argOff laneOff laneLenOff ld st)

theorem RI.of_only {s₀ s t : State} {M : Array Block} {l : Nat} (h : VG.Proof.Argon2.Arm.Derive.RI s₀ M l s) {ds : List Reg}
    (k : Only ds s t) (h11 : Reg.r11 ∉ ds) : VG.Proof.Argon2.Arm.Derive.RI s₀ M l t :=
  ⟨h.inv.only k h11, h.pr.of_mem k.mem, by rw [VG.Proof.Argon2.Arm.Derive.lw_mem k.mem]; exact h.lane, by rw [k.mem]; exact h.first,
    fun j hj j0 => by rw [k.mem]; exact h.rest j hj j0⟩

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.Derive.DPre s₀)
include hp

/-- The first part of a lane's reduction: `r0 :=` the address of its last block. -/
theorem redPart1_ok {s : State} {M : Array Block} {l : Nat} (h : VG.Proof.Argon2.Arm.Derive.RI s₀ M l s) (hl : l < VG.Proof.Argon2.Arm.Derive.lanesN s₀) :
    WP isa (.block (([ld .r0 laneOff, ld .r1 laneLenOff, .dp .sub .r1 .r1 (.imm 1)] : List Instr) ++
      Impl.Argon2.Arm.Derive.blockAddr)) s fun t => VG.Proof.Argon2.Arm.Derive.RI s₀ M l t ∧
      t.gpr .r0 = VG.Proof.Argon2.Arm.Derive.memP s₀ + BitVec.ofNat 32 ((l * (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen + ((VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1)) * 1024) := by
  have L8 := VG.Proof.Argon2.Arm.Derive.laneLen_ge hp
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp h.inv (d := laneOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldloc hp i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => wp_sub (op2_imm (by decide)) fun s₃ u₃ => ?_
  have o₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  have i₃ := h.inv.only o₃ (by decide)
  rw [← List.append_nil Impl.Argon2.Arm.Derive.blockAddr]
  refine VG.Proof.Argon2.Arm.Derive.blockAddr_ok hp i₃ (h.pr.of_mem o₃.mem) hl (col := (VG.Proof.Argon2.Arm.Derive.prm s₀).laneLen - 1) (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.lane])
    (by rw [u₃.gpr, u₂.gpr, VG.Proof.Argon2.Arm.Derive.lw_mem u₁.mem, h.pr.laneLen, VG.Proof.Argon2.Arm.Derive.ofNat_pred (by omega) rfl]) fun s₄ a₄ k₄ =>
      WP.block_nil ⟨h.of_only (o₃.trans k₄) (by decide), a₄⟩

/-- The instructions before `finalOutput`'s call of H′. -/
theorem foBlk_ok {s : State} (h : VG.Proof.Argon2.Arm.Derive.Inv s₀ s) :
    WP isa (.block [ld .r0 (argOff 13), .mov .r1 (.imm 1024), ld .r2 (argOff 16), ld .r3 (argOff 17),
      ld .r12 (argOff 15)]) s fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ t.gpr .r12 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧
      t.gpr .r0 = VG.Proof.Argon2.Arm.Derive.memP s₀ ∧ t.gpr .r1 = 1024 ∧ t.gpr .r2 = VG.Proof.Argon2.Arm.Derive.outP s₀ ∧ t.gpr .r3 = VG.Proof.Argon2.Arm.Derive.arg s₀ 17 := by
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide)
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₂ (i := 16) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₃ (i := 17) (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide)
  refine VG.Proof.Argon2.Arm.Derive.wp_ldarg hp i₄ (i := 15) (by decide) fun s₅ u₅ => WP.block_nil ⟨i₄.upd u₅ (by decide),
    u₅.gpr, ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr]

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.Arm.Derive.Two s₀₁ s₀₂)
include T

/-- `reduce` leaks the same trace in two runs. -/
theorem reduce_rel {M₁ M₂ : Array Block} :
    RelCT isa (fun s₁ s₂ => (VG.Proof.Argon2.Arm.Derive.Inv s₀₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀₁ s₁ ∧ Represents s₁.mem (VG.Proof.Argon2.Arm.Derive.memB s₀₁) (VG.Proof.Argon2.Arm.Derive.prm s₀₁).blocks M₁) ∧
      (VG.Proof.Argon2.Arm.Derive.Inv s₀₂ s₂ ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀₂ s₂ ∧ Represents s₂.mem (VG.Proof.Argon2.Arm.Derive.memB s₀₂) (VG.Proof.Argon2.Arm.Derive.prm s₀₂).blocks M₂))
      Impl.Argon2.Arm.Derive.reduce fun _ _ => True := by
  have pe := T.pb.prm_eq
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  unfold Impl.Argon2.Arm.Derive.reduce
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.reduceStart_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => VG.Proof.Argon2.Arm.Derive.reduceStart_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  generalize hN : VG.Proof.Argon2.Arm.Derive.lanesN s₀₁ = N at hl1
  have hN₂ : VG.Proof.Argon2.Arm.Derive.lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      VG.Proof.Argon2.Arm.Derive.RI s₀₁ M₁ l s₁ ∧ VG.Proof.Argon2.Arm.Derive.RI s₀₂ M₂ l s₂) ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, hl1, h.1, h.2⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, g₁, g₂⟩ e₁ e₂
  have body : RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.RI s₀₁ M₁ l s₁ ∧ VG.Proof.Argon2.Arm.Derive.RI s₀₂ M₂ l s₂)
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
      (fun s h => VG.Proof.Argon2.Arm.Derive.redPart1_ok T.hp₁ h (by rw [hN]; exact hl))
      (fun s h => VG.Proof.Argon2.Arm.Derive.redPart1_ok T.hp₂ h (by rw [hN₂]; exact hl)) ?_)
    exact T.leafI [.r0] (fun s₁ s₂ h => ⟨h.1.1.inv, h.2.1.inv, by
      simp only [List.mem_singleton, forall_eq]; rw [h.1.2, h.2.2, pe, T.pb.memP_eq]⟩) ⟨_, by taint_decide⟩
  obtain ⟨ht, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩ := rel_wp body
    (fun s h => VG.Proof.Argon2.Arm.Derive.reduceLane_ok T.hp₁ h (by rw [hN]; exact hl))
    (fun s h => VG.Proof.Argon2.Arm.Derive.reduceLane_ok T.hp₂ h (by rw [hN₂]; exact hl)) s₁ s₂ t₁ t₂ s₁' s₂' ⟨g₁, g₂⟩ e₁ e₂
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show VG.Arm.eval .ne s₁' = VG.Arm.eval .ne s₂'; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 ≠ N := by
    rw [show isa.eval .ne s₁' = VG.Arm.eval .ne s₁' from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega, l + 1, rfl, by omega, k₁, k₂⟩

/-- `finalOutput` leaks the same trace in two runs. -/
theorem finalOutput_rel :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.Derive.Inv s₀₁ s₁ ∧ VG.Proof.Argon2.Arm.Derive.Inv s₀₂ s₂) Impl.Argon2.Arm.Derive.finalOutput fun _ _ => True := by
  have pre : ∀ {s₀ : State}, VG.Proof.Argon2.Arm.Derive.DPre s₀ → ∀ {t : State}, VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ t.gpr .r12 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧
      t.gpr .r0 = VG.Proof.Argon2.Arm.Derive.memP s₀ ∧ t.gpr .r1 = 1024 ∧ t.gpr .r2 = VG.Proof.Argon2.Arm.Derive.outP s₀ ∧ t.gpr .r3 = VG.Proof.Argon2.Arm.Derive.arg s₀ 17 →
      VG.Proof.Argon2.Arm.Derive.Inv s₀ t ∧ t.gpr .r12 = VG.Proof.Argon2.Arm.Derive.scrP s₀ ∧
        (∃ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.locR s₀], ∃ off, State.addr (t.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .r1).toNat ≤ R.len) ∧ (t.gpr .r0).toNat + (t.gpr .r1).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [VG.Proof.Argon2.Arm.Derive.memR s₀, VG.Proof.Argon2.Arm.Derive.outR s₀], ∃ off, State.addr (t.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .r3).toNat ≤ R.len) ∧ (t.gpr .r2).toNat + (t.gpr .r3).toNat ≤ 2 ^ 32 ∧
        1 ≤ (t.gpr .r3).toNat := fun {s₀} hp {t} ⟨i, d, si, ax, di, cx⟩ => by
    have b1 := VG.Proof.Argon2.Arm.Derive.blocks_pos hp
    have hm := hp.mem_fits
    have ho := hp.out_fits
    have tg := hp.tag_ge
    refine ⟨i, d, ⟨VG.Proof.Argon2.Arm.Derive.memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ VG.Proof.Argon2.Arm.Derive.blocksN s₀ * 1024; omega⟩,
      by rw [si, ax]; show _ + 1024 ≤ 2 ^ 32; omega,
      ⟨VG.Proof.Argon2.Arm.Derive.outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + VG.Proof.Argon2.Arm.Derive.outL s₀ ≤ VG.Proof.Argon2.Arm.Derive.outL s₀; omega⟩,
      by rw [di, cx]; exact ho, by rw [cx]; show 1 ≤ VG.Proof.Argon2.Arm.Derive.outL s₀; omega⟩
  unfold Impl.Argon2.Arm.Derive.finalOutput
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => VG.Proof.Argon2.Arm.Derive.foBlk_ok T.hp₁ h) (fun s h => VG.Proof.Argon2.Arm.Derive.foBlk_ok T.hp₂ h) ?_
  refine T.hcall_rel fun s₁ s₂ ⟨k₁, k₂⟩ => ⟨pre T.hp₁ k₁, pre T.hp₂ k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.2.2.1, k₂.2.2.1, T.pb.memP_eq]
  · rw [k₁.2.2.2.1, k₂.2.2.2.1]
  · rw [k₁.2.2.2.2.1, k₂.2.2.2.2.1, T.pb.outP_eq]
  · rw [k₁.2.2.2.2.2, k₂.2.2.2.2.2, T.pb.arg_eq (by decide)]

end Two

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.BodyCT`. -/
section

/-!
# Argon2 on ARMv7: the derivation is constant time

`body_rel`: the body leaks the same trace in two runs with the same public
data and the same data-dependent references (`deriveArm.pub`), piece by
piece; `derive_ct`: so does the whole function, in its frames.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Spec.Blake2 (bytesAt)

namespace Two
variable {s₀₁ s₀₂ : State} (T : VG.Proof.Argon2.Arm.Derive.Two s₀₁ s₀₂)
include T

/-- The parameters' block leaks the same trace in two runs. -/
theorem parameters_rel :
    RelCT isa (fun s₁ s₂ => s₁ = VG.Proof.Argon2.Arm.Derive.entry s₀₁ ∧ s₂ = VG.Proof.Argon2.Arm.Derive.entry s₀₂)
      (.block (.addSp .r11 0 :: Impl.Argon2.Arm.Derive.parameters)) fun _ _ => True := by
  rw [← List.singleton_append]
  refine RelCT.block_split (RelCT.seqW (F₁ := fun s => s = VG.Proof.Argon2.Arm.Derive.entry s₀₁) (F₂ := fun s => s = VG.Proof.Argon2.Arm.Derive.entry s₀₂)
    (RelCT.quiet fun _ => rfl)
    (fun s h => by subst h; exact VG.Proof.Argon2.Arm.Derive.inv_start fun t i _ _ => WP.block_nil i)
    (fun s h => by subst h; exact VG.Proof.Argon2.Arm.Derive.inv_start fun t i _ _ => WP.block_nil i) ?_)
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1, h.2, by simp⟩) ⟨_, by taint_decide⟩

/-- The body leaks the same trace in two runs with the same data-dependent
references. -/
theorem body_rel
    (href : Spec.Argon2.references (VG.Proof.Argon2.Arm.Derive.prm s₀₁) (VG.Proof.Argon2.Arm.Derive.pwB s₀₁) (VG.Proof.Argon2.Arm.Derive.saltB s₀₁) (VG.Proof.Argon2.Arm.Derive.secB s₀₁) (VG.Proof.Argon2.Arm.Derive.adB s₀₁) =
      Spec.Argon2.references (VG.Proof.Argon2.Arm.Derive.prm s₀₂) (VG.Proof.Argon2.Arm.Derive.pwB s₀₂) (VG.Proof.Argon2.Arm.Derive.saltB s₀₂) (VG.Proof.Argon2.Arm.Derive.secB s₀₂) (VG.Proof.Argon2.Arm.Derive.adB s₀₂)) :
    RelCT isa (fun s₁ s₂ => s₁ = VG.Proof.Argon2.Arm.Derive.entry s₀₁ ∧ s₂ = VG.Proof.Argon2.Arm.Derive.entry s₀₂) Impl.Argon2.Arm.Derive.body fun _ _ => True := by
  have pe := T.pb.prm_eq
  have L8 := VG.Proof.Argon2.Arm.Derive.laneLen_ge T.hp₁
  have hind := Proof.Argon2.references_injective (VG.Proof.Argon2.Arm.Derive.prm s₀₁) (by omega) (VG.Proof.Argon2.Arm.Derive.pwB s₀₁) (VG.Proof.Argon2.Arm.Derive.saltB s₀₁) (VG.Proof.Argon2.Arm.Derive.secB s₀₁) (VG.Proof.Argon2.Arm.Derive.adB s₀₁)
    (VG.Proof.Argon2.Arm.Derive.pwB s₀₂) (VG.Proof.Argon2.Arm.Derive.saltB s₀₂) (VG.Proof.Argon2.Arm.Derive.secB s₀₂) (VG.Proof.Argon2.Arm.Derive.adB s₀₂) (by rw [href, pe])
  rw [← Proof.Argon2.iterations_fill, ← Proof.Argon2.iterations_fill] at hind
  unfold Impl.Argon2.Arm.Derive.body
  refine RelCT.seqW T.parameters_rel (G₁ := fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀₁ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀₁ t)
    (G₂ := fun t => VG.Proof.Argon2.Arm.Derive.Inv s₀₂ t ∧ VG.Proof.Argon2.Arm.Derive.Prm s₀₂ t)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.addSp .r11 0 :: Impl.Argon2.Arm.Derive.parameters)]
      exact VG.Proof.Argon2.Arm.Derive.parameters_ok T.hp₁ fun t i p => WP.block_nil ⟨i, p⟩)
    (fun s h => by
      subst h
      rw [← List.append_nil (Instr.addSp .r11 0 :: Impl.Argon2.Arm.Derive.parameters)]
      exact VG.Proof.Argon2.Arm.Derive.parameters_ok T.hp₂ fun t i p => WP.block_nil ⟨i, p⟩) ?_
  refine RelCT.seqW T.code_rel (fun s h => VG.Proof.Argon2.Arm.Derive.code_ok T.hp₁ h.1 h.2) (fun s h => VG.Proof.Argon2.Arm.Derive.code_ok T.hp₂ h.1 h.2) ?_
  refine RelCT.seqW T.memoryInit_rel (fun s h => VG.Proof.Argon2.Arm.Derive.memoryInit_ok T.hp₁ h.1 h.2.1 h.2.2)
    (fun s h => VG.Proof.Argon2.Arm.Derive.memoryInit_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW ((T.passes_rel (W₁ := Spec.Argon2.initMemory (VG.Proof.Argon2.Arm.Derive.prm s₀₁)
      (Spec.Argon2.initialHash (VG.Proof.Argon2.Arm.Derive.prm s₀₁) (VG.Proof.Argon2.Arm.Derive.pwB s₀₁) (VG.Proof.Argon2.Arm.Derive.saltB s₀₁) (VG.Proof.Argon2.Arm.Derive.secB s₀₁) (VG.Proof.Argon2.Arm.Derive.adB s₀₁)))
      (W₂ := Spec.Argon2.initMemory (VG.Proof.Argon2.Arm.Derive.prm s₀₂)
      (Spec.Argon2.initialHash (VG.Proof.Argon2.Arm.Derive.prm s₀₂) (VG.Proof.Argon2.Arm.Derive.pwB s₀₂) (VG.Proof.Argon2.Arm.Derive.saltB s₀₂) (VG.Proof.Argon2.Arm.Derive.secB s₀₂) (VG.Proof.Argon2.Arm.Derive.adB s₀₂)))
      (by rw [← pe]; exact hind)).mono (fun _ _ h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩)
      fun _ _ h => h)
    (fun s h => VG.Proof.Argon2.Arm.Derive.passes_ok T.hp₁ ⟨h.1, h.2.1, h.2.2⟩) (fun s h => VG.Proof.Argon2.Arm.Derive.passes_ok T.hp₂ ⟨h.1, h.2.1, h.2.2⟩) ?_
  refine RelCT.seqW (T.reduce_rel.mono (fun _ _ h => ⟨⟨h.1.inv, h.1.pr, h.1.mem⟩, ⟨h.2.inv, h.2.pr, h.2.mem⟩⟩)
      fun _ _ h => h)
    (fun s h => VG.Proof.Argon2.Arm.Derive.reduce_ok T.hp₁ h.inv h.pr h.mem) (fun s h => VG.Proof.Argon2.Arm.Derive.reduce_ok T.hp₂ h.inv h.pr h.mem) ?_
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
    rw [← e₁.2, ← e₂.2, VG.Proof.Argon2.Arm.Derive.ldrSps_trace l b₁ b₂ (by rw [exec_sp x₁, exec_sp x₂, hsp]) r₁ r₂]
    simp only [addrs, hsp]

theorem RelCT.restore {P : State → State → Prop} (hsp : ∀ a b, P a b → a.sp = b.sp) :
    RelCT isa P (.block Impl.Argon2.Arm.Derive.restoreRegs) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨VG.Proof.Argon2.Arm.Derive.ldrSps_trace _ s₁ s₂ (hsp _ _ hp) e₁ e₂, trivial⟩

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
  have ea := VG.Proof.Argon2.Arm.Derive.alloc_eq ha
  have eb := VG.Proof.Argon2.Arm.Derive.alloc_eq hb
  subst eu ev ex ey ea eb
  exact Two.body_rel ⟨h₁, h₂, hpub.1⟩ hpub.2 _ _ t₁ t₂ a' b' ⟨rfl, rfl⟩ e₁ e₂

theorem derive_ct : ConstantTime isa deriveArm.pre deriveArm.pub Impl.Argon2.Arm.Derive.derive :=
  derive_rel.constantTime

end VG.Proof.Argon2.Arm.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.Derive.Verified`. -/
section

/-!
# Argon2 on ARMv7: the derivation is verified

`derive_verified`: the derivation against `deriveArm` (correct, constant
time, and satisfiable: `satState`). `deriveShared_verified`: against the
shared contract `Spec.Argon2.deriveContract`, through `deriveFlat`, whose
precondition spells `DPre` out as `Sig.contract` lays the regions out.
-/

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
    ((BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.satStack[(a.toNat - 0x40000) / 4]?.getD 0)) >>> (8 * ((a.toNat - 0x40000) % 4))).setWidth 8
  else 0

def satState : State where
  gpr _ := 0
  sp := 0x40000
  n := false
  z := false
  c := false
  v := false
  mem := VG.Proof.Argon2.Arm.Derive.satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40000, 56⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

/-- The arguments of `satState`. -/
def satArgs : List Nat := [0, 0, 0, 0] ++ VG.Proof.Argon2.Arm.Derive.satStack

theorem sat_args : ∀ i < 18, VG.Proof.Argon2.Arm.Derive.arg VG.Proof.Argon2.Arm.Derive.satState i = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.satArgs[i]?.getD 0) := by decide

theorem sat_pre : VG.Proof.Argon2.Arm.Derive.DPre VG.Proof.Argon2.Arm.Derive.satState := by
  have a : ∀ i < 18, VG.Proof.Argon2.Arm.Derive.arg VG.Proof.Argon2.Arm.Derive.satState i = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.satArgs[i]?.getD 0) := VG.Proof.Argon2.Arm.Derive.sat_args
  have e : stackArgAddr VG.Proof.Argon2.Arm.Derive.satState 0 = 0x40000 := by decide
  have sp : satState.sp = 0x40000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [VG.Proof.Argon2.Arm.Derive.pwR, VG.Proof.Argon2.Arm.Derive.saltR, VG.Proof.Argon2.Arm.Derive.secR, VG.Proof.Argon2.Arm.Derive.adR, VG.Proof.Argon2.Arm.Derive.memR, VG.Proof.Argon2.Arm.Derive.scrR, VG.Proof.Argon2.Arm.Derive.outR, VG.Proof.Argon2.Arm.Derive.argR, VG.Proof.Argon2.Arm.Derive.stkR0, stkR, VG.Proof.Argon2.Arm.Derive.pwP, VG.Proof.Argon2.Arm.Derive.pwL, VG.Proof.Argon2.Arm.Derive.saltP, VG.Proof.Argon2.Arm.Derive.saltL, VG.Proof.Argon2.Arm.Derive.secP,
    VG.Proof.Argon2.Arm.Derive.secL, VG.Proof.Argon2.Arm.Derive.adP, VG.Proof.Argon2.Arm.Derive.adL, VG.Proof.Argon2.Arm.Derive.memP, VG.Proof.Argon2.Arm.Derive.blocksN, VG.Proof.Argon2.Arm.Derive.scrP, VG.Proof.Argon2.Arm.Derive.outP, VG.Proof.Argon2.Arm.Derive.outL, VG.Proof.Argon2.Arm.Derive.E0, VG.Proof.Argon2.Arm.Derive.kindV, VG.Proof.Argon2.Arm.Derive.itersN, VG.Proof.Argon2.Arm.Derive.mcostN, VG.Proof.Argon2.Arm.Derive.lanesN, VG.Proof.Argon2.Arm.Derive.threadsN, VG.Proof.Argon2.Arm.Derive.prm,
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

theorem derive_verified : Verified Arm.target Impl.Argon2.Arm.Derive.derive VG.Proof.Argon2.Arm.Derive.deriveArm :=
  ⟨fun _ hs => VG.Proof.Argon2.Arm.Derive.correct hs, VG.Proof.Argon2.Arm.Derive.derive_ct, ⟨VG.Proof.Argon2.Arm.Derive.satState, VG.Proof.Argon2.Arm.Derive.sat_pre⟩⟩

/-! ## The shared contract -/

/-- `deriveArm`, its precondition spelt out as `Sig.contract` lays the regions
out. -/
def deriveFlat : Contract Arm.isa :=
  { VG.Proof.Argon2.Arm.Derive.deriveArm with
    pre := fun s =>
      let pw : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s 1), (VG.Proof.Argon2.Arm.Derive.arg s 2).toNat⟩
      let salt : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s 3), (VG.Proof.Argon2.Arm.Derive.arg s 4).toNat⟩
      let sec : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s 9), (VG.Proof.Argon2.Arm.Derive.arg s 10).toNat⟩
      let ad : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s 11), (VG.Proof.Argon2.Arm.Derive.arg s 12).toNat⟩
      let mem : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s 13), (VG.Proof.Argon2.Arm.Derive.arg s 14).toNat * 1024⟩
      let scr : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s 15), 16384⟩
      let out : Region := ⟨State.addr (VG.Proof.Argon2.Arm.Derive.arg s 16), (VG.Proof.Argon2.Arm.Derive.arg s 17).toNat⟩
      let args : Region := ⟨stackArgAddr s 0, 56⟩
      let stack : Region := stkR s.sp 240
      s.rd = [pw, salt, sec, ad, args] ∧ s.wr = [mem, scr, out] ∧
      pw.Disjoint mem ∧ pw.Disjoint scr ∧ pw.Disjoint out ∧ salt.Disjoint mem ∧ salt.Disjoint scr ∧
      salt.Disjoint out ∧ sec.Disjoint mem ∧ sec.Disjoint scr ∧ sec.Disjoint out ∧ ad.Disjoint mem ∧
      ad.Disjoint scr ∧ ad.Disjoint out ∧ args.Disjoint mem ∧ args.Disjoint scr ∧ args.Disjoint out ∧
      mem.Disjoint scr ∧ mem.Disjoint out ∧ scr.Disjoint out ∧
      stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint sec ∧ stack.Disjoint ad ∧ stack.Disjoint mem ∧
      stack.Disjoint scr ∧ stack.Disjoint out ∧
      (VG.Proof.Argon2.Arm.Derive.arg s 1).toNat + (VG.Proof.Argon2.Arm.Derive.arg s 2).toNat ≤ 2 ^ 32 ∧ (VG.Proof.Argon2.Arm.Derive.arg s 3).toNat + (VG.Proof.Argon2.Arm.Derive.arg s 4).toNat ≤ 2 ^ 32 ∧
      (VG.Proof.Argon2.Arm.Derive.arg s 9).toNat + (VG.Proof.Argon2.Arm.Derive.arg s 10).toNat ≤ 2 ^ 32 ∧ (VG.Proof.Argon2.Arm.Derive.arg s 11).toNat + (VG.Proof.Argon2.Arm.Derive.arg s 12).toNat ≤ 2 ^ 32 ∧
      (VG.Proof.Argon2.Arm.Derive.arg s 13).toNat + (VG.Proof.Argon2.Arm.Derive.arg s 14).toNat * 1024 ≤ 2 ^ 32 ∧ (VG.Proof.Argon2.Arm.Derive.arg s 15).toNat + 16384 ≤ 2 ^ 32 ∧
      (VG.Proof.Argon2.Arm.Derive.arg s 16).toNat + (VG.Proof.Argon2.Arm.Derive.arg s 17).toNat ≤ 2 ^ 32 ∧ 240 ≤ s.sp.toNat ∧ s.sp.toNat + 56 ≤ 2 ^ 32 ∧
      (VG.Proof.Argon2.Arm.Derive.arg s 0).toNat ≤ 2 ∧
      Spec.Argon2.valid (Spec.Argon2.params (VG.Proof.Argon2.Arm.Derive.arg s 0).toNat (VG.Proof.Argon2.Arm.Derive.arg s 5).toNat (VG.Proof.Argon2.Arm.Derive.arg s 6).toNat (VG.Proof.Argon2.Arm.Derive.arg s 7).toNat
        (VG.Proof.Argon2.Arm.Derive.arg s 17).toNat) (VG.Proof.Argon2.Arm.Derive.arg s 2).toNat (VG.Proof.Argon2.Arm.Derive.arg s 4).toNat (VG.Proof.Argon2.Arm.Derive.arg s 10).toNat (VG.Proof.Argon2.Arm.Derive.arg s 12).toNat ∧
      1 ≤ (VG.Proof.Argon2.Arm.Derive.arg s 8).toNat ∧ (VG.Proof.Argon2.Arm.Derive.arg s 8).toNat < 2 ^ 24 ∧
      (VG.Proof.Argon2.Arm.Derive.arg s 14).toNat = (Spec.Argon2.params (VG.Proof.Argon2.Arm.Derive.arg s 0).toNat (VG.Proof.Argon2.Arm.Derive.arg s 5).toNat (VG.Proof.Argon2.Arm.Derive.arg s 6).toNat (VG.Proof.Argon2.Arm.Derive.arg s 7).toNat
        (VG.Proof.Argon2.Arm.Derive.arg s 17).toNat).blocks }

theorem deriveFlat_pre {s : State} (h : deriveFlat.pre s) : VG.Proof.Argon2.Arm.Derive.DPre s := by
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

theorem deriveFlat_implies : deriveArm.Implies VG.Proof.Argon2.Arm.Derive.deriveFlat :=
  ⟨fun _ h => VG.Proof.Argon2.Arm.Derive.deriveFlat_pre h, fun _ _ _ h => h, fun _ _ _ _ h => h,
    ⟨VG.Proof.Argon2.Arm.Derive.satState, by
      have a : ∀ i < 18, VG.Proof.Argon2.Arm.Derive.arg VG.Proof.Argon2.Arm.Derive.satState i = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.Derive.satArgs[i]?.getD 0) := VG.Proof.Argon2.Arm.Derive.sat_args
      have e : stackArgAddr VG.Proof.Argon2.Arm.Derive.satState 0 = 0x40000 := by decide
      simp only [VG.Proof.Argon2.Arm.Derive.deriveFlat, a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
        a 5 (by decide), a 6 (by decide), a 7 (by decide), a 8 (by decide), a 9 (by decide), a 10 (by decide),
        a 11 (by decide), a 12 (by decide), a 13 (by decide), a 14 (by decide), a 15 (by decide),
        a 16 (by decide), a 17 (by decide), e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide, by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩⟩

theorem flat_implies : deriveFlat.Implies (Spec.Argon2.deriveContract Arm.abi 240) := by
  sig_implies [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, VG.Proof.Argon2.Arm.Derive.deriveFlat, VG.Proof.Argon2.Arm.Derive.deriveArm, stkR, VG.Proof.Argon2.Arm.Derive.arg, VG.Proof.Argon2.Arm.Derive.prm, VG.Proof.Argon2.Arm.Derive.pwB,
    VG.Proof.Argon2.Arm.Derive.saltB, VG.Proof.Argon2.Arm.Derive.secB, VG.Proof.Argon2.Arm.Derive.adB, VG.Proof.Argon2.Arm.Derive.pwR, VG.Proof.Argon2.Arm.Derive.saltR, VG.Proof.Argon2.Arm.Derive.secR, VG.Proof.Argon2.Arm.Derive.adR, VG.Proof.Argon2.Arm.Derive.pwP, VG.Proof.Argon2.Arm.Derive.pwL, VG.Proof.Argon2.Arm.Derive.saltP, VG.Proof.Argon2.Arm.Derive.saltL, VG.Proof.Argon2.Arm.Derive.secP, VG.Proof.Argon2.Arm.Derive.secL, VG.Proof.Argon2.Arm.Derive.adP, VG.Proof.Argon2.Arm.Derive.adL, VG.Proof.Argon2.Arm.Derive.kindV, VG.Proof.Argon2.Arm.Derive.itersN, VG.Proof.Argon2.Arm.Derive.mcostN,
    VG.Proof.Argon2.Arm.Derive.lanesN, VG.Proof.Argon2.Arm.Derive.outL, VG.Proof.Argon2.Arm.Derive.outP,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [satState, satMem, satStack, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read, Spec.Argon2.params,
      Spec.Argon2.valid, Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen] using VG.Proof.Argon2.Arm.Derive.satState

/-- The emitted function, against the shared contract. -/
theorem deriveShared_verified :
    Verified Arm.target Impl.Argon2.Arm.Derive.derive (Spec.Argon2.deriveContract Arm.abi 240) :=
  (derive_verified.of_implies VG.Proof.Argon2.Arm.Derive.deriveFlat_implies).of_implies VG.Proof.Argon2.Arm.Derive.flat_implies

end VG.Proof.Argon2.Arm.Derive

end
