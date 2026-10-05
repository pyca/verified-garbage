import VerifiedGarbage.Proof.Argon2.X86.Divide
import VerifiedGarbage.Proof.Argon2.X86.HPrime.Verified
import VerifiedGarbage.Proof.Argon2.X86.CompressVerified
import VerifiedGarbage.Proof.Argon2.Reference
import VerifiedGarbage.Impl.Argon2.X86.Derive
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Argon2.MemoryInit

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.Body`. -/
section

section

/-!
# Regions at 32-bit addresses

The derivation's regions all lie at 32-bit addresses (`x.setWidth 64`), so
whether they are disjoint, contain an access or lie in one another is a
question about the addresses' values: `disj32`, `contains32` and `sub32`
reduce each to arithmetic on `toNat`, for `omega`.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG

theorem toNat_w (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

theorem disj32 {x y : BitVec 32} {n m : Nat} (h : x.toNat + n ≤ y.toNat ∨ y.toNat + m ≤ x.toNat)
    (hn : x.toNat + n ≤ 2 ^ 32) (hm : y.toNat + m ≤ 2 ^ 32) :
    Region.Disjoint ⟨x.setWidth 64, n⟩ ⟨y.setWidth 64, m⟩ := by
  rcases h with h | h
  · exact Offset.disjoint_of_le (by simp only [VG.Proof.Argon2.X86.Derive.toNat_w]; omega) (by simp only [VG.Proof.Argon2.X86.Derive.toNat_w]; omega)
  · exact (Offset.disjoint_of_le (r₁ := ⟨y.setWidth 64, m⟩) (by simp only [VG.Proof.Argon2.X86.Derive.toNat_w]; omega)
      (by simp only [VG.Proof.Argon2.X86.Derive.toNat_w]; omega)).symm

theorem contains32 {x y : BitVec 32} {n m : Nat} (h₁ : y.toNat ≤ x.toNat)
    (h₂ : x.toNat + n ≤ y.toNat + m) :
    Region.Contains ⟨y.setWidth 64, m⟩ (x.setWidth 64) n := by
  simp only [Region.Contains]
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, VG.Proof.Argon2.X86.Derive.toNat_w]; exact h₁), VG.Proof.Argon2.X86.Derive.toNat_w, VG.Proof.Argon2.X86.Derive.toNat_w]
  omega

theorem sub32 {x y : BitVec 32} {n m : Nat} (h₁ : y.toNat ≤ x.toNat)
    (h₂ : x.toNat + n ≤ y.toNat + m) :
    Region.Sub ⟨x.setWidth 64, n⟩ ⟨y.setWidth 64, m⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  have hx := VG.Proof.Argon2.X86.Derive.toNat_w x
  have hy := VG.Proof.Argon2.X86.Derive.toNat_w y
  have := x.isLt
  bv_omega

/-- `x - k`, as a number. -/
theorem sub_nat {x : BitVec 32} {k : Nat} (h : k ≤ x.toNat) :
    (x - BitVec.ofNat 32 k).toNat = x.toNat - k := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]
  rw [show 2 ^ 32 - k + x.toNat = (x.toNat - k) + 2 ^ 32 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- `x + k`, as a number. -/
theorem add_nat {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt h]

end VG.Proof.Argon2.X86.Derive

end

section

section

/-!
# Argon2 on x86 (32-bit): the contract of the derivation's proof

`deriveX86`: `vg_argon2`'s contract with its eighteen arguments only read
(`Spec.Argon2.deriveContract`, which lets the code write them, is reached by
narrowing), its precondition a structure (`DPre`). The derivation uses the
244 bytes of stack below its return address: 16 for the saved registers,
144 for the locals, and 84 for a call of `vg_argon2_hprime` (five arguments,
the return address and H′'s own 60 bytes).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

section
variable (s₀ : State)

abbrev kindV : BitVec 32 := VG.X86.arg s₀ 0
abbrev pwP : BitVec 32 := VG.X86.arg s₀ 1
abbrev pwL : Nat := (VG.X86.arg s₀ 2).toNat
abbrev saltP : BitVec 32 := VG.X86.arg s₀ 3
abbrev saltL : Nat := (VG.X86.arg s₀ 4).toNat
abbrev itersN : Nat := (VG.X86.arg s₀ 5).toNat
abbrev mcostN : Nat := (VG.X86.arg s₀ 6).toNat
abbrev lanesN : Nat := (VG.X86.arg s₀ 7).toNat
abbrev threadsN : Nat := (VG.X86.arg s₀ 8).toNat
abbrev secP : BitVec 32 := VG.X86.arg s₀ 9
abbrev secL : Nat := (VG.X86.arg s₀ 10).toNat
abbrev adP : BitVec 32 := VG.X86.arg s₀ 11
abbrev adL : Nat := (VG.X86.arg s₀ 12).toNat
abbrev memP : BitVec 32 := VG.X86.arg s₀ 13
abbrev blocksN : Nat := (VG.X86.arg s₀ 14).toNat
abbrev scrP : BitVec 32 := VG.X86.arg s₀ 15
abbrev outP : BitVec 32 := VG.X86.arg s₀ 16
abbrev outL : Nat := (VG.X86.arg s₀ 17).toNat
abbrev E0 : BitVec 32 := s₀.gpr .esp

/-- The parameters. -/
abbrev prm : Params := VG.Spec.Argon2.params (VG.Proof.Argon2.X86.Derive.kindV s₀).toNat (VG.Proof.Argon2.X86.Derive.itersN s₀) (VG.Proof.Argon2.X86.Derive.mcostN s₀) (VG.Proof.Argon2.X86.Derive.lanesN s₀) (VG.Proof.Argon2.X86.Derive.outL s₀)

abbrev pwR : Region := ⟨(VG.Proof.Argon2.X86.Derive.pwP s₀).setWidth 64, VG.Proof.Argon2.X86.Derive.pwL s₀⟩
abbrev saltR : Region := ⟨(VG.Proof.Argon2.X86.Derive.saltP s₀).setWidth 64, VG.Proof.Argon2.X86.Derive.saltL s₀⟩
abbrev secR : Region := ⟨(VG.Proof.Argon2.X86.Derive.secP s₀).setWidth 64, VG.Proof.Argon2.X86.Derive.secL s₀⟩
abbrev adR : Region := ⟨(VG.Proof.Argon2.X86.Derive.adP s₀).setWidth 64, VG.Proof.Argon2.X86.Derive.adL s₀⟩
abbrev memR : Region := ⟨(VG.Proof.Argon2.X86.Derive.memP s₀).setWidth 64, VG.Proof.Argon2.X86.Derive.blocksN s₀ * 1024⟩
abbrev scrR : Region := ⟨(VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64, 16384⟩
abbrev outR : Region := ⟨(VG.Proof.Argon2.X86.Derive.outP s₀).setWidth 64, VG.Proof.Argon2.X86.Derive.outL s₀⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 72⟩
abbrev retR : Region := ⟨(VG.Proof.Argon2.X86.Derive.E0 s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (VG.Proof.Argon2.X86.Derive.E0 s₀) 244

/-- The inputs, on entry. -/
abbrev pwB : List Byte := bytesAt s₀.mem (VG.Proof.Argon2.X86.Derive.pwR s₀).base (VG.Proof.Argon2.X86.Derive.pwL s₀)
abbrev saltB : List Byte := bytesAt s₀.mem (VG.Proof.Argon2.X86.Derive.saltR s₀).base (VG.Proof.Argon2.X86.Derive.saltL s₀)
abbrev secB : List Byte := bytesAt s₀.mem (VG.Proof.Argon2.X86.Derive.secR s₀).base (VG.Proof.Argon2.X86.Derive.secL s₀)
abbrev adB : List Byte := bytesAt s₀.mem (VG.Proof.Argon2.X86.Derive.adR s₀).base (VG.Proof.Argon2.X86.Derive.adL s₀)

end

/-- The facts of `deriveX86`'s precondition. -/
structure DPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Argon2.X86.Derive.pwR s₀, VG.Proof.Argon2.X86.Derive.saltR s₀, VG.Proof.Argon2.X86.Derive.secR s₀, VG.Proof.Argon2.X86.Derive.adR s₀, VG.Proof.Argon2.X86.Derive.argR s₀]
  wr : s₀.wr = [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀]
  ro_w : ∀ r ∈ [VG.Proof.Argon2.X86.Derive.pwR s₀, VG.Proof.Argon2.X86.Derive.saltR s₀, VG.Proof.Argon2.X86.Derive.secR s₀, VG.Proof.Argon2.X86.Derive.adR s₀, VG.Proof.Argon2.X86.Derive.argR s₀], ∀ w ∈ [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀],
    r.Disjoint w
  mem_scr : (VG.Proof.Argon2.X86.Derive.memR s₀).Disjoint (VG.Proof.Argon2.X86.Derive.scrR s₀)
  mem_out : (VG.Proof.Argon2.X86.Derive.memR s₀).Disjoint (VG.Proof.Argon2.X86.Derive.outR s₀)
  scr_out : (VG.Proof.Argon2.X86.Derive.scrR s₀).Disjoint (VG.Proof.Argon2.X86.Derive.outR s₀)
  ret_w : ∀ w ∈ [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀], (VG.Proof.Argon2.X86.Derive.retR s₀).Disjoint w
  stk_all : ∀ r ∈ [VG.Proof.Argon2.X86.Derive.pwR s₀, VG.Proof.Argon2.X86.Derive.saltR s₀, VG.Proof.Argon2.X86.Derive.secR s₀, VG.Proof.Argon2.X86.Derive.adR s₀, VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀], (VG.Proof.Argon2.X86.Derive.stkR s₀).Disjoint r
  pw_fits : (VG.Proof.Argon2.X86.Derive.pwP s₀).toNat + VG.Proof.Argon2.X86.Derive.pwL s₀ ≤ 2 ^ 32
  salt_fits : (VG.Proof.Argon2.X86.Derive.saltP s₀).toNat + VG.Proof.Argon2.X86.Derive.saltL s₀ ≤ 2 ^ 32
  sec_fits : (VG.Proof.Argon2.X86.Derive.secP s₀).toNat + VG.Proof.Argon2.X86.Derive.secL s₀ ≤ 2 ^ 32
  ad_fits : (VG.Proof.Argon2.X86.Derive.adP s₀).toNat + VG.Proof.Argon2.X86.Derive.adL s₀ ≤ 2 ^ 32
  mem_fits : (VG.Proof.Argon2.X86.Derive.memP s₀).toNat + VG.Proof.Argon2.X86.Derive.blocksN s₀ * 1024 ≤ 2 ^ 32
  scr_fits : (VG.Proof.Argon2.X86.Derive.scrP s₀).toNat + 16384 ≤ 2 ^ 32
  out_fits : (VG.Proof.Argon2.X86.Derive.outP s₀).toNat + VG.Proof.Argon2.X86.Derive.outL s₀ ≤ 2 ^ 32
  esp_lo : 244 ≤ (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat
  esp_hi : (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat + 76 ≤ 2 ^ 32
  kind_le : (VG.Proof.Argon2.X86.Derive.kindV s₀).toNat ≤ 2
  valid : valid (VG.Proof.Argon2.X86.Derive.prm s₀) (VG.Proof.Argon2.X86.Derive.pwL s₀) (VG.Proof.Argon2.X86.Derive.saltL s₀) (VG.Proof.Argon2.X86.Derive.secL s₀) (VG.Proof.Argon2.X86.Derive.adL s₀)
  threads : 1 ≤ VG.Proof.Argon2.X86.Derive.threadsN s₀ ∧ VG.Proof.Argon2.X86.Derive.threadsN s₀ < 2 ^ 24
  blocks : VG.Proof.Argon2.X86.Derive.blocksN s₀ = (VG.Proof.Argon2.X86.Derive.prm s₀).blocks

/-- `vg_argon2`, with its arguments only read. -/
def deriveX86 : Contract X86.isa where
  pre := VG.Proof.Argon2.X86.Derive.DPre
  post s s' := bytesAt s'.mem ((VG.Proof.Argon2.X86.Derive.outP s).setWidth 64) (VG.Proof.Argon2.X86.Derive.outL s) =
    derive (VG.Proof.Argon2.X86.Derive.prm s) (VG.Proof.Argon2.X86.Derive.pwB s) (VG.Proof.Argon2.X86.Derive.saltB s) (VG.Proof.Argon2.X86.Derive.secB s) (VG.Proof.Argon2.X86.Derive.adB s)
  pub s₁ s₂ := (s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 18, VG.X86.arg s₁ i = VG.X86.arg s₂ i) ∧
    references (VG.Proof.Argon2.X86.Derive.prm s₁) (VG.Proof.Argon2.X86.Derive.pwB s₁) (VG.Proof.Argon2.X86.Derive.saltB s₁) (VG.Proof.Argon2.X86.Derive.secB s₁) (VG.Proof.Argon2.X86.Derive.adB s₁) =
      references (VG.Proof.Argon2.X86.Derive.prm s₂) (VG.Proof.Argon2.X86.Derive.pwB s₂) (VG.Proof.Argon2.X86.Derive.saltB s₂) (VG.Proof.Argon2.X86.Derive.secB s₂) (VG.Proof.Argon2.X86.Derive.adB s₂)

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
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

theorem lanes_pos : 1 ≤ VG.Proof.Argon2.X86.Derive.lanesN s₀ := hp.valid.1
theorem lanes_lt : VG.Proof.Argon2.X86.Derive.lanesN s₀ < 2 ^ 24 := hp.valid.2.1
theorem passes_pos : 1 ≤ VG.Proof.Argon2.X86.Derive.itersN s₀ := hp.valid.2.2.1
theorem memory_ge : 8 * VG.Proof.Argon2.X86.Derive.lanesN s₀ ≤ VG.Proof.Argon2.X86.Derive.mcostN s₀ := hp.valid.2.2.2.2.1
theorem tag_ge : 4 ≤ VG.Proof.Argon2.X86.Derive.outL s₀ := hp.valid.2.2.2.2.2.2.1


theorem segLen_two : 2 ≤ (VG.Proof.Argon2.X86.Derive.prm s₀).segmentLen :=
  Proof.Argon2.segmentLen_ge_two _ hp.lanes_pos hp.memory_ge

theorem segLen_eq : (VG.Proof.Argon2.X86.Derive.prm s₀).segmentLen = VG.Proof.Argon2.X86.Derive.mcostN s₀ / (4 * VG.Proof.Argon2.X86.Derive.lanesN s₀) :=
  Proof.Argon2.segmentLen_eq _ hp.lanes_pos

theorem laneLen_eq : (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen = 4 * (VG.Proof.Argon2.X86.Derive.prm s₀).segmentLen :=
  Proof.Argon2.laneLen_segments _ hp.lanes_pos

theorem blocks_eq : VG.Proof.Argon2.X86.Derive.blocksN s₀ = VG.Proof.Argon2.X86.Derive.lanesN s₀ * (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen := by
  rw [hp.blocks]; exact Proof.Argon2.blocks_lanes _ hp.lanes_pos

/-- The memory, with the scratch beside it, fits below 2³² with room to spare. -/
theorem blocks_lt : VG.Proof.Argon2.X86.Derive.blocksN s₀ * 1024 + 16384 ≤ 2 ^ 32 := by
  have hm := hp.mem_fits
  have hs := hp.scr_fits
  rcases Nat.eq_zero_or_pos (VG.Proof.Argon2.X86.Derive.blocksN s₀) with h0 | hpos
  · omega
  have := VG.Proof.Argon2.X86.Derive.disjoint_total hp.mem_scr (N := 2 ^ 32)
    (by simp only [BitVec.toNat_setWidth, ]; omega)
    (by simp only [BitVec.toNat_setWidth, ]; omega)
    (by simp only; omega) (by simp only; omega)
  simpa using this

end DPre

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the derivation's frames

`vg_argon2` pushes `ebp`, `edi`, `esi` and `ebx` in frames of their own and
then a frame of 144 bytes for the locals (`Impl.Argon2.X86.Derive.frames`).
`entry s₀` is the state its body starts in; `frames_ok` gives the
callee-saved registers and the return address back, from a body that keeps
`esp`, the saved words and the return address (`BodyDone`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Impl.Argon2.X86.Derive (frames saved body derive locals)

/-- The pushes of the saved registers and the locals. -/
def entry (s₀ : State) : State :=
  pushed (List.replicate 36 .eax) (pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))))

/-- The stack pointer of the body: below the four saved registers and the locals. -/
abbrev E (s₀ : State) : BitVec 32 := VG.Proof.Argon2.X86.Derive.E0 s₀ - BitVec.ofNat 32 160

/-- The caller's registers, in the order of their words above the locals. -/
def savedVal (s₀ : State) : Nat → BitVec 32
  | 0 => s₀.gpr .ebx
  | 1 => s₀.gpr .esi
  | 2 => s₀.gpr .edi
  | _ => s₀.gpr .ebp

/-- The word `j` above the locals, where register `savedVal j` is. -/
abbrev slot (s₀ : State) (j : Nat) : Addr := (VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 (144 + 4 * j)).setWidth 64

/-- What the body must keep for the frames to restore the caller's state. -/
structure BodyDone (s₀ t : State) : Prop where
  esp : t.gpr .esp = VG.Proof.Argon2.X86.Derive.E s₀
  saved : ∀ j < 4, t.mem.readW (VG.Proof.Argon2.X86.Derive.slot s₀ j) 32 = VG.Proof.Argon2.X86.Derive.savedVal s₀ j
  ret : t.mem.readW ((VG.Proof.Argon2.X86.Derive.E0 s₀).setWidth 64) 32 = s₀.mem.readW ((VG.Proof.Argon2.X86.Derive.E0 s₀).setWidth 64) 32

theorem popped_one_self (r : Reg) (s : State) (h : r ≠ .esp) :
    (popped r 1 s).gpr r = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  simp [popped, popReg, State.setReg, h]

section
variable {s₀ : State} (hlo : 160 ≤ (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat)
include hlo

theorem E_sub (k : Nat) (hk : k ≤ 160) :
    VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 k = VG.Proof.Argon2.X86.Derive.E0 s₀ - BitVec.ofNat 32 (160 - k) := by
  apply BitVec.eq_of_toNat_eq
  have := (VG.Proof.Argon2.X86.Derive.E0 s₀).isLt
  rw [BitVec.toNat_add, sub_toNat hlo, sub_toNat (by omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := k) (by omega)]
  omega

theorem frames_ok {Q : State → Prop} (hsp : NoSp body)
    (hb : WP isa body (VG.Proof.Argon2.X86.Derive.entry s₀) fun t => VG.Proof.Argon2.X86.Derive.BodyDone s₀ t ∧ Q t)
    (hQ : ∀ t u, Q t → u.mem = t.mem → Q u) :
    WP isa derive s₀ fun u => abiPreserved s₀ u ∧ Q u := by
  have hE := (VG.Proof.Argon2.X86.Derive.E0 s₀).isLt
  have hlo' : 160 ≤ (s₀.gpr .esp).toNat := hlo
  have nf : ∀ {r : Reg} {k : Nat} {rs : List Reg} {b : Prog isa}, r ≠ .esp → NoSp b →
      NoSp (.frame (.push rs) b (.pop r k)) := fun {r k rs b} hr hb i hi => by
    simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | hi) | rfl
    · rfl
    · exact hb i hi
    · simp [Taint.clobbers, Taint.dst, hr]
  have e1 : ((pushed [.ebp] s₀).gpr .esp).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 4 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega)]; rfl
  have e2 : ((pushed [.edi] (pushed [.ebp] s₀)).gpr .esp).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 8 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega), e1]; rfl
  have e3 : ((pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))).gpr .esp).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 12 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega), e2]; rfl
  have e4 : ((pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))).gpr .esp).toNat =
      (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 16 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega), e3]; rfl
  simp only [derive, saved, frames]
  refine WP.frame (by simp) (by decide) (by decide) (by simp only [List.length_singleton]; omega)
    (nf (by decide) (nf (by decide) (nf (by decide) (nf (by decide) hsp)))) ?_
  refine WP.frame (by simp) (by decide) (by decide) (by simp only [List.length_singleton]; omega)
    (nf (by decide) (nf (by decide) (nf (by decide) hsp))) ?_
  refine WP.frame (by simp) (by decide) (by decide) (by simp only [List.length_singleton]; omega)
    (nf (by decide) (nf (by decide) hsp)) ?_
  refine WP.frame (by simp) (by decide) (by decide) (by simp only [List.length_singleton]; omega)
    (nf (by decide) hsp) ?_
  refine WP.frame (by simp [locals]) (by decide) (by decide)
    (by simp only [List.length_replicate, locals]; omega) hsp (hb.mono fun t ⟨d, q⟩ => ?_)
  -- The pops.
  have add4 : ∀ a : Nat, VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * 1) =
      VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 (a + 4) := fun a => by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  set t₁ := popped .eax (List.replicate (locals / 4) Reg.eax).length t with ht₁
  have sp₁ : t₁.gpr .esp = VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 144 := by
    rw [ht₁, popped_esp, d.esp]; simp [locals]
  set t₂ := popped .ebx [Reg.ebx].length t₁ with ht₂
  have sp₂ : t₂.gpr .esp = VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 148 := by
    rw [ht₂, popped_esp, sp₁]; exact add4 144
  set t₃ := popped .esi [Reg.esi].length t₂ with ht₃
  have sp₃ : t₃.gpr .esp = VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 152 := by
    rw [ht₃, popped_esp, sp₂]; exact add4 148
  set t₄ := popped .edi [Reg.edi].length t₃ with ht₄
  have sp₄ : t₄.gpr .esp = VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 156 := by
    rw [ht₄, popped_esp, sp₃]; exact add4 152
  set u := popped .ebp [Reg.ebp].length t₄ with hu
  have spu : u.gpr .esp = VG.Proof.Argon2.X86.Derive.E0 s₀ := by
    rw [hu, popped_esp, sp₄, List.length_singleton, add4 156, VG.Proof.Argon2.X86.Derive.E_sub hlo 160 (by decide)]; simp
  have mu : u.mem = t.mem := by simp [hu, ht₄, ht₃, ht₂, ht₁]
  have b₂ : t₂.gpr .ebx = s₀.gpr .ebx := by
    rw [ht₂, List.length_singleton, VG.Proof.Argon2.X86.Derive.popped_one_self _ _ (by decide), sp₁, ht₁, popped_mem]
    exact d.saved 0 (by decide)
  have b₃ : t₃.gpr .esi = s₀.gpr .esi := by
    rw [ht₃, List.length_singleton, VG.Proof.Argon2.X86.Derive.popped_one_self _ _ (by decide), sp₂, ht₂, popped_mem, ht₁,
      popped_mem]
    exact d.saved 1 (by decide)
  have b₄ : t₄.gpr .edi = s₀.gpr .edi := by
    rw [ht₄, List.length_singleton, VG.Proof.Argon2.X86.Derive.popped_one_self _ _ (by decide), sp₃, ht₃, popped_mem, ht₂,
      popped_mem, ht₁, popped_mem]
    exact d.saved 2 (by decide)
  have b₅ : u.gpr .ebp = s₀.gpr .ebp := by
    rw [hu, List.length_singleton, VG.Proof.Argon2.X86.Derive.popped_one_self _ _ (by decide), sp₄, ht₄, popped_mem, ht₃,
      popped_mem, ht₂, popped_mem, ht₁, popped_mem]
    exact d.saved 3 (by decide)
  refine ⟨⟨fun r hr => ?_, by rw [mu]; exact d.ret⟩, hQ t u q mu⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hu, popped_gpr _ _ _ (by decide) (by decide), ht₄, popped_gpr _ _ _ (by decide) (by decide),
      ht₃, popped_gpr _ _ _ (by decide) (by decide)]
    exact b₂
  · rw [hu, popped_gpr _ _ _ (by decide) (by decide), ht₄, popped_gpr _ _ _ (by decide) (by decide)]
    exact b₃
  · rw [hu, popped_gpr _ _ _ (by decide) (by decide)]
    exact b₄
  · exact b₅
  · exact spu

end

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the state of the derivation's body

`Inv s₀ s`: in the body, `esp` and `ebp` point to the locals (`E s₀`), the
permissions are those of the body's entry, and memory has changed only in
the memory matrix, `scratch`, the output, the locals and the 84 bytes of
stack below them. The arguments, the inputs, the saved registers and the
return address are therefore kept (`Inv.arg`, `Inv.done`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd)
open VG.Spec.Blake2 (bytesAt)

section
variable (s₀ : State)

/-- The locals. -/
abbrev locR : Region := ⟨(VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64, 144⟩

/-- The stack below the locals. -/
abbrev callR : Region := below (VG.Proof.Argon2.X86.Derive.E s₀) 84

/-- The regions the body may write. -/
abbrev bodyW : List Region := [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀, VG.Proof.Argon2.X86.Derive.locR s₀, VG.Proof.Argon2.X86.Derive.callR s₀]

end

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

theorem E_toNat : (VG.Proof.Argon2.X86.Derive.E s₀).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 160 := sub_toNat (by have := hp.esp_lo; omega)

end

theorem entry_esp (s₀ : State) : (VG.Proof.Argon2.X86.Derive.entry s₀).gpr .esp = VG.Proof.Argon2.X86.Derive.E s₀ := by
  simp only [VG.Proof.Argon2.X86.Derive.entry, pushed_esp, List.length_singleton, List.length_replicate, BitVec.sub_sub,
    BitVec.ofNat_add_ofNat]

theorem entry_gpr (s₀ : State) {r : Reg} (h : r ≠ .esp) : (VG.Proof.Argon2.X86.Derive.entry s₀).gpr r = s₀.gpr r := by
  simp only [VG.Proof.Argon2.X86.Derive.entry, pushed_gpr _ _ h]

theorem entry_rd (s₀ : State) : (VG.Proof.Argon2.X86.Derive.entry s₀).rd = s₀.rd := by simp [VG.Proof.Argon2.X86.Derive.entry]


/-! ## The pushes -/

theorem pushed_esp_nat {rs : List Reg} {s : State} (h : 4 * rs.length ≤ (s.gpr .esp).toNat) :
    ((pushed rs s).gpr .esp).toNat = (s.gpr .esp).toNat - 4 * rs.length := by
  rw [pushed_esp, VG.Proof.Argon2.X86.Derive.sub_nat h]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

theorem entry_frame : Frame [below (VG.Proof.Argon2.X86.Derive.E0 s₀) 160] s₀.mem (VG.Proof.Argon2.X86.Derive.entry s₀).mem := by
  have hlo : 244 ≤ (s₀.gpr .esp).toNat := hp.esp_lo
  have hE := (s₀.gpr .esp).isLt
  have hE0 : (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  -- Each push writes within the 160 bytes below `esp` on entry.
  have step : ∀ {rs : List Reg} {s : State}, .esp ∉ rs → 4 * rs.length ≤ (s.gpr .esp).toNat →
      (s₀.gpr .esp).toNat - 160 ≤ (s.gpr .esp).toNat - 4 * rs.length →
      (s.gpr .esp).toNat ≤ (s₀.gpr .esp).toNat → Frame [below (VG.Proof.Argon2.X86.Derive.E0 s₀) 160] s.mem (pushed rs s).mem :=
    fun {rs s} hrs hn h₁ h₂ => (pushed_frame hrs hn).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, VG.Proof.Argon2.X86.Derive.sub32 ?_ ?_⟩
      · rw [VG.Proof.Argon2.X86.Derive.sub_nat hn, VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega
      · rw [VG.Proof.Argon2.X86.Derive.sub_nat hn, VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega
  have n₁ := VG.Proof.Argon2.X86.Derive.pushed_esp_nat (rs := [.ebp]) (s := s₀) (by simp only [List.length_singleton]; omega)
  have n₂ := VG.Proof.Argon2.X86.Derive.pushed_esp_nat (rs := [.edi]) (s := pushed [.ebp] s₀)
    (by simp only [List.length_singleton] at n₁ ⊢; omega)
  have n₃ := VG.Proof.Argon2.X86.Derive.pushed_esp_nat (rs := [.esi]) (s := pushed [.edi] (pushed [.ebp] s₀))
    (by simp only [List.length_singleton] at n₁ n₂ ⊢; omega)
  have n₄ := VG.Proof.Argon2.X86.Derive.pushed_esp_nat (rs := [.ebx]) (s := pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))
    (by simp only [List.length_singleton] at n₁ n₂ n₃ ⊢; omega)
  simp only [List.length_singleton] at n₁ n₂ n₃ n₄
  exact (((((step (by decide) (by simp only [List.length_singleton]; omega)
    (by simp only [List.length_singleton]; omega) (Nat.le_refl _))).trans
    (step (by decide) (by simp only [List.length_singleton]; omega)
      (by simp only [List.length_singleton]; omega) (by omega))).trans
    (step (by decide) (by simp only [List.length_singleton]; omega)
      (by simp only [List.length_singleton]; omega) (by omega))).trans
    (step (by decide) (by simp only [List.length_singleton]; omega)
      (by simp only [List.length_singleton]; omega) (by omega))).trans
    (step (by decide) (by simp only [List.length_replicate]; omega)
      (by simp only [List.length_replicate]; omega) (by omega))

end


/-- A word above the frame a push writes is kept. -/
theorem push_keep {rs : List Reg} {s : State} (hrs : .esp ∉ rs) (hn : 4 * rs.length ≤ (s.gpr .esp).toNat)
    {a : BitVec 32} (ha : (s.gpr .esp).toNat ≤ a.toNat) (ha' : a.toNat + 4 ≤ 2 ^ 32) :
    (pushed rs s).mem.readW (a.setWidth 64) 32 = s.mem.readW (a.setWidth 64) 32 := by
  refine (pushed_frame hrs hn).readW (r := ⟨a.setWidth 64, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact VG.Proof.Argon2.X86.Derive.disj32 (.inr (by rw [VG.Proof.Argon2.X86.Derive.sub_nat hn]; omega)) ha' (by rw [VG.Proof.Argon2.X86.Derive.sub_nat hn]; have := (s.gpr .esp).isLt; omega)

/-- The word a one-register push writes. -/
theorem push_word {r : Reg} {s : State} (hr : r ≠ .esp) (hn : 4 ≤ (s.gpr .esp).toNat) {a : BitVec 32}
    (ha : a = s.gpr .esp - BitVec.ofNat 32 4) :
    (pushed [r] s).mem.readW (a.setWidth 64) 32 = s.gpr r := by
  have := pushed_word (rs := [r]) (s := s) (by simpa using hr.symm) (by simpa using hn) (i := 0) (by simp)
  rw [pushed_esp] at this
  simp only [List.length_singleton, Nat.mul_zero, BitVec.add_zero] at this
  rw [ha]; exact this

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

theorem entry_saved {j : Nat} (hj : j < 4) : (VG.Proof.Argon2.X86.Derive.entry s₀).mem.readW (VG.Proof.Argon2.X86.Derive.slot s₀ j) 32 = VG.Proof.Argon2.X86.Derive.savedVal s₀ j := by
  have hlo : 244 ≤ (s₀.gpr .esp).toNat := hp.esp_lo
  have hE := (s₀.gpr .esp).isLt
  have hi : (s₀.gpr .esp).toNat + 76 ≤ 2 ^ 32 := hp.esp_hi
  have hE0 : (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have n₁ := VG.Proof.Argon2.X86.Derive.pushed_esp_nat (rs := [.ebp]) (s := s₀) (by simp only [List.length_singleton]; omega)
  have n₂ := VG.Proof.Argon2.X86.Derive.pushed_esp_nat (rs := [.edi]) (s := pushed [.ebp] s₀)
    (by simp only [List.length_singleton] at n₁ ⊢; omega)
  have n₃ := VG.Proof.Argon2.X86.Derive.pushed_esp_nat (rs := [.esi]) (s := pushed [.edi] (pushed [.ebp] s₀))
    (by simp only [List.length_singleton] at n₁ n₂ ⊢; omega)
  have n₄ := VG.Proof.Argon2.X86.Derive.pushed_esp_nat (rs := [.ebx]) (s := pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))
    (by simp only [List.length_singleton] at n₁ n₂ n₃ ⊢; omega)
  simp only [List.length_singleton] at n₁ n₂ n₃ n₄
  have sl : (VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat = (s₀.gpr .esp).toNat - 16 + 4 * j := by
    rw [VG.Proof.Argon2.X86.Derive.add_nat (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega), VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega
  have eq : ∀ (x : BitVec 32), x.toNat = (s₀.gpr .esp).toNat - 16 + 4 * j →
      VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 (144 + 4 * j) = x := fun x hx => BitVec.eq_of_toNat_eq (by rw [sl, hx])
  unfold VG.Proof.Argon2.X86.Derive.entry VG.Proof.Argon2.X86.Derive.slot
  rw [VG.Proof.Argon2.X86.Derive.push_keep (by decide) (by simp only [List.length_replicate]; omega) (by rw [n₄, sl]; omega)
    (by rw [sl]; omega)]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · rw [VG.Proof.Argon2.X86.Derive.push_word (by decide) (by omega) (eq _ (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega)), pushed_gpr _ _ (by decide),
      pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide)]; rfl
  · rw [VG.Proof.Argon2.X86.Derive.push_keep (by decide) (by simp only [List.length_singleton]; omega) (by rw [n₃, sl]; omega)
      (by rw [sl]; omega),
      VG.Proof.Argon2.X86.Derive.push_word (by decide) (by omega) (eq _ (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega)), pushed_gpr _ _ (by decide),
      pushed_gpr _ _ (by decide)]; rfl
  · rw [VG.Proof.Argon2.X86.Derive.push_keep (by decide) (by simp only [List.length_singleton]; omega) (by rw [n₃, sl]; omega)
      (by rw [sl]; omega),
      VG.Proof.Argon2.X86.Derive.push_keep (by decide) (by simp only [List.length_singleton]; omega) (by rw [n₂, sl]; omega)
      (by rw [sl]; omega),
      VG.Proof.Argon2.X86.Derive.push_word (by decide) (by omega) (eq _ (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega)), pushed_gpr _ _ (by decide)]
    rfl
  · rw [VG.Proof.Argon2.X86.Derive.push_keep (by decide) (by simp only [List.length_singleton]; omega) (by rw [n₃, sl]; omega)
      (by rw [sl]; omega),
      VG.Proof.Argon2.X86.Derive.push_keep (by decide) (by simp only [List.length_singleton]; omega) (by rw [n₂, sl]; omega)
      (by rw [sl]; omega),
      VG.Proof.Argon2.X86.Derive.push_keep (by decide) (by simp only [List.length_singleton]; omega) (by rw [n₁, sl]; omega)
      (by rw [sl]; omega),
      VG.Proof.Argon2.X86.Derive.push_word (by decide) (by omega) (eq _ (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega))]
    rfl

end


theorem loc_mem (s₀ : State) : VG.Proof.Argon2.X86.Derive.locR s₀ ∈ (VG.Proof.Argon2.X86.Derive.entry s₀).wr := by
  simp [VG.Proof.Argon2.X86.Derive.entry, pushed_wr, pushed_esp, BitVec.sub_sub, BitVec.ofNat_add_ofNat, below]

theorem wr_mem (s₀ : State) {r : Region} (h : r ∈ s₀.wr) : r ∈ (VG.Proof.Argon2.X86.Derive.entry s₀).wr := by
  simp only [VG.Proof.Argon2.X86.Derive.entry, pushed_wr, List.mem_cons]
  exact .inr (.inr (.inr (.inr (.inr h))))

/-! ## The invariant -/

/-- The state of the body. -/
structure Inv (s₀ s : State) : Prop where
  esp : s.gpr .esp = VG.Proof.Argon2.X86.Derive.E s₀
  ebp : s.gpr .ebp = VG.Proof.Argon2.X86.Derive.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = (VG.Proof.Argon2.X86.Derive.entry s₀).wr
  frame : Frame (VG.Proof.Argon2.X86.Derive.bodyW s₀) (VG.Proof.Argon2.X86.Derive.entry s₀).mem s.mem

/-- A step that writes registers other than `esp` and `ebp`, and memory within the body's regions. -/
theorem Inv.step {s₀ s t : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (he : t.gpr .esp = s.gpr .esp)
    (hb : t.gpr .ebp = s.gpr .ebp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame (VG.Proof.Argon2.X86.Derive.bodyW s₀) s.mem t.mem) : VG.Proof.Argon2.X86.Derive.Inv s₀ t :=
  ⟨he.trans h.esp, hb.trans h.ebp, hrd.trans h.rd, hwr.trans h.wr, h.frame.trans hf⟩

theorem Inv.upd {s₀ s t : State} {r : Reg} {v : BitVec 32} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (u : Upd s t r v)
    (h₁ : r ≠ .esp) (h₂ : r ≠ .ebp) : VG.Proof.Argon2.X86.Derive.Inv s₀ t :=
  h.step (u.other _ h₁.symm) (u.other _ h₂.symm) u.rd u.wr (by rw [u.mem]; exact Frame.refl _ _)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

theorem E_hi : (VG.Proof.Argon2.X86.Derive.E s₀).toNat + 236 ≤ 2 ^ 32 := by
  have := hp.esp_hi; have := hp.esp_lo; rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega

/-- The locals and the stack below them lie in the stack the contract reserves. -/
theorem loc_stk {d n : Nat} (h : d + n ≤ 144) :
    Region.Sub ⟨(VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 d).setWidth 64, n⟩ (VG.Proof.Argon2.X86.Derive.stkR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE : (VG.Proof.Argon2.X86.Derive.E s₀).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 160 := VG.Proof.Argon2.X86.Derive.sub_nat (by omega)
  have h1 : (VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 d).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 160 + d := by
    rw [VG.Proof.Argon2.X86.Derive.add_nat (by omega), hE]
  have h2 : (VG.Proof.Argon2.X86.Derive.E0 s₀ - BitVec.ofNat 32 244).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 244 := VG.Proof.Argon2.X86.Derive.sub_nat (by omega)
  exact VG.Proof.Argon2.X86.Derive.sub32 (by rw [h1, h2]; omega) (by rw [h1, h2]; omega)

theorem call_stk : Region.Sub (VG.Proof.Argon2.X86.Derive.callR s₀) (VG.Proof.Argon2.X86.Derive.stkR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE : (VG.Proof.Argon2.X86.Derive.E s₀).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 160 := VG.Proof.Argon2.X86.Derive.sub_nat (by omega)
  have h1 : (VG.Proof.Argon2.X86.Derive.E s₀ - BitVec.ofNat 32 84).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 244 := by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega), hE]; omega
  have h2 : (VG.Proof.Argon2.X86.Derive.E0 s₀ - BitVec.ofNat 32 244).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 244 := VG.Proof.Argon2.X86.Derive.sub_nat (by omega)
  exact VG.Proof.Argon2.X86.Derive.sub32 (by rw [h1, h2]) (by rw [h1, h2]; omega)

/-- A word of the locals. -/
theorem loc_in {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions s.wr (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) 4 := by
  have := VG.Proof.Argon2.X86.Derive.E_hi hp
  rw [h.wr]
  exact ⟨VG.Proof.Argon2.X86.Derive.locR s₀, VG.Proof.Argon2.X86.Derive.loc_mem s₀, VG.Proof.Argon2.X86.Derive.contains32 (by rw [VG.Proof.Argon2.X86.Derive.add_nat (by omega)]; omega)
    (by rw [VG.Proof.Argon2.X86.Derive.add_nat (by omega)]; omega)⟩

theorem loc_in' {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := VG.Proof.Argon2.X86.Derive.loc_in hp h hd
  ⟨r, List.mem_append_right _ hr, hc⟩

end


section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

theorem E_nat : (VG.Proof.Argon2.X86.Derive.E s₀).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 160 := VG.Proof.Argon2.X86.Derive.sub_nat (by have := hp.esp_lo; omega)

/-- A range within the 160 bytes the frames use. -/
theorem frame_stk {d n : Nat} (h : d + n ≤ 160) :
    Region.Sub ⟨(VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 d).setWidth 64, n⟩ (VG.Proof.Argon2.X86.Derive.stkR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have h1 : (VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 d).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 160 + d := by
    rw [VG.Proof.Argon2.X86.Derive.add_nat (by rw [VG.Proof.Argon2.X86.Derive.E_nat hp]; omega), VG.Proof.Argon2.X86.Derive.E_nat hp]
  have h2 : (VG.Proof.Argon2.X86.Derive.E0 s₀ - BitVec.ofNat 32 244).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 244 := VG.Proof.Argon2.X86.Derive.sub_nat (by omega)
  exact VG.Proof.Argon2.X86.Derive.sub32 (by rw [h1, h2]; omega) (by rw [h1, h2]; omega)

/-- What lies above the locals is outside the body's regions. -/
theorem above_disj {a : BitVec 32} {n : Nat} (ha : (VG.Proof.Argon2.X86.Derive.E s₀).toNat + 144 ≤ a.toNat)
    (ha' : a.toNat + n ≤ (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat + 76)
    (hm : Region.Disjoint ⟨a.setWidth 64, n⟩ (VG.Proof.Argon2.X86.Derive.memR s₀)) (hs : Region.Disjoint ⟨a.setWidth 64, n⟩ (VG.Proof.Argon2.X86.Derive.scrR s₀))
    (ho : Region.Disjoint ⟨a.setWidth 64, n⟩ (VG.Proof.Argon2.X86.Derive.outR s₀)) :
    ∀ r ∈ VG.Proof.Argon2.X86.Derive.bodyW s₀, Region.Disjoint ⟨a.setWidth 64, n⟩ r := by
  have := hp.esp_lo; have := hp.esp_hi; have : (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := VG.Proof.Argon2.X86.Derive.E_nat hp
  intro r hr
  simp only [VG.Proof.Argon2.X86.Derive.bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hm
  · exact hs
  · exact ho
  · exact VG.Proof.Argon2.X86.Derive.disj32 (.inr (by omega)) (by omega) (by omega)
  · exact VG.Proof.Argon2.X86.Derive.disj32 (.inr (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega)) (by omega)
      (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega)

theorem Inv.done {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) : VG.Proof.Argon2.X86.Derive.BodyDone s₀ s := by
  have := hp.esp_lo; have := hp.esp_hi; have : (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := VG.Proof.Argon2.X86.Derive.E_nat hp
  have hE' : (VG.Proof.Argon2.X86.Derive.E0 s₀ - BitVec.ofNat 32 160).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat - 160 := VG.Proof.Argon2.X86.Derive.sub_nat (by omega)
  refine ⟨h.esp, fun j hj => ?_, ?_⟩
  · have sl : (VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat = (VG.Proof.Argon2.X86.Derive.E s₀).toNat + (144 + 4 * j) :=
      VG.Proof.Argon2.X86.Derive.add_nat (by have := VG.Proof.Argon2.X86.Derive.E_hi hp; omega)
    have st := VG.Proof.Argon2.X86.Derive.frame_stk hp (d := 144 + 4 * j) (n := 4) (by omega)
    rw [h.frame.readW (r := ⟨VG.Proof.Argon2.X86.Derive.slot s₀ j, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact VG.Proof.Argon2.X86.Derive.entry_saved hp hj
    refine VG.Proof.Argon2.X86.Derive.above_disj hp (by rw [sl]; omega) (by rw [sl]; omega) ?_ ?_ ?_
    · exact ((hp.stk_all _ (by simp)).sub_left st)
    · exact ((hp.stk_all _ (by simp)).sub_left st)
    · exact ((hp.stk_all _ (by simp)).sub_left st)
  · rw [h.frame.readW (r := VG.Proof.Argon2.X86.Derive.retR s₀) (Region.contains_self _ _) ?_ (by decide)]
    · refine VG.Proof.Argon2.X86.Derive.entry_frame hp |>.readW (r := VG.Proof.Argon2.X86.Derive.retR s₀) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Argon2.X86.Derive.disj32 (.inr (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega)) (by omega) (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega)
    refine VG.Proof.Argon2.X86.Derive.above_disj hp (by omega) (by omega) ?_ ?_ ?_
    · exact hp.ret_w _ (by simp)
    · exact hp.ret_w _ (by simp)
    · exact hp.ret_w _ (by simp)

/-- The arguments' addresses, from `ebp`. -/
theorem arg_addr {i : Nat} (hi : i < 18) :
    addr (VG.Proof.Argon2.X86.Derive.E s₀) (Impl.Argon2.X86.Derive.argOff i) = argAddr s₀ i := by
  have := hp.esp_lo; have := hp.esp_hi; have : (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := VG.Proof.Argon2.X86.Derive.E_nat hp
  simp only [addr, argAddr, Impl.Argon2.X86.Derive.argOff, Impl.Argon2.X86.Derive.locals]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.Argon2.X86.Derive.add_nat (by omega), VG.Proof.Argon2.X86.Derive.add_nat (by omega)]
  show (VG.Proof.Argon2.X86.Derive.E0 s₀ - BitVec.ofNat 32 160).toNat + _ = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat + _
  rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega

theorem arg_word {i : Nat} (hi : i < 18) :
    Region.Sub ⟨argAddr s₀ i, 4⟩ (VG.Proof.Argon2.X86.Derive.argR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  exact VG.Proof.Argon2.X86.Derive.sub32 (by rw [VG.Proof.Argon2.X86.Derive.add_nat (by omega), VG.Proof.Argon2.X86.Derive.add_nat (by omega)]; omega)
    (by rw [VG.Proof.Argon2.X86.Derive.add_nat (by omega), VG.Proof.Argon2.X86.Derive.add_nat (by omega)]; omega)

theorem Inv.arg_in {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {i : Nat} (hi : i < 18) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Argon2.X86.Derive.E s₀) (Impl.Argon2.X86.Derive.argOff i)) 4 := by
  rw [VG.Proof.Argon2.X86.Derive.arg_addr hp hi, h.rd, hp.rd]
  exact ⟨VG.Proof.Argon2.X86.Derive.argR s₀, by simp, VG.Proof.Argon2.X86.Derive.arg_word hp hi (argAddr s₀ i) |> fun _ => by
    have := hp.esp_lo; have := hp.esp_hi; have : (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
    exact VG.Proof.Argon2.X86.Derive.contains32 (by rw [VG.Proof.Argon2.X86.Derive.add_nat (by omega), VG.Proof.Argon2.X86.Derive.add_nat (by omega)]; omega)
      (by rw [VG.Proof.Argon2.X86.Derive.add_nat (by omega), VG.Proof.Argon2.X86.Derive.add_nat (by omega)]; omega)⟩

theorem Inv.arg {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {i : Nat} (hi : i < 18) :
    s.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) (Impl.Argon2.X86.Derive.argOff i)) 32 = VG.X86.arg s₀ i := by
  have := hp.esp_lo; have := hp.esp_hi; have : (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := VG.Proof.Argon2.X86.Derive.E_nat hp
  have ai : (VG.Proof.Argon2.X86.Derive.E0 s₀ + BitVec.ofNat 32 (4 + 4 * i)).toNat = (VG.Proof.Argon2.X86.Derive.E0 s₀).toNat + 4 + 4 * i := by
    rw [VG.Proof.Argon2.X86.Derive.add_nat (by omega)]; omega
  rw [VG.Proof.Argon2.X86.Derive.arg_addr hp hi]
  have sub := VG.Proof.Argon2.X86.Derive.arg_word hp hi
  rw [h.frame.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
  · refine (VG.Proof.Argon2.X86.Derive.entry_frame hp).readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.Argon2.X86.Derive.disj32 (.inr (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega), ai]; omega)) (by rw [ai]; omega)
      (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega)
  refine VG.Proof.Argon2.X86.Derive.above_disj hp (by rw [ai]; omega) (by rw [ai]; omega) ?_ ?_ ?_
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub

/-- The inputs are kept. -/
theorem Inv.input {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {R : Region}
    (hR : R ∈ [VG.Proof.Argon2.X86.Derive.pwR s₀, VG.Proof.Argon2.X86.Derive.saltR s₀, VG.Proof.Argon2.X86.Derive.secR s₀, VG.Proof.Argon2.X86.Derive.adR s₀]) :
    bytesAt s.mem R.base R.len = bytesAt s₀.mem R.base R.len := by
  have hR' : R ∈ [VG.Proof.Argon2.X86.Derive.pwR s₀, VG.Proof.Argon2.X86.Derive.saltR s₀, VG.Proof.Argon2.X86.Derive.secR s₀, VG.Proof.Argon2.X86.Derive.adR s₀, VG.Proof.Argon2.X86.Derive.argR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> simp
  have hS : R ∈ [VG.Proof.Argon2.X86.Derive.pwR s₀, VG.Proof.Argon2.X86.Derive.saltR s₀, VG.Proof.Argon2.X86.Derive.secR s₀, VG.Proof.Argon2.X86.Derive.adR s₀, VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> simp
  have stk := (hp.stk_all R hS).symm
  have hl : R.len ≤ 2 ^ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> exact Nat.le_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  rw [h.frame.bytes (R := R) (fun r hr => ?_) hl hi]
  · exact (VG.Proof.Argon2.X86.Derive.entry_frame hp).bytes (R := R) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact stk.sub_right (VG.Proof.Argon2.X86.Derive.frame_stk hp (d := 0) (n := 160) (by decide) |> fun hs => by
        simpa using hs)) hl hi
  simp only [VG.Proof.Argon2.X86.Derive.bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact stk.sub_right (by simpa using VG.Proof.Argon2.X86.Derive.frame_stk hp (d := 0) (n := 144) (by decide))
  · exact stk.sub_right (VG.Proof.Argon2.X86.Derive.call_stk hp)

end

end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.Scratch`. -/
section

section

section

/-!
# Argon2 on x86 (32-bit): the derivation's locals

`lw s₀ s d`: the word at `[ebp + d]` in the body. A store to the locals keeps
the invariant and every other word (`Inv.store_loc`); writes to the memory
matrix, `scratch`, the output or the stack below the locals keep all of them
(`lw_keep`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd)
open VG.Spec.Blake2 (bytesAt)

/-- The word at `[ebp + d]`. -/
abbrev lw (s₀ s : State) (d : Nat) : BitVec 32 := s.mem.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) 32

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

theorem loc_addr {d : Nat} (hd : d < 236) :
    (VG.Proof.Argon2.X86.Derive.E s₀ + BitVec.ofNat 32 d).toNat = (VG.Proof.Argon2.X86.Derive.E s₀).toNat + d := VG.Proof.Argon2.X86.Derive.add_nat (by have := VG.Proof.Argon2.X86.Derive.E_hi hp; omega)

/-- Another word of the frame, after a store to the locals. -/
theorem lw_store {m : Mem} {d e : Nat} (hd : d + 4 ≤ 236) (he : e + 4 ≤ 236) (hde : d + 4 ≤ e ∨ e + 4 ≤ d)
    (v : BitVec 32) :
    (m.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) v).readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) e) 32 = m.readW (addr (VG.Proof.Argon2.X86.Derive.E s₀) e) 32 :=
  Proof.Sha256.X86.Stream.readW_writeW_addr m v (by have := VG.Proof.Argon2.X86.Derive.E_hi hp; omega) (by have := VG.Proof.Argon2.X86.Derive.E_hi hp; omega) hde.symm

theorem Inv.store_loc {s t : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {v : BitVec 32}
    (u : Mupd s t (s.mem.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) v)) :
    VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ VG.Proof.Argon2.X86.Derive.lw s₀ t d = v ∧ ∀ e, e + 4 ≤ 236 → (d + 4 ≤ e ∨ e + 4 ≤ d) → VG.Proof.Argon2.X86.Derive.lw s₀ t e = VG.Proof.Argon2.X86.Derive.lw s₀ s e := by
  have hE := VG.Proof.Argon2.X86.Derive.E_hi hp
  refine ⟨h.step (by rw [u.gpr]) (by rw [u.gpr]) u.rd u.wr ?_, ?_, fun e he hde => ?_⟩
  · rw [u.mem]
    exact (Frame.refl _ _).writeW (r := VG.Proof.Argon2.X86.Derive.locR s₀) (by simp) v
      (VG.Proof.Argon2.X86.Derive.contains32 (by rw [VG.Proof.Argon2.X86.Derive.loc_addr hp (by omega)]; omega) (by rw [VG.Proof.Argon2.X86.Derive.loc_addr hp (by omega)]; omega))
  · show t.mem.readW _ 32 = v
    rw [u.mem, Mem.readW_writeW_self32]
  · show t.mem.readW _ 32 = _
    rw [u.mem, VG.Proof.Argon2.X86.Derive.lw_store hp (by omega) he hde]

/-- `mov [ebp + d], r` -/
theorem wp_stloc {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.X86.Derive.Inv s₀ t → VG.Proof.Argon2.X86.Derive.lw s₀ t d = s.gpr r → (∀ e, e + 4 ≤ 236 → (d + 4 ≤ e ∨ e + 4 ≤ d) →
      VG.Proof.Argon2.X86.Derive.lw s₀ t e = VG.Proof.Argon2.X86.Derive.lw s₀ s e) → t.gpr = s.gpr → t.mem = s.mem.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) (s.gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (.store ⟨.ebp, d⟩ r :: is)) s Q :=
  VG.X86.Wp.wp_stm h.ebp (VG.Proof.Argon2.X86.Derive.loc_in hp h hd) fun t u =>
    let ⟨i, v, o⟩ := h.store_loc hp hd u
    k t i v o u.gpr u.mem

/-- `mov r, [ebp + d]` -/
theorem wp_ldloc {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (VG.Proof.Argon2.X86.Derive.lw s₀ s d) → WP isa (.block is) t Q) :
    WP isa (.block (.mov r (.mem ⟨.ebp, d⟩) :: is)) s Q :=
  VG.X86.Wp.wp_ldm h.ebp (VG.Proof.Argon2.X86.Derive.loc_in' hp h hd) k

/-- `mov r, [ebp + argOff i]` -/
theorem wp_ldarg {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (VG.X86.arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (.mov r (.mem ⟨.ebp, Impl.Argon2.X86.Derive.argOff i⟩) :: is)) s Q :=
  VG.X86.Wp.wp_ldm h.ebp (h.arg_in hp hi) fun t u => k t (by rw [h.arg hp hi] at u; exact u)

/-- The locals are outside the memory matrix, `scratch`, the output and the stack below them. -/
theorem loc_disj {d : Nat} (hd : d + 4 ≤ 144) :
    ∀ r ∈ [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀, VG.Proof.Argon2.X86.Derive.callR s₀], Region.Disjoint ⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) d, 4⟩ r := by
  have hE := VG.Proof.Argon2.X86.Derive.E_hi hp
  have hl := hp.esp_lo
  have hEn := VG.Proof.Argon2.X86.Derive.E_nat hp
  have sub := VG.Proof.Argon2.X86.Derive.loc_stk hp (d := d) (n := 4) hd
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact VG.Proof.Argon2.X86.Derive.disj32 (.inr (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by rw [VG.Proof.Argon2.X86.Derive.E_nat hp]; omega), VG.Proof.Argon2.X86.Derive.loc_addr hp (by omega)]; omega))
      (by rw [VG.Proof.Argon2.X86.Derive.loc_addr hp (by omega)]; omega) (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by rw [VG.Proof.Argon2.X86.Derive.E_nat hp]; omega)]; omega)

/-- The locals are kept by writes outside them. -/
theorem lw_keep {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀, VG.Proof.Argon2.X86.Derive.callR s₀], Region.Sub r r') {d : Nat}
    (hd : d + 4 ≤ 144) : VG.Proof.Argon2.X86.Derive.lw s₀ t d = VG.Proof.Argon2.X86.Derive.lw s₀ s d :=
  (f.sub hs).readW (Region.contains_self _ _) (VG.Proof.Argon2.X86.Derive.loc_disj hp hd) (by decide)

end

/-- The body's first instruction points `ebp` to the locals. -/
theorem inv_start {s₀ : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.X86.Derive.Inv s₀ t → t.mem = (VG.Proof.Argon2.X86.Derive.entry s₀).mem → (∀ r, r ≠ .ebp → t.gpr r = (VG.Proof.Argon2.X86.Derive.entry s₀).gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (.mov .ebp (.reg .esp) :: is)) (VG.Proof.Argon2.X86.Derive.entry s₀) Q :=
  VG.X86.Wp.wp_mov fun t u => k t
    ⟨by rw [u.other _ (by decide), VG.Proof.Argon2.X86.Derive.entry_esp], by rw [u.gpr, VG.Proof.Argon2.X86.Derive.entry_esp], by rw [u.rd, VG.Proof.Argon2.X86.Derive.entry_rd],
      by rw [u.wr], by rw [u.mem]; exact Frame.refl _ _⟩ u.mem u.other

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the parameters

`parameters_ok`: the body's first instructions point `ebp` to the locals and
store there `4 · lanes` (the divisor), the segment length (by the fixed-time
division), the lane length and its size in bytes (`Prm`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd wp_add wp_addi wp_movi wp_mov)
open VG.Impl.Argon2.X86.Derive (parameters divisorOff segLenOff laneLenOff strideOff argOff)

/-- The parameters in the locals. -/
structure Prm (s₀ s : State) : Prop where
  divisor : VG.Proof.Argon2.X86.Derive.lw s₀ s divisorOff = BitVec.ofNat 32 (4 * VG.Proof.Argon2.X86.Derive.lanesN s₀)
  segLen : VG.Proof.Argon2.X86.Derive.lw s₀ s segLenOff = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.prm s₀).segmentLen
  laneLen : VG.Proof.Argon2.X86.Derive.lw s₀ s laneLenOff = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen
  stride : VG.Proof.Argon2.X86.Derive.lw s₀ s strideOff = BitVec.ofNat 32 ((VG.Proof.Argon2.X86.Derive.prm s₀).laneLen * 1024)

/-- `add ecx, ecx`, `n` times. -/
theorem dbl_ok {s : State} {is : List Instr} {Q : State → Prop} :
    ∀ n, (s.gpr .ecx).toNat * 2 ^ n < 2 ^ 32 →
      (∀ t, (t.gpr .ecx).toNat = (s.gpr .ecx).toNat * 2 ^ n → Divide.Keep s t → WP isa (.block is) t Q) →
      WP isa (.block (List.replicate n (.alu .add .ecx (.reg .ecx)) ++ is)) s Q
  | 0, _, k => k s (by simp) (Divide.Keep.refl s)
  | n + 1, hn, k => by
    rw [List.replicate_succ, List.cons_append]
    have e : (s.gpr .ecx).toNat * 2 ^ (n + 1) = (s.gpr .ecx).toNat * 2 * 2 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]
    have hx : (s.gpr .ecx).toNat ≤ (s.gpr .ecx).toNat * 2 ^ n :=
      Nat.le_mul_of_pos_right _ (Nat.two_pow_pos n)
    have two : (s.gpr .ecx).toNat * 2 < 2 ^ 32 := by
      have := Nat.mul_le_mul_right 2 hx
      rw [Nat.mul_right_comm] at this
      rw [e] at hn
      omega
    refine wp_add fun s₁ u₁ _ => VG.Proof.Argon2.X86.Derive.dbl_ok (s := s₁) n ?_ fun t ht kt => k t ?_
      ((Divide.Keep.of_upd u₁ (by simp)).trans kt)
    · rw [u₁.gpr, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega), ← Nat.two_mul, Nat.mul_comm 2]
      rw [e] at hn; exact hn
    · rw [ht, u₁.gpr, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega), ← Nat.two_mul, Nat.mul_comm 2, e]

theorem lw_mem {s₀ s t : State} (h : t.mem = s.mem) (d : Nat) : VG.Proof.Argon2.X86.Derive.lw s₀ t d = VG.Proof.Argon2.X86.Derive.lw s₀ s d := by
  simp only [VG.Proof.Argon2.X86.Derive.lw, h]

theorem Inv.keep {s₀ s t : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (k : Divide.Keep s t) : VG.Proof.Argon2.X86.Derive.Inv s₀ t :=
  h.step (k.other _ (by decide) (by decide) (by decide)) (k.other _ (by decide) (by decide) (by decide))
    k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

theorem parameters_ok {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.X86.Derive.Inv s₀ t → VG.Proof.Argon2.X86.Derive.Prm s₀ t → WP isa (.block is) t Q) :
    WP isa (.block ((.mov .ebp (.reg .esp) :: parameters) ++ is)) (VG.Proof.Argon2.X86.Derive.entry s₀) Q := by
  have hL := hp.lanes_lt
  have hL1 := hp.lanes_pos
  have hBl := hp.blocks_lt
  have hb := hp.blocks_eq
  have hseg := hp.segLen_eq
  have hlane := hp.laneLen_eq
  simp only [parameters, Impl.Argon2.X86.Derive.fr, List.cons_append, List.append_assoc]
  refine VG.Proof.Argon2.X86.Derive.inv_start fun s₁ i₁ _ _ => ?_
  refine VG.Proof.Argon2.X86.Derive.wp_ldarg hp i₁ (i := Impl.Argon2.X86.Derive.lanesArg) (by decide) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide) (by decide)
  refine wp_add fun s₃ u₃ _ => wp_add fun s₄ u₄ _ => ?_
  have i₄ := (i₂.upd u₃ (by decide) (by decide)).upd u₄ (by decide) (by decide)
  have e₄ : (s₄.gpr .eax).toNat = 4 * VG.Proof.Argon2.X86.Derive.lanesN s₀ := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr]
    simp only [BitVec.toNat_add]
    show (((VG.X86.arg s₀ 7).toNat + (VG.X86.arg s₀ 7).toNat) % 2 ^ 32 + ((VG.X86.arg s₀ 7).toNat + (VG.X86.arg s₀ 7).toNat) % 2 ^ 32)
      % 2 ^ 32 = 4 * (VG.X86.arg s₀ 7).toNat
    have : (VG.X86.arg s₀ 7).toNat < 2 ^ 24 := hL
    omega
  refine VG.Proof.Argon2.X86.Derive.wp_stloc hp i₄ (d := divisorOff) (by decide) fun s₅ i₅ v₅ _ g₅ _ => ?_
  refine VG.Proof.Argon2.X86.Derive.wp_ldarg hp i₅ (i := Impl.Argon2.X86.Derive.memoryCostArg) (by decide) fun s₆ u₆ => ?_
  have i₆ := i₅.upd u₆ (by decide) (by decide)
  have d₆ : VG.Proof.Argon2.X86.Derive.lw s₀ s₆ divisorOff = s₄.gpr .eax := by rw [VG.Proof.Argon2.X86.Derive.lw_mem u₆.mem, v₅]
  refine Divide.code_ok (D := s₄.gpr .eax) (by rw [e₄]; omega) (by rw [e₄]; omega) i₆.ebp
    (VG.Proof.Argon2.X86.Derive.loc_in' hp i₆ (by decide)) d₆ fun s₇ c₇ _ k₇ => ?_
  have i₇ := i₆.keep k₇
  rw [u₆.gpr, e₄] at c₇
  have c₇' : (s₇.gpr .ecx).toNat = (VG.Proof.Argon2.X86.Derive.prm s₀).segmentLen := by rw [c₇, hseg]; rfl
  refine VG.Proof.Argon2.X86.Derive.wp_stloc hp i₇ (d := segLenOff) (by decide) fun s₈ i₈ v₈ o₈ g₈ _ => ?_
  have hll : (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen ≤ VG.Proof.Argon2.X86.Derive.blocksN s₀ :=
    Nat.le_trans (Nat.le_mul_of_pos_left _ hL1) (Nat.le_of_eq hb.symm)
  have hsegL : (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen * 1024 + 16384 ≤ 2 ^ 32 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right 1024 hll) _) hBl
  refine wp_add fun s₉ u₉ _ => wp_add fun s₁₀ u₁₀ _ => ?_
  have i₁₀ := (i₈.upd u₉ (by decide) (by decide)).upd u₁₀ (by decide) (by decide)
  have e₁₀ : (s₁₀.gpr .ecx).toNat = (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen := by
    rw [u₁₀.gpr, u₉.gpr, g₈]
    simp only [BitVec.toNat_add, c₇']
    omega
  refine VG.Proof.Argon2.X86.Derive.wp_stloc hp i₁₀ (d := laneLenOff) (by decide) fun s₁₁ i₁₁ v₁₁ o₁₁ g₁₁ _ => ?_
  refine VG.Proof.Argon2.X86.Derive.dbl_ok 10 (by rw [g₁₁, e₁₀]; omega) fun s₁₂ e₁₂ k₁₂ => ?_
  have i₁₂ := i₁₁.keep k₁₂
  refine VG.Proof.Argon2.X86.Derive.wp_stloc hp i₁₂ (d := strideOff) (by decide) fun s₁₃ i₁₃ v₁₃ o₁₃ _ _ => k s₁₃ i₁₃ ⟨?_, ?_, ?_, ?_⟩
  · rw [o₁₃ _ (by decide) (by decide), VG.Proof.Argon2.X86.Derive.lw_mem k₁₂.mem, o₁₁ _ (by decide) (by decide), VG.Proof.Argon2.X86.Derive.lw_mem u₁₀.mem,
      VG.Proof.Argon2.X86.Derive.lw_mem u₉.mem, o₈ _ (by decide) (by decide), VG.Proof.Argon2.X86.Derive.lw_mem k₇.mem, VG.Proof.Argon2.X86.Derive.lw_mem u₆.mem, v₅]
    exact BitVec.eq_of_toNat_eq (by rw [e₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [o₁₃ _ (by decide) (by decide), VG.Proof.Argon2.X86.Derive.lw_mem k₁₂.mem, o₁₁ _ (by decide) (by decide), VG.Proof.Argon2.X86.Derive.lw_mem u₁₀.mem,
      VG.Proof.Argon2.X86.Derive.lw_mem u₉.mem, v₈]
    exact BitVec.eq_of_toNat_eq (by rw [c₇', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [o₁₃ _ (by decide) (by decide), VG.Proof.Argon2.X86.Derive.lw_mem k₁₂.mem, v₁₁]
    exact BitVec.eq_of_toNat_eq (by rw [e₁₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  · rw [v₁₃]
    exact BitVec.eq_of_toNat_eq (by
      rw [e₁₂, g₁₁, e₁₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])

end

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the derivation's use of H′'s hash macros

The H₀ code calls the BLAKE2b functions through H′'s macros
(`Impl.Argon2.X86.HPrime`), with `ebx` pointing to `scratch` and the stack
below the locals: `ctx` gives their context (`HPrime.Ctx`), and `Inv.keeps`
the body's invariant and locals after them. `Inv.store_scr` is a store to
`scratch` through `ebx`.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd)
open VG.Proof.Argon2.X86.HPrime (Ctx Keeps)

/-- `n` bytes of `scratch` at offset `d`. -/
theorem scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 16384) :
    Region.Sub ⟨(VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ (VG.Proof.Argon2.X86.Derive.scrR s₀) := Offset.sub_base _ h

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

theorem scr_mem : VG.Proof.Argon2.X86.Derive.scrR s₀ ∈ (VG.Proof.Argon2.X86.Derive.entry s₀).wr := VG.Proof.Argon2.X86.Derive.wr_mem s₀ (by rw [hp.wr]; simp)
theorem mem_mem : VG.Proof.Argon2.X86.Derive.memR s₀ ∈ (VG.Proof.Argon2.X86.Derive.entry s₀).wr := VG.Proof.Argon2.X86.Derive.wr_mem s₀ (by rw [hp.wr]; simp)
theorem out_mem : VG.Proof.Argon2.X86.Derive.outR s₀ ∈ (VG.Proof.Argon2.X86.Derive.entry s₀).wr := VG.Proof.Argon2.X86.Derive.wr_mem s₀ (by rw [hp.wr]; simp)


/-- The 60 bytes below the locals that H′'s macros use are outside the body's other regions. -/
theorem below60_call : Region.Sub (VG.X86.below (VG.Proof.Argon2.X86.Derive.E s₀) 60) (VG.Proof.Argon2.X86.Derive.callR s₀) :=
  VG.X86.below_sub (by decide) (by rw [VG.Proof.Argon2.X86.Derive.E_nat hp]; have := hp.esp_lo; omega)

theorem ctx {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (hb : s.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀) : VG.Proof.Argon2.X86.HPrime.Ctx (VG.Proof.Argon2.X86.Derive.scrP s₀) (VG.Proof.Argon2.X86.Derive.E s₀) s := by
  have := hp.scr_fits
  refine ⟨hb, h.esp, by omega, by rw [VG.Proof.Argon2.X86.Derive.E_nat hp]; have := hp.esp_lo; omega,
    by have := VG.Proof.Argon2.X86.Derive.E_hi hp; omega, ?_, ?_⟩
  · rw [h.wr]
    exact (Covers.of_sub (rs' := [VG.Proof.Argon2.X86.Derive.scrR s₀]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
      (fun a n ⟨r, hr, hc⟩ => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Argon2.X86.Derive.scr_mem hp, hc⟩)
  · exact ((hp.stk_all (VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).sub_left fun a ha => VG.Proof.Argon2.X86.Derive.call_stk hp a (VG.Proof.Argon2.X86.Derive.below60_call hp a ha)).sub_right
      (Region.sub_prefix (by decide))

/-- What H′'s macros keep keeps the body's invariant and the locals. -/
theorem Inv.keeps {s t : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (k : Keeps (VG.Proof.Argon2.X86.Derive.scrP s₀) (VG.Proof.Argon2.X86.Derive.E s₀) s t) :
    VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.X86.Derive.lw s₀ t d = VG.Proof.Argon2.X86.Derive.lw s₀ s d := by
  have sub : ∀ r ∈ [(⟨(VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64, 832⟩ : Region), VG.X86.below (VG.Proof.Argon2.X86.Derive.E s₀) 60],
      ∃ r' ∈ [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀, VG.Proof.Argon2.X86.Derive.callR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.Argon2.X86.Derive.callR s₀, by simp, VG.Proof.Argon2.X86.Derive.below60_call hp⟩
  refine ⟨h.step k.esp k.ebp k.rd k.wr (k.frame.sub fun r hr => ?_), fun d hd => VG.Proof.Argon2.X86.Derive.lw_keep hp k.frame sub hd⟩
  obtain ⟨r', hr', hs⟩ := sub r hr
  refine ⟨r', ?_, hs⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl <;> simp

end

/-! ## The hash macros, with `Keeps` -/

section
open VG.Spec.Blake2

variable {B E : BitVec 32} {s : State} (c : VG.Proof.Argon2.X86.HPrime.Ctx B E s)
include c

theorem init_k {n : Nat} (hn : s.gpr .edx = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa Impl.Argon2.X86.HPrime.init s fun t =>
      Repr b (Spec.Blake2.init b n 0) t.mem (B.setWidth 64) [] ∧ Keeps B E s t :=
  (HPrime.init_ok c hn hn₁ hn₂).mono fun t ⟨r, cs, rd, wr, f⟩ =>
    ⟨r, Keeps.of_call (HPrime.of_callee cs) rd wr f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by decide) c.lo⟩⟩

theorem update_k {D : BitVec 32} {L : Nat}
    (hD : s.gpr .esi = D) (hL : (s.gpr .edi).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨D.setWidth 64, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨D.setWidth 64, L⟩ ⟨B.setWidth 64, 768⟩)
    (hDk : (below E 60).Disjoint ⟨D.setWidth 64, L⟩)
    {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (B.setWidth 64) d)
    (hc : s.gpr .edx ++ s.gpr .ecx = BitVec.ofNat 64 d.length) (hlen : d.length + L < 2 ^ 64) :
    WP isa Impl.Argon2.X86.HPrime.update s fun t =>
      Repr b h0 t.mem (B.setWidth 64) (d ++ bytesAt s.mem (D.setWidth 64) L) ∧ Keeps B E s t :=
  (HPrime.update_ok c hD hL hDfit hDc hDs hDk repr hc hlen).mono fun t ⟨r, cs, rd, wr, f⟩ =>
    ⟨r, Keeps.of_call (HPrime.of_callee cs) rd wr f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩⟩

theorem finalize_k {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (B.setWidth 64) d)
    (hc : s.gpr .edx ++ s.gpr .ecx = BitVec.ofNat 64 d.length) (hlen : d.length < 2 ^ 64) :
    WP isa Impl.Argon2.X86.HPrime.finalize s fun t =>
      bytesAt t.mem (B.setWidth 64 + 768) 64 = finalHash b h0 d ∧ Keeps B E s t :=
  (HPrime.finalize_ok c repr hc hlen).mono fun t ⟨dg, cs, rd, wr, f⟩ =>
    ⟨dg, Keeps.of_call (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact cs _ (by decide) (by decide)) rd wr f fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩⟩

end

end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.Initial`. -/
section

/-!
# Argon2 on x86 (32-bit): H₀

`HI s₀ data s`: the BLAKE2b state at `scratch` has absorbed `data`, whose
length is in the locals. `start_ok` absorbs the header, `absorb_ok` an
input with its length prefix, `finish_ok` writes the digest to the first 64
bytes of the locals: `code_ok`, H₀ (`Spec.Argon2.initialHash`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd wp_movi wp_mov wp_add wp_addi)
open VG.Spec.Blake2 (Repr b bytesAt)
open VG.Proof.Argon2.X86.HPrime (Ctx Keeps)
open VG.Impl.Argon2.X86.Derive (countLoOff countHiOff argOff)

/-- H₀'s streaming state at `scratch`, with `data` absorbed. -/
structure HI (s₀ : State) (data : List Byte) (s : State) : Prop where
  inv : VG.Proof.Argon2.X86.Derive.Inv s₀ s
  prm : VG.Proof.Argon2.X86.Derive.Prm s₀ s
  ebx : s.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀
  repr : Repr b (Spec.Blake2.init b 64 0) s.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64) data
  lo : VG.Proof.Argon2.X86.Derive.lw s₀ s countLoOff = BitVec.ofNat 32 data.length
  hi : VG.Proof.Argon2.X86.Derive.lw s₀ s countHiOff = BitVec.ofNat 32 (data.length / 2 ^ 32)
  len : data.length < 2 ^ 36

theorem Prm.of_lw {s₀ s t : State} (pr : VG.Proof.Argon2.X86.Derive.Prm s₀ s)
    (h : ∀ d ∈ [Impl.Argon2.X86.Derive.divisorOff, Impl.Argon2.X86.Derive.segLenOff,
      Impl.Argon2.X86.Derive.laneLenOff, Impl.Argon2.X86.Derive.strideOff], VG.Proof.Argon2.X86.Derive.lw s₀ t d = VG.Proof.Argon2.X86.Derive.lw s₀ s d) :
    VG.Proof.Argon2.X86.Derive.Prm s₀ t :=
  ⟨by rw [h _ (by simp)]; exact pr.divisor, by rw [h _ (by simp)]; exact pr.segLen,
    by rw [h _ (by simp)]; exact pr.laneLen, by rw [h _ (by simp)]; exact pr.stride⟩

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

theorem scr_addr {o : Nat} (ho : o < 16384) :
    addr (VG.Proof.Argon2.X86.Derive.scrP s₀) o = (VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 o :=
  addr_eq (by have := hp.scr_fits; omega)

/-- `mov [ebx + o], r`, to `scratch`. -/
theorem wp_stscr {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (hb : s.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀) {o : Nat} (ho : o + 4 ≤ 16384)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.X86.Derive.Inv s₀ t → t.mem = s.mem.writeW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) o) (s.gpr r) → t.gpr = s.gpr →
      (∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.X86.Derive.lw s₀ t d = VG.Proof.Argon2.X86.Derive.lw s₀ s d) →
      Frame [⟨(VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 o, 4⟩] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store ⟨.ebx, o⟩ r :: is)) s Q := by
  have hc : (VG.Proof.Argon2.X86.Derive.scrR s₀).Contains (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) o) 4 := by
    rw [VG.Proof.Argon2.X86.Derive.scr_addr hp (by omega)]; exact Offset.contains_base _ ho (by omega)
  refine VG.X86.Wp.wp_stm hb (by rw [h.wr]; exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.scr_mem hp, hc⟩) fun t u => ?_
  have f : Frame [⟨(VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 o, 4⟩] s.mem t.mem := by
    rw [u.mem, VG.Proof.Argon2.X86.Derive.scr_addr hp (by omega)]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k t (h.step (by rw [u.gpr]) (by rw [u.gpr]) u.rd u.wr ?_) u.mem u.gpr
    (fun d hd => VG.Proof.Argon2.X86.Derive.lw_keep hp f (fun r hr => ?_) hd) f
  · rw [u.mem]; exact (Frame.refl _ _).writeW (r := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp) _ hc
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, by simp, VG.Proof.Argon2.X86.Derive.scr_sub (by omega)⟩

omit hp in
/-- A store to `scratch` from offset 192 on keeps the streaming state. -/
theorem repr_store {m m' : Mem} {o : Nat} (ho : 192 ≤ o) (ho' : o + 4 ≤ 16384)
    (f : Frame [⟨(VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 o, 4⟩] m m') {data : List Byte}
    (h : Repr b (Spec.Blake2.init b 64 0) m ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64) data) :
    Repr b (Spec.Blake2.init b 64 0) m' ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64) data :=
  HPrime.repr_frame f (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.base_disjoint _ ho (by omega)) h

end

/-- The bytes at `p`: a word, then the rest. -/
theorem bytes_word (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (4 + n) = Spec.Blake2.wordBytes (m.readW p 32) ++ bytesAt m (p + BitVec.ofNat 64 4) n := by
  rw [Proof.Blake2.bytesAt_add, Proof.Blake2.wordBytes_readW (w := 32) m p (.inl rfl)]

theorem variant_code {s₀ : State} (hk : (VG.Proof.Argon2.X86.Derive.kindV s₀).toNat ≤ 2) : (VG.Proof.Argon2.X86.Derive.prm s₀).variant.code = (VG.Proof.Argon2.X86.Derive.kindV s₀).toNat := by
  simp only [VG.Proof.Argon2.X86.Derive.prm]
  rcases (by omega : (kindV s₀).toNat = 0 ∨ (kindV s₀).toNat = 1 ∨ (kindV s₀).toNat = 2) with h | h | h <;>
    simp [h, Spec.Argon2.Variant.code, Spec.Argon2.params]

theorem le32_arg (x : BitVec 32) : Spec.Argon2.le32 x.toNat = Spec.Blake2.wordBytes x := by
  simp only [Spec.Argon2.le32, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem header_eq : Impl.Argon2.X86.Derive.header =
    [.mov .eax (.mem ⟨.ebp, argOff 7⟩), .store ⟨.ebx, 768⟩ .eax,
     .mov .eax (.mem ⟨.ebp, argOff 17⟩), .store ⟨.ebx, 772⟩ .eax,
     .mov .eax (.mem ⟨.ebp, argOff 6⟩), .store ⟨.ebx, 776⟩ .eax,
     .mov .eax (.mem ⟨.ebp, argOff 5⟩), .store ⟨.ebx, 780⟩ .eax,
     .mov .eax (.imm 0x13), .store ⟨.ebx, 784⟩ .eax,
     .mov .eax (.mem ⟨.ebp, argOff 0⟩), .store ⟨.ebx, 788⟩ .eax] := rfl

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

/-- A word of `scratch` is kept by a store to another one. -/
theorem scr_keep {m m' : Mem} {o o' : Nat} (ho : o + 4 ≤ 16384) (ho' : o' + 4 ≤ 16384)
    (hd : o + 4 ≤ o' ∨ o' + 4 ≤ o)
    (f : Frame [⟨(VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 o', 4⟩] m m') :
    m'.readW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) o) 32 = m.readW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) o) 32 := by
  rw [VG.Proof.Argon2.X86.Derive.scr_addr hp (by omega)]
  refine f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ hd (by omega) (by omega)

/-- The six header words, at `scratch + 768`. -/
theorem header_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.X86.Derive.Prm s₀ s) (hb : s.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀)
    (repr : Repr b (Spec.Blake2.init b 64 0) s.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64) []) :
    WP isa (.block Impl.Argon2.X86.Derive.header) s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ t ∧
      t.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ ∧ Repr b (Spec.Blake2.init b 64 0) t.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64) [] ∧
      bytesAt t.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (VG.Proof.Argon2.X86.Derive.prm s₀) ∧
      ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.X86.Derive.lw s₀ t d = VG.Proof.Argon2.X86.Derive.lw s₀ s d := by
  rw [VG.Proof.Argon2.X86.Derive.header_eq]
  refine VG.Proof.Argon2.X86.Derive.wp_ldarg hp h (i := 7) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide) (by decide)
  have b₁ : s₁.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ := by rw [u₁.other _ (by decide), hb]
  refine VG.Proof.Argon2.X86.Derive.wp_stscr hp i₁ b₁ (o := 768) (by decide) fun s₂ i₂ m₂ g₂ l₂ f₂ => ?_
  have b₂ : s₂.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ := by rw [g₂, b₁]
  refine VG.Proof.Argon2.X86.Derive.wp_ldarg hp i₂ (i := 17) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide) (by decide)
  have b₃ : s₃.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ := by rw [u₃.other _ (by decide), b₂]
  refine VG.Proof.Argon2.X86.Derive.wp_stscr hp i₃ b₃ (o := 772) (by decide) fun s₄ i₄ m₄ g₄ l₄ f₄ => ?_
  have b₄ : s₄.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ := by rw [g₄, b₃]
  refine VG.Proof.Argon2.X86.Derive.wp_ldarg hp i₄ (i := 6) (by decide) fun s₅ u₅ => ?_
  have i₅ := i₄.upd u₅ (by decide) (by decide)
  have b₅ : s₅.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ := by rw [u₅.other _ (by decide), b₄]
  refine VG.Proof.Argon2.X86.Derive.wp_stscr hp i₅ b₅ (o := 776) (by decide) fun s₆ i₆ m₆ g₆ l₆ f₆ => ?_
  have b₆ : s₆.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ := by rw [g₆, b₅]
  refine VG.Proof.Argon2.X86.Derive.wp_ldarg hp i₆ (i := 5) (by decide) fun s₇ u₇ => ?_
  have i₇ := i₆.upd u₇ (by decide) (by decide)
  have b₇ : s₇.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ := by rw [u₇.other _ (by decide), b₆]
  refine VG.Proof.Argon2.X86.Derive.wp_stscr hp i₇ b₇ (o := 780) (by decide) fun s₈ i₈ m₈ g₈ l₈ f₈ => ?_
  have b₈ : s₈.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ := by rw [g₈, b₇]
  refine wp_movi fun s₉ u₉ => ?_
  have i₉ := i₈.upd u₉ (by decide) (by decide)
  have b₉ : s₉.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ := by rw [u₉.other _ (by decide), b₈]
  refine VG.Proof.Argon2.X86.Derive.wp_stscr hp i₉ b₉ (o := 784) (by decide) fun s₁₀ i₁₀ m₁₀ g₁₀ l₁₀ f₁₀ => ?_
  have b₁₀ : s₁₀.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ := by rw [g₁₀, b₉]
  refine VG.Proof.Argon2.X86.Derive.wp_ldarg hp i₁₀ (i := 0) (by decide) fun s₁₁ u₁₁ => ?_
  have i₁₁ := i₁₀.upd u₁₁ (by decide) (by decide)
  have b₁₁ : s₁₁.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ := by rw [u₁₁.other _ (by decide), b₁₀]
  refine VG.Proof.Argon2.X86.Derive.wp_stscr hp i₁₁ b₁₁ (o := 788) (by decide) fun t it mt gt lt ft => WP.block_nil ?_
  -- The locals.
  have L : ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.X86.Derive.lw s₀ t d = VG.Proof.Argon2.X86.Derive.lw s₀ s d := fun d hd => by
    rw [lt d hd, VG.Proof.Argon2.X86.Derive.lw_mem u₁₁.mem, l₁₀ d hd, VG.Proof.Argon2.X86.Derive.lw_mem u₉.mem, l₈ d hd, VG.Proof.Argon2.X86.Derive.lw_mem u₇.mem, l₆ d hd, VG.Proof.Argon2.X86.Derive.lw_mem u₅.mem,
      l₄ d hd, VG.Proof.Argon2.X86.Derive.lw_mem u₃.mem, l₂ d hd, VG.Proof.Argon2.X86.Derive.lw_mem u₁.mem]
  -- The streaming state.
  have R : Repr b (Spec.Blake2.init b 64 0) t.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64) [] := by
    refine VG.Proof.Argon2.X86.Derive.repr_store (by decide) (by decide) ft ?_
    rw [u₁₁.mem]; refine VG.Proof.Argon2.X86.Derive.repr_store (by decide) (by decide) f₁₀ ?_
    rw [u₉.mem]; refine VG.Proof.Argon2.X86.Derive.repr_store (by decide) (by decide) f₈ ?_
    rw [u₇.mem]; refine VG.Proof.Argon2.X86.Derive.repr_store (by decide) (by decide) f₆ ?_
    rw [u₅.mem]; refine VG.Proof.Argon2.X86.Derive.repr_store (by decide) (by decide) f₄ ?_
    rw [u₃.mem]; refine VG.Proof.Argon2.X86.Derive.repr_store (by decide) (by decide) f₂ ?_
    rw [u₁.mem]; exact repr
  refine ⟨it, ⟨?_, ?_, ?_, ?_⟩, by rw [gt, b₁₁], R, ?_, L⟩
  · rw [L _ (by decide)]; exact pr.divisor
  · rw [L _ (by decide)]; exact pr.segLen
  · rw [L _ (by decide)]; exact pr.laneLen
  · rw [L _ (by decide)]; exact pr.stride
  -- The words.
  have w0 : t.mem.readW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) 768) 32 = VG.X86.arg s₀ 7 := by
    rw [VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) ft, u₁₁.mem,
      VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) f₈, u₇.mem,
      VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) f₆, u₅.mem,
      VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) f₄, u₃.mem, m₂, Mem.readW_writeW_self32, u₁.gpr]
  have w1 : t.mem.readW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) 772) 32 = VG.X86.arg s₀ 17 := by
    rw [VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) ft, u₁₁.mem,
      VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) f₈, u₇.mem,
      VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) f₆, u₅.mem, m₄, Mem.readW_writeW_self32, u₃.gpr]
  have w2 : t.mem.readW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) 776) 32 = VG.X86.arg s₀ 6 := by
    rw [VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) ft, u₁₁.mem,
      VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) f₁₀, u₉.mem,
      VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) f₈, u₇.mem, m₆, Mem.readW_writeW_self32, u₅.gpr]
  have w3 : t.mem.readW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) 780) 32 = VG.X86.arg s₀ 5 := by
    rw [VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) ft, u₁₁.mem,
      VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) f₁₀, u₉.mem, m₈, Mem.readW_writeW_self32, u₇.gpr]
  have w4 : t.mem.readW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) 784) 32 = 0x13 := by
    rw [VG.Proof.Argon2.X86.Derive.scr_keep hp (by decide) (by decide) (by decide) ft, u₁₁.mem, m₁₀, Mem.readW_writeW_self32, u₉.gpr]
  have w5 : t.mem.readW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) 788) 32 = VG.X86.arg s₀ 0 := by
    rw [mt, Mem.readW_writeW_self32, u₁₁.gpr]
  have a : ∀ o, o < 16384 → (VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 o = addr (VG.Proof.Argon2.X86.Derive.scrP s₀) o :=
    fun o ho => (VG.Proof.Argon2.X86.Derive.scr_addr hp ho).symm
  have step : ∀ o, (VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 o + BitVec.ofNat 64 4 =
      (VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 (o + 4) := fun o => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show (24 : Nat) = 4 + 20 from rfl, VG.Proof.Argon2.X86.Derive.bytes_word, step, show (20 : Nat) = 4 + 16 from rfl, VG.Proof.Argon2.X86.Derive.bytes_word, step,
    show (16 : Nat) = 4 + 12 from rfl, VG.Proof.Argon2.X86.Derive.bytes_word, step, show (12 : Nat) = 4 + 8 from rfl, VG.Proof.Argon2.X86.Derive.bytes_word, step,
    show (8 : Nat) = 4 + 4 from rfl, VG.Proof.Argon2.X86.Derive.bytes_word, step, show (4 : Nat) = 4 + 0 from rfl, VG.Proof.Argon2.X86.Derive.bytes_word]
  simp only [Nat.reduceAdd]
  rw [a 768 (by decide), a 772 (by decide), a 776 (by decide), a 780 (by decide), a 784 (by decide),
    a 788 (by decide), w0, w1, w2, w3, w4, w5]
  simp only [Proof.Argon2.initialHeader, VG.Proof.Argon2.X86.Derive.prm, ← VG.Proof.Argon2.X86.Derive.le32_arg, List.append_assoc,
    bytesAt, List.range_zero, List.map_nil, List.append_nil]
  have vc := VG.Proof.Argon2.X86.Derive.variant_code hp.kind_le
  simp only [VG.Proof.Argon2.X86.Derive.prm] at vc
  rw [vc]
  rfl

end

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

/-- `n` bytes of `scratch` at offset `d` are writable. -/
theorem scr_cov {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {d n : Nat} (hd : d + n ≤ 16384) :
    Covers [⟨(VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] s.wr := by
  rw [h.wr]
  exact Covers.of_sub (rs' := [VG.Proof.Argon2.X86.Derive.scrR s₀]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, List.mem_singleton_self _, d, rfl, hd⟩) |>.trans
    fun a n ⟨r, hr, hc⟩ => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Argon2.X86.Derive.scr_mem hp, hc⟩

/-- The stack below the locals is outside `scratch`. -/
theorem stk_scr {d n k : Nat} (hd : d + n ≤ 16384) (hk : k ≤ 84) :
    (VG.X86.below (VG.Proof.Argon2.X86.Derive.E s₀) k).Disjoint ⟨(VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ :=
  ((hp.stk_all (VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).sub_left fun a ha =>
    VG.Proof.Argon2.X86.Derive.call_stk hp a (VG.X86.below_sub hk (by rw [VG.Proof.Argon2.X86.Derive.E_nat hp]; have := hp.esp_lo; omega) a ha)).sub_right
    (VG.Proof.Argon2.X86.Derive.scr_sub hd)

/-- A store to the locals keeps the streaming state at `scratch`. -/
theorem repr_loc {m : Mem} {d : Nat} (hd : d + 4 ≤ 144) (v : BitVec 32) {h0 : Spec.Blake2.HashValue 64}
    {data : List Byte} (h : Repr b h0 m ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64) data) :
    Repr b h0 (m.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) v) ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64) data :=
  HPrime.repr_frame ((Frame.refl [⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) d, 4⟩] m).writeW (List.mem_singleton_self _) v
    (Region.contains_self _ _)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((VG.Proof.Argon2.X86.Derive.loc_disj hp hd (VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).symm).sub_left (VG.Proof.Argon2.X86.Derive.scr_sub (d := 0) (n := 192) (by decide) |>
        fun hs => by simpa using hs)) h

/-- `start`'s first block: `ebx :=` `scratch`, and the digest length. -/
theorem stA_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.X86.Derive.Prm s₀ s) :
    WP isa (.block [.mov .ebx (Impl.Argon2.X86.Derive.fr (argOff 15)), .mov .edx (.imm 64)]) s fun t =>
      VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ t ∧ t.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ ∧ t.gpr .edx = BitVec.ofNat 32 64 := by
  refine VG.Proof.Argon2.X86.Derive.wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_movi fun s₂ u₂ => WP.block_nil ?_
  have e : ∀ d, VG.Proof.Argon2.X86.Derive.lw s₀ s₂ d = VG.Proof.Argon2.X86.Derive.lw s₀ s d := fun d => by rw [VG.Proof.Argon2.X86.Derive.lw_mem u₂.mem, VG.Proof.Argon2.X86.Derive.lw_mem u₁.mem]
  exact ⟨(h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide),
    ⟨by rw [e]; exact pr.divisor, by rw [e]; exact pr.segLen, by rw [e]; exact pr.laneLen, by rw [e]; exact pr.stride⟩,
    by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr]; rfl⟩

/-- `start`'s `init`. -/
theorem stInit_ok {s : State}
    (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ s ∧ s.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ ∧ s.gpr .edx = BitVec.ofNat 32 64) :
    WP isa Impl.Argon2.X86.HPrime.init s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ t ∧ t.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64) [] :=
  (VG.Proof.Argon2.X86.Derive.init_k (VG.Proof.Argon2.X86.Derive.ctx hp h.1 h.2.2.1) (n := 64) h.2.2.2 (by decide) (by decide)).mono fun _ ⟨r, k⟩ =>
    let ⟨i, l⟩ := h.1.keeps hp k
    ⟨i, Prm.of_lw h.2.1 fun d hd => l d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
      k.ebx.trans h.2.2.1, r⟩

/-- `start`'s hash of the header. -/
theorem stFix_ok {s : State}
    (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ s ∧ s.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) s.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64) [] ∧
      bytesAt s.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 768) 24 = Proof.Argon2.initialHeader (VG.Proof.Argon2.X86.Derive.prm s₀)) :
    WP isa (Impl.Argon2.X86.HPrime.absorbFixed 768 24) s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ t ∧
      t.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) t.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64) (Proof.Argon2.initialHeader (VG.Proof.Argon2.X86.Derive.prm s₀)) := by
  have hs := hp.scr_fits
  obtain ⟨i₄, pr₄, b₄, r₄, hd₄⟩ := h
  refine (HPrime.absorbFixed_ok (VG.Proof.Argon2.X86.Derive.ctx hp i₄ b₄) (offset := 768) (size := 24) (by omega) (by decide)
    (by decide) (VG.Proof.Argon2.X86.Derive.scr_cov hp i₄ (by decide)) (VG.Proof.Argon2.X86.Derive.stk_scr hp (by decide) (by decide)) r₄).mono fun s₅ ⟨r₅, k₅⟩ => ?_
  rw [hd₄] at r₅
  obtain ⟨i₅, l₅⟩ := i₄.keeps hp k₅
  exact ⟨i₅, Prm.of_lw pr₄ fun d hd => l₅ d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    k₅.ebx.trans b₄, r₅⟩

/-- `start`'s count of the header's bytes. -/
theorem stCnt_ok {s : State}
    (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ s ∧ s.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ ∧
      Repr b (Spec.Blake2.init b 64 0) s.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64) (Proof.Argon2.initialHeader (VG.Proof.Argon2.X86.Derive.prm s₀))) :
    WP isa (.block [.mov .eax (.imm 24), .store ⟨.ebp, countLoOff⟩ .eax, .mov .eax (.imm 0),
      .store ⟨.ebp, countHiOff⟩ .eax]) s (VG.Proof.Argon2.X86.Derive.HI s₀ (Proof.Argon2.initialHeader (VG.Proof.Argon2.X86.Derive.prm s₀))) := by
  obtain ⟨i₅, pr₄, b₅, r₅⟩ := h
  refine wp_movi fun s₆ u₆ => ?_
  have i₆ := i₅.upd u₆ (by decide) (by decide)
  refine VG.Proof.Argon2.X86.Derive.wp_stloc hp i₆ (d := countLoOff) (by decide) fun s₇ i₇ v₇ o₇ g₇ m₇ => ?_
  refine wp_movi fun s₈ u₈ => ?_
  have i₈ := i₇.upd u₈ (by decide) (by decide)
  refine VG.Proof.Argon2.X86.Derive.wp_stloc hp i₈ (d := countHiOff) (by decide) fun t it vt ot gt mt => WP.block_nil ?_
  have L : ∀ d, d + 4 ≤ 144 → (d + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ d) → VG.Proof.Argon2.X86.Derive.lw s₀ t d = VG.Proof.Argon2.X86.Derive.lw s₀ s d :=
    fun d hd hd' => by
      rw [ot d (by omega) (by simp only [countHiOff, countLoOff] at hd' ⊢; omega), VG.Proof.Argon2.X86.Derive.lw_mem u₈.mem,
        o₇ d (by omega) (by simp only [countHiOff, countLoOff] at hd' ⊢; omega), VG.Proof.Argon2.X86.Derive.lw_mem u₆.mem]
  refine ⟨it, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [L _ (by decide) (by decide)]; exact pr₄.divisor
  · rw [L _ (by decide) (by decide)]; exact pr₄.segLen
  · rw [L _ (by decide) (by decide)]; exact pr₄.laneLen
  · rw [L _ (by decide) (by decide)]; exact pr₄.stride
  · rw [gt, u₈.other _ (by decide), g₇, u₆.other _ (by decide), b₅]
  · rw [mt, u₈.mem, m₇, u₆.mem]
    exact VG.Proof.Argon2.X86.Derive.repr_loc hp (by decide) _ (VG.Proof.Argon2.X86.Derive.repr_loc hp (by decide) _ r₅)
  · rw [ot _ (by decide) (by decide), VG.Proof.Argon2.X86.Derive.lw_mem u₈.mem, v₇, u₆.gpr, Proof.Argon2.initialHeader_length]; rfl
  · rw [vt, u₈.gpr, Proof.Argon2.initialHeader_length]; rfl
  · rw [Proof.Argon2.initialHeader_length]; decide

theorem start_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.X86.Derive.Prm s₀ s) :
    WP isa Impl.Argon2.X86.Derive.start s (VG.Proof.Argon2.X86.Derive.HI s₀ (Proof.Argon2.initialHeader (VG.Proof.Argon2.X86.Derive.prm s₀))) := by
  unfold Impl.Argon2.X86.Derive.start
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.stA_ok hp h pr).mono fun s₂ h₂ => WP.seq ((VG.Proof.Argon2.X86.Derive.stInit_ok hp h₂).mono fun s₃ ⟨i₃, pr₃, b₃, r₃⟩ =>
    WP.seq ((VG.Proof.Argon2.X86.Derive.header_ok hp i₃ pr₃ b₃ r₃).mono fun s₄ ⟨i₄, pr₄, b₄, r₄, hd₄, _⟩ =>
      WP.seq ((VG.Proof.Argon2.X86.Derive.stFix_ok hp ⟨i₄, pr₄, b₄, r₄, hd₄⟩).mono fun s₅ h₅ => VG.Proof.Argon2.X86.Derive.stCnt_ok hp h₅))))

end

/-- `add d, src`, for a source of known value, and the carry. -/
theorem wp_addC {s : State} {d : Reg} {src : Src} {v : BitVec 32} (hv : readSrc s src = some v)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (s.gpr d + v) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d src :: is)) s Q :=
  VG.X86.Wp.cons (by simp [exec, execAlu, hv]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `adc d, 0`, with a known carry. -/
theorem wp_adc0 {s : State} {d : Reg} {c : Bool} (hc : s.cf = some c) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (s.gpr d + 0 + (BitVec.ofBool c).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .adc d (.imm 0) :: is)) s Q :=
  VG.X86.Wp.cons (by simp [exec, execAlu, readSrc, hc]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

/-- `addCount`: the 64-bit count in the locals, `c`, plus `x`. -/
theorem count_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {c x : Nat} (hx : x < 2 ^ 32)
    (lo : VG.Proof.Argon2.X86.Derive.lw s₀ s countLoOff = BitVec.ofNat 32 c) (hi : VG.Proof.Argon2.X86.Derive.lw s₀ s countHiOff = BitVec.ofNat 32 (c / 2 ^ 32))
    {src : Src} (hsrc : ∀ t, VG.Proof.Argon2.X86.Derive.Inv s₀ t → t.mem = s.mem → readSrc t src = some (BitVec.ofNat 32 x))
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.X86.Derive.Inv s₀ t → VG.Proof.Argon2.X86.Derive.lw s₀ t countLoOff = BitVec.ofNat 32 (c + x) →
      VG.Proof.Argon2.X86.Derive.lw s₀ t countHiOff = BitVec.ofNat 32 ((c + x) / 2 ^ 32) →
      (∀ e, e + 4 ≤ 236 → (e + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ e) → VG.Proof.Argon2.X86.Derive.lw s₀ t e = VG.Proof.Argon2.X86.Derive.lw s₀ s e) →
      (∀ r, r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r) →
      t.mem = (s.mem.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) countLoOff) (BitVec.ofNat 32 (c + x))).writeW
        (addr (VG.Proof.Argon2.X86.Derive.E s₀) countHiOff) (BitVec.ofNat 32 ((c + x) / 2 ^ 32)) →
      t.gpr .ecx = BitVec.ofNat 32 (c + x) → t.gpr .edx = BitVec.ofNat 32 ((c + x) / 2 ^ 32) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.addCount src ++ is)) s Q := by
  simp only [Impl.Argon2.X86.Derive.addCount, Impl.Argon2.X86.Derive.fr, List.cons_append, List.nil_append]
  refine VG.Proof.Argon2.X86.Derive.wp_ldloc hp h (d := countLoOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide) (by decide)
  refine VG.Proof.Argon2.X86.Derive.wp_ldloc hp i₁ (d := countHiOff) (by decide) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine VG.Proof.Argon2.X86.Derive.wp_addC (hsrc s₂ i₂ m₂) fun s₃ u₃ c₃ => ?_
  have i₃ := i₂.upd u₃ (by decide) (by decide)
  refine VG.Proof.Argon2.X86.Derive.wp_adc0 c₃ fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide) (by decide)
  have e₁ : s₂.gpr .ecx = BitVec.ofNat 32 c := by rw [u₂.other _ (by decide), u₁.gpr, lo]
  have vlo : s₄.gpr .ecx = BitVec.ofNat 32 (c + x) := by
    rw [u₄.other _ (by decide), u₃.gpr, e₁, BitVec.ofNat_add]
  have vhi : s₄.gpr .edx = BitVec.ofNat 32 ((c + x) / 2 ^ 32) := by
    have z : ∀ y : BitVec 32, y + 0 = y := fun y => by simp
    rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, VG.Proof.Argon2.X86.Derive.lw_mem u₁.mem, hi, e₁, z]
    exact Proof.Blake2.X86.Stream.carry_ofNat c x hx
  refine VG.Proof.Argon2.X86.Derive.wp_stloc hp i₄ (d := countLoOff) (by decide) fun s₅ i₅ v₅ o₅ g₅ m₅ => ?_
  refine VG.Proof.Argon2.X86.Derive.wp_stloc hp i₅ (d := countHiOff) (by decide) fun t it vt ot gt mt => k t it ?_ ?_ ?_ ?_ ?_
    (by rw [gt, g₅, vlo]) (by rw [gt, g₅, vhi])
  · rw [ot _ (by decide) (by decide), v₅, vlo]
  · rw [vt, g₅, vhi]
  · intro e he hd
    rw [ot e he (by simp only [countHiOff, countLoOff] at hd ⊢; omega),
      o₅ e he (by simp only [countHiOff, countLoOff] at hd ⊢; omega), VG.Proof.Argon2.X86.Derive.lw_mem u₄.mem, VG.Proof.Argon2.X86.Derive.lw_mem u₃.mem,
      VG.Proof.Argon2.X86.Derive.lw_mem m₂]
  · intro r h1 h2
    rw [gt, g₅, u₄.other _ h2, u₃.other _ h1, u₂.other _ h2, u₁.other _ h1]
  · rw [mt, m₅, g₅, vhi, vlo, u₄.mem, u₃.mem, m₂]

end

theorem count64 {n : Nat} (h : n < 2 ^ 64) :
    BitVec.ofNat 32 (n / 2 ^ 32) ++ BitVec.ofNat 32 n = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (by rw [Proof.Blake2.X86.Stream.append_ofNat h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h])

/-- H₀'s streaming state at `scratch`, with `data` absorbed and the count `c` in
the locals. -/
structure HC (s₀ : State) (data : List Byte) (c : Nat) (s : State) : Prop where
  inv : VG.Proof.Argon2.X86.Derive.Inv s₀ s
  prm : VG.Proof.Argon2.X86.Derive.Prm s₀ s
  ebx : s.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀
  repr : Repr b (Spec.Blake2.init b 64 0) s.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64) data
  lo : VG.Proof.Argon2.X86.Derive.lw s₀ s countLoOff = BitVec.ofNat 32 c
  hi : VG.Proof.Argon2.X86.Derive.lw s₀ s countHiOff = BitVec.ofNat 32 (c / 2 ^ 32)

theorem HI.hc {s₀ s : State} {data : List Byte} (h : VG.Proof.Argon2.X86.Derive.HI s₀ data s) : VG.Proof.Argon2.X86.Derive.HC s₀ data data.length s :=
  ⟨h.inv, h.prm, h.ebx, h.repr, h.lo, h.hi⟩

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

/-- `absorb`'s first block: LE32 of the length at `scratch + 792`, and `update`'s arguments. -/
theorem absA_ok {len : Nat} (hlen : len < 18) {data : List Byte} {c : Nat} {s : State} (h : VG.Proof.Argon2.X86.Derive.HC s₀ data c s) :
    WP isa (.block [.mov .eax (Impl.Argon2.X86.Derive.fr (argOff len)), .store ⟨.ebx, 792⟩ .eax,
      .mov .ecx (Impl.Argon2.X86.Derive.fr countLoOff), .mov .edx (Impl.Argon2.X86.Derive.fr countHiOff),
      .mov .esi (.reg .ebx), .alu .add .esi (.imm 792), .mov .edi (.imm 4)]) s fun t =>
      VG.Proof.Argon2.X86.Derive.HC s₀ data c t ∧ t.gpr .esi = VG.Proof.Argon2.X86.Derive.scrP s₀ + 792 ∧ (t.gpr .edi).toNat = 4 ∧ t.gpr .ecx = BitVec.ofNat 32 c ∧
      t.gpr .edx = BitVec.ofNat 32 (c / 2 ^ 32) ∧
      bytesAt t.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀ + 792).setWidth 64) 4 = Spec.Argon2.le32 (VG.X86.arg s₀ len).toNat := by
  have hs := hp.scr_fits
  simp only [Impl.Argon2.X86.Derive.fr]
  refine VG.Proof.Argon2.X86.Derive.wp_ldarg hp h.inv (i := len) hlen fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide) (by decide)
  have b₁ : s₁.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ := by rw [u₁.other _ (by decide), h.ebx]
  refine VG.Proof.Argon2.X86.Derive.wp_stscr hp i₁ b₁ (o := 792) (by decide) fun s₂ i₂ m₂ g₂ l₂ f₂ => ?_
  refine VG.Proof.Argon2.X86.Derive.wp_ldloc hp i₂ (d := countLoOff) (by decide) fun s₃ u₃ => ?_
  refine VG.Proof.Argon2.X86.Derive.wp_ldloc hp (i₂.upd u₃ (by decide) (by decide)) (d := countHiOff) (by decide) fun s₄ u₄ => ?_
  refine wp_mov fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_movi fun s₇ u₇ => WP.block_nil ?_
  have i₇ := ((((i₂.upd u₃ (by decide) (by decide)).upd u₄ (by decide) (by decide)).upd u₅ (by decide)
    (by decide)).upd u₆ (by decide) (by decide)).upd u₇ (by decide) (by decide)
  have m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have L₂ : ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.X86.Derive.lw s₀ s₂ d = VG.Proof.Argon2.X86.Derive.lw s₀ s d := fun d hd => by rw [l₂ d hd, VG.Proof.Argon2.X86.Derive.lw_mem u₁.mem]
  have L₇ : ∀ d, d + 4 ≤ 144 → VG.Proof.Argon2.X86.Derive.lw s₀ s₇ d = VG.Proof.Argon2.X86.Derive.lw s₀ s d := fun d hd => by rw [VG.Proof.Argon2.X86.Derive.lw_mem m₇, L₂ d hd]
  have e792 : (VG.Proof.Argon2.X86.Derive.scrP s₀ + 792).setWidth 64 = (VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 792 :=
    HPrime.setWidth_add (d := 792) (by omega)
  refine ⟨⟨i₇, Prm.of_lw h.prm fun d hd => L₇ d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), g₂, b₁],
    by rw [m₇]; exact VG.Proof.Argon2.X86.Derive.repr_store (by decide) (by decide) f₂ (by rw [u₁.mem]; exact h.repr),
    by rw [L₇ _ (by decide)]; exact h.lo, by rw [L₇ _ (by decide)]; exact h.hi⟩, ?_, by rw [u₇.gpr]; rfl, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, b₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, L₂ _ (by decide), h.lo]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, VG.Proof.Argon2.X86.Derive.lw_mem u₃.mem,
      L₂ _ (by decide), h.hi]
  · rw [e792, show (4 : Nat) = 4 + 0 from rfl, VG.Proof.Argon2.X86.Derive.bytes_word, ← VG.Proof.Argon2.X86.Derive.scr_addr hp (by decide), m₇, m₂,
      Mem.readW_writeW_self32, u₁.gpr, VG.Proof.Argon2.X86.Derive.le32_arg]
    rfl

/-- `absorb`'s first `update`: LE32 of the length. -/
theorem absU1_ok {len : Nat} {data : List Byte} {c : Nat} {s : State} (h : VG.Proof.Argon2.X86.Derive.HC s₀ data c s)
    (hd : data.length = c) (hc : c + 4 < 2 ^ 36) (esi : s.gpr .esi = VG.Proof.Argon2.X86.Derive.scrP s₀ + 792) (edi : (s.gpr .edi).toNat = 4)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 c) (edx : s.gpr .edx = BitVec.ofNat 32 (c / 2 ^ 32))
    (w : bytesAt s.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀ + 792).setWidth 64) 4 = Spec.Argon2.le32 (VG.X86.arg s₀ len).toNat) :
    WP isa Impl.Argon2.X86.HPrime.update s (VG.Proof.Argon2.X86.Derive.HC s₀ (data ++ Spec.Argon2.le32 (VG.X86.arg s₀ len).toNat) c) := by
  have hs := hp.scr_fits
  have e792 : (VG.Proof.Argon2.X86.Derive.scrP s₀ + 792).setWidth 64 = (VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + BitVec.ofNat 64 792 :=
    HPrime.setWidth_add (d := 792) (by omega)
  refine (VG.Proof.Argon2.X86.Derive.update_k (VG.Proof.Argon2.X86.Derive.ctx hp h.inv h.ebx) (D := VG.Proof.Argon2.X86.Derive.scrP s₀ + 792) (L := 4) esi edi
    (by have : (VG.Proof.Argon2.X86.Derive.scrP s₀ + 792).toNat = (VG.Proof.Argon2.X86.Derive.scrP s₀).toNat + 792 := VG.Proof.Argon2.X86.Derive.add_nat (k := 792) (by omega)
        omega)
    (by rw [e792]; exact Covers.right (VG.Proof.Argon2.X86.Derive.scr_cov hp h.inv (by decide)))
    (by rw [e792]; exact Offset.disjoint_base _ (by decide) (by decide))
    (by rw [e792]; exact VG.Proof.Argon2.X86.Derive.stk_scr hp (by decide) (by decide)) h.repr
    (by rw [edx, ecx, hd]; exact VG.Proof.Argon2.X86.Derive.count64 (by omega)) (by omega)).mono fun t ⟨r, k⟩ => ?_
  obtain ⟨i, l⟩ := h.inv.keeps hp k
  rw [w] at r
  exact ⟨i, Prm.of_lw h.prm fun d hd => l d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    k.ebx.trans h.ebx, r, by rw [l _ (by decide)]; exact h.lo, by rw [l _ (by decide)]; exact h.hi⟩

/-- `absorb`'s second block: the count advanced by 4, and `update`'s arguments. -/
theorem absB_ok {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18) {data : List Byte} {c : Nat} {s : State}
    (h : VG.Proof.Argon2.X86.Derive.HC s₀ data c s) :
    WP isa (.block (Impl.Argon2.X86.Derive.addCount (.imm 4) ++
      ([.mov .esi (Impl.Argon2.X86.Derive.fr (argOff ptr)), .mov .edi (Impl.Argon2.X86.Derive.fr (argOff len))] :
        List Instr)))
      s fun t => VG.Proof.Argon2.X86.Derive.HC s₀ data (c + 4) t ∧ t.gpr .esi = VG.X86.arg s₀ ptr ∧ (t.gpr .edi).toNat = (VG.X86.arg s₀ len).toNat ∧
        t.gpr .ecx = BitVec.ofNat 32 (c + 4) ∧ t.gpr .edx = BitVec.ofNat 32 ((c + 4) / 2 ^ 32) := by
  refine VG.Proof.Argon2.X86.Derive.count_ok hp h.inv (x := 4) (by decide) h.lo h.hi (fun _ _ _ => rfl)
    fun s₉ i₉ lo₉ hi₉ o₉ g₉ m₉ c₉ d₉ => VG.Proof.Argon2.X86.Derive.wp_ldarg hp i₉ (i := ptr) hptr fun s₁₀ u₁₀ =>
      VG.Proof.Argon2.X86.Derive.wp_ldarg hp (i₉.upd u₁₀ (by decide) (by decide)) (i := len) hlen fun s₁₁ u₁₁ => WP.block_nil ?_
  have i₁₁ := (i₉.upd u₁₀ (by decide) (by decide)).upd u₁₁ (by decide) (by decide)
  have m₁₁ : s₁₁.mem = s₉.mem := by rw [u₁₁.mem, u₁₀.mem]
  refine ⟨⟨i₁₁, Prm.of_lw h.prm fun d hd => ?_, ?_, ?_, by rw [VG.Proof.Argon2.X86.Derive.lw_mem m₁₁]; exact lo₉, by rw [VG.Proof.Argon2.X86.Derive.lw_mem m₁₁]; exact hi₉⟩,
    by rw [u₁₁.other _ (by decide), u₁₀.gpr], by rw [u₁₁.gpr],
    by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), c₉],
    by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), d₉]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    have hd' : d + 4 ≤ 144 ∧ (d + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ d) := by
      rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [VG.Proof.Argon2.X86.Derive.lw_mem m₁₁, o₉ d (by omega) hd'.2]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), g₉ _ (by decide) (by decide), h.ebx]
  · rw [m₁₁, m₉]; exact VG.Proof.Argon2.X86.Derive.repr_loc hp (by decide) _ (VG.Proof.Argon2.X86.Derive.repr_loc hp (by decide) _ h.repr)

/-- `absorb`'s second `update`: the input. -/
theorem absU2_ok {ptr len : Nat}
    (hR : (⟨(VG.X86.arg s₀ ptr).setWidth 64, (VG.X86.arg s₀ len).toNat⟩ : Region) ∈ [VG.Proof.Argon2.X86.Derive.pwR s₀, VG.Proof.Argon2.X86.Derive.saltR s₀, VG.Proof.Argon2.X86.Derive.secR s₀, VG.Proof.Argon2.X86.Derive.adR s₀])
    (hfit : (VG.X86.arg s₀ ptr).toNat + (VG.X86.arg s₀ len).toNat ≤ 2 ^ 32) {data : List Byte} {c : Nat} {s : State}
    (h : VG.Proof.Argon2.X86.Derive.HC s₀ data c s) (hd : data.length = c) (hc : c + 2 ^ 32 < 2 ^ 36) (esi : s.gpr .esi = VG.X86.arg s₀ ptr)
    (edi : (s.gpr .edi).toNat = (VG.X86.arg s₀ len).toNat) (ecx : s.gpr .ecx = BitVec.ofNat 32 c)
    (edx : s.gpr .edx = BitVec.ofNat 32 (c / 2 ^ 32)) :
    WP isa Impl.Argon2.X86.HPrime.update s
      (VG.Proof.Argon2.X86.Derive.HC s₀ (data ++ bytesAt s₀.mem ((VG.X86.arg s₀ ptr).setWidth 64) (VG.X86.arg s₀ len).toNat) c) := by
  have hlt := (VG.X86.arg s₀ len).isLt
  have hR' : (⟨(VG.X86.arg s₀ ptr).setWidth 64, (VG.X86.arg s₀ len).toNat⟩ : Region) ∈
      [VG.Proof.Argon2.X86.Derive.pwR s₀, VG.Proof.Argon2.X86.Derive.saltR s₀, VG.Proof.Argon2.X86.Derive.secR s₀, VG.Proof.Argon2.X86.Derive.adR s₀, VG.Proof.Argon2.X86.Derive.argR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h | h <;> simp [h]
  have hS : (⟨(VG.X86.arg s₀ ptr).setWidth 64, (VG.X86.arg s₀ len).toNat⟩ : Region) ∈
      [VG.Proof.Argon2.X86.Derive.pwR s₀, VG.Proof.Argon2.X86.Derive.saltR s₀, VG.Proof.Argon2.X86.Derive.secR s₀, VG.Proof.Argon2.X86.Derive.adR s₀, VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h | h <;> simp [h]
  have rin := hp.ro_w _ hR' (VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)
  refine (VG.Proof.Argon2.X86.Derive.update_k (VG.Proof.Argon2.X86.Derive.ctx hp h.inv h.ebx) (D := VG.X86.arg s₀ ptr) (L := (VG.X86.arg s₀ len).toNat) esi edi hfit
    (by rw [h.inv.rd, hp.rd]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_append_left _ hR', 0, by simp, by simp⟩)
    (rin.sub_right (Region.sub_prefix (by decide)))
    ((hp.stk_all _ hS).sub_left fun a ha => VG.Proof.Argon2.X86.Derive.call_stk hp a (VG.Proof.Argon2.X86.Derive.below60_call hp a ha))
    h.repr (by rw [edx, ecx, hd]; exact VG.Proof.Argon2.X86.Derive.count64 (by omega)) (by omega)).mono fun t ⟨r, k⟩ => ?_
  obtain ⟨i, l⟩ := h.inv.keeps hp k
  have inp : bytesAt s.mem ((VG.X86.arg s₀ ptr).setWidth 64) (VG.X86.arg s₀ len).toNat =
      bytesAt s₀.mem ((VG.X86.arg s₀ ptr).setWidth 64) (VG.X86.arg s₀ len).toNat :=
    h.inv.input hp (R := ⟨(VG.X86.arg s₀ ptr).setWidth 64, (VG.X86.arg s₀ len).toNat⟩) hR
  rw [inp] at r
  exact ⟨i, Prm.of_lw h.prm fun d hd => l d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    k.ebx.trans h.ebx, r, by rw [l _ (by decide)]; exact h.lo, by rw [l _ (by decide)]; exact h.hi⟩

/-- `absorb`'s last block: the count advanced by the input's length. -/
theorem absC_ok {len : Nat} (hlen : len < 18) {data : List Byte} {c : Nat} {s : State} (h : VG.Proof.Argon2.X86.Derive.HC s₀ data c s) :
    WP isa (.block (Impl.Argon2.X86.Derive.addCount (Impl.Argon2.X86.Derive.fr (argOff len)))) s
      (VG.Proof.Argon2.X86.Derive.HC s₀ data (c + (VG.X86.arg s₀ len).toNat)) := by
  rw [← List.append_nil (Impl.Argon2.X86.Derive.addCount _)]
  refine VG.Proof.Argon2.X86.Derive.count_ok hp h.inv (x := (VG.X86.arg s₀ len).toNat) (VG.X86.arg s₀ len).isLt h.lo h.hi
    (fun t it mt => by
      show readSrc t (.mem ⟨.ebp, argOff len⟩) = _
      rw [VG.X86.Wp.readSrc_mem it.ebp (it.arg_in hp hlen), it.arg hp hlen, BitVec.ofNat_toNat,
        BitVec.setWidth_eq])
    fun t it lo hi o g mt _ _ => WP.block_nil ⟨it, Prm.of_lw h.prm fun d hd => ?_, ?_, ?_, lo, hi⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    have hd' : d + 4 ≤ 144 ∧ (d + 4 ≤ countLoOff ∨ countHiOff + 4 ≤ d) := by
      rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [o d (by omega) hd'.2]
  · rw [g _ (by decide) (by decide), h.ebx]
  · rw [mt]; exact VG.Proof.Argon2.X86.Derive.repr_loc hp (by decide) _ (VG.Proof.Argon2.X86.Derive.repr_loc hp (by decide) _ h.repr)

theorem absorb_ok {ptr len : Nat} (hptr : ptr < 18) (hlen : len < 18)
    (hR : (⟨(VG.X86.arg s₀ ptr).setWidth 64, (VG.X86.arg s₀ len).toNat⟩ : Region) ∈ [VG.Proof.Argon2.X86.Derive.pwR s₀, VG.Proof.Argon2.X86.Derive.saltR s₀, VG.Proof.Argon2.X86.Derive.secR s₀, VG.Proof.Argon2.X86.Derive.adR s₀])
    (hfit : (VG.X86.arg s₀ ptr).toNat + (VG.X86.arg s₀ len).toNat ≤ 2 ^ 32) {data : List Byte}
    (hd : data.length + 4 + 2 ^ 32 < 2 ^ 36) {s : State} (h : VG.Proof.Argon2.X86.Derive.HI s₀ data s) :
    WP isa (Impl.Argon2.X86.Derive.absorb ptr len) s
      (VG.Proof.Argon2.X86.Derive.HI s₀ (Proof.Argon2.appendInput data (bytesAt s₀.mem ((VG.X86.arg s₀ ptr).setWidth 64) (VG.X86.arg s₀ len).toNat))) := by
  have hlt := (VG.X86.arg s₀ len).isLt
  unfold Impl.Argon2.X86.Derive.absorb
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.absA_ok hp hlen h.hc).mono fun s₁ ⟨h₁, e₁, d₁, c₁, x₁, w₁⟩ => ?_)
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.absU1_ok hp h₁ rfl (by omega) e₁ d₁ c₁ x₁ w₁).mono fun s₂ h₂ => ?_)
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.absB_ok hp hptr hlen h₂).mono fun s₃ ⟨h₃, e₃, d₃, c₃, x₃⟩ => ?_)
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.absU2_ok hp hR hfit h₃ (by simp [Proof.Argon2.le32_length]) (by omega) e₃ d₃ c₃ x₃).mono
    fun s₄ h₄ => ?_)
  refine (VG.Proof.Argon2.X86.Derive.absC_ok hp hlen h₄).mono fun t ht => ?_
  have hd' : Proof.Argon2.appendInput data (bytesAt s₀.mem ((VG.X86.arg s₀ ptr).setWidth 64) (VG.X86.arg s₀ len).toNat) =
      data ++ Spec.Argon2.le32 (VG.X86.arg s₀ len).toNat ++
        bytesAt s₀.mem ((VG.X86.arg s₀ ptr).setWidth 64) (VG.X86.arg s₀ len).toNat := by
    simp only [Proof.Argon2.appendInput, bytesAt, List.length_map, List.length_range]
  have hl : (Proof.Argon2.appendInput data (bytesAt s₀.mem ((VG.X86.arg s₀ ptr).setWidth 64) (VG.X86.arg s₀ len).toNat)).length =
      data.length + 4 + (VG.X86.arg s₀ len).toNat := by
    rw [Proof.Argon2.appendInput_length]; simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨ht.inv, ht.prm, ht.ebx, by rw [hd']; exact ht.repr, by rw [hl]; exact ht.lo, by rw [hl]; exact ht.hi,
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
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

/-- A store to the locals keeps `scratch`. -/
theorem scr_loc {m : Mem} {d o : Nat} (hd : d + 4 ≤ 144) (ho : o + 4 ≤ 16384) (v : BitVec 32) :
    (m.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) v).readW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) o) 32 = m.readW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) o) 32 := by
  refine ((Frame.refl [⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) d, 4⟩] m).writeW (List.mem_singleton_self _) v
    (Region.contains_self _ _)).readW (r := ⟨addr (VG.Proof.Argon2.X86.Derive.scrP s₀) o, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rw [VG.Proof.Argon2.X86.Derive.scr_addr hp (by omega)]
  exact ((VG.Proof.Argon2.X86.Derive.loc_disj hp hd (VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).symm.sub_left (VG.Proof.Argon2.X86.Derive.scr_sub ho))

/-- The first `k` words of the digest, copied to the locals. -/
theorem copy_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (hb : s.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀) :
    ∀ k ≤ 16, WP isa (.block ((List.range k).flatMap Impl.Argon2.X86.Derive.copyWord)) s fun t =>
      VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ t.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ ∧
      (∀ j < k, VG.Proof.Argon2.X86.Derive.lw s₀ t (4 * j) = s.mem.readW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) (768 + 4 * j)) 32) ∧
      (∀ o, o + 4 ≤ 16384 → t.mem.readW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) o) 32 = s.mem.readW (addr (VG.Proof.Argon2.X86.Derive.scrP s₀) o) 32) ∧
      (∀ e, e + 4 ≤ 236 → 4 * k ≤ e → VG.Proof.Argon2.X86.Derive.lw s₀ t e = VG.Proof.Argon2.X86.Derive.lw s₀ s e)
  | 0, _ => WP.block_nil ⟨h, hb, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, fun _ _ _ => rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((VG.Proof.Argon2.X86.Derive.copy_ok h hb k (by omega)).mono fun t ⟨it, bt, wt, st, lt⟩ => ?_)
    simp only [Impl.Argon2.X86.Derive.copyWord]
    refine VG.X86.Wp.wp_ldm bt (by
        rw [it.rd, it.wr]
        exact ⟨VG.Proof.Argon2.X86.Derive.scrR s₀, List.mem_append_right _ (VG.Proof.Argon2.X86.Derive.scr_mem hp), by
          rw [VG.Proof.Argon2.X86.Derive.scr_addr hp (by omega)]; exact Offset.contains_base _ (by omega) (by omega)⟩)
      fun t₁ u₁ => ?_
    have i₁ := it.upd u₁ (by decide) (by decide)
    refine VG.Proof.Argon2.X86.Derive.wp_stloc hp i₁ (d := 4 * k) (by omega) fun t₂ i₂ v₂ o₂ g₂ m₂ => WP.block_nil
      ⟨i₂, by rw [g₂, u₁.other _ (by decide), bt], fun j hj => ?_, fun o ho => ?_, fun e he hke => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [o₂ _ (by omega) (by omega), VG.Proof.Argon2.X86.Derive.lw_mem u₁.mem]; exact wt j hj
      · rw [v₂, u₁.gpr, st _ (by omega)]
    · rw [m₂, VG.Proof.Argon2.X86.Derive.scr_loc hp (by omega) ho, u₁.mem]; exact st o ho
    · rw [o₂ _ he (by omega), VG.Proof.Argon2.X86.Derive.lw_mem u₁.mem]; exact lt e he (by omega)

end

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

/-- `finish`'s first block: the count, for `finalize`. -/
theorem fiA_ok {data : List Byte} {s : State} (h : VG.Proof.Argon2.X86.Derive.HI s₀ data s) :
    WP isa (.block [.mov .ecx (Impl.Argon2.X86.Derive.fr countLoOff),
      .mov .edx (Impl.Argon2.X86.Derive.fr countHiOff)]) s fun t => VG.Proof.Argon2.X86.Derive.HI s₀ data t ∧
      t.gpr .ecx = BitVec.ofNat 32 data.length ∧ t.gpr .edx = BitVec.ofNat 32 (data.length / 2 ^ 32) := by
  simp only [Impl.Argon2.X86.Derive.fr]
  refine VG.Proof.Argon2.X86.Derive.wp_ldloc hp h.inv (d := countLoOff) (by decide) fun s₁ u₁ =>
    VG.Proof.Argon2.X86.Derive.wp_ldloc hp (h.inv.upd u₁ (by decide) (by decide)) (d := countHiOff) (by decide) fun s₂ u₂ =>
      WP.block_nil ?_
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨⟨(h.inv.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide), Prm.of_lw h.prm fun d _ => VG.Proof.Argon2.X86.Derive.lw_mem m₂ d,
    by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ebx], by rw [m₂]; exact h.repr,
    by rw [VG.Proof.Argon2.X86.Derive.lw_mem m₂]; exact h.lo, by rw [VG.Proof.Argon2.X86.Derive.lw_mem m₂]; exact h.hi, h.len⟩,
    by rw [u₂.other _ (by decide), u₁.gpr, h.lo], by rw [u₂.gpr, VG.Proof.Argon2.X86.Derive.lw_mem u₁.mem, h.hi]⟩

/-- `finish`'s `finalize`: the digest at `scratch + 768`. -/
theorem fiFin_ok {data : List Byte} {s : State} (h : VG.Proof.Argon2.X86.Derive.HI s₀ data s)
    (ecx : s.gpr .ecx = BitVec.ofNat 32 data.length) (edx : s.gpr .edx = BitVec.ofNat 32 (data.length / 2 ^ 32)) :
    WP isa Impl.Argon2.X86.HPrime.finalize s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ t ∧ t.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ ∧
      bytesAt t.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + 768) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) data := by
  have hn := h.len
  refine (VG.Proof.Argon2.X86.Derive.finalize_k (VG.Proof.Argon2.X86.Derive.ctx hp h.inv h.ebx) (h0 := Spec.Blake2.init b 64 0) h.repr
    (by rw [edx, ecx]; exact VG.Proof.Argon2.X86.Derive.count64 (by omega)) (by omega)).mono fun s₃ ⟨dg, k₃⟩ => ?_
  obtain ⟨i₃, l₃⟩ := h.inv.keeps hp k₃
  exact ⟨i₃, Prm.of_lw h.prm fun d hd => l₃ d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    k₃.ebx.trans h.ebx, dg⟩

/-- `finish`'s copy of the digest to the locals. -/
theorem fiCopy_ok {s : State} {dg : List Byte} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ s ∧ s.gpr .ebx = VG.Proof.Argon2.X86.Derive.scrP s₀ ∧
      bytesAt s.mem ((VG.Proof.Argon2.X86.Derive.scrP s₀).setWidth 64 + 768) 64 = dg) :
    WP isa (.block ((List.range 16).flatMap Impl.Argon2.X86.Derive.copyWord)) s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ t ∧
      bytesAt t.mem ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64) 64 = dg := by
  have hs := hp.scr_fits
  have hE := VG.Proof.Argon2.X86.Derive.E_hi hp
  obtain ⟨i₃, pr₃, b₃, dg₃⟩ := h
  refine (VG.Proof.Argon2.X86.Derive.copy_ok hp i₃ b₃ 16 (Nat.le_refl _)).mono fun t ⟨it, _, wt, _, lt⟩ =>
    ⟨it, Prm.of_lw pr₃ fun d hd => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    have hd' : 64 ≤ d ∧ d + 4 ≤ 144 := by
      rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [lt d (by omega) hd'.1]
  · rw [← dg₃]
    refine VG.Proof.Argon2.X86.Derive.bytes_of_words (k := 16) fun j hj => ?_
    have := wt j hj
    simp only [VG.Proof.Argon2.X86.Derive.lw] at this
    rw [addr_eq (by omega), addr_eq (by omega)] at this
    rw [this, BitVec.add_assoc, show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.ofNat_add_ofNat]

theorem finish_ok {data : List Byte} {s : State} (h : VG.Proof.Argon2.X86.Derive.HI s₀ data s) :
    WP isa Impl.Argon2.X86.Derive.finish s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ t ∧
      bytesAt t.mem ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64) 64 = Spec.Blake2.finalHash b (Spec.Blake2.init b 64 0) data := by
  unfold Impl.Argon2.X86.Derive.finish
  exact WP.seq ((VG.Proof.Argon2.X86.Derive.fiA_ok hp h).mono fun s₂ ⟨h₂, c₂, d₂⟩ => WP.seq ((VG.Proof.Argon2.X86.Derive.fiFin_ok hp h₂ c₂ d₂).mono
    fun s₃ h₃ => VG.Proof.Argon2.X86.Derive.fiCopy_ok hp h₃))

theorem code_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.X86.Derive.Prm s₀ s) :
    WP isa Impl.Argon2.X86.Derive.code s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ t ∧
      bytesAt t.mem ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64) 64 =
        Spec.Argon2.initialHash (VG.Proof.Argon2.X86.Derive.prm s₀) (VG.Proof.Argon2.X86.Derive.pwB s₀) (VG.Proof.Argon2.X86.Derive.saltB s₀) (VG.Proof.Argon2.X86.Derive.secB s₀) (VG.Proof.Argon2.X86.Derive.adB s₀) := by
  have l1 := (VG.X86.arg s₀ 2).isLt
  have l2 := (VG.X86.arg s₀ 4).isLt
  have l3 := (VG.X86.arg s₀ 10).isLt
  unfold Impl.Argon2.X86.Derive.code
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.start_ok hp h pr).mono fun s₁ h₁ => ?_)
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.absorb_ok hp (ptr := 1) (len := 2) (by decide) (by decide) (by simp) hp.pw_fits
    (by rw [Proof.Argon2.initialHeader_length]; omega) h₁).mono fun s₂ h₂ => ?_)
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.absorb_ok hp (ptr := 3) (len := 4) (by decide) (by decide) (by simp) hp.salt_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega) h₂).mono fun s₃ h₃ => ?_)
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.absorb_ok hp (ptr := 9) (len := 10) (by decide) (by decide) (by simp) hp.sec_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega) h₃).mono fun s₄ h₄ => ?_)
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.absorb_ok hp (ptr := 11) (len := 12) (by decide) (by decide) (by simp) hp.ad_fits
    (by simp only [Proof.Argon2.appendInput_length, Proof.Argon2.initialHeader_length, bytesAt,
      List.length_map, List.length_range]; omega) h₄).mono fun s₅ h₅ => ?_)
  refine (VG.Proof.Argon2.X86.Derive.finish_ok hp h₅).mono fun t ⟨it, pt, bt⟩ => ⟨it, pt, ?_⟩
  rw [bt, Proof.Argon2.initialHash_stream, List.take_of_length_le (by rw [HPrime.finalHash_length])]
  rfl

end

end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.HCall`. -/
section

/-!
# Argon2 on x86 (32-bit): calls of H′ in the derivation

The derivation calls `vg_argon2_hprime` in a frame of its five arguments,
`hprime(r, eax, edi, ecx, edx)` with `r` the input's pointer (`ebp` for the
first blocks of a lane, `esi` for the tag), from the body (`Inv`).
`hcall_ok` runs one: its input lies in the memory matrix or the locals, its
output in the memory matrix or `out`, and `scratch` is its working space. The
call writes only the output, `scratch` and the 84 bytes below the locals.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Blake2 (bytesAt)

theorem hPrime_nosp : NoSp Impl.Argon2.X86.HPrime.code := NoSp.of_all (by lit_decide)
theorem hPrime_stack : stackUse Impl.Argon2.X86.HPrime.code = 60 := by lit_decide

/-- The bytes of a region a frame's regions miss are kept. -/
theorem bytes_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hR : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n :=
  Proof.Blake2.bytesAt_congr fun _ hi => f.bytes (R := ⟨p, n⟩) hd hR hi

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

/-- A range of the 84 bytes below the locals. -/
theorem in_call {x : BitVec 32} {n : Nat} (h₁ : (VG.Proof.Argon2.X86.Derive.E s₀).toNat ≤ x.toNat + 84)
    (h₂ : x.toNat + n ≤ (VG.Proof.Argon2.X86.Derive.E s₀).toNat) : Region.Sub ⟨x.setWidth 64, n⟩ (VG.Proof.Argon2.X86.Derive.callR s₀) := by
  have hE := VG.Proof.Argon2.X86.Derive.E_nat hp
  have := hp.esp_lo
  exact VG.Proof.Argon2.X86.Derive.sub32 (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega) (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega)

theorem call_disj {R : Region} (hR : R ∈ [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀]) : (VG.Proof.Argon2.X86.Derive.callR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left (VG.Proof.Argon2.X86.Derive.call_stk hp)

theorem loc_call : (VG.Proof.Argon2.X86.Derive.locR s₀).Disjoint (VG.Proof.Argon2.X86.Derive.callR s₀) := by
  have hE := VG.Proof.Argon2.X86.Derive.E_nat hp
  have := hp.esp_lo
  have := VG.Proof.Argon2.X86.Derive.E_hi hp
  exact VG.Proof.Argon2.X86.Derive.disj32 (.inr (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega)) (by omega) (by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]; omega)

theorem loc_sub_stk : Region.Sub (VG.Proof.Argon2.X86.Derive.locR s₀) (VG.Proof.Argon2.X86.Derive.stkR s₀) := by
  simpa using VG.Proof.Argon2.X86.Derive.frame_stk hp (d := 0) (n := 144) (by decide)

theorem loc_disj' {R : Region} (hR : R ∈ [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀]) : (VG.Proof.Argon2.X86.Derive.locR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left (VG.Proof.Argon2.X86.Derive.loc_sub_stk hp)

/-- What H′ needs, from the body: `hprime(r, eax, edi, ecx, edx)`. -/
theorem hcall_pre {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {r : Reg} (hr : r ≠ .esp)
    (hdx : s.gpr .edx = VG.Proof.Argon2.X86.Derive.scrP s₀)
    (hin : ∃ R ∈ [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.locR s₀], ∃ off, (s.gpr r).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .eax).toNat ≤ R.len)
    (hinfit : (s.gpr r).toNat + (s.gpr .eax).toNat ≤ 2 ^ 32)
    (hout : ∃ R ∈ [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.outR s₀], ∃ off, (s.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .ecx).toNat ≤ R.len)
    (houtfit : (s.gpr .edi).toNat + (s.gpr .ecx).toNat ≤ 2 ^ 32)
    (hL : 1 ≤ (s.gpr .ecx).toNat) :
    CallPre HPrime.hPrimeX86 [.edx, .ecx, .edi, .eax, r]
      [⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩, ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩]
      [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩, VG.Proof.Argon2.X86.Derive.scrR s₀] s := by
  have hE := VG.Proof.Argon2.X86.Derive.E_nat hp
  have hlo := hp.esp_lo
  have hhi := VG.Proof.Argon2.X86.Derive.E_hi hp
  have hs := hp.scr_fits
  have esp := h.esp
  have nesp : Reg.esp ∉ [Reg.edx, .ecx, .edi, .eax, r] := by simp [Ne.symm hr]
  have fit : 4 * [Reg.edx, .ecx, .edi, .eax, r].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; rw [esp]; omega
  have a0 := callEntry_arg fit nesp (i := 0) (by simp)
  have a1 := callEntry_arg fit nesp (i := 1) (by simp)
  have a2 := callEntry_arg fit nesp (i := 2) (by simp)
  have a3 := callEntry_arg fit nesp (i := 3) (by simp)
  have a4 := callEntry_arg fit nesp (i := 4) (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceAdd, Nat.reduceSub] at a0 a1 a2 a3 a4
  rw [hdx] at a4
  -- The input and the output.
  obtain ⟨RI, hRI, oI, bI, lI⟩ := hin
  obtain ⟨RO, hRO, oO, bO, lO⟩ := hout
  have sI : Region.Sub ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ RI := by
    rw [bI]; exact Offset.sub_base _ lI
  have sO : Region.Sub ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ RO := by
    rw [bO]; exact Offset.sub_base _ lO
  have inW : RI ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact VG.Proof.Argon2.X86.Derive.mem_mem hp
    · exact VG.Proof.Argon2.X86.Derive.loc_mem s₀
  have outW : RO ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact VG.Proof.Argon2.X86.Derive.mem_mem hp
    · exact VG.Proof.Argon2.X86.Derive.out_mem hp
  have cI : Covers [⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RI, inW, oI, bI, lI⟩
  have cO : Covers [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RO, outW, oO, bO, lO⟩
  have scrW : VG.Proof.Argon2.X86.Derive.scrR s₀ ∈ s.wr := by rw [h.wr]; exact VG.Proof.Argon2.X86.Derive.scr_mem hp
  have I_scr : Region.Disjoint ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ (VG.Proof.Argon2.X86.Derive.scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact hp.mem_scr.sub_left sI
    · exact (VG.Proof.Argon2.X86.Derive.loc_disj' hp (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).sub_left sI
  have I_call : Region.Disjoint ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ (VG.Proof.Argon2.X86.Derive.callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact (VG.Proof.Argon2.X86.Derive.call_disj hp (R := VG.Proof.Argon2.X86.Derive.memR s₀) (by simp)).symm.sub_left sI
    · exact (VG.Proof.Argon2.X86.Derive.loc_call hp).sub_left sI
  have O_scr : Region.Disjoint ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ (VG.Proof.Argon2.X86.Derive.scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact hp.mem_scr.sub_left sO
    · exact hp.scr_out.symm.sub_left sO
  have O_call : Region.Disjoint ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ (VG.Proof.Argon2.X86.Derive.callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact (VG.Proof.Argon2.X86.Derive.call_disj hp (R := VG.Proof.Argon2.X86.Derive.memR s₀) (by simp)).symm.sub_left sO
    · exact (VG.Proof.Argon2.X86.Derive.call_disj hp (R := VG.Proof.Argon2.X86.Derive.outR s₀) (by simp)).symm.sub_left sO
  have S_call : (VG.Proof.Argon2.X86.Derive.scrR s₀).Disjoint (VG.Proof.Argon2.X86.Derive.callR s₀) := (VG.Proof.Argon2.X86.Derive.call_disj hp (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).symm
  -- The callee's stack, arguments and return address.
  have e20 : (s.gpr .esp - BitVec.ofNat 32 20).toNat = (VG.Proof.Argon2.X86.Derive.E s₀).toNat - 20 := by rw [esp, VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]
  have e24 : (s.gpr .esp - BitVec.ofNat 32 24).toNat = (VG.Proof.Argon2.X86.Derive.E s₀).toNat - 24 := by rw [esp, VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]
  have e84 : (s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 60).toNat = (VG.Proof.Argon2.X86.Derive.E s₀).toNat - 84 := by
    rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega), e24]; omega
  have cA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ (VG.Proof.Argon2.X86.Derive.callR s₀) :=
    VG.Proof.Argon2.X86.Derive.in_call hp (by omega) (by omega)
  have cR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 4⟩ (VG.Proof.Argon2.X86.Derive.callR s₀) :=
    VG.Proof.Argon2.X86.Derive.in_call hp (by omega) (by omega)
  have cS : Region.Sub (below (s.gpr .esp - BitVec.ofNat 32 24) 60) (VG.Proof.Argon2.X86.Derive.callR s₀) :=
    VG.Proof.Argon2.X86.Derive.in_call hp (by omega) (by omega)
  have a20 : argAddr (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry 0 =
      (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := callEntry_argAddr0 _ _
  have ce : (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 :=
    callEntry_esp' _ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.hPrimeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
      argAddr_withRegions, a0, a1, a2, a3, a4, a20, ce]
    refine ⟨trivial, trivial, I_scr, O_scr, ?_, ?_,
      ?_, ?_,
      I_call.symm.sub_left cS, O_call.symm.sub_left cS, S_call.symm.sub_left cS, hinfit, houtfit,
      by omega, by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by rw [esp]; omega), esp]; omega, by rw [VG.Proof.Argon2.X86.Derive.sub_nat (by rw [esp]; omega), esp]; omega,
      hL⟩
    · exact O_call.symm.sub_left cA
    · exact S_call.symm.sub_left cA
    · exact O_call.symm.sub_left cR
    · exact S_call.symm.sub_left cR
  · intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cI a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl (by simpa using hc))
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · exact InRegions_append_cons.mpr (.inr ⟨_, List.mem_append_right _ scrW, hc⟩)
  · intro a n ⟨q, hq, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩
    · exact ⟨_, List.mem_cons_of_mem _ scrW, hc⟩

/-- A call of H′ from the body: `hprime(r, eax, edi, ecx, edx)`. -/
theorem hcall_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {r : Reg} (hr : r ≠ .esp)
    (hdx : s.gpr .edx = VG.Proof.Argon2.X86.Derive.scrP s₀)
    (hin : ∃ R ∈ [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.locR s₀], ∃ off, (s.gpr r).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .eax).toNat ≤ R.len)
    (hinfit : (s.gpr r).toNat + (s.gpr .eax).toNat ≤ 2 ^ 32)
    (hout : ∃ R ∈ [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.outR s₀], ∃ off, (s.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .ecx).toNat ≤ R.len)
    (houtfit : (s.gpr .edi).toNat + (s.gpr .ecx).toNat ≤ 2 ^ 32)
    (hL : 1 ≤ (s.gpr .ecx).toNat) {Q : State → Prop}
    (k : ∀ t, VG.Proof.Argon2.X86.Derive.Inv s₀ t → (∀ q ∈ calleeSaved, t.gpr q = s.gpr q) →
      Frame [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.callR s₀] s.mem t.mem →
      bytesAt t.mem ((s.gpr .edi).setWidth 64) (s.gpr .ecx).toNat =
        Spec.Argon2.hPrime (s.gpr .ecx).toNat
          (bytesAt s.mem ((s.gpr r).setWidth 64) (s.gpr .eax).toNat) → Q t) :
    WP isa (.frame (.push [.edx, .ecx, .edi, .eax, r]) (.call Impl.Argon2.X86.Derive.hPrimeName
      Impl.Argon2.X86.HPrime.code) (.pop .eax 5)) s Q := by
  have hE := VG.Proof.Argon2.X86.Derive.E_nat hp
  have hlo := hp.esp_lo
  have hhi := VG.Proof.Argon2.X86.Derive.E_hi hp
  have hs := hp.scr_fits
  have esp := h.esp
  have nesp : Reg.esp ∉ [Reg.edx, .ecx, .edi, .eax, r] := by simp [Ne.symm hr]
  have fit : 4 * [Reg.edx, .ecx, .edi, .eax, r].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; rw [esp]; omega
  have a0 := callEntry_arg fit nesp (i := 0) (by simp)
  have a1 := callEntry_arg fit nesp (i := 1) (by simp)
  have a2 := callEntry_arg fit nesp (i := 2) (by simp)
  have a3 := callEntry_arg fit nesp (i := 3) (by simp)
  have a4 := callEntry_arg fit nesp (i := 4) (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceAdd, Nat.reduceSub] at a0 a1 a2 a3 a4
  rw [hdx] at a4
  -- The input and the output.
  obtain ⟨RI, hRI, oI, bI, lI⟩ := hin
  obtain ⟨RO, hRO, oO, bO, lO⟩ := hout
  have sI : Region.Sub ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ RI := by
    rw [bI]; exact Offset.sub_base _ lI
  have sO : Region.Sub ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ RO := by
    rw [bO]; exact Offset.sub_base _ lO
  have inW : RI ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact VG.Proof.Argon2.X86.Derive.mem_mem hp
    · exact VG.Proof.Argon2.X86.Derive.loc_mem s₀
  have outW : RO ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact VG.Proof.Argon2.X86.Derive.mem_mem hp
    · exact VG.Proof.Argon2.X86.Derive.out_mem hp
  have cI : Covers [⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RI, inW, oI, bI, lI⟩
  have cO : Covers [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RO, outW, oO, bO, lO⟩
  have scrW : VG.Proof.Argon2.X86.Derive.scrR s₀ ∈ s.wr := by rw [h.wr]; exact VG.Proof.Argon2.X86.Derive.scr_mem hp
  have I_scr : Region.Disjoint ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ (VG.Proof.Argon2.X86.Derive.scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact hp.mem_scr.sub_left sI
    · exact (VG.Proof.Argon2.X86.Derive.loc_disj' hp (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).sub_left sI
  have I_call : Region.Disjoint ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ (VG.Proof.Argon2.X86.Derive.callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact (VG.Proof.Argon2.X86.Derive.call_disj hp (R := VG.Proof.Argon2.X86.Derive.memR s₀) (by simp)).symm.sub_left sI
    · exact (VG.Proof.Argon2.X86.Derive.loc_call hp).sub_left sI
  have O_scr : Region.Disjoint ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ (VG.Proof.Argon2.X86.Derive.scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact hp.mem_scr.sub_left sO
    · exact hp.scr_out.symm.sub_left sO
  have O_call : Region.Disjoint ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ (VG.Proof.Argon2.X86.Derive.callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact (VG.Proof.Argon2.X86.Derive.call_disj hp (R := VG.Proof.Argon2.X86.Derive.memR s₀) (by simp)).symm.sub_left sO
    · exact (VG.Proof.Argon2.X86.Derive.call_disj hp (R := VG.Proof.Argon2.X86.Derive.outR s₀) (by simp)).symm.sub_left sO
  have S_call : (VG.Proof.Argon2.X86.Derive.scrR s₀).Disjoint (VG.Proof.Argon2.X86.Derive.callR s₀) := (VG.Proof.Argon2.X86.Derive.call_disj hp (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).symm
  -- The callee's stack, arguments and return address.
  have e20 : (s.gpr .esp - BitVec.ofNat 32 20).toNat = (VG.Proof.Argon2.X86.Derive.E s₀).toNat - 20 := by rw [esp, VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]
  have e24 : (s.gpr .esp - BitVec.ofNat 32 24).toNat = (VG.Proof.Argon2.X86.Derive.E s₀).toNat - 24 := by rw [esp, VG.Proof.Argon2.X86.Derive.sub_nat (by omega)]
  have e84 : (s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 60).toNat = (VG.Proof.Argon2.X86.Derive.E s₀).toNat - 84 := by
    rw [VG.Proof.Argon2.X86.Derive.sub_nat (by omega), e24]; omega
  have cA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ (VG.Proof.Argon2.X86.Derive.callR s₀) :=
    VG.Proof.Argon2.X86.Derive.in_call hp (by omega) (by omega)
  have cR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 4⟩ (VG.Proof.Argon2.X86.Derive.callR s₀) :=
    VG.Proof.Argon2.X86.Derive.in_call hp (by omega) (by omega)
  have cS : Region.Sub (below (s.gpr .esp - BitVec.ofNat 32 24) 60) (VG.Proof.Argon2.X86.Derive.callR s₀) :=
    VG.Proof.Argon2.X86.Derive.in_call hp (by omega) (by omega)
  have a20 : argAddr (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry 0 =
      (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := callEntry_argAddr0 _ _
  have ce : (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 :=
    callEntry_esp' _ _
  have pre := VG.Proof.Argon2.X86.Derive.hcall_pre hp h hr hdx ⟨RI, hRI, oI, bI, lI⟩ hinfit ⟨RO, hRO, oO, bO, lO⟩ houtfit hL
  refine WP.callWith HPrime.hPrime_verified.1 VG.Proof.Argon2.X86.Derive.hPrime_nosp (by simp) nesp
    (by rw [VG.Proof.Argon2.X86.Derive.hPrime_stack, esp]; simp only [List.length_cons, List.length_nil]; omega) pre
    fun t rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  simp only [HPrime.hPrimeX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3] at post
  have cB : Region.Sub (below (s.gpr .esp) 24) (VG.Proof.Argon2.X86.Derive.callR s₀) := VG.Proof.Argon2.X86.Derive.in_call hp (by rw [e24]; omega) (by rw [e24]; omega)
  have cf := callEntry_frame fit nesp
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.zero_add] at cf
  rw [VG.Proof.Argon2.X86.Derive.hPrime_stack] at f'
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.zero_add] at f'
  have bk : bytesAt (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry.mem ((s.gpr r).setWidth 64)
      (s.gpr .eax).toNat = bytesAt s.mem ((s.gpr r).setWidth 64) (s.gpr .eax).toNat :=
    VG.Proof.Argon2.X86.Derive.bytes_keep cf
    (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact I_call.sub_right cB)
    (Nat.le_of_lt (Nat.lt_trans (s.gpr .eax).isLt (by decide)))
  rw [m₂, bk] at post
  have f₁ : Frame [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.callR s₀] s.mem t.mem :=
    f'.sub fun q hq => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · refine ⟨VG.Proof.Argon2.X86.Derive.callR s₀, by simp, ?_⟩
        rw [esp]
        exact fun _ h => h
  refine k t (h.step (cs' .esp (by decide)) (cs' .ebp (by decide)) rd' wr' (f₁.sub fun q hq => ?_)) cs' f₁ post
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · refine ⟨RO, ?_, sO⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl <;> simp
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.Argon2.X86.Derive

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Derive.MemoryInit`. -/
section

section

/-!
# Argon2 on x86 (32-bit): clearing the memory matrix

`clear_ok`: `clear` zeroes the `blocks · 1024` bytes of the memory matrix,
one word per iteration, and writes nothing else. Its loop counts the words
left in `ecx` (`blocks · 256`, by eight doublings), with `edi` the next
word's address.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd wp_movi wp_mov wp_add wp_addi wp_subi)
open VG.Spec.Blake2 (bytesAt)

/-- The memory matrix, as an address. -/
abbrev memB (s₀ : State) : Addr := (VG.Proof.Argon2.X86.Derive.memP s₀).setWidth 64

/-- A byte after a zero word is stored at `a`. -/
theorem writeW_zero (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 32)) x = if (x - a).toNat < 4 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- `[x + d + k]`, at a 32-bit address that does not wrap. -/
theorem addr32 {x : BitVec 32} {d k : Nat} (h : x.toNat + d + k < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 d) k = x.setWidth 64 + BitVec.ofNat 64 (d + k) := by
  rw [addr_eq (by rw [VG.Proof.Argon2.X86.Derive.add_nat (by omega)]; omega), HPrime.setWidth_add (by omega), BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]

/-- A store to a region the body may write keeps the invariant. -/
theorem Inv.store {s₀ s t : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) {R : Region} (hR : R ∈ VG.Proof.Argon2.X86.Derive.bodyW s₀) {a : Addr}
    {v : BitVec 32} (hc : R.Contains a 4) (u : Mupd s t (s.mem.writeW a v)) : VG.Proof.Argon2.X86.Derive.Inv s₀ t :=
  h.step (by rw [u.gpr]) (by rw [u.gpr]) u.rd u.wr (by rw [u.mem]; exact (Frame.refl _ _).writeW hR v hc)

/-- `cmp d, [b + o]`, and the borrow. -/
theorem wp_cmpm {s : State} {is : List Instr} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Wp.Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)) →
      s'.zf = some (s.gpr d - s.mem.readW (addr B o) 32 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.mem ⟨b, o⟩) :: is)) s Q :=
  Wp.cons (s' := arithFlags s (s.gpr d - s.mem.readW (addr B o) 32)
      (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat))
      (subOverflow (s.gpr d) (s.mem.readW (addr B o) 32) (s.gpr d - s.mem.readW (addr B o) 32)))
    (by simp only [exec, execAlu, Wp.readSrc_mem hb hin, Option.bind_some])
    (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)

/-- The loop's state after `j` words. -/
structure CI (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  inv : VG.Proof.Argon2.X86.Derive.Inv s₀ s
  edi : s.gpr .edi = VG.Proof.Argon2.X86.Derive.memP s₀ + BitVec.ofNat 32 (4 * j)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.blocksN s₀ * 256 - j)
  eax : s.gpr .eax = 0
  zero : ∀ i < 4 * j, s.mem (VG.Proof.Argon2.X86.Derive.memB s₀ + BitVec.ofNat 64 i) = 0
  frame : Frame [VG.Proof.Argon2.X86.Derive.memR s₀] s₁.mem s.mem

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

theorem blocks_pos : 1 ≤ VG.Proof.Argon2.X86.Derive.blocksN s₀ := by
  rw [hp.blocks_eq, hp.laneLen_eq]
  have := Nat.mul_le_mul hp.lanes_pos (show 1 ≤ 4 * (VG.Proof.Argon2.X86.Derive.prm s₀).segmentLen by have := hp.segLen_two; omega)
  omega

theorem clearLoop_ok {s₁ : State} (h : VG.Proof.Argon2.X86.Derive.CI s₀ s₁ 0 s₁) :
    WP isa (.loop (.block Impl.Argon2.X86.Derive.clearWord) .ne) s₁ (VG.Proof.Argon2.X86.Derive.CI s₀ s₁ (VG.Proof.Argon2.X86.Derive.blocksN s₀ * 256)) := by
  have hm := hp.mem_fits
  have hb := hp.blocks_lt
  have b1 := VG.Proof.Argon2.X86.Derive.blocks_pos hp
  refine WP.loop (M := isa) (fun n s => ∃ j, n = VG.Proof.Argon2.X86.Derive.blocksN s₀ * 256 - j ∧ j < VG.Proof.Argon2.X86.Derive.blocksN s₀ * 256 ∧ VG.Proof.Argon2.X86.Derive.CI s₀ s₁ j s)
    ?_ (VG.Proof.Argon2.X86.Derive.blocksN s₀ * 256) s₁ ⟨0, by omega, by omega, h⟩
  rintro n s ⟨j, rfl, hj, c⟩
  have ea : addr (s.gpr .edi) 0 = VG.Proof.Argon2.X86.Derive.memB s₀ + BitVec.ofNat 64 (4 * j) := by
    rw [c.edi, VG.Proof.Argon2.X86.Derive.addr32 (by omega), Nat.add_zero]
  have hc : (VG.Proof.Argon2.X86.Derive.memR s₀).Contains (addr (s.gpr .edi) 0) 4 := by
    rw [ea]; exact Offset.contains_base _ (by omega) (by omega)
  simp only [Impl.Argon2.X86.Derive.clearWord]
  refine Wp.wp_stm rfl (by rw [c.inv.wr]; exact ⟨_, VG.Proof.Argon2.X86.Derive.mem_mem hp, hc⟩) fun t₁ u₁ => ?_
  have i₁ := c.inv.store (R := VG.Proof.Argon2.X86.Derive.memR s₀) (by simp) hc u₁
  refine wp_addi fun t₂ u₂ => wp_subi fun t u _ zf => WP.block_nil ?_
  have i₃ := (i₁.upd u₂ (by decide) (by decide)).upd u (by decide) (by decide)
  have e₁ : t.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Argon2.X86.Derive.blocksN s₀ * 256 - (j + 1)) := by
    rw [u.gpr, u₂.other _ (by decide), u₁.gpr, c.ecx, Wp.ofNat_pred (by omega)]; rfl
  have next : VG.Proof.Argon2.X86.Derive.CI s₀ s₁ (j + 1) t := by
    refine ⟨i₃, ?_, e₁, ?_, fun i hi => ?_, ?_⟩
    · rw [u.other _ (by decide), u₂.gpr, u₁.gpr, c.edi, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl
    · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.gpr, c.eax]
    · rw [u.mem, u₂.mem, u₁.mem, c.eax, ea, VG.Proof.Argon2.X86.Derive.writeW_zero]
      by_cases hi' : i < 4 * j
      · split
        · rfl
        · exact c.zero i hi'
      · rw [show VG.Proof.Argon2.X86.Derive.memB s₀ + BitVec.ofNat 64 i = VG.Proof.Argon2.X86.Derive.memB s₀ + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 (i - 4 * j) by
          rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' (by omega)],
          Offset.add_sub_cancel_left]
        split
        · rfl
        · rename_i hn; rw [BitVec.toNat_ofNat] at hn; omega
    · rw [u.mem, u₂.mem, u₁.mem]
      exact c.frame.writeW (List.mem_singleton_self _) _ hc
  have z : t.zf = some (decide (VG.Proof.Argon2.X86.Derive.blocksN s₀ * 256 - (j + 1) = 0)) := by
    rw [zf, u₂.other _ (by decide), u₁.gpr, c.ecx, Wp.ofNat_pred (by omega), Wp.ofNat_beq_zero (by omega)]
    rfl
  by_cases done : j + 1 = VG.Proof.Argon2.X86.Derive.blocksN s₀ * 256
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, z, show VG.Proof.Argon2.X86.Derive.blocksN s₀ * 256 - (j + 1) = 0 by omega, decide_true, Option.map_some,
      Bool.not_true]
  · refine .inr ⟨?_, VG.Proof.Argon2.X86.Derive.blocksN s₀ * 256 - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    simp only [eval, z, show VG.Proof.Argon2.X86.Derive.blocksN s₀ * 256 - (j + 1) ≠ 0 by omega, decide_false, Option.map_some,
      Bool.not_false]

theorem clear_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) :
    WP isa Impl.Argon2.X86.Derive.clear s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ Frame [VG.Proof.Argon2.X86.Derive.memR s₀] s.mem t.mem ∧
      ∀ i < VG.Proof.Argon2.X86.Derive.blocksN s₀ * 1024, t.mem (VG.Proof.Argon2.X86.Derive.memB s₀ + BitVec.ofNat 64 i) = 0 := by
  have hb := hp.blocks_lt
  have eb : VG.Proof.Argon2.X86.Derive.blocksN s₀ = (VG.X86.arg s₀ 14).toNat := rfl
  unfold Impl.Argon2.X86.Derive.clear Impl.Argon2.X86.Derive.clearSetup
  simp only [List.cons_append]
  refine WP.seq (VG.Proof.Argon2.X86.Derive.wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ =>
    VG.Proof.Argon2.X86.Derive.wp_ldarg hp (h.upd u₁ (by decide) (by decide)) (i := 14) (by decide) fun s₂ u₂ => ?_)
  have i₂ := (h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide)
  refine VG.Proof.Argon2.X86.Derive.dbl_ok 8 (by rw [u₂.gpr]; omega) fun s₃ e₃ k₃ => wp_movi fun s₄ u₄ => WP.block_nil ?_
  have i₄ := (i₂.keep k₃).upd u₄ (by decide) (by decide)
  refine (VG.Proof.Argon2.X86.Derive.clearLoop_ok hp ⟨i₄, ?_, ?_, u₄.gpr, fun i hi => absurd hi (by omega), Frame.refl _ _⟩).mono
    fun t c => ⟨c.inv, ?_, fun i hi => c.zero i (by omega)⟩
  · rw [u₄.other _ (by decide), k₃.other _ (by decide) (by decide) (by decide), u₂.other _ (by decide), u₁.gpr]
    simp
  · rw [u₄.other _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [e₃, u₂.gpr, Wp.toNat_ofNat_lt (by omega)]
    omega
  · rw [show s.mem = s₄.mem by rw [u₄.mem, k₃.mem, u₂.mem, u₁.mem]]
    exact c.frame

end

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): the memory's initialization

`memoryInit_ok`: after `memoryInit`, the memory matrix represents
`initMemory` (`Proof.Argon2.Represents`). The matrix is cleared, then each
lane's first two blocks are H′ of the 72 bytes at the start of the locals
(`initBlock_ok`), H₀ followed by the column and the lane, written there just
before the call. `LI s₀ h0 l` is the state after `l` lanes (`initCell`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd wp_movi wp_mov wp_add wp_addi wp_subi)
open VG.Spec.Blake2 (bytesAt)
open VG.Spec.Argon2 (Block blockAt zeroBlock parseBlock)

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
  exact VG.Proof.Argon2.X86.Derive.read_zero fun i hi => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact h _ (by omega)

/-! ## The initialized cells -/

/-- Cell `k` after the first two blocks of the first `l` lanes are initialized. -/
def initCell (p : Spec.Argon2.Params) (h0 : List Byte) (l k : Nat) : Block :=
  if k / p.laneLen < l ∧ k % p.laneLen < 2 then
    parseBlock (initialBytes h0 (k / p.laneLen) (k % p.laneLen))
  else zeroBlock

theorem initCell_zero (p : Spec.Argon2.Params) (h0 : List Byte) (k : Nat) : VG.Proof.Argon2.X86.Derive.initCell p h0 0 k = zeroBlock := by
  unfold VG.Proof.Argon2.X86.Derive.initCell
  exact ite_eq_right fun h => Nat.not_lt_zero _ h.1

theorem cell_div {L l c : Nat} (hc : c < L) : (l * L + c) / L = l := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem cell_mod {L l c : Nat} (hc : c < L) : (l * L + c) % L = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem initCell_new (p : Spec.Argon2.Params) (h0 : List Byte) {l c : Nat} (hL : 2 ≤ p.laneLen) (hc : c < 2) :
    VG.Proof.Argon2.X86.Derive.initCell p h0 (l + 1) (l * p.laneLen + c) = parseBlock (initialBytes h0 l c) := by
  unfold VG.Proof.Argon2.X86.Derive.initCell
  rw [VG.Proof.Argon2.X86.Derive.cell_div (by omega), VG.Proof.Argon2.X86.Derive.cell_mod (by omega)]
  exact ite_eq_left ⟨by omega, hc⟩

theorem initCell_old (p : Spec.Argon2.Params) (h0 : List Byte) {l k : Nat}
    (h₀ : k ≠ l * p.laneLen) (h₁ : k ≠ l * p.laneLen + 1) :
    VG.Proof.Argon2.X86.Derive.initCell p h0 (l + 1) k = VG.Proof.Argon2.X86.Derive.initCell p h0 l k := by
  unfold VG.Proof.Argon2.X86.Derive.initCell
  have hdm := Nat.div_add_mod k p.laneLen
  by_cases hq : k / p.laneLen = l
  · rw [hq, Nat.mul_comm] at hdm
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · by_cases hc : k / p.laneLen < l ∧ k % p.laneLen < 2
    · rw [ite_eq_left (by omega), ite_eq_left hc]
    · rw [ite_eq_right (by omega), ite_eq_right hc]

/-! ## A lane's first blocks -/

/-- A store to the locals at `d` keeps their first `n ≤ d` bytes. -/
theorem loc_bytes_store {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀) {m : Mem} {d n : Nat} (hn : n ≤ d) (hd : d + 4 ≤ 144)
    (v : BitVec 32) :
    bytesAt (m.writeW (addr (VG.Proof.Argon2.X86.Derive.E s₀) d) v) ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64) n = bytesAt m ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64) n := by
  have := VG.Proof.Argon2.X86.Derive.E_hi hp
  refine VG.Proof.Argon2.X86.Derive.bytes_keep
    ((Frame.refl [⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) d, 4⟩] m).writeW (List.mem_singleton_self _) v (Region.contains_self _ _))
    (fun r hr => ?_) (by omega)
  simp only [List.mem_singleton] at hr; subst hr
  exact VG.Proof.Argon2.X86.Derive.disj32 (.inl (by rw [VG.Proof.Argon2.X86.Derive.add_nat (by omega)]; omega)) (by omega) (by rw [VG.Proof.Argon2.X86.Derive.add_nat (by omega)]; omega)

/-- The 72 bytes of H′'s input: H₀, then two words. -/
theorem bytes72 (m : Mem) (p : Addr) :
    bytesAt m p 72 = bytesAt m p 64 ++ Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 64) 32) ++
      Spec.Blake2.wordBytes (m.readW (p + BitVec.ofNat 64 68) 32) := by
  rw [show (72 : Nat) = 64 + (4 + (4 + 0)) from rfl, Proof.Blake2.bytesAt_add, VG.Proof.Argon2.X86.Derive.bytes_word, VG.Proof.Argon2.X86.Derive.bytes_word,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  simp [bytesAt]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

omit hp in
/-- The call's frame lies in the body's regions. -/
theorem call_sub {O : Region} (hO : Region.Sub O (VG.Proof.Argon2.X86.Derive.memR s₀) ∨ Region.Sub O (VG.Proof.Argon2.X86.Derive.outR s₀)) :
    ∀ r ∈ [O, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.callR s₀], ∃ r' ∈ [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀, VG.Proof.Argon2.X86.Derive.callR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The first 64 bytes of the locals are outside a call's frame. -/
theorem h0_call {O : Region} (hO : Region.Sub O (VG.Proof.Argon2.X86.Derive.memR s₀) ∨ Region.Sub O (VG.Proof.Argon2.X86.Derive.outR s₀)) :
    ∀ r ∈ [O, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.callR s₀], Region.Disjoint ⟨(VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64, 64⟩ r := by
  have sub : Region.Sub ⟨(VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64, 64⟩ (VG.Proof.Argon2.X86.Derive.locR s₀) := Region.sub_prefix (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hO with h | h
    · exact ((VG.Proof.Argon2.X86.Derive.loc_disj' hp (R := VG.Proof.Argon2.X86.Derive.memR s₀) (by simp)).sub_left sub).sub_right h
    · exact ((VG.Proof.Argon2.X86.Derive.loc_disj' hp (R := VG.Proof.Argon2.X86.Derive.outR s₀) (by simp)).sub_left sub).sub_right h
  · exact (VG.Proof.Argon2.X86.Derive.loc_disj' hp (R := VG.Proof.Argon2.X86.Derive.scrR s₀) (by simp)).sub_left sub
  · exact (VG.Proof.Argon2.X86.Derive.loc_call hp).sub_left sub

/-- A cell of the memory matrix is outside `scratch`, `out`'s and the stack below the locals. -/
theorem cell_disj {k : Nat} (hk : k < VG.Proof.Argon2.X86.Derive.blocksN s₀) :
    ∀ r ∈ [VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.callR s₀], Region.Disjoint ⟨matrixCell (VG.Proof.Argon2.X86.Derive.memB s₀) k, 1024⟩ r := by
  have sub : Region.Sub ⟨matrixCell (VG.Proof.Argon2.X86.Derive.memB s₀) k, 1024⟩ (VG.Proof.Argon2.X86.Derive.memR s₀) := matrixCell_sub _ _ _ hk
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.mem_scr.sub_left sub
  · exact (VG.Proof.Argon2.X86.Derive.call_disj hp (R := VG.Proof.Argon2.X86.Derive.memR s₀) (by simp)).symm.sub_left sub

theorem cell_addr {k : Nat} (hk : k < VG.Proof.Argon2.X86.Derive.blocksN s₀) :
    (VG.Proof.Argon2.X86.Derive.memP s₀ + BitVec.ofNat 32 (k * 1024)).setWidth 64 = matrixCell (VG.Proof.Argon2.X86.Derive.memB s₀) k := by
  have := hp.mem_fits
  have : k * 1024 + 1024 ≤ VG.Proof.Argon2.X86.Derive.blocksN s₀ * 1024 := by omega
  exact HPrime.setWidth_add (by omega)

omit hp in
theorem cell_in_mem {k : Nat} (hk : k < VG.Proof.Argon2.X86.Derive.blocksN s₀) :
    Region.Sub ⟨matrixCell (VG.Proof.Argon2.X86.Derive.memB s₀) k, 1024⟩ (VG.Proof.Argon2.X86.Derive.memR s₀) := matrixCell_sub _ _ _ hk

/-- Cells other than `k` are outside its region. -/
theorem cell_other {j k : Nat} (hj : j < VG.Proof.Argon2.X86.Derive.blocksN s₀) (hk : k < VG.Proof.Argon2.X86.Derive.blocksN s₀) (ne : j ≠ k) :
    Region.Disjoint ⟨matrixCell (VG.Proof.Argon2.X86.Derive.memB s₀) j, 1024⟩ ⟨matrixCell (VG.Proof.Argon2.X86.Derive.memB s₀) k, 1024⟩ :=
  matrixCell_disjoint _ _ _ _ (by have := hp.blocks_lt; omega) hj hk ne

/-- Block `c < 2` of lane `l`: H′ of H₀, `c` and `l`. -/
theorem initBlock_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.X86.Derive.Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64) 64 = h0) {l c : Nat} (hl : l < VG.Proof.Argon2.X86.Derive.lanesN s₀) (hc : c < 2)
    (esi : s.gpr .esi = BitVec.ofNat 32 l)
    (edi : s.gpr .edi = VG.Proof.Argon2.X86.Derive.memP s₀ + BitVec.ofNat 32 ((l * (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen + c) * 1024)) :
    WP isa (Impl.Argon2.X86.Derive.initBlock c) s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ t ∧
      bytesAt t.mem ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64) 64 = h0 ∧ t.gpr .esi = s.gpr .esi ∧ t.gpr .edi = s.gpr .edi ∧
      blockAt t.mem (matrixCell (VG.Proof.Argon2.X86.Derive.memB s₀) (l * (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen + c)) = parseBlock (initialBytes h0 l c) ∧
      ∀ k < VG.Proof.Argon2.X86.Derive.blocksN s₀, k ≠ l * (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen + c →
        blockAt t.mem (matrixCell (VG.Proof.Argon2.X86.Derive.memB s₀) k) = blockAt s.mem (matrixCell (VG.Proof.Argon2.X86.Derive.memB s₀) k) := by
  have hE := VG.Proof.Argon2.X86.Derive.E_hi hp
  have hs := hp.scr_fits
  have hm := hp.mem_fits
  have hlt := hp.lanes_lt
  have L2 : 2 ≤ (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega
  have hcell : l * (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen + c < VG.Proof.Argon2.X86.Derive.blocksN s₀ := by
    rw [hp.blocks_eq]
    have := Nat.mul_le_mul_right (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen (show l + 1 ≤ VG.Proof.Argon2.X86.Derive.lanesN s₀ by omega)
    rw [Nat.succ_mul] at this
    omega
  unfold Impl.Argon2.X86.Derive.initBlock Impl.Argon2.X86.Derive.hPrimeCall
  refine WP.seq (wp_movi fun s₁ u₁ => ?_)
  have i₁ := h.upd u₁ (by decide) (by decide)
  refine VG.Proof.Argon2.X86.Derive.wp_stloc hp i₁ (d := 64) (by decide) fun s₂ i₂ v₂ o₂ g₂ m₂ => ?_
  refine VG.Proof.Argon2.X86.Derive.wp_stloc hp i₂ (d := 68) (by decide) fun s₃ i₃ v₃ o₃ g₃ m₃ => ?_
  refine wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ => VG.Proof.Argon2.X86.Derive.wp_ldarg hp ((i₃.upd u₄ (by decide) (by decide)).upd u₅
    (by decide) (by decide)) (i := 15) (by decide) fun s₆ u₆ => WP.block_nil ?_
  have i₆ := ((i₃.upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide) (by decide)
  have m₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have g₆ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₆.gpr r = s.gpr r := fun r a b d => by
    rw [u₆.other _ d, u₅.other _ b, u₄.other _ a, g₃, g₂, u₁.other _ a]
  have ebp₆ : s₆.gpr .ebp = VG.Proof.Argon2.X86.Derive.E s₀ := i₆.ebp
  have eax₆ : (s₆.gpr .eax).toNat = 72 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl
  have ecx₆ : (s₆.gpr .ecx).toNat = 1024 := by rw [u₆.other _ (by decide), u₅.gpr]; rfl
  have edi₆ : s₆.gpr .edi = s.gpr .edi := g₆ _ (by decide) (by decide) (by decide)
  have O : (s₆.gpr .edi).setWidth 64 = matrixCell (VG.Proof.Argon2.X86.Derive.memB s₀) (l * (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen + c) := by
    rw [edi₆, edi, VG.Proof.Argon2.X86.Derive.cell_addr hp hcell]
  have sO : Region.Sub ⟨(s₆.gpr .edi).setWidth 64, (s₆.gpr .ecx).toNat⟩ (VG.Proof.Argon2.X86.Derive.memR s₀) := by
    rw [O, ecx₆]; exact VG.Proof.Argon2.X86.Derive.cell_in_mem hcell
  have hcell' : (l * (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen + c) * 1024 + 1024 ≤ VG.Proof.Argon2.X86.Derive.blocksN s₀ * 1024 := by omega
  refine VG.Proof.Argon2.X86.Derive.hcall_ok hp i₆ (r := .ebp) (by decide) u₆.gpr
    ⟨VG.Proof.Argon2.X86.Derive.locR s₀, by simp, 0, by rw [ebp₆]; simp, by rw [eax₆]; show 0 + 72 ≤ 144; omega⟩ (by rw [ebp₆, eax₆]; omega)
    ⟨VG.Proof.Argon2.X86.Derive.memR s₀, by simp, (l * (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen + c) * 1024, by rw [O]; rfl, by rw [ecx₆]; exact hcell'⟩
    (by rw [edi₆, edi, ecx₆, VG.Proof.Argon2.X86.Derive.add_nat (by omega)]; omega) (by rw [ecx₆]; decide)
    fun t it cs fr post => ⟨it, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The parameters.
    exact Prm.of_lw pr fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      have hd' : 72 ≤ d ∧ d + 4 ≤ 144 := by rcases hd with rfl | rfl | rfl | rfl <;> decide
      rw [VG.Proof.Argon2.X86.Derive.lw_keep hp fr (VG.Proof.Argon2.X86.Derive.call_sub (.inl sO)) hd'.2, VG.Proof.Argon2.X86.Derive.lw_mem m₆, o₃ d (by omega) (by omega),
        o₂ d (by omega) (by omega), VG.Proof.Argon2.X86.Derive.lw_mem u₁.mem]
  · rw [VG.Proof.Argon2.X86.Derive.bytes_keep fr (VG.Proof.Argon2.X86.Derive.h0_call hp (.inl sO)) (by omega), m₆, m₃,
      VG.Proof.Argon2.X86.Derive.loc_bytes_store hp (by decide) (by decide), m₂, VG.Proof.Argon2.X86.Derive.loc_bytes_store hp (by decide) (by decide), u₁.mem, b0]
  · rw [cs .esi (by decide), g₆ _ (by decide) (by decide) (by decide)]
  · rw [cs .edi (by decide), edi₆]
  · refine Proof.Argon2.blockAt_of_initialBytes _ _ _ _ _ ?_
    rw [← O, ← ecx₆, post, ecx₆, ebp₆, eax₆, VG.Proof.Argon2.X86.Derive.bytes72, m₆]
    have w64 : s₃.mem.readW ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64 + BitVec.ofNat 64 64) 32 = BitVec.ofNat 32 c := by
      rw [← addr_eq (by omega)]
      show VG.Proof.Argon2.X86.Derive.lw s₀ s₃ 64 = _
      rw [o₃ 64 (by decide) (by decide), v₂, u₁.gpr]
    have w68 : s₃.mem.readW ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64 + BitVec.ofNat 64 68) 32 = BitVec.ofNat 32 l := by
      rw [← addr_eq (by omega)]
      show VG.Proof.Argon2.X86.Derive.lw s₀ s₃ 68 = _
      rw [v₃, g₂, u₁.other _ (by decide), esi]
    rw [w64, w68, m₃, VG.Proof.Argon2.X86.Derive.loc_bytes_store hp (by decide) (by decide), m₂, VG.Proof.Argon2.X86.Derive.loc_bytes_store hp (by decide) (by decide),
      u₁.mem, b0]
    rfl
  · intro k hk ne
    have fs : Frame [⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) 64, 4⟩, ⟨addr (VG.Proof.Argon2.X86.Derive.E s₀) 68, 4⟩] s.mem s₃.mem := by
      rw [m₃, m₂, u₁.mem]
      exact ((Frame.refl _ _).writeW (w := 32) List.mem_cons_self _ (Region.contains_self _ _)).writeW (w := 32)
        (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
    rw [VG.Proof.Argon2.X86.Derive.blockAt_keep fr (fun r hr => ?_), m₆]
    · -- The stores to the locals.
      refine VG.Proof.Argon2.X86.Derive.blockAt_keep fs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((VG.Proof.Argon2.X86.Derive.loc_disj hp (d := 64) (by decide) (VG.Proof.Argon2.X86.Derive.memR s₀) (by simp)).symm.sub_left (VG.Proof.Argon2.X86.Derive.cell_in_mem hk))
      · exact ((VG.Proof.Argon2.X86.Derive.loc_disj hp (d := 68) (by decide) (VG.Proof.Argon2.X86.Derive.memR s₀) (by simp)).symm.sub_left (VG.Proof.Argon2.X86.Derive.cell_in_mem hk))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [O, ecx₆]; exact VG.Proof.Argon2.X86.Derive.cell_other hp hk hcell ne
      · exact VG.Proof.Argon2.X86.Derive.cell_disj hp hk _ (by simp)
      · exact VG.Proof.Argon2.X86.Derive.cell_disj hp hk _ (by simp)

end

/-- The state after the first two blocks of `l` lanes. -/
structure LI (s₀ : State) (h0 : List Byte) (l : Nat) (s : State) : Prop where
  inv : VG.Proof.Argon2.X86.Derive.Inv s₀ s
  pr : VG.Proof.Argon2.X86.Derive.Prm s₀ s
  b0 : bytesAt s.mem ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64) 64 = h0
  esi : s.gpr .esi = BitVec.ofNat 32 l
  edi : s.gpr .edi = VG.Proof.Argon2.X86.Derive.memP s₀ + BitVec.ofNat 32 (l * (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen * 1024)
  cells : ∀ k < VG.Proof.Argon2.X86.Derive.blocksN s₀, blockAt s.mem (matrixCell (VG.Proof.Argon2.X86.Derive.memB s₀) k) = VG.Proof.Argon2.X86.Derive.initCell (VG.Proof.Argon2.X86.Derive.prm s₀) h0 l k

theorem Prm.of_mem {s₀ s t : State} (pr : VG.Proof.Argon2.X86.Derive.Prm s₀ s) (h : t.mem = s.mem) : VG.Proof.Argon2.X86.Derive.Prm s₀ t :=
  Prm.of_lw pr fun d _ => VG.Proof.Argon2.X86.Derive.lw_mem h d

theorem edi_next (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + 1024 + BitVec.ofNat 32 b - 1024 = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc (x + _) 1024, BitVec.add_comm 1024 (BitVec.ofNat 32 b), ← BitVec.add_assoc,
    BitVec.add_sub_cancel, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Derive.DPre s₀)
include hp

theorem lane_ok {h0 : List Byte} {l : Nat} {s : State} (hl : l < VG.Proof.Argon2.X86.Derive.lanesN s₀) (h : VG.Proof.Argon2.X86.Derive.LI s₀ h0 l s) :
    WP isa Impl.Argon2.X86.Derive.initLane s fun t =>
      VG.Proof.Argon2.X86.Derive.LI s₀ h0 (l + 1) t ∧ t.cf = some (decide (l + 1 < VG.Proof.Argon2.X86.Derive.lanesN s₀)) := by
  have L2 : 2 ≤ (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega
  have hlt := hp.lanes_lt
  unfold Impl.Argon2.X86.Derive.initLane
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.initBlock_ok hp h.inv h.pr h.b0 hl (c := 0) (by decide) h.esi
    (by rw [h.edi, Nat.add_zero])).mono fun s₁ ⟨i₁, p₁, b₁, e₁, d₁, w₁, o₁⟩ => ?_)
  refine WP.seq (wp_addi fun s₂ u₂ => WP.block_nil ?_)
  have i₂ := i₁.upd u₂ (by decide) (by decide)
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.initBlock_ok hp i₂ (p₁.of_mem u₂.mem) (h0 := h0) (by rw [u₂.mem]; exact b₁) hl (c := 1) (by decide)
    (by rw [u₂.other _ (by decide), e₁, h.esi]) (by rw [u₂.gpr, d₁, h.edi, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat, Nat.succ_mul])).mono fun s₃ ⟨i₃, p₃, b₃, e₃, d₃, w₃, o₃⟩ => ?_)
  simp only [Impl.Argon2.X86.Derive.nextLane, Impl.Argon2.X86.Derive.fr]
  refine VG.Proof.Argon2.X86.Derive.wp_ldloc hp i₃ (d := Impl.Argon2.X86.Derive.strideOff) (by decide) fun s₄ u₄ =>
    wp_add fun s₅ u₅ _ => wp_subi fun s₆ u₆ _ _ => wp_addi fun s₇ u₇ => ?_
  have i₇ := (((i₃.upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide)
    (by decide)).upd u₇ (by decide) (by decide)
  have m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have esi₇ : s₇.gpr .esi = BitVec.ofNat 32 (l + 1) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃,
      u₂.other _ (by decide), e₁, h.esi, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_add_ofNat]
  refine VG.Proof.Argon2.X86.Derive.wp_cmpm i₇.ebp (i₇.arg_in hp (i := 7) (by decide)) fun t f c _ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact i₇.step (by rw [f.gpr]) (by rw [f.gpr]) f.rd f.wr (by rw [f.mem]; exact Frame.refl _ _)
  · exact p₃.of_mem (by rw [f.mem, m₇])
  · rw [f.mem, m₇, b₃]
  · rw [f.gpr, esi₇]
  · rw [f.gpr, u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₄.other _ (by decide), d₃, u₂.gpr, d₁, h.edi,
      p₃.stride, VG.Proof.Argon2.X86.Derive.edi_next, Nat.succ_mul, Nat.add_mul]
  · intro k hk
    rw [f.mem, m₇]
    by_cases k1 : k = l * (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen + 1
    · rw [k1, w₃]; exact (VG.Proof.Argon2.X86.Derive.initCell_new _ _ L2 (by decide)).symm
    rw [o₃ k hk k1]
    by_cases k0 : k = l * (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen
    · rw [u₂.mem, k0, show l * (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen = l * (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen + 0 from rfl, w₁]
      exact (VG.Proof.Argon2.X86.Derive.initCell_new _ _ L2 (by decide)).symm
    rw [u₂.mem, o₁ k hk (by omega), h.cells k hk, VG.Proof.Argon2.X86.Derive.initCell_old _ _ k0 k1]
  · rw [c, esi₇, i₇.arg hp (by decide), Wp.toNat_ofNat_lt (by omega)]; rfl

/-- `clear`, from the body with H₀ in the locals. -/
theorem clearW_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.X86.Derive.Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64) 64 = h0) :
    WP isa Impl.Argon2.X86.Derive.clear s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ t ∧
      bytesAt t.mem ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64) 64 = h0 ∧ ∀ i < VG.Proof.Argon2.X86.Derive.blocksN s₀ * 1024,
        t.mem ((VG.Proof.Argon2.X86.Derive.memP s₀).setWidth 64 + BitVec.ofNat 64 i) = 0 := by
  refine (VG.Proof.Argon2.X86.Derive.clear_ok hp h).mono fun s₁ ⟨i₁, f₁, z₁⟩ => ⟨i₁, ?_, ?_, z₁⟩
  · have fsub : ∀ r ∈ [VG.Proof.Argon2.X86.Derive.memR s₀], ∃ r' ∈ [VG.Proof.Argon2.X86.Derive.memR s₀, VG.Proof.Argon2.X86.Derive.scrR s₀, VG.Proof.Argon2.X86.Derive.outR s₀, VG.Proof.Argon2.X86.Derive.callR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
    exact Prm.of_lw pr fun d hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      exact VG.Proof.Argon2.X86.Derive.lw_keep hp f₁ fsub (by rcases hd with rfl | rfl | rfl | rfl <;> decide)
  · rw [VG.Proof.Argon2.X86.Derive.bytes_keep f₁ (fun r hr => ?_) (by omega), b0]
    simp only [List.mem_singleton] at hr; subst hr
    exact (VG.Proof.Argon2.X86.Derive.loc_disj' hp (R := VG.Proof.Argon2.X86.Derive.memR s₀) (by simp)).sub_left (Region.sub_prefix (by decide))

/-- The first lane's first block, after `clear`. -/
theorem laneStart_ok {s : State} {h0 : List Byte} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ s ∧
      bytesAt s.mem ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64) 64 = h0 ∧ ∀ i < VG.Proof.Argon2.X86.Derive.blocksN s₀ * 1024,
        s.mem ((VG.Proof.Argon2.X86.Derive.memP s₀).setWidth 64 + BitVec.ofNat 64 i) = 0) :
    WP isa (.block [.mov .edi (Impl.Argon2.X86.Derive.fr (Impl.Argon2.X86.Derive.argOff 13)), .mov .esi (.imm 0)]) s (VG.Proof.Argon2.X86.Derive.LI s₀ h0 0) := by
  obtain ⟨i₁, p₁, b₁, z₁⟩ := h
  refine VG.Proof.Argon2.X86.Derive.wp_ldarg hp i₁ (i := 13) (by decide) fun s₂ u₂ => wp_movi fun s₃ u₃ => WP.block_nil ?_
  have i₃ := (i₁.upd u₂ (by decide) (by decide)).upd u₃ (by decide) (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem]
  refine ⟨i₃, p₁.of_mem m₃, by rw [m₃]; exact b₁, u₃.gpr, ?_, fun k hk => ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr]; simp
  · rw [VG.Proof.Argon2.X86.Derive.initCell_zero, m₃]
    refine VG.Proof.Argon2.X86.Derive.blockAt_zero fun i hi => ?_
    rw [matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact z₁ _ (by omega)

theorem memoryInit_ok {s : State} (h : VG.Proof.Argon2.X86.Derive.Inv s₀ s) (pr : VG.Proof.Argon2.X86.Derive.Prm s₀ s) {h0 : List Byte}
    (b0 : bytesAt s.mem ((VG.Proof.Argon2.X86.Derive.E s₀).setWidth 64) 64 = h0) :
    WP isa Impl.Argon2.X86.Derive.memoryInit s fun t => VG.Proof.Argon2.X86.Derive.Inv s₀ t ∧ VG.Proof.Argon2.X86.Derive.Prm s₀ t ∧
      Represents t.mem (VG.Proof.Argon2.X86.Derive.memB s₀) (VG.Proof.Argon2.X86.Derive.prm s₀).blocks (Spec.Argon2.initMemory (VG.Proof.Argon2.X86.Derive.prm s₀) h0).memory := by
  have hlt := hp.lanes_lt
  have hl1 := hp.lanes_pos
  have hb := hp.blocks_lt
  unfold Impl.Argon2.X86.Derive.memoryInit
  refine WP.seq ((VG.Proof.Argon2.X86.Derive.clearW_ok hp h pr b0).mono fun s₁ h₁ => WP.seq ((VG.Proof.Argon2.X86.Derive.laneStart_ok hp h₁).mono fun s₃ start => ?_))
  refine WP.loop (M := isa) (fun n t => ∃ l, n = VG.Proof.Argon2.X86.Derive.lanesN s₀ - l ∧ l < VG.Proof.Argon2.X86.Derive.lanesN s₀ ∧ VG.Proof.Argon2.X86.Derive.LI s₀ h0 l t) ?_
    (VG.Proof.Argon2.X86.Derive.lanesN s₀) s₃ ⟨0, by omega, by omega, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (VG.Proof.Argon2.X86.Derive.lane_ok hp hl ht).mono fun u ⟨hu, cu⟩ => ?_
  by_cases done : l + 1 < VG.Proof.Argon2.X86.Derive.lanesN s₀
  · refine .inr ⟨by simp only [eval, cu, done, decide_true], VG.Proof.Argon2.X86.Derive.lanesN s₀ - (l + 1), by omega, l + 1, rfl, done, hu⟩
  · refine .inl ⟨by simp only [eval, cu, done, decide_false], hu.inv, hu.pr, ?_⟩
    have hl' : l + 1 = VG.Proof.Argon2.X86.Derive.lanesN s₀ := by omega
    refine ⟨Proof.Argon2.initMemory_size _ _, fun k hk => ?_⟩
    have hk' : k < VG.Proof.Argon2.X86.Derive.blocksN s₀ := by rw [hp.blocks]; exact hk
    rw [hu.cells k hk', Array.getElem?_eq_getElem (by rw [Proof.Argon2.initMemory_size]; exact hk),
      Option.getD_some, Proof.Argon2.initMemory_cell _ _ _ hk, VG.Proof.Argon2.X86.Derive.initCell, hl']
    have : k / (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen < VG.Proof.Argon2.X86.Derive.lanesN s₀ := by
      rw [hp.blocks_eq] at hk'
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk')
    by_cases c2 : k % (VG.Proof.Argon2.X86.Derive.prm s₀).laneLen < 2
    · rw [ite_eq_left ⟨this, c2⟩, ite_eq_left c2]
    · rw [ite_eq_right (fun h => c2 h.2), ite_eq_right c2]

end

end VG.Proof.Argon2.X86.Derive

end
