module

public import VerifiedGarbage.Proof.Argon2.X86.Divide
public import VerifiedGarbage.Proof.Argon2.X86.HPrime.Next
import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.X86.CompressLit
import VerifiedGarbage.Proof.Blake2.X86.Blake2b
import VerifiedGarbage.Proof.Blake2.X86.LitB
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Argon2.Dimensions
public import VerifiedGarbage.Impl.Argon2.X86.Derive
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Blake2.Stream
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! ### `Argon2.X86.Derive.Body`, which this module and modules that import it used -/

section

@[expose] public section

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
  exact Nat.mod_eq_of_lt (by have := x.isLt; omega_arith)

theorem disj32 {x y : BitVec 32} {n m : Nat} (h : x.toNat + n ≤ y.toNat ∨ y.toNat + m ≤ x.toNat)
    (hn : x.toNat + n ≤ 2 ^ 32) (hm : y.toNat + m ≤ 2 ^ 32) :
    Region.Disjoint ⟨x.setWidth 64, n⟩ ⟨y.setWidth 64, m⟩ := by
  rcases h with h | h
  · exact Offset.disjoint_of_le (by simp only [toNat_w]; omega_arith) (by simp only [toNat_w]; omega_arith)
  · exact (Offset.disjoint_of_le (r₁ := ⟨y.setWidth 64, m⟩) (by simp only [toNat_w]; omega_arith)
      (by simp only [toNat_w]; omega_arith)).symm

theorem contains32 {x y : BitVec 32} {n m : Nat} (h₁ : y.toNat ≤ x.toNat)
    (h₂ : x.toNat + n ≤ y.toNat + m) :
    Region.Contains ⟨y.setWidth 64, m⟩ (x.setWidth 64) n := by
  simp only [Region.Contains]
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, toNat_w]; exact h₁), toNat_w, toNat_w]
  omega_arith

theorem sub32 {x y : BitVec 32} {n m : Nat} (h₁ : y.toNat ≤ x.toNat)
    (h₂ : x.toNat + n ≤ y.toNat + m) :
    Region.Sub ⟨x.setWidth 64, n⟩ ⟨y.setWidth 64, m⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  obtain hx := toNat_w x
  obtain hy := toNat_w y
  have := x.isLt
  bv_omega

/-- `x - k`, as a number. -/
theorem sub_nat {x : BitVec 32} {k : Nat} (h : k ≤ x.toNat) :
    (x - BitVec.ofNat 32 k).toNat = x.toNat - k := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith)]
  rw [show 2 ^ 32 - k + x.toNat = (x.toNat - k) + 2 ^ 32 by omega_arith, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega_arith)]

/-- `x + k`, as a number. -/
theorem add_nat {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith),
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
abbrev E0 : BitVec 32 := s₀.gpr .esp

/-- The parameters. -/
abbrev prm : Params := params (kindV s₀).toNat (itersN s₀) (mcostN s₀) (lanesN s₀) (outL s₀)

abbrev pwR : Region := ⟨(pwP s₀).setWidth 64, pwL s₀⟩
abbrev saltR : Region := ⟨(saltP s₀).setWidth 64, saltL s₀⟩
abbrev secR : Region := ⟨(secP s₀).setWidth 64, secL s₀⟩
abbrev adR : Region := ⟨(adP s₀).setWidth 64, adL s₀⟩
abbrev memR : Region := ⟨(memP s₀).setWidth 64, blocksN s₀ * 1024⟩
abbrev scrR : Region := ⟨(scrP s₀).setWidth 64, 16384⟩
abbrev outR : Region := ⟨(outP s₀).setWidth 64, outL s₀⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 72⟩
abbrev retR : Region := ⟨(E0 s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E0 s₀) 244

/-- The inputs, on entry. -/
abbrev pwB : List Byte := bytesAt s₀.mem (pwR s₀).base (pwL s₀)
abbrev saltB : List Byte := bytesAt s₀.mem (saltR s₀).base (saltL s₀)
abbrev secB : List Byte := bytesAt s₀.mem (secR s₀).base (secL s₀)
abbrev adB : List Byte := bytesAt s₀.mem (adR s₀).base (adL s₀)

end

/-- The facts of `deriveX86`'s precondition. -/
structure DPre (s₀ : State) : Prop where
  rd : s₀.rd = [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀]
  wr : s₀.wr = [memR s₀, scrR s₀, outR s₀]
  ro_w : ∀ r ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀], ∀ w ∈ [memR s₀, scrR s₀, outR s₀],
    r.Disjoint w
  mem_scr : (memR s₀).Disjoint (scrR s₀)
  mem_out : (memR s₀).Disjoint (outR s₀)
  scr_out : (scrR s₀).Disjoint (outR s₀)
  ret_w : ∀ w ∈ [memR s₀, scrR s₀, outR s₀], (retR s₀).Disjoint w
  stk_all : ∀ r ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀], (stkR s₀).Disjoint r
  pw_fits : (pwP s₀).toNat + pwL s₀ ≤ 2 ^ 32
  salt_fits : (saltP s₀).toNat + saltL s₀ ≤ 2 ^ 32
  sec_fits : (secP s₀).toNat + secL s₀ ≤ 2 ^ 32
  ad_fits : (adP s₀).toNat + adL s₀ ≤ 2 ^ 32
  mem_fits : (memP s₀).toNat + blocksN s₀ * 1024 ≤ 2 ^ 32
  scr_fits : (scrP s₀).toNat + 16384 ≤ 2 ^ 32
  out_fits : (outP s₀).toNat + outL s₀ ≤ 2 ^ 32
  esp_lo : 244 ≤ (E0 s₀).toNat
  esp_hi : (E0 s₀).toNat + 76 ≤ 2 ^ 32
  kind_le : (kindV s₀).toNat ≤ 2
  valid : valid (prm s₀) (pwL s₀) (saltL s₀) (secL s₀) (adL s₀)
  threads : 1 ≤ threadsN s₀ ∧ threadsN s₀ < 2 ^ 24
  blocks : blocksN s₀ = (prm s₀).blocks

/-- `vg_argon2`, with its arguments only read. -/
def deriveX86 : Contract X86.isa where
  pre := DPre
  post s s' := bytesAt s'.mem ((outP s).setWidth 64) (outL s) =
    derive (prm s) (pwB s) (saltB s) (secB s) (adB s)
  pub s₁ s₂ := (s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 18, arg s₁ i = arg s₂ i) ∧
    references (prm s₁) (pwB s₁) (saltB s₁) (secB s₁) (adB s₁) =
      references (prm s₂) (pwB s₂) (saltB s₂) (secB s₂) (adB s₂)

/-! ## Facts of the precondition -/

/-- Two disjoint, nonempty regions within `[0, N)` have at most `N` bytes in all. -/
theorem disjoint_total {a b : Region} (h : a.Disjoint b) {N : Nat}
    (ha : a.base.toNat + a.len ≤ N) (hb : b.base.toNat + b.len ≤ N) (pa : 0 < a.len) (pb : 0 < b.len) :
    a.len + b.len ≤ N := by
  obtain key : ∀ {a b : Region}, a.Disjoint b → a.base.toNat ≤ b.base.toNat → b.base.toNat + b.len ≤ N →
      0 < b.len → a.base.toNat + a.len ≤ b.base.toNat := fun {a b} h hle hb pb => by
    by_contra hlt
    refine h b.base ?_ ?_
    · simp only [Region.Contains]
      rw [BitVec.toNat_sub_of_le (by simpa [BitVec.le_def] using hle)]
      omega_arith
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  rcases Nat.le_total a.base.toNat b.base.toNat with hle | hle
  · have := key h hle hb pb; omega_arith
  · have := key h.symm hle ha pa; omega_arith

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
  · omega_arith
  have := disjoint_total hp.mem_scr (N := 2 ^ 32)
    (by simp only [BitVec.toNat_setWidth, ]; omega_arith)
    (by simp only [BitVec.toNat_setWidth, ]; omega_arith)
    (by simp only; omega_arith) (by simp only; omega_arith)
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
abbrev E (s₀ : State) : BitVec 32 := E0 s₀ - BitVec.ofNat 32 160

/-- The caller's registers, in the order of their words above the locals. -/
def savedVal (s₀ : State) : Nat → BitVec 32
  | 0 => s₀.gpr .ebx
  | 1 => s₀.gpr .esi
  | 2 => s₀.gpr .edi
  | _ => s₀.gpr .ebp

/-- The word `j` above the locals, where register `savedVal j` is. -/
abbrev slot (s₀ : State) (j : Nat) : Addr := (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).setWidth 64

/-- What the body must keep for the frames to restore the caller's state. -/
structure BodyDone (s₀ t : State) : Prop where
  esp : t.gpr .esp = E s₀
  saved : ∀ j < 4, t.mem.readW (slot s₀ j) 32 = savedVal s₀ j
  ret : t.mem.readW ((E0 s₀).setWidth 64) 32 = s₀.mem.readW ((E0 s₀).setWidth 64) 32

theorem popped_one_self (r : Reg) (s : State) (h : r ≠ .esp) :
    (popped r 1 s).gpr r = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  simp [popped, popReg, State.setReg, h]

section
variable {s₀ : State} (hlo : 160 ≤ (E0 s₀).toNat)
include hlo

theorem E_sub (k : Nat) (hk : k ≤ 160) :
    E s₀ + BitVec.ofNat 32 k = E0 s₀ - BitVec.ofNat 32 (160 - k) := by
  apply BitVec.eq_of_toNat_eq
  have := (E0 s₀).isLt
  rw [BitVec.toNat_add, sub_toNat hlo, sub_toNat (by omega_arith), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := k) (by omega_arith)]
  omega_arith

/-- `E s₀ + a`, widened, is the 64-bit `E s₀` plus `a`. -/
theorem E_add_setWidth {a : Nat} (ha : a ≤ 160) :
    (E s₀ + BitVec.ofNat 32 a).setWidth 64 = (E s₀).setWidth 64 + BitVec.ofNat 64 a := by
  have hE := (E0 s₀).isLt
  have hEt : (E s₀).toNat = (E0 s₀).toNat - 160 := sub_toNat hlo
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [hEt]
  omega_arith

/-- The `n` bytes below `E s₀ + a` lie in the `b ≥ a` bytes from `E s₀`. -/
theorem below_loc {x : BitVec 32} {a n b : Nat} (hx : x = E s₀ + BitVec.ofNat 32 a) (hn : n ≤ a)
    (hb : a ≤ b) (hb' : b ≤ 160) : Region.Sub (below x n) ⟨(E s₀).setWidth 64, b⟩ := by
  subst hx
  have hE := (E0 s₀).isLt
  obtain e : E s₀ + BitVec.ofNat 32 a - BitVec.ofNat 32 n = E s₀ + BitVec.ofNat 32 (a - n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  show Region.Sub ⟨(E s₀ + BitVec.ofNat 32 a - BitVec.ofNat 32 n).setWidth 64, n⟩ _
  rw [e, E_add_setWidth hlo (by omega_arith)]
  exact Offset.sub_base _ (by omega_arith)

/-- A saved word is apart from the bytes from `E s₀` below it. -/
theorem keep_slot {m m' : Mem} {b : Nat} (f : Frame [⟨(E s₀).setWidth 64, b⟩] m m') {j : Nat}
    (hj : j < 4) (hb : b ≤ 144 + 4 * j) : m'.readW (slot s₀ j) 32 = m.readW (slot s₀ j) 32 := by
  rw [slot, E_add_setWidth hlo (by omega_arith)]
  exact f.readW (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ hb (by omega_arith)) (by decide)

/-- The return address is apart from the 160 bytes below it. -/
theorem keep_ret {m m' : Mem} (f : Frame [⟨(E s₀).setWidth 64, 160⟩] m m') :
    m'.readW ((E0 s₀).setWidth 64) 32 = m.readW ((E0 s₀).setWidth 64) 32 := by
  rw [show E0 s₀ = E s₀ + BitVec.ofNat 32 160 by rw [E_sub hlo 160 (by decide)]; simp,
    E_add_setWidth hlo (by decide)]
  exact f.readW (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith)) (by decide)

/-- A frame of the region below `x`, widened to the `b` bytes from `E s₀`. -/
theorem frame_loc {m m' : Mem} {x : BitVec 32} {a n b : Nat} (f : Frame [below x n] m m')
    (hx : x = E s₀ + BitVec.ofNat 32 a) (hn : n ≤ a) (hb : a ≤ b) (hb' : b ≤ 160) :
    Frame [⟨(E s₀).setWidth 64, b⟩] m m' :=
  f.sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, below_loc hlo hx hn hb hb'⟩

omit hlo in
theorem frame_widen {m m' : Mem} {a b : Nat} (f : Frame [⟨(E s₀).setWidth 64, a⟩] m m') (h : a ≤ b) :
    Frame [⟨(E s₀).setWidth 64, b⟩] m m' :=
  f.sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h⟩

theorem frames_ok {Q : State → Prop} (hsp : NoSp body)
    (hb : WP isa body (entry s₀) fun t => BodyDone s₀ t ∧ Q t)
    (hQ : ∀ t u, Q t → Frame [below (E0 s₀) 160] t.mem u.mem → Q u) :
    WP isa derive s₀ fun u => abiPreserved s₀ u ∧ Q u := by
  obtain hE := (E0 s₀).isLt
  have hlo' : 160 ≤ (s₀.gpr .esp).toNat := hlo
  obtain nf : ∀ {r : Reg} {k : Nat} {rs : List Reg} {b : Prog isa}, r ≠ .esp → NoSp b →
      NoSp (.frame (.push rs) b (.pop r k)) := fun {r k rs b} hr hb i hi => by
    simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | hi) | rfl
    · rfl
    · exact hb i hi
    · simp [Taint.clobbers, Taint.dst, hr]
  obtain e1 : ((pushed [.ebp] s₀).gpr .esp).toNat = (E0 s₀).toNat - 4 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega_arith)]; rfl
  obtain e2 : ((pushed [.edi] (pushed [.ebp] s₀)).gpr .esp).toNat = (E0 s₀).toNat - 8 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega_arith), e1]; rfl
  obtain e3 : ((pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))).gpr .esp).toNat = (E0 s₀).toNat - 12 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega_arith), e2]; rfl
  obtain e4 : ((pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))).gpr .esp).toNat =
      (E0 s₀).toNat - 16 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega_arith), e3]; rfl
  obtain x4 : (pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))).gpr .esp =
      E s₀ + BitVec.ofNat 32 144 := by
    apply BitVec.eq_of_toNat_eq; rw [e4, E_sub hlo 144 (by decide), sub_toNat (by omega_arith)]
  obtain x3 : (pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))).gpr .esp = E s₀ + BitVec.ofNat 32 148 := by
    apply BitVec.eq_of_toNat_eq; rw [e3, E_sub hlo 148 (by decide), sub_toNat (by omega_arith)]
  obtain x2 : (pushed [.edi] (pushed [.ebp] s₀)).gpr .esp = E s₀ + BitVec.ofNat 32 152 := by
    apply BitVec.eq_of_toNat_eq; rw [e2, E_sub hlo 152 (by decide), sub_toNat (by omega_arith)]
  obtain x1 : (pushed [.ebp] s₀).gpr .esp = E s₀ + BitVec.ofNat 32 156 := by
    apply BitVec.eq_of_toNat_eq; rw [e1, E_sub hlo 156 (by decide), sub_toNat (by omega_arith)]
  obtain x0 : s₀.gpr .esp = E s₀ + BitVec.ofNat 32 160 := by
    rw [E_sub hlo 160 (by decide)]; simp
  simp only [derive, saved, frames]
  refine WP.frame (by simp) (by decide) (by decide) (by simp only [List.length_singleton]; omega_arith)
    (nf (by decide) (nf (by decide) (nf (by decide) (nf (by decide) hsp)))) ?_
  refine WP.frame (by simp) (by decide) (by decide) (by simp only [List.length_singleton]; omega_arith)
    (nf (by decide) (nf (by decide) (nf (by decide) hsp))) ?_
  refine WP.frame (by simp) (by decide) (by decide) (by simp only [List.length_singleton]; omega_arith)
    (nf (by decide) (nf (by decide) hsp)) ?_
  refine WP.frame (by simp) (by decide) (by decide) (by simp only [List.length_singleton]; omega_arith)
    (nf (by decide) hsp) ?_
  refine WP.frame (by simp [locals]) (by decide) (by decide)
    (by simp only [List.length_replicate, locals]; omega_arith) hsp
    (hb.mono fun t ⟨d, q⟩ m₁ v₁ f₁ m₂ v₂ f₂ m₃ v₃ f₃ m₄ v₄ f₄ m₅ v₅ f₅ => ?_)
  -- The pops: each restores a register from its slot, which the frames below it miss.
  obtain add4 : ∀ a : Nat, E s₀ + BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * 1) =
      E s₀ + BitVec.ofNat 32 (a + 4) := fun a => by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  let t₁ : State := { popped .eax (List.replicate (locals / 4) Reg.eax).length t with mem := m₁, unknowns := v₁ }
  let t₂ : State := { popped .ebx [Reg.ebx].length t₁ with mem := m₂, unknowns := v₂ }
  let t₃ : State := { popped .esi [Reg.esi].length t₂ with mem := m₃, unknowns := v₃ }
  let t₄ : State := { popped .edi [Reg.edi].length t₃ with mem := m₄, unknowns := v₄ }
  obtain F₁ : Frame [⟨(E s₀).setWidth 64, 144⟩] t.mem m₁ :=
    frame_loc hlo f₁ x4 (by simp only [List.length_replicate, locals]; omega_arith) (Nat.le_refl _) (by decide)
  obtain F₂ : Frame [⟨(E s₀).setWidth 64, 148⟩] t.mem m₂ :=
    (frame_widen F₁ (by decide)).trans (frame_loc hlo f₂ x3 (by simp) (Nat.le_refl _) (by decide))
  obtain F₃ : Frame [⟨(E s₀).setWidth 64, 152⟩] t.mem m₃ :=
    (frame_widen F₂ (by decide)).trans (frame_loc hlo f₃ x2 (by simp) (Nat.le_refl _) (by decide))
  obtain F₄ : Frame [⟨(E s₀).setWidth 64, 156⟩] t.mem m₄ :=
    (frame_widen F₃ (by decide)).trans (frame_loc hlo f₄ x1 (by simp) (Nat.le_refl _) (by decide))
  obtain F₅ : Frame [⟨(E s₀).setWidth 64, 160⟩] t.mem m₅ :=
    (frame_widen F₄ (by decide)).trans (frame_loc hlo f₅ x0 (by simp) (Nat.le_refl _) (by decide))
  obtain sp₁ : t₁.gpr .esp = E s₀ + BitVec.ofNat 32 144 := by
    show (popped .eax (List.replicate (locals / 4) Reg.eax).length t).gpr .esp = _
    rw [popped_esp, d.esp]; simp [locals]
  obtain sp₂ : t₂.gpr .esp = E s₀ + BitVec.ofNat 32 148 := by
    show (popped .ebx [Reg.ebx].length t₁).gpr .esp = _
    rw [popped_esp, sp₁]; exact add4 144
  obtain sp₃ : t₃.gpr .esp = E s₀ + BitVec.ofNat 32 152 := by
    show (popped .esi [Reg.esi].length t₂).gpr .esp = _
    rw [popped_esp, sp₂]; exact add4 148
  obtain sp₄ : t₄.gpr .esp = E s₀ + BitVec.ofNat 32 156 := by
    show (popped .edi [Reg.edi].length t₃).gpr .esp = _
    rw [popped_esp, sp₃]; exact add4 152
  obtain b₂ : t₂.gpr .ebx = s₀.gpr .ebx := by
    show (popped .ebx 1 t₁).gpr .ebx = _
    rw [popped_one_self _ _ (by decide), sp₁]
    exact (keep_slot hlo F₁ (j := 0) (by decide) (by decide)).trans (d.saved 0 (by decide))
  obtain b₃ : t₃.gpr .esi = s₀.gpr .esi := by
    show (popped .esi 1 t₂).gpr .esi = _
    rw [popped_one_self _ _ (by decide), sp₂]
    exact (keep_slot hlo F₂ (j := 1) (by decide) (by decide)).trans (d.saved 1 (by decide))
  obtain b₄ : t₄.gpr .edi = s₀.gpr .edi := by
    show (popped .edi 1 t₃).gpr .edi = _
    rw [popped_one_self _ _ (by decide), sp₃]
    exact (keep_slot hlo F₃ (j := 2) (by decide) (by decide)).trans (d.saved 2 (by decide))
  obtain b₅ : (popped .ebp [Reg.ebp].length t₄).gpr .ebp = s₀.gpr .ebp := by
    show (popped .ebp 1 t₄).gpr .ebp = _
    rw [popped_one_self _ _ (by decide), sp₄]
    exact (keep_slot hlo F₄ (j := 3) (by decide) (by decide)).trans (d.saved 3 (by decide))
  obtain spu : (popped .ebp [Reg.ebp].length t₄).gpr .esp = E0 s₀ := by
    rw [popped_esp, sp₄, List.length_singleton, add4 156, E_sub hlo 160 (by decide)]; simp
  refine ⟨⟨fun r hr => ?_, (keep_ret hlo F₅).trans d.ret⟩, hQ t _ q F₅⟩
  show (popped .ebp [Reg.ebp].length t₄).gpr r = s₀.gpr r
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [popped_gpr _ _ _ (by decide) (by decide)]
    show (popped .edi [Reg.edi].length t₃).gpr .ebx = _
    rw [popped_gpr _ _ _ (by decide) (by decide)]
    show (popped .esi [Reg.esi].length t₂).gpr .ebx = _
    rw [popped_gpr _ _ _ (by decide) (by decide)]
    exact b₂
  · rw [popped_gpr _ _ _ (by decide) (by decide)]
    show (popped .edi [Reg.edi].length t₃).gpr .esi = _
    rw [popped_gpr _ _ _ (by decide) (by decide)]
    exact b₃
  · rw [popped_gpr _ _ _ (by decide) (by decide)]
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
abbrev locR : Region := ⟨(E s₀).setWidth 64, 144⟩

/-- The stack below the locals. -/
abbrev callR : Region := below (E s₀) 84

/-- The regions the body may write. -/
abbrev bodyW : List Region := [memR s₀, scrR s₀, outR s₀, locR s₀, callR s₀]

end

theorem entry_esp (s₀ : State) : (entry s₀).gpr .esp = E s₀ := by
  simp only [entry, pushed_esp, List.length_singleton, List.length_replicate, BitVec.sub_sub,
    BitVec.ofNat_add_ofNat]

theorem entry_rd (s₀ : State) : (entry s₀).rd = s₀.rd := by simp [entry]

/-! ## The pushes -/

theorem pushed_esp_nat {rs : List Reg} {s : State} (h : 4 * rs.length ≤ (s.gpr .esp).toNat) :
    ((pushed rs s).gpr .esp).toNat = (s.gpr .esp).toNat - 4 * rs.length := by
  rw [pushed_esp, sub_nat h]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem entry_frame : Frame [below (E0 s₀) 160] s₀.mem (entry s₀).mem := by
  have hlo : 244 ≤ (s₀.gpr .esp).toNat := hp.esp_lo
  obtain hE := (s₀.gpr .esp).isLt
  have hE0 : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  -- Each push writes within the 160 bytes below `esp` on entry.
  obtain step : ∀ {rs : List Reg} {s : State}, .esp ∉ rs → 4 * rs.length ≤ (s.gpr .esp).toNat →
      (s₀.gpr .esp).toNat - 160 ≤ (s.gpr .esp).toNat - 4 * rs.length →
      (s.gpr .esp).toNat ≤ (s₀.gpr .esp).toNat → Frame [below (E0 s₀) 160] s.mem (pushed rs s).mem :=
    fun {rs s} hrs hn h₁ h₂ => (pushed_frame hrs hn).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, sub32 ?_ ?_⟩
      · rw [sub_nat hn, sub_nat (by omega_arith)]; omega_arith
      · rw [sub_nat hn, sub_nat (by omega_arith)]; omega_arith
  -- The stack pointer after each push.
  obtain n₁ : ((pushed [.ebp] s₀).gpr .esp).toNat = (s₀.gpr .esp).toNat - 4 :=
    pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo])
  obtain n₂ : ((pushed [.edi] (pushed [.ebp] s₀)).gpr .esp).toNat = (s₀.gpr .esp).toNat - 8 := by
    rw [pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo, n₁]), n₁]; rfl
  obtain n₃ : ((pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))).gpr .esp).toNat =
      (s₀.gpr .esp).toNat - 12 := by
    rw [pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo, n₂]), n₂]; rfl
  obtain n₄ : ((pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))).gpr .esp).toNat =
      (s₀.gpr .esp).toNat - 16 := by
    rw [pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo, n₃]), n₃]; rfl
  exact ((((step (by decide) (by rw [List.length_singleton]; omega_using [hlo])
    (by rw [List.length_singleton]; omega_using [hlo]) (Nat.le_refl _)).trans
    (step (by decide) (by rw [List.length_singleton, n₁]; omega_using [hlo])
      (by rw [List.length_singleton, n₁]; omega_using [hlo])
      (by rw [n₁]; omega_using [hlo]))).trans
    (step (by decide) (by rw [List.length_singleton, n₂]; omega_using [hlo])
      (by rw [List.length_singleton, n₂]; omega_using [hlo])
      (by rw [n₂]; omega_using [hlo]))).trans
    (step (by decide) (by rw [List.length_singleton, n₃]; omega_using [hlo])
      (by rw [List.length_singleton, n₃]; omega_using [hlo])
      (by rw [n₃]; omega_using [hlo]))).trans
    (step (by decide) (by rw [List.length_replicate, n₄]; omega_using [hlo])
      (by rw [List.length_replicate, n₄]; omega_using [hlo]) (by rw [n₄]; omega_using [hlo]))

end

/-- A word above the frame a push writes is kept. -/
theorem push_keep {rs : List Reg} {s : State} (hrs : .esp ∉ rs) (hn : 4 * rs.length ≤ (s.gpr .esp).toNat)
    {a : BitVec 32} (ha : (s.gpr .esp).toNat ≤ a.toNat) (ha' : a.toNat + 4 ≤ 2 ^ 32) :
    (pushed rs s).mem.readW (a.setWidth 64) 32 = s.mem.readW (a.setWidth 64) 32 := by
  refine (pushed_frame hrs hn).readW (r := ⟨a.setWidth 64, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact disj32 (.inr (by rw [sub_nat hn]; omega_arith)) ha' (by rw [sub_nat hn]; have := (s.gpr .esp).isLt; omega_arith)

/-- The word a one-register push writes. -/
theorem push_word {r : Reg} {s : State} (hr : r ≠ .esp) (hn : 4 ≤ (s.gpr .esp).toNat) {a : BitVec 32}
    (ha : a = s.gpr .esp - BitVec.ofNat 32 4) :
    (pushed [r] s).mem.readW (a.setWidth 64) 32 = s.gpr r := by
  have := pushed_word (rs := [r]) (s := s) (by simpa using hr.symm) (by simpa using hn) (i := 0) (by simp)
  rw [pushed_esp] at this
  simp only [List.length_singleton, Nat.mul_zero, BitVec.add_zero] at this
  rw [ha]; exact this

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem entry_saved {j : Nat} (hj : j < 4) : (entry s₀).mem.readW (slot s₀ j) 32 = savedVal s₀ j := by
  have hlo : 244 ≤ (s₀.gpr .esp).toNat := hp.esp_lo
  have hi : (s₀.gpr .esp).toNat + 76 ≤ 2 ^ 32 := hp.esp_hi
  -- The stack pointer after each push, and the facts the pushes need, once.
  obtain n₁ : ((pushed [.ebp] s₀).gpr .esp).toNat = (s₀.gpr .esp).toNat - 4 :=
    pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo])
  obtain n₂ : ((pushed [.edi] (pushed [.ebp] s₀)).gpr .esp).toNat = (s₀.gpr .esp).toNat - 8 := by
    rw [pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo, n₁]), n₁]; rfl
  obtain n₃ : ((pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))).gpr .esp).toNat =
      (s₀.gpr .esp).toNat - 12 := by
    rw [pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo, n₂]), n₂]; rfl
  obtain n₄ : ((pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))).gpr .esp).toNat =
      (s₀.gpr .esp).toNat - 16 := by
    rw [pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo, n₃]), n₃]; rfl
  obtain k₁ : 4 * [Reg.ebx].length ≤ ((pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))).gpr .esp).toNat := by
    rw [List.length_singleton, n₃]; omega_using [hlo]
  obtain k₂ : 4 * [Reg.esi].length ≤ ((pushed [.edi] (pushed [.ebp] s₀)).gpr .esp).toNat := by
    rw [List.length_singleton, n₂]; omega_using [hlo]
  obtain k₃ : 4 * [Reg.edi].length ≤ ((pushed [.ebp] s₀).gpr .esp).toNat := by
    rw [List.length_singleton, n₁]; omega_using [hlo]
  obtain sl : (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat = (s₀.gpr .esp).toNat - 16 + 4 * j := by
    have := (s₀.gpr .esp).isLt
    have hlo' : 244 ≤ (E0 s₀).toNat := hp.esp_lo
    have hE0 : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
    rw [add_nat (by rw [sub_nat (by omega_using [hlo'])]; omega_using [hlo', hE0, hi, hj]),
      sub_nat (by omega_using [hlo'])]
    omega_using [hlo', hE0]
  obtain ha : (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat + 4 ≤ 2 ^ 32 := by rw [sl]; omega_using [hlo, hi, hj]
  obtain p₃ : 1 ≤ j → ((pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))).gpr .esp).toNat ≤
      (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat := fun h => by rw [n₃, sl]; omega_using [hlo, h]
  obtain p₂ : 2 ≤ j → ((pushed [.edi] (pushed [.ebp] s₀)).gpr .esp).toNat ≤
      (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat := fun h => by rw [n₂, sl]; omega_using [hlo, h]
  obtain p₁ : 3 ≤ j → ((pushed [.ebp] s₀).gpr .esp).toNat ≤
      (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat := fun h => by rw [n₁, sl]; omega_using [hlo, h]
  -- The slot is the word the push of `savedVal j` wrote.
  obtain w : ∀ (s : State), (s.gpr .esp).toNat = (s₀.gpr .esp).toNat - 12 + 4 * j →
      4 ≤ (s.gpr .esp).toNat ∧ E s₀ + BitVec.ofNat 32 (144 + 4 * j) = s.gpr .esp - BitVec.ofNat 32 4 :=
    fun s h => ⟨by rw [h]; omega_using [hlo],
      BitVec.eq_of_toNat_eq (by rw [sl, sub_nat (by rw [h]; omega_using [hlo]), h]; omega_using [hlo])⟩
  unfold entry slot
  rw [push_keep (by decide) (by simp only [List.length_replicate]; omega_using [hlo, n₄])
    (by rw [n₄, sl]; omega_using [hlo]) ha]
  rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · have ⟨h₁, h₂⟩ := w (pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))) (by rw [n₃]; omega_using [hlo])
    rw [push_word (by decide) h₁ h₂, pushed_gpr _ _ (by decide), pushed_gpr _ _ (by decide),
      pushed_gpr _ _ (by decide)]; rfl
  · have ⟨h₁, h₂⟩ := w (pushed [.edi] (pushed [.ebp] s₀)) (by rw [n₂]; omega_using [hlo])
    rw [push_keep (by decide) k₁ (p₃ (by decide)) ha, push_word (by decide) h₁ h₂, pushed_gpr _ _ (by decide),
      pushed_gpr _ _ (by decide)]; rfl
  · have ⟨h₁, h₂⟩ := w (pushed [.ebp] s₀) (by rw [n₁]; omega_using [hlo])
    rw [push_keep (by decide) k₁ (p₃ (by decide)) ha, push_keep (by decide) k₂ (p₂ (by decide)) ha,
      push_word (by decide) h₁ h₂, pushed_gpr _ _ (by decide)]
    rfl
  · have ⟨h₁, h₂⟩ := w s₀ (by omega_using [hlo])
    rw [push_keep (by decide) k₁ (p₃ (by decide)) ha, push_keep (by decide) k₂ (p₂ (by decide)) ha,
      push_keep (by decide) k₃ (p₁ (by decide)) ha, push_word (by decide) h₁ h₂]
    rfl

end

theorem loc_mem (s₀ : State) : locR s₀ ∈ (entry s₀).wr := by
  simp [entry, pushed_wr, pushed_esp, BitVec.sub_sub, BitVec.ofNat_add_ofNat, below]

theorem wr_mem (s₀ : State) {r : Region} (h : r ∈ s₀.wr) : r ∈ (entry s₀).wr := by
  simp only [entry, pushed_wr, List.mem_cons]
  exact .inr (.inr (.inr (.inr (.inr h))))

/-! ## The invariant -/

/-- The state of the body. -/
structure Inv (s₀ s : State) : Prop where
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = (entry s₀).wr
  frame : Frame (bodyW s₀) (entry s₀).mem s.mem

/-- A step that writes registers other than `esp` and `ebp`, and memory within the body's regions. -/
theorem Inv.step {s₀ s t : State} (h : Inv s₀ s) (he : t.gpr .esp = s.gpr .esp)
    (hb : t.gpr .ebp = s.gpr .ebp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame (bodyW s₀) s.mem t.mem) : Inv s₀ t :=
  ⟨he.trans h.esp, hb.trans h.ebp, hrd.trans h.rd, hwr.trans h.wr, h.frame.trans hf⟩

theorem Inv.upd {s₀ s t : State} {r : Reg} {v : BitVec 32} (h : Inv s₀ s) (u : Upd s t r v)
    (h₁ : r ≠ .esp) (h₂ : r ≠ .ebp) : Inv s₀ t :=
  h.step (u.other _ h₁.symm) (u.other _ h₂.symm) u.rd u.wr (by rw [u.mem]; exact Frame.refl _ _)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem E_hi : (E s₀).toNat + 236 ≤ 2 ^ 32 := by
  have := hp.esp_hi; have := hp.esp_lo; rw [sub_nat (by omega_arith)]; omega_arith

/-- The locals and the stack below them lie in the stack the contract reserves. -/
theorem loc_stk {d n : Nat} (h : d + n ≤ 144) :
    Region.Sub ⟨(E s₀ + BitVec.ofNat 32 d).setWidth 64, n⟩ (stkR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  obtain hE : (E s₀).toNat = (E0 s₀).toNat - 160 := sub_nat (by omega_arith)
  obtain h1 : (E s₀ + BitVec.ofNat 32 d).toNat = (E0 s₀).toNat - 160 + d := by
    rw [add_nat (by omega_arith), hE]
  obtain h2 : (E0 s₀ - BitVec.ofNat 32 244).toNat = (E0 s₀).toNat - 244 := sub_nat (by omega_arith)
  exact sub32 (by rw [h1, h2]; omega_arith) (by rw [h1, h2]; omega_arith)

theorem call_stk : Region.Sub (callR s₀) (stkR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  obtain hE : (E s₀).toNat = (E0 s₀).toNat - 160 := sub_nat (by omega_arith)
  obtain h1 : (E s₀ - BitVec.ofNat 32 84).toNat = (E0 s₀).toNat - 244 := by rw [sub_nat (by omega_arith), hE]; omega_arith
  obtain h2 : (E0 s₀ - BitVec.ofNat 32 244).toNat = (E0 s₀).toNat - 244 := sub_nat (by omega_arith)
  exact sub32 (by rw [h1, h2]) (by rw [h1, h2]; omega_arith)

/-- A word of the locals. -/
theorem loc_in {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions s.wr (addr (E s₀) d) 4 := by
  have := E_hi hp
  rw [h.wr]
  exact ⟨locR s₀, loc_mem s₀, contains32 (by rw [add_nat (by omega_arith)]; omega_arith)
    (by rw [add_nat (by omega_arith)]; omega_arith)⟩

theorem loc_in' {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := loc_in hp h hd
  ⟨r, List.mem_append_right _ hr, hc⟩

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem E_nat : (E s₀).toNat = (E0 s₀).toNat - 160 := sub_nat (by have := hp.esp_lo; omega_arith)

/-- A range within the 160 bytes the frames use. -/
theorem frame_stk {d n : Nat} (h : d + n ≤ 160) :
    Region.Sub ⟨(E s₀ + BitVec.ofNat 32 d).setWidth 64, n⟩ (stkR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  obtain h1 : (E s₀ + BitVec.ofNat 32 d).toNat = (E0 s₀).toNat - 160 + d := by
    rw [add_nat (by rw [E_nat hp]; omega_arith), E_nat hp]
  obtain h2 : (E0 s₀ - BitVec.ofNat 32 244).toNat = (E0 s₀).toNat - 244 := sub_nat (by omega_arith)
  exact sub32 (by rw [h1, h2]; omega_arith) (by rw [h1, h2]; omega_arith)

/-- What lies above the locals is outside the body's regions. -/
theorem above_disj {a : BitVec 32} {n : Nat} (ha : (E s₀).toNat + 144 ≤ a.toNat)
    (ha' : a.toNat + n ≤ (E0 s₀).toNat + 76)
    (hm : Region.Disjoint ⟨a.setWidth 64, n⟩ (memR s₀)) (hs : Region.Disjoint ⟨a.setWidth 64, n⟩ (scrR s₀))
    (ho : Region.Disjoint ⟨a.setWidth 64, n⟩ (outR s₀)) :
    ∀ r ∈ bodyW s₀, Region.Disjoint ⟨a.setWidth 64, n⟩ r := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  obtain hE := E_nat hp
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hm
  · exact hs
  · exact ho
  · exact disj32 (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  · exact disj32 (.inr (by rw [sub_nat (by omega_arith)]; omega_arith)) (by omega_arith)
      (by rw [sub_nat (by omega_arith)]; omega_arith)

theorem Inv.done {s : State} (h : Inv s₀ s) : BodyDone s₀ s := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  obtain hE := E_nat hp
  obtain hE' : (E0 s₀ - BitVec.ofNat 32 160).toNat = (E0 s₀).toNat - 160 := sub_nat (by omega_arith)
  refine ⟨h.esp, fun j hj => ?_, ?_⟩
  · have sl : (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat = (E s₀).toNat + (144 + 4 * j) :=
      add_nat (by have := E_hi hp; omega_arith)
    obtain st := frame_stk hp (d := 144 + 4 * j) (n := 4) (by omega_arith)
    rw [h.frame.readW (r := ⟨slot s₀ j, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact entry_saved hp hj
    refine above_disj hp (by rw [sl]; omega_arith) (by rw [sl]; omega_arith) ?_ ?_ ?_
    · exact ((hp.stk_all _ (by simp)).sub_left st)
    · exact ((hp.stk_all _ (by simp)).sub_left st)
    · exact ((hp.stk_all _ (by simp)).sub_left st)
  · rw [h.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)]
    · refine entry_frame hp |>.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact disj32 (.inr (by rw [sub_nat (by omega_arith)]; omega_arith)) (by omega_arith) (by rw [sub_nat (by omega_arith)]; omega_arith)
    refine above_disj hp (by omega_arith) (by omega_arith) ?_ ?_ ?_
    · exact hp.ret_w _ (by simp)
    · exact hp.ret_w _ (by simp)
    · exact hp.ret_w _ (by simp)

/-- The arguments' addresses, from `ebp`. -/
theorem arg_addr {i : Nat} (hi : i < 18) :
    addr (E s₀) (Impl.Argon2.X86.Derive.argOff i) = argAddr s₀ i := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  obtain hE := E_nat hp
  simp only [addr, argAddr, Impl.Argon2.X86.Derive.argOff, Impl.Argon2.X86.Derive.locals]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [add_nat (by omega_arith), add_nat (by omega_arith)]
  show (E0 s₀ - BitVec.ofNat 32 160).toNat + _ = (E0 s₀).toNat + _
  rw [sub_nat (by omega_arith)]; omega_arith

theorem arg_word {i : Nat} (hi : i < 18) :
    Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  exact sub32 (by rw [add_nat (by omega_arith), add_nat (by omega_arith)]; omega_arith)
    (by rw [add_nat (by omega_arith), add_nat (by omega_arith)]; omega_arith)

theorem Inv.arg_in {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) (Impl.Argon2.X86.Derive.argOff i)) 4 := by
  rw [arg_addr hp hi, h.rd, hp.rd]
  exact ⟨argR s₀, by simp, arg_word hp hi (argAddr s₀ i) |> fun _ => by
    have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
    exact contains32 (by rw [add_nat (by omega_arith), add_nat (by omega_arith)]; omega_arith)
      (by rw [add_nat (by omega_arith), add_nat (by omega_arith)]; omega_arith)⟩

theorem Inv.arg {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    s.mem.readW (addr (E s₀) (Impl.Argon2.X86.Derive.argOff i)) 32 = arg s₀ i := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  obtain hE := E_nat hp
  obtain ai : (E0 s₀ + BitVec.ofNat 32 (4 + 4 * i)).toNat = (E0 s₀).toNat + 4 + 4 * i := by
    rw [add_nat (by omega_arith)]; omega_arith
  rw [arg_addr hp hi]
  obtain sub := arg_word hp hi
  rw [h.frame.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
  · refine (entry_frame hp).readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact disj32 (.inr (by rw [sub_nat (by omega_arith), ai]; omega_arith)) (by rw [ai]; omega_arith)
      (by rw [sub_nat (by omega_arith)]; omega_arith)
  refine above_disj hp (by rw [ai]; omega_arith) (by rw [ai]; omega_arith) ?_ ?_ ?_
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub

/-- The inputs are kept. -/
theorem Inv.input {s : State} (h : Inv s₀ s) {R : Region}
    (hR : R ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀]) :
    bytesAt s.mem R.base R.len = bytesAt s₀.mem R.base R.len := by
  obtain hR' : R ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> simp
  obtain hS : R ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> simp
  obtain stk := (hp.stk_all R hS).symm
  obtain hl : R.len ≤ 2 ^ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> exact Nat.le_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  rw [h.frame.bytes (R := R) (fun r hr => ?_) hl hi]
  · exact (entry_frame hp).bytes (R := R) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact stk.sub_right (frame_stk hp (d := 0) (n := 160) (by decide) |> fun hs => by
        simpa using hs)) hl hi
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact stk.sub_right (by simpa using frame_stk hp (d := 0) (n := 144) (by decide))
  · exact stk.sub_right (call_stk hp)

end

end VG.Proof.Argon2.X86.Derive

end

end

@[expose] public section

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
abbrev lw (s₀ s : State) (d : Nat) : BitVec 32 := s.mem.readW (addr (E s₀) d) 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem loc_addr {d : Nat} (hd : d < 236) :
    (E s₀ + BitVec.ofNat 32 d).toNat = (E s₀).toNat + d := add_nat (by have := E_hi hp; omega_arith)

/-- Another word of the frame, after a store to the locals. -/
theorem lw_store {m : Mem} {d e : Nat} (hd : d + 4 ≤ 236) (he : e + 4 ≤ 236) (hde : d + 4 ≤ e ∨ e + 4 ≤ d)
    (v : BitVec 32) :
    (m.writeW (addr (E s₀) d) v).readW (addr (E s₀) e) 32 = m.readW (addr (E s₀) e) 32 :=
  Proof.Sha256.X86.Stream.readW_writeW_addr m v (by have := E_hi hp; omega_arith) (by have := E_hi hp; omega_arith) hde.symm

theorem Inv.store_loc {s t : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {v : BitVec 32}
    (u : Mupd s t (s.mem.writeW (addr (E s₀) d) v)) :
    Inv s₀ t ∧ lw s₀ t d = v ∧ ∀ e, e + 4 ≤ 236 → (d + 4 ≤ e ∨ e + 4 ≤ d) → lw s₀ t e = lw s₀ s e := by
  have hE := E_hi hp
  refine ⟨h.step (by rw [u.gpr]) (by rw [u.gpr]) u.rd u.wr ?_, ?_, fun e he hde => ?_⟩
  · rw [u.mem]
    exact (Frame.refl _ _).writeW (r := locR s₀) (by simp) v
      (contains32 (by rw [loc_addr hp (by omega_arith)]; omega_arith) (by rw [loc_addr hp (by omega_arith)]; omega_arith))
  · show t.mem.readW _ 32 = v
    rw [u.mem, Mem.readW_writeW_self32]
  · show t.mem.readW _ 32 = _
    rw [u.mem, lw_store hp (by omega_arith) he hde]

/-- `mov [ebp + d], r` -/
theorem wp_stloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → lw s₀ t d = s.gpr r → (∀ e, e + 4 ≤ 236 → (d + 4 ≤ e ∨ e + 4 ≤ d) →
      lw s₀ t e = lw s₀ s e) → t.gpr = s.gpr → t.mem = s.mem.writeW (addr (E s₀) d) (s.gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (.store ⟨.ebp, d⟩ r :: is)) s Q :=
  VG.X86.Wp.wp_stm h.ebp (loc_in hp h hd) fun t u =>
    let ⟨i, v, o⟩ := h.store_loc hp hd u
    k t i v o u.gpr u.mem

/-- `mov r, [ebp + d]` -/
theorem wp_ldloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (lw s₀ s d) → WP isa (.block is) t Q) :
    WP isa (.block (.mov r (.mem ⟨.ebp, d⟩) :: is)) s Q :=
  VG.X86.Wp.wp_ldm h.ebp (loc_in' hp h hd) k

/-- `mov r, [ebp + argOff i]` -/
theorem wp_ldarg {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (.mov r (.mem ⟨.ebp, Impl.Argon2.X86.Derive.argOff i⟩) :: is)) s Q :=
  VG.X86.Wp.wp_ldm h.ebp (h.arg_in hp hi) fun t u => k t (by rw [h.arg hp hi] at u; exact u)

/-- The locals are outside the memory matrix, `scratch`, the output and the stack below them. -/
theorem loc_disj {d : Nat} (hd : d + 4 ≤ 144) :
    ∀ r ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Disjoint ⟨addr (E s₀) d, 4⟩ r := by
  have hE := E_hi hp
  have hl := hp.esp_lo
  have hEn := E_nat hp
  have sub := loc_stk hp (d := d) (n := 4) hd
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact (hp.stk_all _ (by simp)).sub_left sub
  · exact disj32 (.inr (by rw [sub_nat (by rw [E_nat hp]; omega_arith), loc_addr hp (by omega_arith)]; omega_arith))
      (by rw [loc_addr hp (by omega_arith)]; omega_arith) (by rw [sub_nat (by rw [E_nat hp]; omega_arith)]; omega_arith)

/-- The locals are kept by writes outside them. -/
theorem lw_keep {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r') {d : Nat}
    (hd : d + 4 ≤ 144) : lw s₀ t d = lw s₀ s d :=
  (f.sub hs).readW (Region.contains_self _ _) (loc_disj hp hd) (by decide)

end

/-- The body's first instruction points `ebp` to the locals. -/
theorem inv_start {s₀ : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = (entry s₀).mem → (∀ r, r ≠ .ebp → t.gpr r = (entry s₀).gpr r) →
      WP isa (.block is) t Q) :
    WP isa (.block (.mov .ebp (.reg .esp) :: is)) (entry s₀) Q :=
  VG.X86.Wp.wp_mov fun t u => k t
    ⟨by rw [u.other _ (by decide), entry_esp], by rw [u.gpr, entry_esp], by rw [u.rd, entry_rd],
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
  divisor : lw s₀ s divisorOff = BitVec.ofNat 32 (4 * lanesN s₀)
  segLen : lw s₀ s segLenOff = BitVec.ofNat 32 (prm s₀).segmentLen
  laneLen : lw s₀ s laneLenOff = BitVec.ofNat 32 (prm s₀).laneLen
  stride : lw s₀ s strideOff = BitVec.ofNat 32 ((prm s₀).laneLen * 1024)

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
      omega_arith
    refine wp_add fun s₁ u₁ _ => dbl_ok (s := s₁) n ?_ fun t ht kt => k t ?_
      ((Divide.Keep.of_upd u₁ (by simp)).trans kt)
    · rw [u₁.gpr, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega_arith), ← Nat.two_mul, Nat.mul_comm 2]
      rw [e] at hn; exact hn
    · rw [ht, u₁.gpr, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega_arith), ← Nat.two_mul, Nat.mul_comm 2, e]

theorem lw_mem {s₀ s t : State} (h : t.mem = s.mem) (d : Nat) : lw s₀ t d = lw s₀ s d := by
  simp only [lw, h]

theorem Inv.keep {s₀ s t : State} (h : Inv s₀ s) (k : Divide.Keep s t) : Inv s₀ t :=
  h.step (k.other _ (by decide) (by decide) (by decide)) (k.other _ (by decide) (by decide) (by decide))
    k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem parameters_ok {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → Prm s₀ t → WP isa (.block is) t Q) :
    WP isa (.block ((.mov .ebp (.reg .esp) :: parameters) ++ is)) (entry s₀) Q := by
  have hL := hp.lanes_lt
  have hL1 := hp.lanes_pos
  have hBl := hp.blocks_lt
  have hb := hp.blocks_eq
  have hseg := hp.segLen_eq
  have hlane := hp.laneLen_eq
  simp only [parameters, Impl.Argon2.X86.Derive.fr, List.cons_append, List.append_assoc]
  refine inv_start fun s₁ i₁ _ _ => ?_
  refine wp_ldarg hp i₁ (i := Impl.Argon2.X86.Derive.lanesArg) (by decide) fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide) (by decide)
  refine wp_add fun s₃ u₃ _ => wp_add fun s₄ u₄ _ => ?_
  have i₄ := (i₂.upd u₃ (by decide) (by decide)).upd u₄ (by decide) (by decide)
  have e₄ : (s₄.gpr .eax).toNat = 4 * lanesN s₀ := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr]
    simp only [BitVec.toNat_add]
    show (((arg s₀ 7).toNat + (arg s₀ 7).toNat) % 2 ^ 32 + ((arg s₀ 7).toNat + (arg s₀ 7).toNat) % 2 ^ 32)
      % 2 ^ 32 = 4 * (arg s₀ 7).toNat
    have : (arg s₀ 7).toNat < 2 ^ 24 := hL
    omega_arith
  refine wp_stloc hp i₄ (d := divisorOff) (by decide) fun s₅ i₅ v₅ _ g₅ _ => ?_
  refine wp_ldarg hp i₅ (i := Impl.Argon2.X86.Derive.memoryCostArg) (by decide) fun s₆ u₆ => ?_
  have i₆ := i₅.upd u₆ (by decide) (by decide)
  have d₆ : lw s₀ s₆ divisorOff = s₄.gpr .eax := by rw [lw_mem u₆.mem, v₅]
  refine Divide.code_ok (D := s₄.gpr .eax) (by rw [e₄]; omega_arith) (by rw [e₄]; omega_arith) i₆.ebp
    (loc_in' hp i₆ (by decide)) d₆ fun s₇ c₇ _ k₇ => ?_
  have i₇ := i₆.keep k₇
  rw [u₆.gpr, e₄] at c₇
  have c₇' : (s₇.gpr .ecx).toNat = (prm s₀).segmentLen := by rw [c₇, hseg]; rfl
  refine wp_stloc hp i₇ (d := segLenOff) (by decide) fun s₈ i₈ v₈ o₈ g₈ _ => ?_
  have hll : (prm s₀).laneLen ≤ blocksN s₀ :=
    Nat.le_trans (Nat.le_mul_of_pos_left _ hL1) (Nat.le_of_eq hb.symm)
  have hsegL : (prm s₀).laneLen * 1024 + 16384 ≤ 2 ^ 32 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right 1024 hll) _) hBl
  refine wp_add fun s₉ u₉ _ => wp_add fun s₁₀ u₁₀ _ => ?_
  have i₁₀ := (i₈.upd u₉ (by decide) (by decide)).upd u₁₀ (by decide) (by decide)
  have e₁₀ : (s₁₀.gpr .ecx).toNat = (prm s₀).laneLen := by
    rw [u₁₀.gpr, u₉.gpr, g₈]
    simp only [BitVec.toNat_add, c₇']
    omega_arith
  refine wp_stloc hp i₁₀ (d := laneLenOff) (by decide) fun s₁₁ i₁₁ v₁₁ o₁₁ g₁₁ _ => ?_
  refine dbl_ok 10 (by rw [g₁₁, e₁₀]; omega_arith) fun s₁₂ e₁₂ k₁₂ => ?_
  have i₁₂ := i₁₁.keep k₁₂
  refine wp_stloc hp i₁₂ (d := strideOff) (by decide) fun s₁₃ i₁₃ v₁₃ o₁₃ _ _ => k s₁₃ i₁₃ ⟨?_, ?_, ?_, ?_⟩
  · rw [o₁₃ _ (by decide) (by decide), lw_mem k₁₂.mem, o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem,
      lw_mem u₉.mem, o₈ _ (by decide) (by decide), lw_mem k₇.mem, lw_mem u₆.mem, v₅]
    exact BitVec.eq_of_toNat_eq (by rw [e₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)])
  · rw [o₁₃ _ (by decide) (by decide), lw_mem k₁₂.mem, o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem,
      lw_mem u₉.mem, v₈]
    exact BitVec.eq_of_toNat_eq (by rw [c₇', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)])
  · rw [o₁₃ _ (by decide) (by decide), lw_mem k₁₂.mem, v₁₁]
    exact BitVec.eq_of_toNat_eq (by rw [e₁₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)])
  · rw [v₁₃]
    exact BitVec.eq_of_toNat_eq (by
      rw [e₁₂, g₁₁, e₁₀, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)])

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
    Region.Sub ⟨(scrP s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ (scrR s₀) := Offset.sub_base _ h

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_mem : scrR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)
theorem mem_mem : memR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)
theorem out_mem : outR s₀ ∈ (entry s₀).wr := wr_mem s₀ (by rw [hp.wr]; simp)


/-- The 60 bytes below the locals that H′'s macros use are outside the body's other regions. -/
theorem below60_call : Region.Sub (VG.X86.below (E s₀) 60) (callR s₀) :=
  VG.X86.below_sub (by decide) (by rw [E_nat hp]; have := hp.esp_lo; omega_arith)

theorem ctx {s : State} (h : Inv s₀ s) (hb : s.gpr .ebx = scrP s₀) : Ctx (scrP s₀) (E s₀) s := by
  have := hp.scr_fits
  refine ⟨hb, h.esp, by omega_arith, by rw [E_nat hp]; have := hp.esp_lo; omega_arith,
    by have := E_hi hp; omega_arith, ?_, ?_⟩
  · rw [h.wr]
    exact (Covers.of_sub (rs' := [scrR s₀]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
      (fun a n ⟨r, hr, hc⟩ => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact scr_mem hp, hc⟩)
  · exact ((hp.stk_all (scrR s₀) (by simp)).sub_left fun a ha => call_stk hp a (below60_call hp a ha)).sub_right
      (Region.sub_prefix (by decide))

/-- What H′'s macros keep keeps the body's invariant and the locals. -/
theorem Inv.keeps {s t : State} (h : Inv s₀ s) (k : Keeps (scrP s₀) (E s₀) s t) :
    Inv s₀ t ∧ ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d := by
  have sub : ∀ r ∈ [(⟨(scrP s₀).setWidth 64, 832⟩ : Region), VG.X86.below (E s₀) 60],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨callR s₀, by simp, below60_call hp⟩
  refine ⟨h.step k.esp k.ebp k.rd k.wr (k.frame.sub fun r hr => ?_), fun d hd => lw_keep hp k.frame sub hd⟩
  obtain ⟨r', hr', hs⟩ := sub r hr
  refine ⟨r', ?_, hs⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl <;> simp

end

/-! ## The hash macros, with `Keeps` -/

section
open VG.Spec.Blake2

variable {B E : BitVec 32} {s : State} (c : Ctx B E s)
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
