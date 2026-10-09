import VerifiedGarbage.Proof.Argon2.X86.Divide
import VerifiedGarbage.Proof.Argon2.X86.HPrime.Verified
import VerifiedGarbage.Proof.Argon2.X86.CompressVerified
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Impl.Argon2.X86.Derive
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.TCB.X86.Target

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
  · exact Offset.disjoint_of_le (by simp only [toNat_w]; omega) (by simp only [toNat_w]; omega)
  · exact (Offset.disjoint_of_le (r₁ := ⟨y.setWidth 64, m⟩) (by simp only [toNat_w]; omega)
      (by simp only [toNat_w]; omega)).symm

theorem contains32 {x y : BitVec 32} {n m : Nat} (h₁ : y.toNat ≤ x.toNat)
    (h₂ : x.toNat + n ≤ y.toNat + m) :
    Region.Contains ⟨y.setWidth 64, m⟩ (x.setWidth 64) n := by
  simp only [Region.Contains]
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, toNat_w]; exact h₁), toNat_w, toNat_w]
  omega

theorem sub32 {x y : BitVec 32} {n m : Nat} (h₁ : y.toNat ≤ x.toNat)
    (h₂ : x.toNat + n ≤ y.toNat + m) :
    Region.Sub ⟨x.setWidth 64, n⟩ ⟨y.setWidth 64, m⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  have hx := toNat_w x
  have hy := toNat_w y
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
  · omega
  have := disjoint_total hp.mem_scr (N := 2 ^ 32)
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
  rw [BitVec.toNat_add, sub_toNat hlo, sub_toNat (by omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := k) (by omega)]
  omega

theorem frames_ok {Q : State → Prop} (hsp : NoSp body)
    (hb : WP isa body (entry s₀) fun t => BodyDone s₀ t ∧ Q t)
    (hQ : ∀ t u, Q t → u.mem = t.mem → Q u) :
    WP isa derive s₀ fun u => abiPreserved s₀ u ∧ Q u := by
  have hE := (E0 s₀).isLt
  have hlo' : 160 ≤ (s₀.gpr .esp).toNat := hlo
  have nf : ∀ {r : Reg} {k : Nat} {rs : List Reg} {b : Prog isa}, r ≠ .esp → NoSp b →
      NoSp (.frame (.push rs) b (.pop r k)) := fun {r k rs b} hr hb i hi => by
    simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | hi) | rfl
    · rfl
    · exact hb i hi
    · simp [Taint.clobbers, Taint.dst, hr]
  have e1 : ((pushed [.ebp] s₀).gpr .esp).toNat = (E0 s₀).toNat - 4 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega)]; rfl
  have e2 : ((pushed [.edi] (pushed [.ebp] s₀)).gpr .esp).toNat = (E0 s₀).toNat - 8 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega), e1]; rfl
  have e3 : ((pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))).gpr .esp).toNat = (E0 s₀).toNat - 12 := by
    rw [pushed_esp, sub_toNat (by simp only [List.length_singleton]; omega), e2]; rfl
  have e4 : ((pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))).gpr .esp).toNat =
      (E0 s₀).toNat - 16 := by
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
  have add4 : ∀ a : Nat, E s₀ + BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * 1) =
      E s₀ + BitVec.ofNat 32 (a + 4) := fun a => by rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  set t₁ := popped .eax (List.replicate (locals / 4) Reg.eax).length t with ht₁
  have sp₁ : t₁.gpr .esp = E s₀ + BitVec.ofNat 32 144 := by
    rw [ht₁, popped_esp, d.esp]; simp [locals]
  set t₂ := popped .ebx [Reg.ebx].length t₁ with ht₂
  have sp₂ : t₂.gpr .esp = E s₀ + BitVec.ofNat 32 148 := by
    rw [ht₂, popped_esp, sp₁]; exact add4 144
  set t₃ := popped .esi [Reg.esi].length t₂ with ht₃
  have sp₃ : t₃.gpr .esp = E s₀ + BitVec.ofNat 32 152 := by
    rw [ht₃, popped_esp, sp₂]; exact add4 148
  set t₄ := popped .edi [Reg.edi].length t₃ with ht₄
  have sp₄ : t₄.gpr .esp = E s₀ + BitVec.ofNat 32 156 := by
    rw [ht₄, popped_esp, sp₃]; exact add4 152
  set u := popped .ebp [Reg.ebp].length t₄ with hu
  have spu : u.gpr .esp = E0 s₀ := by
    rw [hu, popped_esp, sp₄, List.length_singleton, add4 156, E_sub hlo 160 (by decide)]; simp
  have mu : u.mem = t.mem := by simp [hu, ht₄, ht₃, ht₂, ht₁]
  have b₂ : t₂.gpr .ebx = s₀.gpr .ebx := by
    rw [ht₂, List.length_singleton, popped_one_self _ _ (by decide), sp₁, ht₁, popped_mem]
    exact d.saved 0 (by decide)
  have b₃ : t₃.gpr .esi = s₀.gpr .esi := by
    rw [ht₃, List.length_singleton, popped_one_self _ _ (by decide), sp₂, ht₂, popped_mem, ht₁,
      popped_mem]
    exact d.saved 1 (by decide)
  have b₄ : t₄.gpr .edi = s₀.gpr .edi := by
    rw [ht₄, List.length_singleton, popped_one_self _ _ (by decide), sp₃, ht₃, popped_mem, ht₂,
      popped_mem, ht₁, popped_mem]
    exact d.saved 2 (by decide)
  have b₅ : u.gpr .ebp = s₀.gpr .ebp := by
    rw [hu, List.length_singleton, popped_one_self _ _ (by decide), sp₄, ht₄, popped_mem, ht₃,
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
abbrev locR : Region := ⟨(E s₀).setWidth 64, 144⟩

/-- The stack below the locals. -/
abbrev callR : Region := below (E s₀) 84

/-- The regions the body may write. -/
abbrev bodyW : List Region := [memR s₀, scrR s₀, outR s₀, locR s₀, callR s₀]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem E_toNat : (E s₀).toNat = (E0 s₀).toNat - 160 := sub_toNat (by have := hp.esp_lo; omega)

end

theorem entry_esp (s₀ : State) : (entry s₀).gpr .esp = E s₀ := by
  simp only [entry, pushed_esp, List.length_singleton, List.length_replicate, BitVec.sub_sub,
    BitVec.ofNat_add_ofNat]

theorem entry_gpr (s₀ : State) {r : Reg} (h : r ≠ .esp) : (entry s₀).gpr r = s₀.gpr r := by
  simp only [entry, pushed_gpr _ _ h]

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
  have hE := (s₀.gpr .esp).isLt
  have hE0 : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  -- Each push writes within the 160 bytes below `esp` on entry.
  have step : ∀ {rs : List Reg} {s : State}, .esp ∉ rs → 4 * rs.length ≤ (s.gpr .esp).toNat →
      (s₀.gpr .esp).toNat - 160 ≤ (s.gpr .esp).toNat - 4 * rs.length →
      (s.gpr .esp).toNat ≤ (s₀.gpr .esp).toNat → Frame [below (E0 s₀) 160] s.mem (pushed rs s).mem :=
    fun {rs s} hrs hn h₁ h₂ => (pushed_frame hrs hn).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, sub32 ?_ ?_⟩
      · rw [sub_nat hn, sub_nat (by omega)]; omega
      · rw [sub_nat hn, sub_nat (by omega)]; omega
  -- The stack pointer after each push.
  have n₁ : ((pushed [.ebp] s₀).gpr .esp).toNat = (s₀.gpr .esp).toNat - 4 :=
    pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo])
  have n₂ : ((pushed [.edi] (pushed [.ebp] s₀)).gpr .esp).toNat = (s₀.gpr .esp).toNat - 8 := by
    rw [pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo, n₁]), n₁]; rfl
  have n₃ : ((pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))).gpr .esp).toNat =
      (s₀.gpr .esp).toNat - 12 := by
    rw [pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo, n₂]), n₂]; rfl
  have n₄ : ((pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))).gpr .esp).toNat =
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
  exact disj32 (.inr (by rw [sub_nat hn]; omega)) ha' (by rw [sub_nat hn]; have := (s.gpr .esp).isLt; omega)

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
  have n₁ : ((pushed [.ebp] s₀).gpr .esp).toNat = (s₀.gpr .esp).toNat - 4 :=
    pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo])
  have n₂ : ((pushed [.edi] (pushed [.ebp] s₀)).gpr .esp).toNat = (s₀.gpr .esp).toNat - 8 := by
    rw [pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo, n₁]), n₁]; rfl
  have n₃ : ((pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))).gpr .esp).toNat =
      (s₀.gpr .esp).toNat - 12 := by
    rw [pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo, n₂]), n₂]; rfl
  have n₄ : ((pushed [.ebx] (pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀)))).gpr .esp).toNat =
      (s₀.gpr .esp).toNat - 16 := by
    rw [pushed_esp_nat (by simp only [List.length_singleton]; omega_using [hlo, n₃]), n₃]; rfl
  have k₁ : 4 * [Reg.ebx].length ≤ ((pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))).gpr .esp).toNat := by
    rw [List.length_singleton, n₃]; omega_using [hlo]
  have k₂ : 4 * [Reg.esi].length ≤ ((pushed [.edi] (pushed [.ebp] s₀)).gpr .esp).toNat := by
    rw [List.length_singleton, n₂]; omega_using [hlo]
  have k₃ : 4 * [Reg.edi].length ≤ ((pushed [.ebp] s₀).gpr .esp).toNat := by
    rw [List.length_singleton, n₁]; omega_using [hlo]
  have sl : (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat = (s₀.gpr .esp).toNat - 16 + 4 * j := by
    have := (s₀.gpr .esp).isLt
    have hlo' : 244 ≤ (E0 s₀).toNat := hp.esp_lo
    have hE0 : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
    rw [add_nat (by rw [sub_nat (by omega_using [hlo'])]; omega_using [hlo', hE0, hi, hj]),
      sub_nat (by omega_using [hlo'])]
    omega_using [hlo', hE0]
  have ha : (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat + 4 ≤ 2 ^ 32 := by rw [sl]; omega_using [hlo, hi, hj]
  have p₃ : 1 ≤ j → ((pushed [.esi] (pushed [.edi] (pushed [.ebp] s₀))).gpr .esp).toNat ≤
      (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat := fun h => by rw [n₃, sl]; omega_using [hlo, h]
  have p₂ : 2 ≤ j → ((pushed [.edi] (pushed [.ebp] s₀)).gpr .esp).toNat ≤
      (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat := fun h => by rw [n₂, sl]; omega_using [hlo, h]
  have p₁ : 3 ≤ j → ((pushed [.ebp] s₀).gpr .esp).toNat ≤
      (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat := fun h => by rw [n₁, sl]; omega_using [hlo, h]
  -- The slot is the word the push of `savedVal j` wrote.
  have w : ∀ (s : State), (s.gpr .esp).toNat = (s₀.gpr .esp).toNat - 12 + 4 * j →
      4 ≤ (s.gpr .esp).toNat ∧ E s₀ + BitVec.ofNat 32 (144 + 4 * j) = s.gpr .esp - BitVec.ofNat 32 4 :=
    fun s h => ⟨by rw [h]; omega_using [hlo],
      BitVec.eq_of_toNat_eq (by rw [sl, sub_nat (by rw [h]; omega_using [hlo]), h]; omega_using [hlo])⟩
  unfold entry slot
  rw [push_keep (by decide) (by simp only [List.length_replicate]; omega_using [hlo, n₄])
    (by rw [n₄, sl]; omega_using [hlo]) ha]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
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
  have := hp.esp_hi; have := hp.esp_lo; rw [sub_nat (by omega)]; omega

/-- The locals and the stack below them lie in the stack the contract reserves. -/
theorem loc_stk {d n : Nat} (h : d + n ≤ 144) :
    Region.Sub ⟨(E s₀ + BitVec.ofNat 32 d).setWidth 64, n⟩ (stkR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE : (E s₀).toNat = (E0 s₀).toNat - 160 := sub_nat (by omega)
  have h1 : (E s₀ + BitVec.ofNat 32 d).toNat = (E0 s₀).toNat - 160 + d := by
    rw [add_nat (by omega), hE]
  have h2 : (E0 s₀ - BitVec.ofNat 32 244).toNat = (E0 s₀).toNat - 244 := sub_nat (by omega)
  exact sub32 (by rw [h1, h2]; omega) (by rw [h1, h2]; omega)

theorem call_stk : Region.Sub (callR s₀) (stkR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE : (E s₀).toNat = (E0 s₀).toNat - 160 := sub_nat (by omega)
  have h1 : (E s₀ - BitVec.ofNat 32 84).toNat = (E0 s₀).toNat - 244 := by rw [sub_nat (by omega), hE]; omega
  have h2 : (E0 s₀ - BitVec.ofNat 32 244).toNat = (E0 s₀).toNat - 244 := sub_nat (by omega)
  exact sub32 (by rw [h1, h2]) (by rw [h1, h2]; omega)

/-- A word of the locals. -/
theorem loc_in {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions s.wr (addr (E s₀) d) 4 := by
  have := E_hi hp
  rw [h.wr]
  exact ⟨locR s₀, loc_mem s₀, contains32 (by rw [add_nat (by omega)]; omega)
    (by rw [add_nat (by omega)]; omega)⟩

theorem loc_in' {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := loc_in hp h hd
  ⟨r, List.mem_append_right _ hr, hc⟩

end


section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem E_nat : (E s₀).toNat = (E0 s₀).toNat - 160 := sub_nat (by have := hp.esp_lo; omega)

/-- A range within the 160 bytes the frames use. -/
theorem frame_stk {d n : Nat} (h : d + n ≤ 160) :
    Region.Sub ⟨(E s₀ + BitVec.ofNat 32 d).setWidth 64, n⟩ (stkR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have h1 : (E s₀ + BitVec.ofNat 32 d).toNat = (E0 s₀).toNat - 160 + d := by
    rw [add_nat (by rw [E_nat hp]; omega), E_nat hp]
  have h2 : (E0 s₀ - BitVec.ofNat 32 244).toNat = (E0 s₀).toNat - 244 := sub_nat (by omega)
  exact sub32 (by rw [h1, h2]; omega) (by rw [h1, h2]; omega)

/-- What lies above the locals is outside the body's regions. -/
theorem above_disj {a : BitVec 32} {n : Nat} (ha : (E s₀).toNat + 144 ≤ a.toNat)
    (ha' : a.toNat + n ≤ (E0 s₀).toNat + 76)
    (hm : Region.Disjoint ⟨a.setWidth 64, n⟩ (memR s₀)) (hs : Region.Disjoint ⟨a.setWidth 64, n⟩ (scrR s₀))
    (ho : Region.Disjoint ⟨a.setWidth 64, n⟩ (outR s₀)) :
    ∀ r ∈ bodyW s₀, Region.Disjoint ⟨a.setWidth 64, n⟩ r := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := E_nat hp
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hm
  · exact hs
  · exact ho
  · exact disj32 (.inr (by omega)) (by omega) (by omega)
  · exact disj32 (.inr (by rw [sub_nat (by omega)]; omega)) (by omega)
      (by rw [sub_nat (by omega)]; omega)

theorem Inv.done {s : State} (h : Inv s₀ s) : BodyDone s₀ s := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := E_nat hp
  have hE' : (E0 s₀ - BitVec.ofNat 32 160).toNat = (E0 s₀).toNat - 160 := sub_nat (by omega)
  refine ⟨h.esp, fun j hj => ?_, ?_⟩
  · have sl : (E s₀ + BitVec.ofNat 32 (144 + 4 * j)).toNat = (E s₀).toNat + (144 + 4 * j) :=
      add_nat (by have := E_hi hp; omega)
    have st := frame_stk hp (d := 144 + 4 * j) (n := 4) (by omega)
    rw [h.frame.readW (r := ⟨slot s₀ j, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
    · exact entry_saved hp hj
    refine above_disj hp (by rw [sl]; omega) (by rw [sl]; omega) ?_ ?_ ?_
    · exact ((hp.stk_all _ (by simp)).sub_left st)
    · exact ((hp.stk_all _ (by simp)).sub_left st)
    · exact ((hp.stk_all _ (by simp)).sub_left st)
  · rw [h.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)]
    · refine entry_frame hp |>.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact disj32 (.inr (by rw [sub_nat (by omega)]; omega)) (by omega) (by rw [sub_nat (by omega)]; omega)
    refine above_disj hp (by omega) (by omega) ?_ ?_ ?_
    · exact hp.ret_w _ (by simp)
    · exact hp.ret_w _ (by simp)
    · exact hp.ret_w _ (by simp)

/-- The arguments' addresses, from `ebp`. -/
theorem arg_addr {i : Nat} (hi : i < 18) :
    addr (E s₀) (Impl.Argon2.X86.Derive.argOff i) = argAddr s₀ i := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := E_nat hp
  simp only [addr, argAddr, Impl.Argon2.X86.Derive.argOff, Impl.Argon2.X86.Derive.locals]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [add_nat (by omega), add_nat (by omega)]
  show (E0 s₀ - BitVec.ofNat 32 160).toNat + _ = (E0 s₀).toNat + _
  rw [sub_nat (by omega)]; omega

theorem arg_word {i : Nat} (hi : i < 18) :
    Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  exact sub32 (by rw [add_nat (by omega), add_nat (by omega)]; omega)
    (by rw [add_nat (by omega), add_nat (by omega)]; omega)

theorem Inv.arg_in {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) (Impl.Argon2.X86.Derive.argOff i)) 4 := by
  rw [arg_addr hp hi, h.rd, hp.rd]
  exact ⟨argR s₀, by simp, arg_word hp hi (argAddr s₀ i) |> fun _ => by
    have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
    exact contains32 (by rw [add_nat (by omega), add_nat (by omega)]; omega)
      (by rw [add_nat (by omega), add_nat (by omega)]; omega)⟩

theorem Inv.arg {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    s.mem.readW (addr (E s₀) (Impl.Argon2.X86.Derive.argOff i)) 32 = arg s₀ i := by
  have := hp.esp_lo; have := hp.esp_hi; have : (E0 s₀).toNat = (s₀.gpr .esp).toNat := rfl
  have hE := E_nat hp
  have ai : (E0 s₀ + BitVec.ofNat 32 (4 + 4 * i)).toNat = (E0 s₀).toNat + 4 + 4 * i := by
    rw [add_nat (by omega)]; omega
  rw [arg_addr hp hi]
  have sub := arg_word hp hi
  rw [h.frame.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
  · refine (entry_frame hp).readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact disj32 (.inr (by rw [sub_nat (by omega), ai]; omega)) (by rw [ai]; omega)
      (by rw [sub_nat (by omega)]; omega)
  refine above_disj hp (by rw [ai]; omega) (by rw [ai]; omega) ?_ ?_ ?_
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub

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
