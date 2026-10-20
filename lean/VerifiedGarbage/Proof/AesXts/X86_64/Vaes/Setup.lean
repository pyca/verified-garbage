module
public import VerifiedGarbage.Proof.AesXts.X86_64.Steps
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Loop

import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# One-pass XTS-AES on x86-64: the arguments and the first eight tweaks

`enter` moves the arguments and loads the tweak into `rax` and `rcx`; `gen`
stores the tweaks of blocks `0 … 7` at `scratch + 256`, multiplying by `α`
in registers between them (`genStep_ok`, `gen_ok`), and puts the last round
key's address in `r10` (`gen_all_ok`). `SInv`: the state during, and
`SInvK` after, from which `GInv 0 0` follows for anything the rounds need
that it keeps.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0)
open VG.Impl.AesXts.X86_64Vaes (bufOff enter mulAr genStep gen)
open VG.X86_64.RegUpd
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at ofInt_natCast)

/-- During `gen`, after `n` tweaks. -/
structure SInv (s₀ : State) (n : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = S s₀
  r9 : s.gpr .r9 = BitVec.ofNat 64 (N s₀)
  r11 : s.gpr .r11 = Dp s₀
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scrR s₀] s₀.mem s.mem
  buf : ∀ j < n, bytesAt s.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) j
  rdx : s.gpr .rdx = Iv s₀
  tw : tw (s.gpr .rax) (s.gpr .rcx) = Spec.Xts.next (iv0 s₀) n

/-- After `gen`: the tweaks, and the last round key's address in `r10`. -/
def SInvK (s₀ s : State) : Prop := SInv s₀ 8 s ∧ s.gpr .r10 = W s₀ + BitVec.ofNat 64 (16 * R s₀)

theorem mulAr_ok (s : State) :
    ∃ s', runBlock isa mulAr s = some s' ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.gpr .rax = (s.gpr .rax <<< 1) ^^^ (if (s.gpr .rcx).msb then (0x87 : BitVec 64) else 0) ∧
      s'.gpr .rcx = (s.gpr .rcx <<< 1) ||| (if (s.gpr .rax).msb then (1 : BitVec 64) else 0) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, mulAr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags, cf_setReg, cf_arithFlags]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ => ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, h₁, h₂, h₃]
  · simp only [gpr_setReg, ↓reduceIte, carry_self, add_self, mask_87]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, carry_self, carry_self_c, add_self,
      shl_add_bit]

theorem genStep_ok {s₀ : State} (hp : UPre s₀) {n : Nat} (hn : n < 8) {s : State} (h : SInv s₀ n s) :
    WP isa (.block (genStep n)) s (SInv s₀ (n + 1)) := by
  have hsw := hp.scr_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have a0 : s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 16 * n : Nat) : Int) = slot s₀ n := by
    rw [h.r8, ofInt_natCast]
  have a8 : s.gpr .r8 + BitVec.ofInt 64 ((bufOff + 16 * n + 8 : Nat) : Int) = slot s₀ n + BitVec.ofNat 64 8 := by
    rw [h.r8, ofInt_natCast, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
  have in0 : InRegions s.wr (slot s₀ n) 8 := ⟨scrR s₀, by rw [hW]; simp,
    Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩
  have in8 : InRegions s.wr (slot s₀ n + BitVec.ofNat 64 8) 8 := ⟨scrR s₀, by rw [hW]; simp, by
    rw [slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩
  rw [genStep, WP.block_append_iff]
  have st₁ : WP isa (.block [.store (at_ .r8 (bufOff + 16 * n)) .rax, .store (at_ .r8 (bufOff + 16 * n + 8)) .rcx]) s
      fun s₁ => s₁.mem = (s.mem.writeW (slot s₀ n) (s.gpr .rax)).writeW (slot s₀ n + BitVec.ofNat 64 8) (s.gpr .rcx) ∧
        s₁.gpr = s.gpr ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_at, a0, a8, in0, in8, ↓reduceIte,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, trivial, trivial⟩
  refine WP.mono st₁ fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => ?_
  obtain ⟨s₂, run₂, g₂, rax₂, rcx₂, m₂, rd₂, wr₂⟩ := mulAr_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have fS : Frame [⟨slot s₀ n, 16⟩] s.mem s₂.mem := by rw [m₂, m₁]; exact AesCbc.frame_store2 _ _ _
  have hg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [g₂ r h1 h2 h3, g₁]
  refine ⟨by rw [hg _ (by decide) (by decide) (by decide), h.r8], by rw [hg _ (by decide) (by decide) (by decide), h.r9],
    by rw [hg _ (by decide) (by decide) (by decide), h.r11],
    fun r h1 h2 h3 h4 h5 h6 h7 => by rw [hg r h1 h2 h6, h.keep r h1 h2 h3 h4 h5 h6 h7],
    by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr],
    h.frame.trans (fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, slot_scr (j := n) (by omega)⟩), fun j hj => ?_,
    by rw [hg _ (by decide) (by decide) (by decide), h.rdx], ?_⟩
  · by_cases hjn : j = n
    · subst hjn
      rw [m₂, m₁, Proof.Cmac.bytesAt_store2, ← h.tw]
    · rw [AesCbc.X86_64.bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by simp only [bufOff]; omega) (by simp only [bufOff]; omega))
        (by decide), h.buf j (by omega)]
  · rw [rax₂, rcx₂, mulAlpha_le8, g₁, h.tw]; rfl

theorem gen_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : SInv s₀ 0 s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap genStep)) s (SInv s₀ n)
  | 0, _ => WP.block_nil h
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (gen_ok hp h n (by omega)) fun s₁ h₁ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact genStep_ok hp (by omega) h₁

/-- The last round key's address, `rdi + 16 · rounds`, into `r10`. -/
theorem lastKey_ok {s₀ : State} {s : State} (h : SInv s₀ 8 s) :
    WP isa (.block ([.mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
      .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)] : List Instr)) s
      (SInvK s₀) := by
  have hrsi := h.keep .rsi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hrdi := h.keep .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    arithFlags, State.setFlags, State.setReg, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [h.r8], by simp [h.r9], by simp [h.r11], fun r h1 h2 h3 h4 h5 h6 h7 => by
    simp [h6, h.keep r h1 h2 h3 h4 h5 h6 h7], h.rd, h.wr, h.frame, h.buf, by simp [h.rdx], by simpa using h.tw⟩, ?_⟩
  simp only [↓reduceIte, hrsi, hrdi, W, R]
  bv_omega

theorem gen_all_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : SInv s₀ 0 s) :
    WP isa (.block gen) s (SInvK s₀) := by
  rw [gen, WP.block_append_iff]
  exact WP.mono (gen_ok hp h 8 (Nat.le_refl _)) fun s₁ h₁ => lastKey_ok h₁

/-- The arguments moved. -/
theorem enter_ok {s₀ : State} (hp : UPre s₀) : WP isa (.block enter) s₀ (SInv s₀ 0) := by
  have hIv8 : InRegions (s₀.rd ++ s₀.wr) (Iv s₀ + BitVec.ofNat 64 8) 8 := ⟨ivR s₀, by rw [hp.wr]; simp, AesCbc.X86_64.cIv8⟩
  have z0 : BitVec.ofInt 64 ((0 : Nat) : Int) = 0 := rfl
  have z8 : BitVec.ofInt 64 ((8 : Nat) : Int) = BitVec.ofNat 64 8 := rfl
  have hIv : InRegions (s₀.rd ++ s₀.wr) (Iv s₀) 8 := ⟨ivR s₀, by rw [hp.wr]; simp, AesCbc.X86_64.cIv0⟩
  have hIv0 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdx + 0) 8 := by simpa using hIv
  apply WP.of_runBlock
  simp only [enter, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.setReg, State.load64, ea_at, z0, z8, hIv0, hIv8,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by simp, by simp, by simp, fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h1, h2, h4, h5, h7],
    rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _), by simp, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte]
  rw [show s₀.gpr .rdx + 0 = Iv s₀ by simp, tw_readW]
  rfl

end VG.Proof.AesXts.X86_64.Vaes
