module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Layout
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step

/-!
# Deterministic ECDSA on PPC64LE: the blocks setting a call's arguments

The frame's base in `r11` and `scratch` in `r12` (`scrBase_ok`), and the
arguments of the streaming `init` (`initArgs_ok`), `update`, with the data
at the address a block sets `r5` to (`updArgs_ok`: in the frame, `dataV_ok`,
or in `scratch`, `dataS_ok`), and `finalize` (`finArgs_ok`); the table's
word `j` into `r12` (`tword_ok`): each keeps `Ctx` and memory, and writes
only registers that are not callee-saved.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- The registers the argument blocks write. -/
abbrev argRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r11, .r12]

/-- The frame's base in `r11` and `scratch` in `r12`. -/
theorem scrBase_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.scrBase) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧ Kp [.r11, .r12] t t' ∧
      t'.gpr .r11 = L.B + BitVec.ofNat 64 96 ∧ t'.gpr .r12 = L.scr := by
  have hnB := hL.nB
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  have hc₁ := hc.kp hL k₁ m₁
  refine stepLd (a := L.B + BitVec.ofNat 64 312) (by decide) (by decide) (by rw [hb, fr_add]; rfl) (hc₁.inFr (by omega) (by omega))
    fun t₂ k₂ m₂ v₂ => wp_nil ?_
  refine ⟨hc₁.kp hL k₂ m₂, by rw [m₂, m₁], (k₁.mono (rs' := [.r11, .r12])).trans (k₂.mono (rs' := [.r11, .r12])), by rw [k₂.gpr _ (by decide), hb], ?_⟩
  rw [v₂, hc₁.pScr]

/-- The state at `scratch + o` in `r3`, after `scrBase`. -/
theorem initArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {o : Nat} (ho : o < 2 ^ 15) :
    WP isa (.block (Cfg.scrBase ++ [.addi .r3 .r12 o])) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧
      Kp argRegs t t' ∧ t'.gpr .r3 = L.scr + BitVec.ofNat 64 o := by
  rw [WP.block_append_iff]
  refine WP.mono (scrBase_ok hL hc) fun t₁ ⟨hc₁, m₁, k₁, b₁, s₁⟩ => ?_
  refine stepAddi (by decide) ho fun t₂ k₂ m₂ v₂ => wp_nil ?_
  exact ⟨hc₁.kp hL k₂ m₂, by rw [m₂, m₁], k₁.mono.trans k₂.mono, by rw [v₂, s₁]⟩

/-- The arguments of the streaming `update`: the state at `scratch + o`
holding `cnt` bytes, the data at `da`, which `dataA` sets `r5` to, writing
only `r5` (from `scratch` in `r12`), its length and the working space. -/
theorem updArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {o cnt len : Nat} (ho : o < 2 ^ 15)
    (hcnt : cnt < 2 ^ 15) (hlen : len < 2 ^ 15) {dataA : List Instr} {da : Addr}
    (hdA : ∀ u, Ctx L g lr m₀ u → u.gpr .r12 = L.scr → WP isa (.block dataA) u fun u' =>
      Kp [.r5] u u' ∧ u'.mem = u.mem ∧ u'.gpr .r5 = da) :
    WP isa (.block (Cfg.updArgs o cnt dataA len)) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧
      Kp argRegs t t' ∧ t'.gpr .r3 = L.scr + BitVec.ofNat 64 o ∧ t'.gpr .r4 = BitVec.ofNat 64 cnt ∧
      t'.gpr .r5 = da ∧ t'.gpr .r6 = BitVec.ofNat 64 len ∧ t'.gpr .r7 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.updArgs, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (scrBase_ok hL hc) fun t₁ ⟨hc₁, m₁, k₁, b₁, s₁⟩ => ?_
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine stepAddi (by decide) ho fun t₂ k₂ m₂ v₂ => ?_
  refine stepLi hcnt fun t₃ k₃ m₃ v₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hdA t₃ (hc₁.kp hL (rs := [.r3, .r4]) (k₂.mono.trans k₃.mono) (by rw [m₃, m₂]))
    (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁])) fun t₄ ⟨k₄, m₄, v₄⟩ => ?_
  refine stepLi hlen fun t₅ k₅ m₅ v₅ => ?_
  refine stepAddi (by decide) (by decide) fun t₆ k₆ m₆ v₆ => wp_nil ?_
  have K : Kp argRegs t₁ t₆ :=
    ((((k₂.mono.trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono)
  refine ⟨hc₁.kp hL K (by rw [m₆, m₅, m₄, m₃, m₂]), by rw [m₆, m₅, m₄, m₃, m₂, m₁], (k₁.mono.trans K), ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), v₂, s₁]
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), v₃]
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), v₄]
  · rw [k₆.gpr _ (by decide), v₅]
  · rw [v₆, k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁]; rfl

/-- The data at `V`. -/
theorem dataV_ok {t : State} (hc : Ctx L g lr m₀ t) (u : State) (hu : u.sp = t.sp) :
    WP isa (.block [.addSp .r5 fV]) u fun u' => Kp [.r5] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .r5 = L.B + BitVec.ofNat 64 192 :=
  stepAddSp (by decide) fun u' k m v => wp_nil ⟨k, m, by rw [v, hu, hc.sp, fr_add]; rfl⟩

/-- The data at `scratch + o`. -/
theorem dataS_ok (u : State) (hu : u.gpr .r12 = L.scr) {o : Nat} (ho : o < 2 ^ 15) :
    WP isa (.block [.addi .r5 .r12 o]) u fun u' => Kp [.r5] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .r5 = L.scr + BitVec.ofNat 64 o :=
  stepAddi (by decide) ho fun u' k m v => wp_nil ⟨k, m, by rw [v, hu]⟩

/-- The arguments of the streaming `finalize`: the state at `scratch + o`
holding `cnt` bytes, the output at `scratch + sTmp` and the working space. -/
theorem finArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {o cnt : Nat} (ho : o < 2 ^ 15)
    (hcnt : cnt < 2 ^ 15) :
    WP isa (.block (Cfg.finArgs o cnt)) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧
      Kp argRegs t t' ∧ t'.gpr .r3 = L.scr + BitVec.ofNat 64 o ∧ t'.gpr .r4 = BitVec.ofNat 64 cnt ∧
      t'.gpr .r5 = L.scr + BitVec.ofNat 64 1920 ∧ t'.gpr .r6 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.finArgs, WP.block_append_iff]
  refine WP.mono (scrBase_ok hL hc) fun t₁ ⟨hc₁, m₁, k₁, b₁, s₁⟩ => ?_
  refine stepAddi (by decide) ho fun t₂ k₂ m₂ v₂ => ?_
  refine stepLi hcnt fun t₃ k₃ m₃ v₃ => ?_
  refine stepAddi (by decide) (by decide) fun t₄ k₄ m₄ v₄ => ?_
  refine stepAddi (by decide) (by decide) fun t₅ k₅ m₅ v₅ => wp_nil ?_
  have K : Kp argRegs t₁ t₅ := (((k₂.mono.trans k₃.mono).trans k₄.mono).trans k₅.mono)
  refine ⟨hc₁.kp hL K (by rw [m₅, m₄, m₃, m₂]), by rw [m₅, m₄, m₃, m₂, m₁], (k₁.mono.trans K), ?_, ?_, ?_, ?_⟩
  · rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), v₂, s₁]
  · rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), v₃]
  · rw [k₅.gpr _ (by decide), v₄, k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁]; rfl
  · rw [v₅, k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁]; rfl

/-- The table's word `j` into `r12`, through its address in the frame: the
word as on entry. -/
theorem tword_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {j : Nat} (hj : 8 * j + 8 ≤ 40) :
    WP isa (.block [.addSp .r12 0, .load .d .r12 .r12 fTab, .load .d .r12 .r12 (8 * j)]) t fun t' =>
      Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧ Kp [.r12] t t' ∧
      t'.gpr .r12 = m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 := by
  have hnB := hL.nB
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r12 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  have hc₁ := hc.kp hL k₁ m₁
  refine stepLd (a := L.B + BitVec.ofNat 64 344) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc₁.inFr (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => ?_
  have hc₂ := hc₁.kp hL k₂ m₂
  have ht : t₂.gpr .r12 = L.tab := by rw [v₂, hc₁.pTab]
  refine stepLd (a := L.tab + BitVec.ofNat 64 (8 * j)) (by decide) ⟨by omega, by omega⟩ (by rw [ht])
    (hc₂.inTab hL hj) fun t₃ k₃ m₃ v₃ => wp_nil ?_
  refine ⟨hc₂.kp hL k₃ m₃, by rw [m₃, m₂, m₁], (k₁.trans k₂).trans k₃, ?_⟩
  rw [v₃, hc₂.tabWord hL hj]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
