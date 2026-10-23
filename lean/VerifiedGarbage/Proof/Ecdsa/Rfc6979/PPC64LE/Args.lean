module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on PPC64LE: the blocks setting a call's arguments

The frame's base in `r11` and `scratch` in `r12` (`scrBase_ok`), and the
arguments of HMAC's `init` (`args₁_ok`), of the streaming `update`, with the
data at the frame's `V` or at `scratch + sMsg` (`args₂V_ok`, `args₂M_ok`),
and of HMAC's `finalize` (`args₃_ok`): each keeps `Ctx` and memory, and
writes only registers that are not callee-saved.
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

/-- The arguments of HMAC's `init`. -/
theorem args₁_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {D : Nat} (hD : D < 2 ^ 15) :
    WP isa (.block (Cfg.hmacArgs₁ D)) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧ Kp argRegs t t' ∧
      t'.gpr .r3 = L.scr + BitVec.ofNat 64 0 ∧ t'.gpr .r4 = L.scr + BitVec.ofNat 64 192 ∧
      t'.gpr .r5 = L.B + BitVec.ofNat 64 128 ∧ t'.gpr .r6 = BitVec.ofNat 64 D ∧
      t'.gpr .r7 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.hmacArgs₁, WP.block_append_iff]
  refine WP.mono (scrBase_ok hL hc) fun t₁ ⟨hc₁, m₁, k₁, b₁, s₁⟩ => ?_
  refine stepAddi (by decide) (by decide) fun t₂ k₂ m₂ v₂ => ?_
  refine stepAddi (by decide) (by decide) fun t₃ k₃ m₃ v₃ => ?_
  refine stepAddSp (by decide) fun t₄ k₄ m₄ v₄ => ?_
  refine stepLi hD fun t₅ k₅ m₅ v₅ => ?_
  refine stepAddi (by decide) (by decide) fun t₆ k₆ m₆ v₆ => wp_nil ?_
  have K : Kp argRegs t₁ t₆ :=
    ((((k₂.mono.trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono)
  refine ⟨hc₁.kp hL K (by rw [m₆, m₅, m₄, m₃, m₂]), by rw [m₆, m₅, m₄, m₃, m₂, m₁], (k₁.mono.trans K), ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), v₂, s₁]; rfl
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), v₃, k₂.gpr _ (by decide), s₁]; rfl
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), v₄, k₃.sp, k₂.sp, hc₁.sp, fr_add]; rfl
  · rw [k₆.gpr _ (by decide), v₅]
  · rw [v₆, k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁]; rfl

/-- The arguments of the streaming `update`, with the data at `da`, which
`dataA` sets `r5` to, writing only `r5` (from `scratch` in `r12`). -/
theorem args₂_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {B len : Nat} (hB : B < 2 ^ 15)
    (hlen : len < 2 ^ 15) {dataA : List Instr} {da : Addr}
    (hdA : ∀ u, Ctx L g lr m₀ u → u.gpr .r12 = L.scr → WP isa (.block dataA) u fun u' =>
      Kp [.r5] u u' ∧ u'.mem = u.mem ∧ u'.gpr .r5 = da) :
    WP isa (.block (Cfg.hmacArgs₂ B dataA len)) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧
      Kp argRegs t t' ∧ t'.gpr .r3 = L.scr + BitVec.ofNat 64 0 ∧ t'.gpr .r4 = BitVec.ofNat 64 B ∧
      t'.gpr .r5 = da ∧ t'.gpr .r6 = BitVec.ofNat 64 len ∧ t'.gpr .r7 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.hmacArgs₂, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (scrBase_ok hL hc) fun t₁ ⟨hc₁, m₁, k₁, b₁, s₁⟩ => ?_
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine stepAddi (by decide) (by decide) fun t₂ k₂ m₂ v₂ => ?_
  refine stepLi hB fun t₃ k₃ m₃ v₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hdA t₃ (hc₁.kp hL (rs := [.r3, .r4]) (k₂.mono.trans k₃.mono) (by rw [m₃, m₂]))
    (by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁])) fun t₄ ⟨k₄, m₄, v₄⟩ => ?_
  refine stepLi hlen fun t₅ k₅ m₅ v₅ => ?_
  refine stepAddi (by decide) (by decide) fun t₆ k₆ m₆ v₆ => wp_nil ?_
  have K : Kp argRegs t₁ t₆ :=
    ((((k₂.mono.trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono)
  refine ⟨hc₁.kp hL K (by rw [m₆, m₅, m₄, m₃, m₂]), by rw [m₆, m₅, m₄, m₃, m₂, m₁], (k₁.mono.trans K), ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), v₂, s₁]; rfl
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), v₃]
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), v₄]
  · rw [k₆.gpr _ (by decide), v₅]
  · rw [v₆, k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁]; rfl

/-- The data at `V`. -/
theorem dataV_ok {t : State} (hc : Ctx L g lr m₀ t) (u : State) (hu : u.sp = t.sp) :
    WP isa (.block [.addSp .r5 fV]) u fun u' => Kp [.r5] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .r5 = L.B + BitVec.ofNat 64 192 :=
  stepAddSp (by decide) fun u' k m v => wp_nil ⟨k, m, by rw [v, hu, hc.sp, fr_add]; rfl⟩

/-- The data at `scratch + sMsg`. -/
theorem dataM_ok (u : State) (hu : u.gpr .r12 = L.scr) :
    WP isa (.block [.addi .r5 .r12 sMsg]) u fun u' => Kp [.r5] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .r5 = L.scr + BitVec.ofNat 64 2256 :=
  stepAddi (by decide) (by decide) fun u' k m v => wp_nil ⟨k, m, by rw [v, hu]; rfl⟩

/-- The arguments of HMAC's `finalize`. -/
theorem args₃_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {B len dst : Nat} (hBl : B + len < 2 ^ 15)
    (hdst : dst < 2 ^ 15) :
    WP isa (.block (Cfg.hmacArgs₃ B len dst)) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧
      Kp argRegs t t' ∧ t'.gpr .r3 = L.scr + BitVec.ofNat 64 0 ∧ t'.gpr .r4 = L.scr + BitVec.ofNat 64 192 ∧
      t'.gpr .r5 = BitVec.ofNat 64 (B + len) ∧ t'.gpr .r6 = L.B + BitVec.ofNat 64 (96 + dst) ∧
      t'.gpr .r7 = L.scr + BitVec.ofNat 64 384 := by
  rw [Cfg.hmacArgs₃, WP.block_append_iff]
  refine WP.mono (scrBase_ok hL hc) fun t₁ ⟨hc₁, m₁, k₁, b₁, s₁⟩ => ?_
  refine stepAddi (by decide) (by decide) fun t₂ k₂ m₂ v₂ => ?_
  refine stepAddi (by decide) (by decide) fun t₃ k₃ m₃ v₃ => ?_
  refine stepLi hBl fun t₄ k₄ m₄ v₄ => ?_
  refine stepAddSp hdst fun t₅ k₅ m₅ v₅ => ?_
  refine stepAddi (by decide) (by decide) fun t₆ k₆ m₆ v₆ => wp_nil ?_
  have K : Kp argRegs t₁ t₆ :=
    ((((k₂.mono.trans k₃.mono).trans k₄.mono).trans k₅.mono).trans k₆.mono)
  refine ⟨hc₁.kp hL K (by rw [m₆, m₅, m₄, m₃, m₂]), by rw [m₆, m₅, m₄, m₃, m₂, m₁], (k₁.mono.trans K), ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), v₂, s₁]; rfl
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), v₃, k₂.gpr _ (by decide), s₁]; rfl
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), v₄]
  · rw [k₆.gpr _ (by decide), v₅, k₄.sp, k₃.sp, k₂.sp, hc₁.sp, fr_add]
  · rw [v₆, k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), s₁]; rfl

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
