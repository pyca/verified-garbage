module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Layout
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Deterministic ECDSA on PPC64LE: steps in the frame, and the entry

`addSp` (`exec_addSp`), addresses in the frame (`fr_add`), the frame's base
in `r11` (`frBase_ok`), and the arguments saved in the frame by `saveArgs`
(`entry_ok`), after which `Ctx` holds.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp wp_step write_gpr)

/-- An address in the frame, from its base. -/
theorem fr_add (B : Addr) (a o : Nat) : B + BitVec.ofNat 64 a + BitVec.ofNat 64 o = B + BitVec.ofNat 64 (a + o) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- `Ctx` through a step that writes registers that are not callee-saved
and no memory. -/
theorem Ctx.kp (hL : L.Ok) {t t' : State} (hc : Ctx L g lr m₀ t) {rs : List Reg} (k : Kp rs t t')
    (hm : t'.mem = t.mem) (hrs : ∀ r ∈ rs, r ∉ preserved := by decide) : Ctx L g lr m₀ t' :=
  hc.regs hL k.rd k.wr hm k.sp fun r hr => k.gpr r fun h => hrs r h hr

/-- The arguments saved in the frame: `Ctx` holds. -/
theorem entry_ok {I : Spec.Ecdsa.Rfc6979.Instance} {s : State}
    (h : (rfcPPC I (400 + extraOf I.hashLen I.ecdsa.curve.len)).pre s) :
    WP isa (.block Impl.Ecdsa.Rfc6979.PPC64LE.Cfg.saveArgs) (entered (lay I.hashLen I.ecdsa.curve.len s).e s)
      (Ctx (lay I.hashLen I.ecdsa.curve.len s) s.gpr s.lr s.mem) := by
  have hL := lay_ok h
  have hsp := entered_sp I.hashLen I.ecdsa.curve.len s
  have hwr := entered_wr I.hashLen I.ecdsa.curve.len s
  have hm := entered_mem I.hashLen I.ecdsa.curve.len s
  have hrd : (entered (lay I.hashLen I.ecdsa.curve.len s).e s).rd = [(lay I.hashLen I.ecdsa.curve.len s).D, (lay I.hashLen I.ecdsa.curve.len s).DG] := by
    rw [entered_rd]; exact h.1
  have hw₀ : s.wr = [(lay I.hashLen I.ecdsa.curve.len s).OUT, (lay I.hashLen I.ecdsa.curve.len s).SCR] := h.2.1
  have hg : ∀ r, r ≠ .r0 → (entered (lay I.hashLen I.ecdsa.curve.len s).e s).gpr r = s.gpr r := fun r hr => entered_gpr _ s hr
  have hspS : s.sp = (lay I.hashLen I.ecdsa.curve.len s).B +
      BitVec.ofNat 64 (400 + (lay I.hashLen I.ecdsa.curve.len s).e) := by
    show s.sp = s.sp - BitVec.ofNat 64 (400 + (lay I.hashLen I.ecdsa.curve.len s).e) +
      BitVec.ofNat 64 (400 + (lay I.hashLen I.ecdsa.curve.len s).e); bv_omega
  have hlr : (lay I.hashLen I.ecdsa.curve.len s).B + BitVec.ofNat 64 (384 + (lay I.hashLen I.ecdsa.curve.len s).e) =
      s.sp - 16 := by
    rw [hspS]; generalize (lay I.hashLen I.ecdsa.curve.len s).e = e
    simp only [← BitVec.ofNat_add_ofNat]; generalize BitVec.ofNat 64 e = E; bv_omega
  obtain ⟨L, hl⟩ : ∃ L, lay I.hashLen I.ecdsa.curve.len s = L := ⟨_, rfl⟩
  rw [hl] at hL hsp hwr hm hrd hw₀ hspS hlr hg ⊢
  have hnB := hL.nB
  have he := L.e_le
  have hw : ∀ d, 128 ≤ d → d + 8 ≤ 352 + L.e → InRegions (entered L.e s).wr (L.B + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => ⟨L.FR, by rw [hwr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
  have hp : ∀ (n : Reg), n ∉ preserved → n ≠ .r0 → (entered L.e s).gpr n = s.gpr n := fun n _ h => hg n h
  have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 400 + L.e → y + 8 ≤ 400 + L.e →
      Mem.Sep (L.B + BitVec.ofNat 64 x) (64 / 8) (L.B + BitVec.ofNat 64 y) (64 / 8) :=
    fun x y h h₁ h₂ => Offset.sep L.B h (by omega) (by omega)
  simp only [Impl.Ecdsa.Rfc6979.PPC64LE.Cfg.saveArgs, Impl.Ecdsa.Rfc6979.PPC64LE.fOut,
    Impl.Ecdsa.Rfc6979.PPC64LE.fD, Impl.Ecdsa.Rfc6979.PPC64LE.fDigest, Impl.Ecdsa.Rfc6979.PPC64LE.fScratch]
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have a₁ : ∀ o, t₁.gpr .r11 + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (96 + o) := fun o => by
    rw [v₁, BitVec.add_zero, hsp, fr_add]
  have w₁ : ∀ d, 128 ≤ d → d + 8 ≤ 352 + L.e → InRegions t₁.wr (L.B + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ => by
    rw [k₁.wr]; exact hw d h₁ h₂
  refine stepStd (a := L.B + BitVec.ofNat 64 336) (by decide) (by decide) (a₁ 240) (w₁ 336 (by omega) (by omega)) fun t₂ k₂ g₂ m₂ => ?_
  refine stepStd (a := L.B + BitVec.ofNat 64 328) (by decide) (by decide) (by rw [g₂]; exact a₁ 232) (by rw [k₂.wr]; exact w₁ 328 (by omega) (by omega))
    fun t₃ k₃ g₃ m₃ => ?_
  refine stepStd (a := L.B + BitVec.ofNat 64 320) (by decide) (by decide) (by rw [g₃, g₂]; exact a₁ 224)
    (by rw [k₃.wr, k₂.wr]; exact w₁ 320 (by omega) (by omega)) fun t₄ k₄ g₄ m₄ => ?_
  refine stepStd (a := L.B + BitVec.ofNat 64 312) (by decide) (by decide) (by rw [g₄, g₃, g₂]; exact a₁ 216)
    (by rw [k₄.wr, k₃.wr, k₂.wr]; exact w₁ 312 (by omega) (by omega)) fun t₅ k₅ g₅ m₅ => ?_
  refine wp_nil ?_
  have r₁ : ∀ r, r ≠ .r11 → r ≠ .r0 → t₁.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [k₁.gpr r (by simp [h₁]), hg r h₂]
  have eOut : L.out = s.gpr .r3 := by rw [← hl]; rfl
  have eD : L.d = s.gpr .r4 := by rw [← hl]; rfl
  have eDg : L.dg = s.gpr .r5 := by rw [← hl]; rfl
  have eScr : L.scr = s.gpr .r6 := by rw [← hl]; rfl
  have k₅ : Kp [Reg.r11] (entered L.e s) t₅ :=
    (((k₁.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans k₅.mono
  have hM : t₅.mem = ((((((s.mem.writeW (L.B + BitVec.ofNat 64 (352 + L.e)) s.sp).writeW (L.B + BitVec.ofNat 64 (384 + L.e)) s.lr).writeW
      (L.B + BitVec.ofNat 64 96) (s.sp - 48)).writeW (L.B + BitVec.ofNat 64 336) (s.gpr .r3)).writeW
      (L.B + BitVec.ofNat 64 328) (s.gpr .r4)).writeW (L.B + BitVec.ofNat 64 320) (s.gpr .r5)).writeW
      (L.B + BitVec.ofNat 64 312) (s.gpr .r6) := by
    simp only [m₅, m₄, m₃, m₂, m₁, g₄, g₃, g₂, hm]
    rw [r₁ .r6 (by decide) (by decide), r₁ .r5 (by decide) (by decide), r₁ .r4 (by decide) (by decide),
      r₁ .r3 (by decide) (by decide)]
  have rd : ∀ x y v (m : Mem), x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 400 + L.e → y + 8 ≤ 400 + L.e →
      (m.writeW (L.B + BitVec.ofNat 64 y) v).readW (L.B + BitVec.ofNat 64 x) 64 = m.readW (L.B + BitVec.ofNat 64 x) 64 :=
    fun x y v m h h₁ h₂ => Mem.readW_writeW_sep (sep x y h h₁ h₂) (by decide)
  have st : ∀ y (v : BitVec 64) (m m' : Mem), y + 8 ≤ 400 + L.e → Frame [L.OUT, L.SCR, L.STK] m m' →
      Frame [L.OUT, L.SCR, L.STK] m (m'.writeW (L.B + BitVec.ofNat 64 y) v) :=
    fun y v m m' hy f => f.writeW (r := L.STK) (by simp) _ (Offset.contains_base _ hy (by omega))
  refine ⟨by rw [k₅.rd, hrd], by rw [k₅.wr, hwr, hw₀], by rw [k₅.sp, hsp], fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    he⟩
  · have h₁ : r ≠ .r11 := fun e => by subst e; simp [preserved] at hr
    have h₀ : r ≠ .r0 := fun e => by subst e; simp [preserved] at hr
    rw [k₅.gpr r (by simp [h₁]), hg r h₀]
  · rw [hM, Mem.readW_writeW_self64, eScr]
  · rw [hM, rd 320 312 _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64, eDg]
  · rw [hM, rd 328 312 _ _ (by omega) (by omega) (by omega), rd 328 320 _ _ (by omega) (by omega) (by omega),
      Mem.readW_writeW_self64, eD]
  · rw [hM, rd 336 312 _ _ (by omega) (by omega) (by omega), rd 336 320 _ _ (by omega) (by omega) (by omega),
      rd 336 328 _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64, eOut]
  · rw [hM, rd (384 + L.e) 312 _ _ (by omega) (by omega) (by omega), rd (384 + L.e) 320 _ _ (by omega) (by omega) (by omega),
      rd (384 + L.e) 328 _ _ (by omega) (by omega) (by omega), rd (384 + L.e) 336 _ _ (by omega) (by omega) (by omega),
      rd (384 + L.e) 96 _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
  · rw [hM]
    exact st 312 _ _ _ (by omega) (st 320 _ _ _ (by omega) (st 328 _ _ _ (by omega) (st 336 _ _ _ (by omega)
      (st 96 _ _ _ (by omega) (st (384 + L.e) _ _ _ (by omega) (st (352 + L.e) _ _ _ (by omega) (Frame.refl _ _)))))))

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
