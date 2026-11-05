module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Layout
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Deterministic ECDSA on PPC64LE: steps in the frame, and the entry

Addresses in the frame (`fr_add`), `Ctx` through steps that write only
registers (`Ctx.kp`), and the arguments saved in the frame by `saveArgs`,
with the table's digest length and HMAC's block size (`entry_ok`), after
which `Ctx` holds.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp wp_step write_gpr)
open VG.Impl.RsaOaep.PPC64LE (Fns)
open VG.Proof.HmacTable.PPC64LE (HVar)

/-- An address in the frame, from its base. -/
theorem fr_add (B : Addr) (a o : Nat) : B + BitVec.ofNat 64 a + BitVec.ofNat 64 o = B + BitVec.ofNat 64 (a + o) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- `Ctx` through a step that writes registers that are not callee-saved
and no memory. -/
theorem Ctx.kp (hL : L.Ok) {t t' : State} (hc : Ctx L g lr m₀ t) {rs : List Reg} (k : Kp rs t t')
    (hm : t'.mem = t.mem) (hsy : t'.syms = t.syms) (hrs : ∀ r ∈ rs, r ∉ preserved := by decide) :
    Ctx L g lr m₀ t' :=
  hc.regs hL k.rd k.wr hm k.sp (fun r hr => k.gpr r fun h => hrs r h hr) hsy

/-- The arguments saved in the frame: `Ctx` holds. -/
theorem entry_ok {I : Spec.Ecdsa.Rfc6979.Instance} {w : HVar} {f : Fns} {ns : List String} {s : State}
    (h : (rfcPPC I 736 (tabFacts w f) ns).pre s) :
    WP isa (.block Impl.Ecdsa.Rfc6979.PPC64LE.Cfg.saveArgs) (entered s)
      (Ctx (lay I.hashLen I.ecdsa.curve.len w f s) s.gpr s.lr s.mem) := by
  have hL := lay_ok h
  have hsp := entered_sp I.hashLen I.ecdsa.curve.len w f s
  have hwr := entered_wr I.hashLen I.ecdsa.curve.len w f s
  have hm := entered_mem I.hashLen I.ecdsa.curve.len w f s
  have hrd : (entered s).rd = [(lay I.hashLen I.ecdsa.curve.len w f s).D, (lay I.hashLen I.ecdsa.curve.len w f s).DG,
      (lay I.hashLen I.ecdsa.curve.len w f s).TAB] := by
    rw [entered_rd]; exact h.1
  have hw₀ : s.wr = [(lay I.hashLen I.ecdsa.curve.len w f s).OUT, (lay I.hashLen I.ecdsa.curve.len w f s).SCR] :=
    h.2.1
  have htf : tabFacts w f s := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hg : ∀ r, r ≠ .r0 → (entered s).gpr r = s.gpr r := fun r hr => entered_gpr s hr
  have hspS : s.sp = (lay I.hashLen I.ecdsa.curve.len w f s).B + BitVec.ofNat 64 736 := by
    show s.sp = s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 736; bv_omega
  have hlr : (lay I.hashLen I.ecdsa.curve.len w f s).B + BitVec.ofNat 64 720 = s.sp - 16 := by
    rw [hspS]; bv_omega
  have eOut : (lay I.hashLen I.ecdsa.curve.len w f s).out = s.gpr .r3 := rfl
  have eD : (lay I.hashLen I.ecdsa.curve.len w f s).d = s.gpr .r4 := rfl
  have eDg : (lay I.hashLen I.ecdsa.curve.len w f s).dg = s.gpr .r5 := rfl
  have eScr : (lay I.hashLen I.ecdsa.curve.len w f s).scr = s.gpr .r7 := rfl
  have eTab : (lay I.hashLen I.ecdsa.curve.len w f s).tab = s.gpr .r8 := rfl
  have eW : (lay I.hashLen I.ecdsa.curve.len w f s).w = w := rfl
  have eF : (lay I.hashLen I.ecdsa.curve.len w f s).f = f := rfl
  have eFa : (lay I.hashLen I.ecdsa.curve.len w f s).fa =
      fun n => if n ∈ [w.initN, w.H.updN, w.finN] then s.syms n else 0 := rfl
  obtain ⟨L, hl⟩ : ∃ L, lay I.hashLen I.ecdsa.curve.len w f s = L := ⟨_, rfl⟩
  rw [hl] at hL hsp hwr hm hrd hw₀ hspS hlr eOut eD eDg eScr eTab eW eF eFa ⊢
  have hnB := hL.nB
  have hnt := hL.nt
  have hw : ∀ d, 128 ≤ d → d + 8 ≤ 688 → InRegions (entered s).wr (L.B + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => ⟨L.FR, by rw [hwr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
  have hin : ∀ o, o + 8 ≤ 48 → InRegions ((entered s).rd ++ (entered s).wr) (L.tab + BitVec.ofNat 64 o) 8 :=
    fun o ho => ⟨L.TAB, by rw [hrd]; simp, Offset.contains_base _ ho (by omega)⟩
  have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 736 → y + 8 ≤ 736 →
      Mem.Sep (L.B + BitVec.ofNat 64 x) (64 / 8) (L.B + BitVec.ofNat 64 y) (64 / 8) :=
    fun x y h h₁ h₂ => Offset.sep L.B h (by omega) (by omega)
  simp only [Impl.Ecdsa.Rfc6979.PPC64LE.Cfg.saveArgs, Impl.Ecdsa.Rfc6979.PPC64LE.fOut,
    Impl.Ecdsa.Rfc6979.PPC64LE.fD, Impl.Ecdsa.Rfc6979.PPC64LE.fDigest, Impl.Ecdsa.Rfc6979.PPC64LE.fScratch,
    Impl.Ecdsa.Rfc6979.PPC64LE.fTab, Impl.Ecdsa.Rfc6979.PPC64LE.fDl, Impl.Ecdsa.Rfc6979.PPC64LE.fBl]
  refine WP.of_syms (stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  have a₁ : ∀ o, t₁.gpr .r11 + BitVec.ofNat 64 o = L.B + BitVec.ofNat 64 (96 + o) := fun o => by
    rw [v₁, BitVec.add_zero, hsp, fr_add]
  have w₁ : ∀ d, 128 ≤ d → d + 8 ≤ 688 → InRegions t₁.wr (L.B + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ => by
    rw [k₁.wr]; exact hw d h₁ h₂
  have r₁ : ∀ r, r ≠ .r11 → r ≠ .r0 → t₁.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [k₁.gpr r (by simp [h₁]), hg r h₂]
  refine stepStd (a := L.B + BitVec.ofNat 64 296) (by decide) (by decide) (a₁ 200) (w₁ 296 (by omega) (by omega))
    fun t₂ k₂ g₂ m₂ => ?_
  refine stepStd (a := L.B + BitVec.ofNat 64 288) (by decide) (by decide) (by rw [g₂]; exact a₁ 192)
    (by rw [k₂.wr]; exact w₁ 288 (by omega) (by omega)) fun t₃ k₃ g₃ m₃ => ?_
  refine stepStd (a := L.B + BitVec.ofNat 64 280) (by decide) (by decide) (by rw [g₃, g₂]; exact a₁ 184)
    (by rw [k₃.wr, k₂.wr]; exact w₁ 280 (by omega) (by omega)) fun t₄ k₄ g₄ m₄ => ?_
  refine stepStd (a := L.B + BitVec.ofNat 64 272) (by decide) (by decide) (by rw [g₄, g₃, g₂]; exact a₁ 176)
    (by rw [k₄.wr, k₃.wr, k₂.wr]; exact w₁ 272 (by omega) (by omega)) fun t₅ k₅ g₅ m₅ => ?_
  refine stepStd (a := L.B + BitVec.ofNat 64 320) (by decide) (by decide) (by rw [g₅, g₄, g₃, g₂]; exact a₁ 224)
    (by rw [k₅.wr, k₄.wr, k₃.wr, k₂.wr]; exact w₁ 320 (by omega) (by omega)) fun t₆ k₆ g₆ m₆ => ?_
  have g₆' : t₆.gpr = t₁.gpr := by rw [g₆, g₅, g₄, g₃, g₂]
  have r8 : t₆.gpr .r8 = L.tab := by rw [g₆', r₁ .r8 (by decide) (by decide), eTab]
  have K₆ : Kp [Reg.r11] (entered s) t₆ :=
    (((k₁.trans k₂.mono).trans k₃.mono).trans k₄.mono).trans (k₅.mono.trans k₆.mono)
  have hM₆ : t₆.mem = (((((((s.mem.writeW (L.B + BitVec.ofNat 64 688) s.sp).writeW
      (L.B + BitVec.ofNat 64 720) s.lr).writeW (L.B + BitVec.ofNat 64 96) (s.sp - 48)).writeW
      (L.B + BitVec.ofNat 64 296) (s.gpr .r3)).writeW (L.B + BitVec.ofNat 64 288) (s.gpr .r4)).writeW
      (L.B + BitVec.ofNat 64 280) (s.gpr .r5)).writeW (L.B + BitVec.ofNat 64 272) (s.gpr .r7)).writeW
      (L.B + BitVec.ofNat 64 320) (s.gpr .r8) := by
    simp only [m₆, m₅, m₄, m₃, m₂, m₁, g₅, g₄, g₃, g₂, hm]
    rw [r₁ .r8 (by decide) (by decide), r₁ .r7 (by decide) (by decide), r₁ .r5 (by decide) (by decide),
      r₁ .r4 (by decide) (by decide), r₁ .r3 (by decide) (by decide)]
  -- The table's words, as on entry: the stack is apart from it.
  have tw : ∀ o, o + 8 ≤ 48 → t₆.mem.readW (L.tab + BitVec.ofNat 64 o) 64 = s.mem.readW (L.tab + BitVec.ofNat 64 o) 64 := by
    intro o ho
    have d : ∀ y, y + 8 ≤ 736 → Mem.Sep (L.tab + BitVec.ofNat 64 o) (64 / 8) (L.B + BitVec.ofNat 64 y) (64 / 8) :=
      fun y hy => hL.tstk.sep (Offset.contains_base _ ho (by omega)) (Offset.contains_base _ hy (by omega))
    rw [hM₆, Mem.readW_writeW_sep (d 320 (by omega)) (by decide), Mem.readW_writeW_sep (d 272 (by omega)) (by decide),
      Mem.readW_writeW_sep (d 280 (by omega)) (by decide), Mem.readW_writeW_sep (d 288 (by omega)) (by decide),
      Mem.readW_writeW_sep (d 296 (by omega)) (by decide), Mem.readW_writeW_sep (d 96 (by omega)) (by decide),
      Mem.readW_writeW_sep (d 720 (by omega)) (by decide), Mem.readW_writeW_sep (d 688 (by omega)) (by decide)]
  refine stepLd (a := L.tab + BitVec.ofNat 64 32) (by decide) (by decide) (by rw [r8])
    (by rw [K₆.rd, K₆.wr]; exact hin 32 (by omega)) fun t₇ k₇ m₇ v₇ => ?_
  have v₇' : t₇.gpr .r9 = BitVec.ofNat 64 w.H.D := by rw [v₇, tw 32 (by omega), eTab]; exact htf.2.2.1
  refine stepStd (a := L.B + BitVec.ofNat 64 304) (by decide) (by decide)
    (by rw [k₇.gpr _ (by decide), g₆']; exact a₁ 208)
    (by rw [k₇.wr, K₆.wr]; exact hw 304 (by omega) (by omega)) fun t₈ k₈ g₈ m₈ => ?_
  refine stepLd (a := L.tab + BitVec.ofNat 64 40) (by decide) (by decide)
    (by rw [g₈, k₇.gpr _ (by decide), r8])
    (by rw [k₈.rd, k₈.wr, k₇.rd, k₇.wr, K₆.rd, K₆.wr]; exact hin 40 (by omega)) fun t₉ k₉ m₉ v₉ => ?_
  have hM₈ : t₈.mem = t₆.mem.writeW (L.B + BitVec.ofNat 64 304) (BitVec.ofNat 64 w.H.D) := by
    rw [m₈, m₇, v₇']
  have v₉' : t₉.gpr .r9 = BitVec.ofNat 64 w.H.B := by
    rw [v₉, hM₈, Mem.readW_writeW_sep (hL.tstk.sep (Offset.contains_base _ (show 40 + 8 ≤ 48 by omega) (by omega))
        (Offset.contains_base _ (show 304 + 8 ≤ 736 by omega) (by omega))) (by decide), tw 40 (by omega), eTab]
    exact htf.2.2.2
  refine stepStd (a := L.B + BitVec.ofNat 64 312) (by decide) (by decide)
    (by rw [k₉.gpr _ (by decide), g₈, k₇.gpr _ (by decide), g₆']; exact a₁ 216)
    (by rw [k₉.wr, k₈.wr, k₇.wr, K₆.wr]; exact hw 312 (by omega) (by omega)) fun t₁₀ k₁₀ g₁₀ m₁₀ => ?_
  refine wp_nil fun hsy' => ?_
  have K : Kp [Reg.r11, .r9] (entered s) t₁₀ :=
    ((((K₆.mono.trans k₇.mono).trans k₈.mono).trans k₉.mono).trans k₁₀.mono)
  have hM : t₁₀.mem = (t₆.mem.writeW (L.B + BitVec.ofNat 64 304) (BitVec.ofNat 64 w.H.D)).writeW
      (L.B + BitVec.ofNat 64 312) (BitVec.ofNat 64 w.H.B) := by
    rw [m₁₀, m₉, hM₈, v₉']
  have rd : ∀ x y v (m : Mem), x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 736 → y + 8 ≤ 736 →
      (m.writeW (L.B + BitVec.ofNat 64 y) v).readW (L.B + BitVec.ofNat 64 x) 64 = m.readW (L.B + BitVec.ofNat 64 x) 64 :=
    fun x y v m h h₁ h₂ => Mem.readW_writeW_sep (sep x y h h₁ h₂) (by decide)
  have st : ∀ y (v : BitVec 64) (m m' : Mem), y + 8 ≤ 736 → Frame [L.OUT, L.SCR, L.STK] m m' →
      Frame [L.OUT, L.SCR, L.STK] m (m'.writeW (L.B + BitVec.ofNat 64 y) v) :=
    fun y v m m' hy f => f.writeW (r := L.STK) (by simp) _ (Offset.contains_base _ hy (by omega))
  have hsy : t₁₀.syms = s.syms := by rw [hsy', entered_syms]
  refine ⟨by rw [K.rd, hrd], by rw [K.wr, hwr, hw₀], by rw [K.sp, hsp], fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · have h₁ : r ≠ .r11 := fun e => by subst e; simp [preserved] at hr
    have h₂ : r ≠ .r9 := fun e => by subst e; simp [preserved] at hr
    have h₀ : r ≠ .r0 := fun e => by subst e; simp [preserved] at hr
    rw [K.gpr r (by simp [h₁, h₂]), hg r h₀]
  · rw [hM, rd 272 312 _ _ (by omega) (by omega) (by omega), rd 272 304 _ _ (by omega) (by omega) (by omega), hM₆,
      rd 272 320 _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64, eScr]
  · rw [hM, rd 280 312 _ _ (by omega) (by omega) (by omega), rd 280 304 _ _ (by omega) (by omega) (by omega), hM₆,
      rd 280 320 _ _ (by omega) (by omega) (by omega), rd 280 272 _ _ (by omega) (by omega) (by omega),
      Mem.readW_writeW_self64, eDg]
  · rw [hM, rd 288 312 _ _ (by omega) (by omega) (by omega), rd 288 304 _ _ (by omega) (by omega) (by omega), hM₆,
      rd 288 320 _ _ (by omega) (by omega) (by omega), rd 288 272 _ _ (by omega) (by omega) (by omega),
      rd 288 280 _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64, eD]
  · rw [hM, rd 296 312 _ _ (by omega) (by omega) (by omega), rd 296 304 _ _ (by omega) (by omega) (by omega), hM₆,
      rd 296 320 _ _ (by omega) (by omega) (by omega), rd 296 272 _ _ (by omega) (by omega) (by omega),
      rd 296 280 _ _ (by omega) (by omega) (by omega), rd 296 288 _ _ (by omega) (by omega) (by omega),
      Mem.readW_writeW_self64, eOut]
  · rw [hM, rd 304 312 _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64, eW]
  · rw [hM, Mem.readW_writeW_self64, eW]
  · rw [hM, rd 320 312 _ _ (by omega) (by omega) (by omega), rd 320 304 _ _ (by omega) (by omega) (by omega), hM₆,
      Mem.readW_writeW_self64, eTab]
  · rw [hM, rd 720 312 _ _ (by omega) (by omega) (by omega), rd 720 304 _ _ (by omega) (by omega) (by omega), hM₆,
      rd 720 320 _ _ (by omega) (by omega) (by omega), rd 720 272 _ _ (by omega) (by omega) (by omega),
      rd 720 280 _ _ (by omega) (by omega) (by omega), rd 720 288 _ _ (by omega) (by omega) (by omega),
      rd 720 296 _ _ (by omega) (by omega) (by omega), rd 720 96 _ _ (by omega) (by omega) (by omega),
      Mem.readW_writeW_self64]
  · rw [hM, hM₆]
    exact st 312 _ _ _ (by omega) (st 304 _ _ _ (by omega) (st 320 _ _ _ (by omega) (st 272 _ _ _ (by omega)
      (st 280 _ _ _ (by omega) (st 288 _ _ _ (by omega) (st 296 _ _ _ (by omega) (st 96 _ _ _ (by omega)
      (st 720 _ _ _ (by omega) (st 688 _ _ _ (by omega) (Frame.refl _ _))))))))))
  · rw [hsy, eW, eF]; exact htf.1
  · rw [hsy, eW, eTab]; exact htf.2.1
  · intro n hn
    rw [eW] at hn
    rw [hsy, eFa]
    simp only [hn, ite_true]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
