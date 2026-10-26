module
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Rsa.Arm.RvKS

import VerifiedGarbage.Proof.Rsa.Arm.RvOps
import VerifiedGarbage.Proof.Rsa.Arm.KeyEq
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Basic.IsEmpty.Defs
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! # `vg_rsa_recover_primes` on ARMv7: copies, selections, subtractions, halvings and bits on a stage -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

section
variable {P : RP} {σ s : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

theorem KS.r8_of {t : State} (h : KS P σ A live AW liveW V ls s) (r : Rest opRegs s t) : t.gpr .r8 = P.B := by
  rw [r.gpr _ (by decide), h.r8]

theorem KS.copy_w {o a : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (ho : o < nArr) (ha : a ∈ live) (hoa : o ≠ a) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (copy o a) s fun t => KS P σ (upd A o (A a)) (o :: live) AW liveW V ls t ∧
      Ws t P.B P.Z P.w nArr ∧ Rest opRegs s t ∧
      w32 t.mem (State.addr P.B) (arr P.w o + 4 * P.w) = w32 s.mem (State.addr P.B) (arr P.w o + 4 * P.w) :=
  WP.mono (Keys.copy_ok hv ho (h.live_lt a ha) (by decide) hoa) fun _ ⟨ht, k, e, r, top⟩ =>
    ⟨h.write_w k ho (by simp) (h.r8_of r) r.sp r.rd r.wr (e.trans (h.arrs a ha)) hlW (by simp), ht, r, top⟩

theorem KS.copy_W {o a : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (ho : o < 22) (ha : a ∈ liveW) (hoa : o ≠ a) (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (copy o a) s fun t => KS P σ A live (upd AW o (AW a)) (o :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t :=
  WP.mono (Keys.copy_ok hv ho (h.liveW_lt a ha) (by decide) hoa) fun _ ⟨ht, k, e, r, _⟩ =>
    ⟨h.write_W k ho (by simp) (h.r8_of r) r.sp r.rd r.wr (e.trans (h.arrsW a ha)) hl (by simp), ht, r⟩

theorem KS.sel_w {o a b sl : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ ls)
    (bit : V sl ≤ 1) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sel o a b sl) s fun t =>
      KS P σ (upd A o (if V sl = 0 then A a else A b)) (o :: live) AW liveW V ls t ∧
      Ws t P.B P.Z P.w nArr ∧ Rest opRegs s t := by
  have hs := h.sl sl hsl
  refine WP.mono (Keys.sel_ok hv ho (h.live_lt a ha) (h.live_lt b hb) (by decide) hoa hob
    (h.ls_ok sl hsl).1 (by rw [hs]; exact bit)) fun _ ⟨ht, k, e, r⟩ => ?_
  refine ⟨h.write_w k ho (by simp) (h.r8_of r) r.sp r.rd r.wr ?_ hlW (by simp), ht, r⟩
  rw [e, hs, h.arrs a ha, h.arrs b hb]

theorem KS.sel_W {o a b sl : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (ho : o < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ ls)
    (bit : V sl ≤ 1) (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (sel o a b sl) s fun t =>
      KS P σ A live (upd AW o (if V sl = 0 then AW a else AW b)) (o :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t := by
  have hs := h.sl sl hsl
  refine WP.mono (Keys.sel_ok hv ho (h.liveW_lt a ha) (h.liveW_lt b hb) (by decide) hoa hob
    (h.ls_ok sl hsl).1 (by rw [hs]; exact bit)) fun _ ⟨ht, k, e, r⟩ => ?_
  refine ⟨h.write_W k ho (by simp) (h.r8_of r) r.sp r.rd r.wr ?_ hl (by simp), ht, r⟩
  rw [e, hs, h.arrsW a ha, h.arrsW b hb]

theorem KS.sub3_w {o a b : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hoa : o ≠ a) (hob : o ≠ b)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sub3 o a b) s fun t => ∃ X, KS P σ (upd A o X) (o :: live) AW liveW V ls t ∧
      Ws t P.B P.Z P.w nArr ∧ Rest opRegs s t ∧
      X + A b = A a + 2 ^ (32 * P.w) * (t.gpr .r11).toNat ∧ (t.gpr .r11).toNat ≤ 1 :=
  WP.mono (Keys.sub3_ok hv ho (h.live_lt a ha) (h.live_lt b hb) (by decide) hoa hob)
    fun t ⟨ht, k, e, b1, r⟩ => ⟨num t.mem P.B P.w o,
      h.write_w k ho (by simp) (h.r8_of r) r.sp r.rd r.wr rfl hlW (by simp), ht, r,
      by rw [← h.arrs a ha, ← h.arrs b hb]; exact e, b1⟩

theorem KS.sub3_W {o a b : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (ho : o < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hoa : o ≠ a) (hob : o ≠ b)
    (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (sub3 o a b) s fun t => ∃ X, KS P σ A live (upd AW o X) (o :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t ∧
      X + AW b = AW a + 2 ^ (32 * P.W) * (t.gpr .r11).toNat ∧ (t.gpr .r11).toNat ≤ 1 :=
  WP.mono (Keys.sub3_ok hv ho (h.liveW_lt a ha) (h.liveW_lt b hb) (by decide) hoa hob)
    fun t ⟨ht, k, e, b1, r⟩ => ⟨num t.mem P.B P.W o,
      h.write_W k ho (by simp) (h.r8_of r) r.sp r.rd r.wr rfl hl (by simp), ht, r,
      by rw [← h.arrsW a ha, ← h.arrsW b hb]; exact e, b1⟩

theorem KS.half_W {j : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (hj : j ∈ liveW) (r11 : (s.gpr .r11).toNat = 0) (hl : ∀ i ∈ live, i / 2 ≠ j) :
    WP isa (half j) s fun t => KS P σ A live (upd AW j (AW j / 2)) (j :: liveW) V ls t ∧
      Ws t P.B P.Z P.W 22 ∧ Rest opRegs s t :=
  WP.mono (Keys.half_ok hv (h.liveW_lt j hj) (by decide) (by omega)) fun _ ⟨ht, k, e, r⟩ =>
    ⟨h.write_W k (h.liveW_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr
      (by rw [e, r11, Nat.mul_zero, Nat.add_zero, h.arrsW j hj]) hl (by simp), ht, r⟩

theorem KS.bitOf_w {j sl : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (hj : j ∈ live) (hsl : SlotOk sl) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V sl (A j % 2)) (sl :: ls) t → Ws t P.B P.Z P.w nArr →
      Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (bitOf sl j ++ rest)) s Q :=
  Keys.bitOf_ok hv (h.live_lt j hj) (by decide) hsl.1 fun t ht kt e r =>
    k t (h.slot1 kt hsl (h.r8_of r) r.sp r.rd r.wr (by rw [e, h.arrs j hj])) ht r

theorem KS.bitOf_W {j sl : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (hj : j ∈ liveW) (hsl : SlotOk sl) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V sl (AW j % 2)) (sl :: ls) t → Ws t P.B P.Z P.W 22 →
      Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (bitOf sl j ++ rest)) s Q :=
  Keys.bitOf_ok hv (h.liveW_lt j hj) (by decide) hsl.1 fun t ht kt e r =>
    k t (h.slot1 kt hsl (h.r8_of r) r.sp r.rd r.wr (by rw [e, h.arrsW j hj])) ht r

theorem KS.clrLow_W {j : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.W 22)
    (hj : j ∈ liveW) (hl : ∀ i ∈ live, i / 2 ≠ j) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live (upd AW j (2 * (AW j / 2))) (j :: liveW) V ls t → Ws t P.B P.Z P.W 22 →
      Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (clrLow j ++ rest)) s Q :=
  Keys.clrLow_ok hv (h.liveW_lt j hj) (by decide) fun t ht kt e r _ =>
    k t (h.write_W kt (h.liveW_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr (by rw [e, h.arrsW j hj]) hl
      (by simp)) ht r

theorem KS.setOne_w {j : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (hj : j ∈ live) (hlW : ∀ i ∈ liveW, j / 2 ≠ i) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ (upd A j (1 + 2 ^ 32 * (A j / 2 ^ 32))) (j :: live) AW liveW V ls t →
      Ws t P.B P.Z P.w nArr → Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (setOne j ++ rest)) s Q :=
  Keys.setOne_ok hv (h.live_lt j hj) (by decide) fun t ht kt e r =>
    k t (h.write_w kt (h.live_lt j hj) (by simp) (h.r8_of r) r.sp r.rd r.wr (by rw [e, h.arrs j hj]) hlW
      (by simp)) ht r

/-- `eqS d a b aW`: the header word `d := [a] = [b]`, through `aW` and `sT`. -/
theorem KS.eqS_w {d a b : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z P.w nArr)
    (ha : a ∈ live) (hb : b ∈ live) (hd : SlotOk d) (hW : aW ∉ live) (hlW : ∀ j ∈ liveW, aW / 2 ≠ j)
    (hls : ∀ e ∈ ls, e + 4 ≤ sT ∨ sT + 4 ≤ e) (hdT : d ≠ sT) :
    WP isa (eqS d a b aW) s fun t =>
      KS P σ A live AW liveW (upd V d (if A a = A b then 1 else 0)) (d :: ls) t ∧
      Ws t P.B P.Z P.w nArr ∧ Rest opRegs s t := by
  have hWa : aW ≠ a := fun e => hW (e ▸ ha)
  have hWb : aW ≠ b := fun e => hW (e ▸ hb)
  refine WP.mono (Keys.eqS_ok hv (t := aW) (by decide) (h.live_lt a ha) (h.live_lt b hb) (by decide)
    hWa hWb hd.1) fun t ⟨ht, k, e, r⟩ => ⟨?_, ht, r⟩
  have hT : SlotOk sT := by decide
  refine h.core k (by simpa using fitZ_w h.sizes (show aW < nArr by decide))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro x (rfl | rfl) <;> with_reducible assumption)
    (h.r8_of r) r.sp r.rd r.wr
    (h.arrs_w k (fun j hj i hi => by simp at hi; subst hi; exact fun e => hW (e ▸ hj))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro x (rfl | rfl) <;> with_reducible assumption))
    h.live_lt
    (h.arrsW_w k (fun j hj i hi => by simp at hi; subst hi; exact hlW j hj)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro x (rfl | rfl) <;> with_reducible assumption))
    h.liveW_lt (fun x hx => ?_) (fun x hx => ?_)
  · by_cases e' : x = d
    · subst e'; rw [upd_self, e, h.arrs a ha, h.arrs b hb]
    · have hx' := (List.mem_cons.mp hx).resolve_left e'
      have a1 := h.ls_ok x hx'
      rw [upd_ne _ _ e', k.slot a1.1 (fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact hls x hx'
        · have := a1.2.2; have := hd.2.2; omega), h.sl x hx']
  · rcases List.mem_cons.mp hx with rfl | hx'
    · exact hd
    · exact h.ls_ok x hx'

end

end VG.Proof.Rsa.Arm.Recover
