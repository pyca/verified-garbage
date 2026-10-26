module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Compare
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Rsa.X86.RvFrames
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! # Bit extraction, low-word updates and comparisons during recovery -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.KeyRt (bitOf clrLow setOne eqSFast)

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.bitOf_w {j sl : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hj : j ∈ live) (hsl : SlotOk sl) :
    WP isa (.block (bitOf nar sl j)) s fun t =>
      KS g s0 A live AW liveW (upd V sl (A j % 2)) (sl :: ls) t ∧ Keeps opRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.bitOf_ok h.rt (h.live_lt j hj) hsl.2.1) fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_nar] at k e
  exact ⟨h.slot1 k hsl (r.mono (by decide)) (by rw [e, h.arrs j hj]), r.mono (by decide)⟩

theorem KS.bitOf_W {j sl : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hj : j ∈ liveW) (hsl : SlotOk sl) :
    WP isa (.block (bitOf wid sl j)) s fun t =>
      KS g s0 A live AW liveW (upd V sl (AW j % 2)) (sl :: ls) t ∧ Keeps opRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.bitOf_ok h.rtW (h.liveW_lt j hj) hsl.2.1) fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_wid] at k e
  exact ⟨h.slot1 k hsl (r.mono (by decide)) (by rw [e, h.arrsW j hj]), r.mono (by decide)⟩

theorem KS.clrLow_W {j : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hj : j ∈ liveW) (hl : ∀ i ∈ live, i / 2 ≠ j) :
    WP isa (.block (clrLow wid j)) s fun t =>
      KS g s0 A live (upd AW j (2 * (AW j / 2))) (j :: liveW) V ls t ∧ Keeps opRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.clrLow_ok h.rtW (h.liveW_lt j hj)) fun t ⟨_, k, e, r, _⟩ => ?_
  rw [kw_wid] at k e
  exact ⟨h.write_W k (h.liveW_lt j hj) (by simp) (r.mono (by decide))
    (by rw [e, h.arrsW j hj]) hl (by simp), r.mono (by decide)⟩

theorem KS.setOne_w {j : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hj : j ∈ live) (hlW : ∀ i ∈ liveW, j / 2 ≠ i) :
    WP isa (.block (setOne nar j)) s fun t =>
      KS g s0 (upd A j (1 + 2 ^ 32 * (A j / 2 ^ 32))) (j :: live) AW liveW V ls t ∧
      Keeps opRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.setOne_ok h.rt (h.live_lt j hj)) fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_nar] at k e
  exact ⟨h.write_w k (h.live_lt j hj) (by simp) (r.mono (by decide))
    (by rw [e, h.arrs j hj]) hlW (by simp), r.mono (by decide)⟩

theorem KS.eqS_w {d a b : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ha : a ∈ live) (hb : b ∈ live) (hd : SlotOk d) (hW : aW ∉ live)
    (hlW : ∀ j ∈ liveW, aW / 2 ≠ j)
    (hls : ∀ e ∈ ls, e + 4 ≤ sT ∨ sT + 4 ≤ e) :
    WP isa (eqSFast nar d a b) s fun t =>
      KS g s0 A live AW liveW (upd V d (if A a = A b then 1 else 0)) (d :: ls) t ∧
      Keeps opRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.eqSFast_ok h.rt
    (h.live_lt a ha) (h.live_lt b hb) hd.2.1) fun t ⟨_, k0, e, r⟩ => ?_
  have k := k0.mono (js' := [aW]) (ds' := [sT, d]) (by simp) (by simp)
  rw [kw_nar] at k e
  have hdT : ∀ d' ∈ [sT, d], SlotOk d' := by
    intro d' hm
    rcases List.mem_cons.mp hm with rfl | hm
    · decide
    · simpa using (show d' = d from List.mem_singleton.mp hm) ▸ hd
  refine ⟨h.core k (by simpa using h.ws.arr_fit (show aW < nArr by decide)) hdT
    (r.mono (by decide))
    (h.arrs_w k (fun j hj i hi => by simp at hi; subst hi; exact fun e => hW (e ▸ hj)) hdT)
    h.live_lt (h.arrsW_w k (fun j hj i hi => by simp at hi; subst hi; exact hlW j hj) hdT)
    h.liveW_lt ?_ ?_, r.mono (by decide)⟩
  · intro x hx
    by_cases eq : x = d
    · subst eq; rw [upd_self, e, h.arrs a ha, h.arrs b hb]
    · have old := (List.mem_cons.mp hx).resolve_left eq
      have info := h.ls_ok x old
      rw [upd_ne _ _ eq, k.slot info.2.1 (fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact hls x old
        · have := info.2.2; have := hd.2.2; omega), h.sl x old]
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | old
    · exact hd
    · exact h.ls_ok x old

end
end VG.Proof.Rsa.X86.Recover
