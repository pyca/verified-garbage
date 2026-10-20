module
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Rsa.X86.KeyCopy
import VerifiedGarbage.Proof.Rsa.X86.KeyHalf
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Proof.Rsa.X86.KeySub
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Array arithmetic on the two recovery workspace views -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.copy_w {o a : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < nArr) (ha : a ∈ live) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (copy g.w o a) s fun t =>
      KS g s0 (upd A o (A a)) (o :: live) AW liveW V ls t ∧ Keeps opRegs s t ∧
      w32 t.mem g.B (arr g.w o + 4 * g.w) = w32 s.mem g.B (arr g.w o + 4 * g.w) :=
  WP.mono (Keys.copy_ok h.ws ho (h.live_lt a ha)) fun _ ⟨_, k, e, r, top⟩ =>
    ⟨h.write_w k ho (by simp) (r.mono (by decide)) (e.trans (h.arrs a ha)) hlW (by simp),
      r.mono (by decide), top⟩

theorem KS.copy_W {o a : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < 22) (ha : a ∈ liveW) (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (copy g.W o a) s fun t =>
      KS g s0 A live (upd AW o (AW a)) (o :: liveW) V ls t ∧ Keeps opRegs s t :=
  WP.mono (Keys.copy_ok h.wsW ho (h.liveW_lt a ha)) fun _ ⟨_, k, e, r, _⟩ =>
    ⟨h.write_W k ho (by simp) (r.mono (by decide)) (e.trans (h.arrsW a ha)) hl (by simp),
      r.mono (by decide)⟩

theorem KS.sel_w {o a b sl : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hsl : sl ∈ ls)
    (bit : V sl ≤ 1) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sel g.w o a b sl) s fun t =>
      KS g s0 (upd A o (if V sl = 0 then A a else A b)) (o :: live) AW liveW V ls t ∧
      Keeps opRegs s t := by
  refine WP.mono (Keys.sel_ok h.ws ho (h.live_lt a ha) (h.live_lt b hb)
    (h.ls_ok sl hsl).2.1 (by rw [h.sl sl hsl]; exact bit)) fun t ⟨_, k, e, r⟩ => ?_
  refine ⟨h.write_w k ho (by simp) (r.mono (by decide)) ?_ hlW (by simp), r.mono (by decide)⟩
  rw [e, h.sl sl hsl, h.arrs a ha, h.arrs b hb]

theorem KS.sel_W {o a b sl : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hsl : sl ∈ ls)
    (bit : V sl ≤ 1) (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (sel g.W o a b sl) s fun t =>
      KS g s0 A live (upd AW o (if V sl = 0 then AW a else AW b)) (o :: liveW) V ls t ∧
      Keeps opRegs s t := by
  refine WP.mono (Keys.sel_ok h.wsW ho (h.liveW_lt a ha) (h.liveW_lt b hb)
    (h.ls_ok sl hsl).2.1 (by rw [h.sl sl hsl]; exact bit)) fun t ⟨_, k, e, r⟩ => ?_
  refine ⟨h.write_W k ho (by simp) (r.mono (by decide)) ?_ hl (by simp), r.mono (by decide)⟩
  rw [e, h.sl sl hsl, h.arrsW a ha, h.arrsW b hb]

theorem KS.sub3_w {o a b : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hoa : o ≠ a) (hob : o ≠ b)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sub3 g.w o a b) s fun t => ∃ X,
      KS g s0 (upd A o X) (o :: live) AW liveW V ls t ∧ Keeps opRegs s t ∧
      X + A b = A a + 2 ^ (32 * g.w) * (t.gpr .ebx).toNat ∧ (t.gpr .ebx).toNat ≤ 1 :=
  WP.mono (Keys.sub3_ok h.ws ho (h.live_lt a ha) (h.live_lt b hb) hoa hob)
    fun t ⟨_, k, e, b1, r⟩ => ⟨num t.mem g.B g.w o,
      h.write_w k ho (by simp) (r.mono (by decide)) rfl hlW (by simp), r.mono (by decide),
      by rw [← h.arrs a ha, ← h.arrs b hb]; exact e, b1⟩

theorem KS.sub3_W {o a b : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hoa : o ≠ a) (hob : o ≠ b)
    (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (sub3 g.W o a b) s fun t => ∃ X,
      KS g s0 A live (upd AW o X) (o :: liveW) V ls t ∧ Keeps opRegs s t ∧
      X + AW b = AW a + 2 ^ (32 * g.W) * (t.gpr .ebx).toNat ∧ (t.gpr .ebx).toNat ≤ 1 :=
  WP.mono (Keys.sub3_ok h.wsW ho (h.liveW_lt a ha) (h.liveW_lt b hb) hoa hob)
    fun t ⟨_, k, e, b1, r⟩ => ⟨num t.mem g.B g.W o,
      h.write_W k ho (by simp) (r.mono (by decide)) rfl hl (by simp), r.mono (by decide),
      by rw [← h.arrsW a ha, ← h.arrsW b hb]; exact e, b1⟩

theorem KS.half_W {j : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hj : j ∈ liveW) (zero : (s.gpr .ebx).toNat = 0) (hl : ∀ i ∈ live, i / 2 ≠ j) :
    WP isa (half g.W j) s fun t =>
      KS g s0 A live (upd AW j (AW j / 2)) (j :: liveW) V ls t ∧ Keeps opRegs s t :=
  WP.mono (Keys.half_ok h.wsW (h.liveW_lt j hj) (by omega)) fun _ ⟨_, k, e, r⟩ =>
    ⟨h.write_W k (h.liveW_lt j hj) (by simp) (r.mono (by decide))
      (by rw [e, zero, Nat.mul_zero, Nat.add_zero, h.arrsW j hj]) hl (by simp), r.mono (by decide)⟩

end
end VG.Proof.Rsa.X86.Recover
