module

import VerifiedGarbage.Proof.Ed448.X86_64.Window.DirectKey
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Digit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-! Constant-time selection from the runtime projective table. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window VG.Proof.Ed448.X86_64
open VG.Proof.Ed448 (pt)
open VG.Proof.X448.X86_64 (Scr Index Env E F Keep mask cswapE opSwap)
open VG.Impl.X448.X86_64 (slot)

theorem coord_keep {base : Addr} {s u : State} (h : Keep base s u) {i c : Nat}
    (hi : i < 17) (hc : c < 3) : F u.mem base (tabOffset i c) = F s.mem base (tabOffset i c) := by
  unfold F
  rw [h.mem.fe (by simp only [tabOffset, TAB]; omega) (by simp only [tabOffset, TAB]; omega)]

def KeyKeeps (e e' : Env) : Prop :=
  ∀ j : Index, j ≠ 3 → j ≠ 4 → j ≠ 5 → j ≠ 8 → j ≠ 9 → j ≠ 10 → e' j = e j

/-- Only the projective point selected by the public digit is read. -/
theorem selectKey_ok {s : State} {base : Addr} (hs : Scr s base) {o k t : Nat}
    (ho : 2048 ≤ o) (hbnd : o + 460 ≤ 8192) (ht : t + 5 ≤ 460)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base o k s) :
    WP isa (.block (selectKey o)) s fun u => Keep base s u ∧
      pt (E u.mem base) 8 9 10 = tablePoint s.mem base (SignedWindow.magnitude k t) ∧
      KeyKeeps (E s.mem base) (E u.mem base) := by
  rw [selectKey, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadDigit_bits_ok hs hbnd (by omega) ht hb bs) fun v0 ⟨dv0, kv0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (keyAddress_ok v0 (SignedWindow.magnitude_lt k t) dv0) fun v ⟨dv, kva⟩ => ?_
  have kv := kv0.trans kva
  rw [WP.block_append_iff]
  refine WP.mono (directKeyCoord_ok (hs.of_keeps kv (by decide)) (SignedWindow.magnitude_lt k t) (by decide : 0 < 3) dv) fun w ⟨kw, dw, ew⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (directKeyCoord_ok (kw.scr (hs.of_keeps kv (by decide))) (SignedWindow.magnitude_lt k t) (by decide : 1 < 3) (dw.trans dv)) fun x ⟨kx, dx, ex⟩ => ?_
  refine WP.mono (directKeyCoord_ok (kx.scr (kw.scr (hs.of_keeps kv (by decide)))) (SignedWindow.magnitude_lt k t) (by decide : 2 < 3) (dx.trans (dw.trans dv))) fun u ⟨ku, _, eu⟩ => ?_
  have kv' : Keep base s v := ⟨fun r hr => kv.1 r (fun h => hr
    ((show ∀ r ∈ [Reg.rax, .rdx, .r15], r ∈ VG.Proof.X448.X86_64.clob from by decide) r h)),
    kv.2.2.1, kv.2.2.2, by rw [kv.2.1]; exact VG.Proof.X448.X86_64.Outside.refl _ _ _ _⟩
  refine ⟨((kv'.trans kw).trans kx).trans ku, ?_, ?_⟩
  · rw [eu, ex, ew, coord_keep kx (SignedWindow.magnitude_lt k t) (by decide),
      coord_keep kw (SignedWindow.magnitude_lt k t) (by decide),
      coord_keep kw (SignedWindow.magnitude_lt k t) (by decide), kv.2.1]
    rfl
  · intro j _ _ _ h8 h9 h10
    rw [eu, ex, ew, kv.2.1]
    simp only [Function.update_apply]; split_ifs <;> simp_all

end VG.Proof.Ed448.X86_64.Window
