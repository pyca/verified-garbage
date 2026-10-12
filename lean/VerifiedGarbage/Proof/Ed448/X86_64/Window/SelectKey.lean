module

public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Scan
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! Constant-time selection from the runtime projective table. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window VG.Proof.Ed448.X86_64
open VG.Proof.Ed448 (pt)
open VG.Proof.X448.X86_64 (Scr Index Env E F Keep mask cswapE opSwap)
open VG.Impl.X448.X86_64 (slot)

private theorem coord_keep {base : Addr} {s u : State} (h : Keep base s u) {i c : Nat}
    (hi : i < 17) (hc : c < 3) : F u.mem base (tabOffset i c) = F s.mem base (tabOffset i c) := by
  unfold F
  rw [h.mem.fe (by simp only [tabOffset, TAB]; omega) (by simp only [tabOffset, TAB]; omega)]

def KeyKeeps (e e' : Env) : Prop :=
  ∀ j : Index, j ≠ 3 → j ≠ 4 → j ≠ 5 → j ≠ 8 → j ≠ 9 → j ≠ 10 → e' j = e j

private theorem key_pick (c : Nat) (hc : c < 3) :
    PickOk (fun i => chooseMem (tabOffset i c)) (fun m b i => F m b (tabOffset i c)) := by
  intro i hi s base hs sw hz
  refine WP.mono (chooseMem_ok hs (by simp only [tabOffset, TAB]; omega) hz)
    fun u ⟨eu, ku⟩ => ⟨?_, ku.mono (fun _ h => List.mem_cons_of_mem _ h)⟩
  rw [eu]
  cases sw <;> rfl

/-- Every entry is read, with a mask deciding which one is retained. -/
theorem selectKey_ok {s : State} {base : Addr} (hs : Scr s base) {o k t : Nat}
    (ho : 2048 ≤ o) (hbnd : o + 460 ≤ 8192) (ht : t + 5 ≤ 460)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base o k s) :
    WP isa (.block (selectKey o)) s fun u => Keep base s u ∧
      pt (E u.mem base) 8 9 10 = tablePoint s.mem base (SignedWindow.magnitude k t) ∧
      KeyKeeps (E s.mem base) (E u.mem base) := by
  rw [selectKey, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadDigit_bits_ok hs hbnd (by omega) ht hb bs) fun v ⟨dv, kv⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scanCoord_ok (key_pick 0 (by decide)) (hs.of_keeps kv (by decide)) 8
    (SignedWindow.magnitude_lt k t) dv) fun w ⟨kw, dw, ew⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scanCoord_ok (key_pick 1 (by decide)) (kw.scr (hs.of_keeps kv (by decide))) 9
    (SignedWindow.magnitude_lt k t) (dw.trans dv)) fun x ⟨kx, dx, ex⟩ => ?_
  refine WP.mono (scanCoord_ok (key_pick 2 (by decide)) (kx.scr (kw.scr (hs.of_keeps kv (by decide)))) 10
    (SignedWindow.magnitude_lt k t) (dx.trans (dw.trans dv))) fun u ⟨ku, _, eu⟩ => ?_
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
    simp only [Function.update_of_ne h8, Function.update_of_ne h9, Function.update_of_ne h10]

end VG.Proof.Ed448.X86_64.Window
