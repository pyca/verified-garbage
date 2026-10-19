module

public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Scan
public import VerifiedGarbage.Impl.Ed448.X86_64.Window
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Mask
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Digit
import VerifiedGarbage.Proof.Framework.Block

/-! Constant-time selection of the fixed-base verification window point. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep mask cswapE opSwap)
open VG.Impl.X448.X86_64 (BITS slot)

private theorem entry_words : ∀ i < 17,
    VG.Proof.X448.toFe (VG.Proof.X448.X86_64.wv (words7 (Impl.Ed448.SignedWindow.entry i).1.val)) =
      (Impl.Ed448.SignedWindow.entry i).1 ∧
    VG.Proof.X448.toFe (VG.Proof.X448.X86_64.wv (words7 (Impl.Ed448.SignedWindow.entry i).2.val)) =
      (Impl.Ed448.SignedWindow.entry i).2 := by decide +kernel

/-- Selection changes only the selected coordinates and two temporary coordinates. -/
def SelKeeps (e e' : Env) : Prop :=
  ∀ j, j ≠ 3 → j ≠ 4 → j ≠ 8 → j ≠ 9 → e' j = e j

theorem base_pick (c : Nat) :
    PickOk (fun i => chooseConst (if c = 0 then (Impl.Ed448.SignedWindow.entry i).1 else (Impl.Ed448.SignedWindow.entry i).2))
      (fun _ _ i => if c = 0 then (Impl.Ed448.SignedWindow.entry i).1 else (Impl.Ed448.SignedWindow.entry i).2) := by
  intro i hi s base hs sw hz
  refine WP.mono (chooseConst_ok _ hz) fun u ⟨eu, ku⟩ => ⟨?_, ku⟩
  rw [eu]
  cases sw
  · rfl
  · simp only [ite_true]
    split
    · exact (entry_words i hi).1
    · exact (entry_words i hi).2

/-- The selected affine point, while preserving the accumulator and curve constant. -/
theorem selectBase_ok {s : State} {base : Addr} (hs : Scr s base) {k t : Nat}
    (ht : t + 5 ≤ 460) (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base BITS k s) :
    WP isa (.block selectBase) s fun u => Keep base s u ∧
      (E u.mem base 8, E u.mem base 9) = Impl.Ed448.SignedWindow.entry (SignedWindow.magnitude k t) ∧
      SelKeeps (E s.mem base) (E u.mem base) := by
  rw [selectBase, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadDigit_bits_ok hs (by decide) (by decide) ht hb bs) fun v ⟨dv, kv⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scanCoord_ok (base_pick 0) (hs.of_keeps kv (by decide)) 8
    (SignedWindow.magnitude_lt k t) dv) fun w ⟨kw, dw, ew⟩ => ?_
  refine WP.mono (scanCoord_ok (base_pick 1) (kw.scr (hs.of_keeps kv (by decide))) 9
    (SignedWindow.magnitude_lt k t) (dw.trans dv)) fun u ⟨ku, _, eu⟩ => ?_
  have kv' : Keep base s v := ⟨fun r hr => kv.1 r (fun h => hr
    ((show ∀ r ∈ [Reg.rax, .rdx, .r15], r ∈ VG.Proof.X448.X86_64.clob from by decide) r h)),
    kv.2.2.1, kv.2.2.2, by rw [kv.2.1]; exact VG.Proof.X448.X86_64.Outside.refl _ _ _ _⟩
  refine ⟨(kv'.trans kw).trans ku, ?_, ?_⟩
  · rw [eu, ew, kv.2.1]; rfl
  · intro j _ _ h8 h9
    rw [eu, ew, kv.2.1]
    simp only [Function.update_of_ne h8, Function.update_of_ne h9]

end VG.Proof.Ed448.X86_64.Window
