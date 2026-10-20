module

public import VerifiedGarbage.Proof.Ed448.X86_64.Window.SelectBase
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.SelectKey
import VerifiedGarbage.Proof.Ed448.X86_64.Window.DirectKey
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-! Reuse the dense tables with sparse signed magnitudes. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.Ed448.X86_64.Window
open VG.Proof.X448.X86_64

theorem keeps_keep {base : Addr} {s u : State}
    (k : Keeps [Reg.rax, .rdx, .r15] s u) : Keep base s u :=
  ⟨fun r hr => k.1 r (fun h => hr
    ((show ∀ r ∈ [Reg.rax, .rdx, .r15], r ∈ clob from by decide) r h)),
    k.2.2.1, k.2.2.2, by rw [k.2.1]; exact Outside.refl _ _ _ _⟩

theorem baseCoords_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat}
    (hd : d < 17) (hr : s.gpr .r15 = BitVec.ofNat 64 d) :
    WP isa (.block (baseCoord 0 ++ baseCoord 1)) s fun u => Keep base s u ∧
      (E u.mem base 8, E u.mem base 9) = Impl.Ed448.SignedWindow.entry d ∧
      SelKeeps (E s.mem base) (E u.mem base) := by
  rw [WP.block_append_iff]
  refine WP.mono (scanCoord_ok (base_pick 0) hs 8 hd hr) fun a ⟨ka, da, ea⟩ => ?_
  refine WP.mono (scanCoord_ok (base_pick 1) (ka.scr hs) 9 hd (da.trans hr)) fun u ⟨ku, _, eu⟩ => ?_
  refine ⟨ka.trans ku, ?_, ?_⟩
  · rw [eu, ea]; rfl
  · intro j _ _ h8 h9
    rw [eu, ea]
    simp only [Function.update_of_ne h8, Function.update_of_ne h9]

theorem keyCoords_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat}
    (hd : d < 17) (hr : s.gpr .r15 = BitVec.ofNat 64 d) :
    WP isa (.block (keyAddress ++ directKeyCoord 0 ++ directKeyCoord 1 ++ directKeyCoord 2)) s
      fun u => Keep base s u ∧ Proof.Ed448.pt (E u.mem base) 8 9 10 = tablePoint s.mem base d ∧
        KeyKeeps (E s.mem base) (E u.mem base) := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (keyAddress_ok s hd hr) fun v ⟨dv, kv⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (directKeyCoord_ok (hs.of_keeps kv (by decide)) hd (by decide : 0 < 3) dv)
    fun w ⟨kw, dw, ew⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (directKeyCoord_ok (kw.scr (hs.of_keeps kv (by decide))) hd (by decide : 1 < 3)
    (dw.trans dv)) fun x ⟨kx, dx, ex⟩ => ?_
  refine WP.mono (directKeyCoord_ok (kx.scr (kw.scr (hs.of_keeps kv (by decide)))) hd (by decide : 2 < 3)
    (dx.trans (dw.trans dv))) fun u ⟨ku, _, eu⟩ => ?_
  refine ⟨((keeps_keep kv |>.trans kw).trans kx).trans ku, ?_, ?_⟩
  · rw [eu, ex, ew, coord_keep kx hd (by decide), coord_keep kw hd (by decide),
      coord_keep kw hd (by decide), kv.2.1]
    rfl
  · intro j _ _ _ h8 h9 h10
    rw [eu, ex, ew, kv.2.1]
    simp only [Function.update_apply]; split_ifs <;> simp_all

end VG.Proof.Ed448.X86_64.Wnaf
