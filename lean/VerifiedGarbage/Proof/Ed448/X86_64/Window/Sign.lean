module
public import VerifiedGarbage.Impl.Ed448.X86_64.Window
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Mask

import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
import VerifiedGarbage.Proof.X448.X86_64.Setup
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.X448.X86_64.Chain
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! Conditional point negation for balanced window digits. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.X448.X86_64
open VG.Impl.X448.X86_64 (W slot loads stores)

private theorem signFlag_ok {s : State} {base : Addr} (hs : Scr s base) {o t b : Nat}
    (ho : o + t + 5 ≤ 8192) (hb : b < 2) (hr : s.gpr .rbx = BitVec.ofNat 64 t)
    (hm : s.mem (off base (o + t + 4)) = BitVec.ofNat 8 b) :
    WP isa (.block (signFlag o)) s fun u =>
      u.zf = decide (b = 1) ∧ Keeps [.rax] s u := by
  have he : s.ea { base := .rdi, index := some .rbx, disp := ((o + 4 : Nat) : Int) } =
      off base (o + t + 4) := by rw [ea_bitsAt hs.rdi hr]; congr 1; omega
  have hd : InRegions (s.rd ++ s.wr) (off base (o + t + 4)) 1 := hs.read (by omega)
  have hc : ∀ b < 2, (((BitVec.ofNat 8 b).setWidth 64 - (1 : BitVec 32).signExtend 64) == 0) = decide (b = 1) := by decide +kernel
  apply WP.of_runBlock
  simp only [signFlag, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load8, he, hd, hm, RegUpd.gpr_setReg_self, RegUpd.zf_arithFlags,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨hc b hb, fun r hr => by
    have hn : r ≠ .rax := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr
    simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, hn, ite_false], rfl, rfl, rfl⟩

/-- The sign bit selects X or -X; all coordinates except the temporary and X survive. -/
theorem negateSelected_ok {s : State} {base : Addr} (hs : Scr s base) {o k t : Nat}
    (ho : 2048 ≤ o) (hb : o + 460 ≤ 8192) (ht : t + 5 ≤ 460)
    (hr : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base o k s) :
    WP isa (negateSelected o) s fun u => Keep base s u ∧
      E u.mem base 8 = (if SignedWindow.negative k t then -(E s.mem base 8) else E s.mem base 8) ∧
      ∀ j : Index, j ≠ 3 → j ≠ 8 → E u.mem base j = E s.mem base j := by
  rw [negateSelected]
  refine WP.seq (WP.mono (constE_ok hs 3 0 c0) fun v ⟨kv, ev⟩ => ?_)
  refine WP.seq (WP.mono (Point64.fop_frame baseline_ok (kv.scr hs) (.sub 3 3 8) (by decide))
    fun w ⟨kw, ew, _⟩ => ?_)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  have ksw := kv.trans kw
  refine WP.mono (loads_ok (ksw.scr hs) (slot 8) W (by decide) (by decide) (by decide))
    fun x ⟨_, vx, kx⟩ => ?_
  rw [WP.block_append_iff]
  have bsx : Bits base o k x := by rw [Bits, kx.2.1]; exact bs.keep ho hb ksw
  refine WP.mono (signFlag_ok ((ksw.scr hs).of_keeps kx (by decide)) (by omega)
    (b := k / 2 ^ (t + 4) % 2) (Nat.mod_lt _ (by decide)) ((kx.1 _ (by decide)).trans ((ksw.gpr _ (by decide)).trans hr))
    (by simpa only [Nat.add_assoc, Nat.add_left_comm t 4] using bsx.bit (by omega) (t := t + 4) (by omega))) fun y ⟨zy, ky⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (chooseMem_ok (((ksw.scr hs).of_keeps kx (by decide)).of_keeps ky (by decide))
    (a := slot 3) (by decide) zy) fun z ⟨vz, kz⟩ => ?_
  have hsz := (((ksw.scr hs).of_keeps kx (by decide)).of_keeps ky (by decide)).of_keeps kz (by decide)
  refine WP.mono (stores_E hsz 8 W rfl) fun u ⟨eu, ou, gu, ru, wu⟩ => ?_
  have km : z.mem = w.mem := kz.2.1.trans (ky.2.1.trans kx.2.1)
  have kg : ∀ r, r ∉ clob → z.gpr r = w.gpr r := by
    intro r hr
    have hw : r ∉ W := fun h => hr ((show ∀ r ∈ W, r ∈ clob from by decide) r h)
    have ha : r ∉ [Reg.rax] := fun h => hr ((show ∀ r ∈ [Reg.rax], r ∈ clob from by decide) r h)
    exact (kz.1 r hw).trans ((ky.1 r ha).trans (kx.1 r hw))
  have ku : Keep base w u := ⟨fun r hr => (gu r).trans (kg r hr),
    ru.trans (kz.2.2.1.trans (ky.2.2.1.trans kx.2.2.1)),
    wu.trans (kz.2.2.2.trans (ky.2.2.2.trans kx.2.2.2)), by
      rw [km] at ou; exact ou.mono (by decide) (by decide)⟩
  refine ⟨ksw.trans ku, ?_, ?_⟩
  · have vy : rv y W = rv x W := rv_congr (fun r hr => ky.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; intro h; subst r; exact absurd hr (by decide)))
    rw [eu, Function.update_self, vz, vy, vx, ky.2.1, kx.2.1]
    change VG.Proof.X448.toFe (if decide (k / 2 ^ (t + 4) % 2 = 1) then fe w.mem base (slot 3)
      else fe w.mem base (slot 8)) = _
    simp only [apply_ite VG.Proof.X448.toFe]
    change (if decide (k / 2 ^ (t + 4) % 2 = 1) then E w.mem base 3 else E w.mem base 8) = _
    rw [ew, ev]
    simp only [VG.Proof.Ed448.evalOp, show VG.Proof.Ed448.idx 3 = (3 : Index) from rfl,
      show VG.Proof.Ed448.idx 8 = (8 : Index) from rfl, Function.update_self, Function.update_of_ne (by decide : (8 : Index) ≠ 3),
      zero_sub, SignedWindow.negative]
    rfl
  · intro j h3 h8
    rw [eu, Function.update_of_ne h8, km, ew, ev]
    simp only [VG.Proof.Ed448.evalOp, show VG.Proof.Ed448.idx 3 = (3 : Index) from rfl,
      show VG.Proof.Ed448.idx 8 = (8 : Index) from rfl, Function.update_of_ne h3]

end VG.Proof.Ed448.X86_64.Window
