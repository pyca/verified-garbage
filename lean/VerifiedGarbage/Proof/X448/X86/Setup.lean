module

import VerifiedGarbage.Proof.X448.X86.Initial
public import VerifiedGarbage.Proof.X448.X86.Save
public import VerifiedGarbage.Proof.X448.X86.Env
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.Radix16Bytes
public import VerifiedGarbage.Proof.X448.X86.Mem
import VerifiedGarbage.Proof.X448.X86.Decode
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.X86.Swap
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `X448.X86.DecodeAll`, which only this module used -/

section

/-!
# X448 on x86 (32-bit): decoding the whole coordinate

The 28 limb loads fill two slots while preserving input bytes outside the
working space.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem decoded_congr {m m' : Mem} {p : Addr} {i : Nat} (hi : i < 28)
    (h : ∀ j < 56, m' (off p j) = m (off p j)) : decoded m' p i = decoded m p i := by
  simp only [decoded, byteN]
  rw [h (2 * i) (by omega_using [hi]), h (2 * i + 1) (by omega_using [hi])]

theorem decodeAll_ok {s : State} {base p : Addr} (hs : Scr s base)
    (hp : (s.gpr .esi).setWidth 64 = p) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block ((List.range 28).flatMap decodeLimb)) s fun t =>
      (∀ j < 28, limbs t.mem base X1 j = decoded s.mem p j) ∧
      (∀ j < 28, limbs t.mem base X3 j = decoded s.mem p j) ∧
      Outside2 base X1 112 X3 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, limbs t.mem base X1 j = decoded s.mem p j) ∧
    (∀ j < n, limbs t.mem base X3 j = decoded s.mem p j) ∧
    Outside2 base X1 (4 * n) X3 (4 * n) s.mem t.mem ∧ Keeps [.eax, .edx] s t
  have step : ∀ n t, n < 28 → inv n t → WP isa (.block (decodeLimb n)) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tp : (t.gpr .esi).setWidth 64 = p := by rw [tk.1 _ (by decide)]; exact hp
    have tfit : (t.gpr .esi).toNat + 56 ≤ 2 ^ 32 := by rw [tk.1 _ (by decide)]; exact hfit
    have tr : ∀ j < 56, InRegions (t.rd ++ t.wr) (off p j) 1 := by
      intro j hj; rw [tk.2.1, tk.2.2]; exact hr j hj
    have byte : ∀ j < 56, t.mem (off p j) = s.mem (off p j) := by
      intro j hj
      have h := hd j hj
      exact tm _ (Or.inr (by simp only [X1, slot]; omega_using [hn, h])) (Or.inr (by simp only [X3, slot]; omega_using [hn, h]))
    have eq := decoded_congr hn byte
    refine WP.mono (decodeLimb_ok (hs.of_keeps tk (by decide)) hn tp tfit tr) fun u ⟨um, uk⟩ => ?_
    rw [eq] at um
    let v := BitVec.ofNat 32 (decoded s.mem p n)
    have vn : v.toNat = decoded s.mem p n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (decoded_lt s.mem p n) (by decide))]
    have pair := fun j (hj : j < 28) => pair_write (m := t.mem) (base := base)
      (x := X1) (y := X3) (by decide) (by decide) (by decide) hn hj v v
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · intro j hj
      rw [um, (pair j (by omega_using [hn, hj])).1]
      by_cases h : j = n
      · rw [ite_eq_left h, vn, h]
      · rw [ite_eq_right h]; exact tx j (by omega_using [hj, h])
    · intro j hj
      rw [um, (pair j (by omega_using [hn, hj])).2]
      by_cases h : j = n
      · rw [ite_eq_left h, vn, h]
      · rw [ite_eq_right h]; exact ty j (by omega_using [hj, h])
    · rw [um]
      exact (tm.mono (by omega_using []) (by omega_using [])).trans (decodeLimb_outside _ _ hn _)
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hj => by omega, fun _ hj => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

end

end

/-!
# X448 on x86 (32-bit): reading the arguments

Setup saves the callee-saved registers, decodes the coordinate, and
initializes the ladder.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

def setupRegs : List Reg := [.eax, .edx, .edi, .esi]

theorem setup_ok {s : State} (hp : Pre s) {base p : Addr}
    (hc : (arg s 3).setWidth 64 = base) (hpoint : (arg s 2).setWidth 64 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block setup) s fun t =>
      Scr t base ∧ BoundedEnv t.mem base ∧ Keeps setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ Saved base s.gpr t.mem ∧
      E t.mem base 0 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      E t.mem base 1 = 1 ∧ E t.mem base 2 = 0 ∧
      E t.mem base 3 = E t.mem base 0 ∧ E t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 := by
  simp only [setup, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hp) fun t ⟨ts, tv, tm, tk⟩ => ?_
  refine loadArg_ok hp (tk.1 _ (by decide)) tk.2.1 tk.2.2
    (XFrame.of_outside (tm.mono (by decide) (by decide))) (by decide : 2 < 4) fun t' ht => ?_
  rw [hc] at ts tv tm
  have ts' := ts.of_upd ht (by decide)
  have tm' : Outside base 0 16 s.mem t'.mem := by rw [ht.mem]; exact tm
  have tk' : Keeps setupRegs s t' := (tk.mono (by simp [setupRegs])).trans (ht.rest (by decide))
  change WP isa (.block ((List.range 28).flatMap decodeLimb ++ initSlots)) t' _
  rw [WP.block_append_iff]
  refine WP.mono (decodeAll_ok ts' (by rw [ht.gpr]; exact hpoint)
    (by rw [ht.gpr]; exact hp.point_fit)
    (by intro j hj; rw [tk'.2.1, tk'.2.2]; exact hr j hj) hd) fun u ⟨ux, uy, um, uk⟩ => ?_
  have ub0 : Bounded u.mem base X1 := by intro j hj; rw [ux j hj]; exact decoded_lt _ _ _
  have ub3 : Bounded u.mem base X3 := by intro j hj; rw [uy j hj]; exact decoded_lt _ _ _
  have uv0 : E u.mem base 0 = toFe (VG.Proof.X25519.leNum (Spec.X448.bytesAt t'.mem p 56)) := by
    apply congrArg toFe
    exact (valN_congr ux).trans (decoded_val t'.mem p 28).symm
  have uv3 : E u.mem base 3 = E u.mem base 0 := congrArg toFe ((valN_congr uy).trans (valN_congr ux).symm)
  have byte : Spec.X448.bytesAt t'.mem p 56 = Spec.X448.bytesAt s.mem p 56 := by
    apply List.map_congr_left
    intro j hj
    exact tm' _ (Or.inr (Nat.le_trans (by decide) (hd j (List.mem_range.mp hj))))
  rw [byte] at uv0
  refine WP.mono (initSlots_ok (ts'.of_keeps uk (by decide)) ub0 ub3)
    fun v ⟨vb, v0, v1, v2, v3, v4, vw, vm, vk⟩ => ?_
  refine ⟨(ts'.of_keeps uk (by decide)).of_keeps vk (by decide), vb,
    tk'.trans ((uk.mono ?_).trans (vk.mono ?_)),
    (tm'.mono (by decide) (by decide)).trans ?_,
    ((show Saved base s.gpr t'.mem from ht.mem ▸ tv).outside2 um (by decide) (by decide)).outside vm (by decide),
    ?_, v1, v2, v3.trans (uv3.trans v0.symm), v4, vw⟩
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> decide
  · intro r h; simp only [List.mem_singleton] at h; subst r; decide
  · exact (show Outside base 0 8192 t'.mem u.mem from fun q h =>
      um q (by simp only [X1, slot]; omega_using [h]) (by simp only [X3, slot]; omega_using [h])).trans
      (vm.mono (by decide) (by decide))
  · rw [decodeUCoordinate_eq (length_bytesAt _ _ _)]
    exact v0.trans uv0

end VG.Proof.X448.X86
