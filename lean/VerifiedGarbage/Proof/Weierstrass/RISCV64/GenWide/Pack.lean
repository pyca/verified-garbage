module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Product
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed

/-!
# Arithmetic modulo a wide modulus on RISC-V: the byte-wise copies

`pack k p a dst` and `unpack k p o src` (`Impl/Weierstrass/RISCV64/GenWide.lean`),
as P-384's (`Proof/Weierstrass/RISCV64/P384Field/Fn.lean`) for `2 k` words of 32
bits: the `8 k` bytes of the element at `a` (from `a3`) to `p + dst`
(`pack_ok`), and back (`unpack_ok`), any of them unaligned.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Weierstrass.RISCV64.GenWide VG.Proof.X25519.RISCV64
open VG.Proof.Ed25519.RISCV64 (not_a4_a5)
open VG.Proof.X448.RISCV64.R64 (dw dw_split colsV)

/-- After `j` words of `pack k p a dst` from `s0`. -/
structure PackInv (b q : Addr) (a dst : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a5] s0 s
  frame : Frame [⟨q + BitVec.ofNat 64 dst, 4 * j⟩] s0.mem s.mem
  outs : ∀ i < j, wd s.mem q (dst + 4 * i) = limb s0.mem b a i

theorem pack_ok {k : Nat} {b q : Addr} {s0 : State} (hc : Ctx b s0) {p : Reg}
    (hp : p ∉ [Reg.a4, .a5]) (h14 : s0.gpr p = q) {a dst : Nat}
    (ha : a + 8 * k ≤ 2048) (ha4 : a % 4 = 0) (hdst : dst + 8 * k < 2048)
    (hw : ∀ j < 2 * k, InRegions s0.wr (q + BitVec.ofNat 64 (dst + 4 * j)) 4)
    (hd : (⟨q + BitVec.ofNat 64 dst, 8 * k⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 8 * k⟩) :
    WP isa (.block (pack k p a dst)) s0 (PackInv b q a dst s0 (2 * k)) := by
  have hp' := not_a4_a5 hp
  refine wp_range_flatMap (M := isa) (PackInv b q a dst s0) (fun j s hj h => ?_)
    (2 * k) (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => by omega⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  refine lw0_ok hcs (d := a + 4 * j) (by omega) (by omega) fun t1 v1 => ?_
  have hq1 : t1.gpr p = q := by rw [v1.other _ hp'.1, h.rest.gpr _ hp, h14]
  refine WP.mono (ByteLoad.storeLE32_ok (v := .a4) (tmp := .a5) (n := p) (off := dst + 4 * j)
    (by decide) hp'.2.symm (by omega) (by rw [hq1, v1.wr, h.rest.wr]; exact hw j hj)) fun t2 e2 => ?_
  have em : t2.mem = s.mem.writeW (q + BitVec.ofNat 64 (dst + 4 * j)) ((t1.gpr .a4).setWidth 32) := by
    rw [e2, RegUpd.mem_write, hq1]
    show t1.mem.writeW _ _ = _
    rw [v1.mem]
  have hr2 : Rest [.a4, .a5] t1 t2 := by
    rw [e2]
    exact ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr).2, rfl, rfl, rfl⟩
  have hsrc : wd s.mem b (a + 4 * j) = limb s0.mem b a j := by
    refine wd_frame h.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine fun x hx hx' => hd x ?_ ?_
    · exact Region.sub_prefix (by omega) x hx'
    · exact Offset.sub b (d := a + 4 * j) (n := 4) (e := a) (k := 8 * k) (by omega) (by omega) x hx
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans hr2), ?_, fun i hi => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.outs i hi
    · rw [wd_write_self, toNat_lo32, v1.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
      exact hsrc

/-- After `j` words of `unpack k p o src` from `s0`. -/
structure UnpackInv (b : Addr) (o : Nat) (s0 : State) (f : Nat → Nat) (j : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a5] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 4 * j⟩] s0.mem s.mem
  outs : ∀ i < j, limb s.mem b o i = f i

/-- `unpack k p o src`: the words at `src` from `p` into the element at `o`. -/
theorem unpack_ok {k : Nat} {b q : Addr} {s0 : State} (hc : Ctx b s0) {p : Reg}
    (hp : p ∉ [Reg.a4, .a5]) (h14 : s0.gpr p = q) {o src : Nat}
    (ho : o + 8 * k ≤ 2048) (ho4 : o % 4 = 0) (hsrc : src + 8 * k < 2048)
    (hr : ∀ j < 2 * k, InRegions (s0.rd ++ s0.wr) (q + BitVec.ofNat 64 (src + 4 * j)) 4)
    (hd : (⟨q + BitVec.ofNat 64 src, 8 * k⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 o, 8 * k⟩) :
    WP isa (.block (unpack k p o src)) s0 fun t =>
      Rest [.a4, .a5] s0 t ∧ Frame [⟨b + BitVec.ofNat 64 o, 8 * k⟩] s0.mem t.mem ∧
      ∀ i < 2 * k, limb t.mem b o i = wd s0.mem q (src + 4 * i) := by
  have hp' := not_a4_a5 hp
  let f := fun j => wd s0.mem q (src + 4 * j)
  refine WP.mono (wp_range_flatMap (M := isa) (UnpackInv b o s0 f) (fun j s hj h => ?_)
    (2 * k) (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => by omega⟩)
    fun t ht => ⟨ht.rest, by rw [show 8 * k = 4 * (2 * k) by omega]; exact ht.frame, ht.outs⟩
  have hq' : s.gpr p = q := by rw [h.rest.gpr _ hp, h14]
  refine WP.append (ByteLoad.loadLE32_ok (d := .a4) (tmp := .a5) (n := p) (off := src + 4 * j)
    hp'.1.symm hp'.2.symm (by decide) (by omega)
    (by rw [hq', h.rest.rd, h.rest.wr]; exact hr j hj)) fun t1 e1 => ?_
  have hr1 : Rest [.a4, .a5] s t1 := by
    rw [e1]
    refine ⟨fun r hr' => ?_, rfl, rfl, rfl⟩
    rw [RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr').1, RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr').2]
  have hm1 : t1.mem = s.mem := by rw [e1]; rfl
  have hv : (t1.gpr .a4).toNat % 2 ^ 32 = f j := by
    rw [e1, RegUpd.gpr_write_self, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _), hq']
    show wd s.mem q (src + 4 * j) = _
    refine wd_frame h.frame fun r hr' => ?_
    rw [List.mem_singleton.mp hr']
    refine fun x hx hx' => hd x ?_ ?_
    · exact Offset.sub q (d := src + 4 * j) (n := 4) (e := src) (k := 8 * k) (by omega) (by omega) x hx
    · exact Region.sub_prefix (by omega) x hx'
  refine sw0_ok ((hc.of_rest h.rest (by decide)).of_rest hr1 (by decide))
    (by omega) (by omega) fun u hu => WP.block_nil ?_
  have em : u.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 4 * j)) ((t1.gpr .a4).setWidth 32) := by
    rw [hu.mem, hm1]
  refine ⟨h.rest.trans (hr1.trans (hu.rest _)), ?_, fun i hi => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [limb, em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.outs i hi
    · rw [wd_write_self, toNat_lo32, hv]

/-- `k` doublewords are their `2 k` words. -/
theorem dv_congr_wd {k : Nat} {m m' : Mem} {O O' : Addr} (h : ∀ j < 2 * k, wd m' O' (4 * j) = wd m O (4 * j)) :
    colsV (fun i => dw m' O' (8 * i)) k = colsV (fun i => dw m O (8 * i)) k := by
  have e : ∀ {n}, n ≤ k → colsV (fun i => dw m' O' (8 * i)) n = colsV (fun i => dw m O (8 * i)) n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [colsV]
      rw [ih (by omega), dw_split, dw_split, show 8 * n = 4 * (2 * n) by omega,
        show 4 * (2 * n) + 4 = 4 * (2 * n + 1) by omega, h _ (by omega), h _ (by omega)]
  exact e (Nat.le_refl _)

end VG.Proof.Weierstrass.RISCV64.GenWide
