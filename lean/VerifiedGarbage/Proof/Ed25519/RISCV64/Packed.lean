module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Scalar
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.RISCV64.Field

/-!
# Ed25519 on RISC-V: elements to and from memory outside the working space

`packField p a dst` stores the eight words of the element at `a` of the
working space as the bytes at `dst` from the pointer in `p`, a word at a time
(`storeLE32`; `packField_ok`), and `unpackField p o src` loads eight words
from `src` at `p` (`loadLE32`) into the element at `o` (`unpackField_ok`),
for buffers apart from the element.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64

theorem not_a4_a5 {r : Reg} (h : r ∉ [Reg.a4, .a5]) : r ≠ .a4 ∧ r ≠ .a5 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact h

/-- After `k` words of `packField p a dst` from `s0`. -/
structure PackInv (b q : Addr) (a dst : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a5] s0 s
  frame : Frame [⟨q + BitVec.ofNat 64 dst, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem q (dst + 4 * j) = limb s0.mem b a j

theorem packField_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) {p : Reg}
    (hp : p ∉ [Reg.a4, .a5]) (h14 : s0.gpr p = q) {a dst : Nat}
    (ha : a + 32 ≤ 2048) (ha4 : a % 4 = 0) (hdst : dst + 32 < 2048)
    (hw : ∀ k < 8, InRegions s0.wr (q + BitVec.ofNat 64 (dst + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 dst, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 32⟩) :
    WP isa (.block (packField p a dst)) s0 (PackInv b q a dst s0 8) := by
  have hp' := not_a4_a5 hp
  refine wp_range_flatMap (M := isa) (PackInv b q a dst s0) (fun k s hk h => ?_)
    8 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  refine lw0_ok hcs (d := a + 4 * k) (by omega) (by omega) fun t1 v1 => ?_
  have hq1 : t1.gpr p = q := by rw [v1.other _ hp'.1, h.rest.gpr _ hp, h14]
  refine WP.mono (ByteLoad.storeLE32_ok (v := .a4) (tmp := .a5) (n := p) (off := dst + 4 * k)
    (by decide) hp'.2.symm (by omega) (by rw [hq1, v1.wr, h.rest.wr]; exact hw k hk)) fun t2 e2 => ?_
  have em : t2.mem = s.mem.writeW (q + BitVec.ofNat 64 (dst + 4 * k)) ((t1.gpr .a4).setWidth 32) := by
    rw [e2, RegUpd.mem_write, hq1]
    show t1.mem.writeW _ _ = _
    rw [v1.mem]
  have hr2 : Rest [.a4, .a5] t1 t2 := by
    rw [e2]
    exact ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr).2, rfl, rfl, rfl⟩
  have hsrc : wd s.mem b (a + 4 * k) = limb s0.mem b a k := by
    refine wd_frame h.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine fun x hx hx' => hd x ?_ ?_
    · exact Region.sub_prefix (by omega) x hx'
    · exact Offset.sub b (d := a + 4 * k) (n := 4) (e := a) (k := 32) (by omega) (by omega) x hx
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans hr2), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.outs j hj
    · rw [wd_write_self, toNat_lo32, v1.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
      exact hsrc

/-- After `k` words of `unpackField p o src` from `s0`. -/
structure UnpackInv (b : Addr) (o : Nat) (s0 : State) (f : Nat → Nat) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a5] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, limb s.mem b o j = f j

/-- `unpackField p o src`: the words at `src` from `p` into the element at `o`. -/
theorem unpackField_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) {p : Reg}
    (hp : p ∉ [Reg.a4, .a5]) (h14 : s0.gpr p = q) {o src : Nat}
    (ho : o + 32 ≤ 2048) (ho4 : o % 4 = 0) (hsrc : src + 32 < 2048)
    (hr : ∀ k < 8, InRegions (s0.rd ++ s0.wr) (q + BitVec.ofNat 64 (src + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 src, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 o, 32⟩) :
    WP isa (.block (unpackField p o src)) s0 fun t =>
      Rest [.a4, .a5] s0 t ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s0.mem t.mem ∧
      ∀ j < 8, limb t.mem b o j = wd s0.mem q (src + 4 * j) := by
  have hp' := not_a4_a5 hp
  let f := fun k => wd s0.mem q (src + 4 * k)
  refine WP.mono (wp_range_flatMap (M := isa) (UnpackInv b o s0 f) (fun k s hk h => ?_)
    8 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩)
    fun t ht => ⟨ht.rest, ht.frame, ht.outs⟩
  have hq : s.gpr p = q := by rw [h.rest.gpr _ hp, h14]
  refine WP.append (ByteLoad.loadLE32_ok (d := .a4) (tmp := .a5) (n := p) (off := src + 4 * k)
    hp'.1.symm hp'.2.symm (by decide) (by omega)
    (by rw [hq, h.rest.rd, h.rest.wr]; exact hr k hk)) fun t1 e1 => ?_
  have hr1 : Rest [.a4, .a5] s t1 := by
    rw [e1]
    refine ⟨fun r hr' => ?_, rfl, rfl, rfl⟩
    rw [RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr').1, RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr').2]
  have hm1 : t1.mem = s.mem := by rw [e1]; rfl
  have hv : (t1.gpr .a4).toNat % 2 ^ 32 = f k := by
    rw [e1, RegUpd.gpr_write_self, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _), hq]
    show wd s.mem q (src + 4 * k) = _
    refine wd_frame h.frame fun r hr' => ?_
    rw [List.mem_singleton.mp hr']
    refine fun x hx hx' => hd x ?_ ?_
    · exact Offset.sub q (d := src + 4 * k) (n := 4) (e := src) (k := 32) (by omega) (by omega) x hx
    · exact Region.sub_prefix (by omega) x hx'
  refine sw0_ok ((hc.of_rest h.rest (by decide)).of_rest hr1 (by decide))
    (by omega) (by omega) fun u hu => WP.block_nil ?_
  have em : u.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 4 * k)) ((t1.gpr .a4).setWidth 32) := by
    rw [hu.mem, hm1]
  refine ⟨h.rest.trans (hr1.trans (hu.rest _)), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [limb, em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.outs j hj
    · rw [wd_write_self, toNat_lo32, hv]

end VG.Proof.Ed25519.RISCV64
