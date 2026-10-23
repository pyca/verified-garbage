module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Packed
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field

/-!
# Ed25519 on PPC64LE: elements to and from memory outside the working space

`packField a dst` copies the eight words of the element at `a` of the working
space to `dst` at `r14` (`packField_ok`), and `unpackField o src` copies
eight words from `src` at `r14` to the element at `o` (`unpackField_ok`), for
buffers apart from the element.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE

/-- After `k` words of `packField a dst` from `s0`. -/
structure PackInv (b q : Addr) (a dst : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r7] s0 s
  frame : Frame [⟨q + BitVec.ofNat 64 dst, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem q (dst + 4 * j) = limb s0.mem b a j

theorem packField_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) (h14 : s0.gpr .r14 = q) {a dst : Nat}
    (ha : a + 32 ≤ 4096) (hdst : dst + 32 < 2 ^ 15)
    (hw : ∀ k < 8, InRegions s0.wr (q + BitVec.ofNat 64 (dst + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 dst, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 32⟩) :
    WP isa (.block (packField a dst)) s0 (PackInv b q a dst s0 8) := by
  refine wp_range_flatMap (M := isa) (PackInv b q a dst s0) (fun k s hk h => ?_)
    8 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  unfold packStep
  refine lw0_ok hcs (d := a + 4 * k) (by omega) fun t1 v1 => ?_
  refine wp_sw (a := q + BitVec.ofNat 64 (dst + 4 * k)) (by decide) (by omega)
    (by rw [v1.other _ (by decide), h.rest.gpr _ (by decide), h14])
    (by rw [v1.wr, h.rest.wr]; exact hw k hk) fun t2 v2 => WP.block_nil ?_
  have em : t2.mem = s.mem.writeW (q + BitVec.ofNat 64 (dst + 4 * k)) ((t1.gpr .r7).setWidth 32) := by
    rw [v2.mem, v1.mem]
  have hsrc : wd s.mem b (a + 4 * k) = limb s0.mem b a k := by
    refine wd_frame h.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine fun x hx hx' => hd x ?_ ?_
    · exact Region.sub_prefix (by omega) x hx'
    · exact Offset.sub b (d := a + 4 * k) (n := 4) (e := a) (k := 32) (by omega) (by omega) x hx
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans (v2.rest _)), ?_, fun j hj => ?_⟩
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

/-- `unpackField o src`: the words at `src` from `r14` into the element at `o`. -/
theorem unpackField_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) (h14 : s0.gpr .r14 = q) {o src : Nat}
    (ho : o + 32 ≤ 4096) (hsrc : src + 32 < 2 ^ 15)
    (hr : ∀ k < 8, InRegions (s0.rd ++ s0.wr) (q + BitVec.ofNat 64 (src + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 src, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 o, 32⟩) :
    WP isa (.block (unpackField o src)) s0 fun t =>
      Rest [.r7] s0 t ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s0.mem t.mem ∧
      ∀ j < 8, limb t.mem b o j = wd s0.mem q (src + 4 * j) := by
  refine WP.mono (fill_ok (f := fun k => wd s0.mem q (src + 4 * k)) hc ho fun k hk s h => ?_)
    fun t ht => ⟨ht.rest, ht.frame, ht.outs⟩
  unfold unpackSrc
  refine wp_lw (a := q + BitVec.ofNat 64 (src + 4 * k)) (by decide) (by omega)
    (by rw [h.rest.gpr _ (by decide), h14]) (by rw [h.rest.rd, h.rest.wr]; exact hr k hk)
    fun t1 v1 => WP.block_nil ⟨?_, v1.rest (by decide), v1.mem⟩
  rw [v1.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
  show wd s.mem q (src + 4 * k) = _
  refine wd_frame h.frame fun r hr' => ?_
  rw [List.mem_singleton.mp hr']
  refine fun x hx hx' => hd x ?_ ?_
  · exact Offset.sub q (d := src + 4 * k) (n := 4) (e := src) (k := 32) (by omega) (by omega) x hx
  · exact Region.sub_prefix (by omega) x hx'

end VG.Proof.Ed25519.PPC64LE
