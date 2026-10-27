module

public import VerifiedGarbage.Impl.Ed448.RISCV64.Scalar
public import VerifiedGarbage.Proof.X448.RISCV64.Field
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.X448.RISCV64.Freeze
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.X25519.RISCV64.Pass

/-!
# Ed448 on RISCV64: remainders to memory outside the working space

`packWords a n` copies the `n` words at `a` of the working space to the
aligned words at `t3` (`packWords_ok`), and `scalarFinish` the remainder at
`SR` to the 57 bytes at `out` (`a0`), a byte at a time: its fourteen words and
a zero byte, the encoding of a number below `2⁴⁴⁸` (`finish_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519

/-- After `k` words of `packWords a n` from `s0`. -/
structure PackInv (b q : Addr) (a : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4] s0 s
  frame : Frame [⟨q, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem q (4 * j) = limb s0.mem b a j

theorem packWords_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) (h14 : s0.gpr .t3 = q) {a n : Nat}
    (ha : a + 4 * n ≤ 2048) (hn : 4 * n < 2048) (ha4 : a % 4 = 0)
    (hq4 : ∀ k < n, (q + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0)
    (hw : ∀ k < n, InRegions s0.wr (q + BitVec.ofNat 64 (4 * k)) 4)
    (hd : (⟨q, 4 * n⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 4 * n⟩) :
    WP isa (.block (packWords a n)) s0 (PackInv b q a s0 n) := by
  refine wp_range_flatMap (M := isa) (PackInv b q a s0) (fun k s hk h => ?_)
    n (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  unfold packStep
  refine lw0_ok hcs (d := a + 4 * k) (by omega) (by omega) fun t1 v1 => ?_
  refine wp_stw (a := q + BitVec.ofNat 64 (4 * k)) (by omega)
    (by rw [v1.other _ (by decide), h.rest.gpr _ (by decide), h14]) (hq4 k hk)
    (by rw [v1.wr, h.rest.wr]; exact hw k hk) fun t2 v2 => WP.block_nil ?_
  have em : t2.mem = s.mem.writeW (q + BitVec.ofNat 64 (4 * k)) ((t1.gpr .a4).setWidth 32) := by
    rw [v2.mem, v1.mem]
  have hsrc : wd s.mem b (a + 4 * k) = limb s0.mem b a k := by
    refine wd_frame h.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine fun x hx hx' => hd x ?_ ?_
    · exact Region.sub_prefix (by omega) x hx'
    · exact Offset.sub b (d := a + 4 * k) (n := 4) (e := a) (k := 4 * n) (by omega) (by omega) x hx
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans (v2.rest _)), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.outs j hj
    · rw [wd_write_self, toNat_lo32, v1.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
      exact hsrc

theorem pow448_256 : (256 : Nat) ^ 56 = 2 ^ 224 * 2 ^ 224 := by decide +kernel

/-- The 57 bytes of a number below `2⁴⁴⁸`: its 56 bytes and a zero byte. -/
theorem encodeLE_57_zero {x : Nat} (hx : x < 2 ^ 224 * 2 ^ 224) :
    Spec.Ed448.encodeLE 57 x = Proof.X25519.leBytes 56 x ++ [0] := by
  rw [Proof.Ed448.encodeLE_eq, show 57 = 56 + 1 from rfl, Proof.X25519.leBytes_add, Proof.Ed448.leBytes_one,
    Nat.div_eq_of_lt (by rw [pow448_256]; exact hx)]
  rfl

/-- The output of `scalarFinish` from `s0`, after `j` words. -/
structure FinInv (q : Addr) (r : Nat → Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a5] s0 s
  frame : Frame [⟨q, 4 * j⟩] s0.mem s.mem
  words : ∀ i < j, wd s.mem q (4 * i) = r i

theorem outWords_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) (h3 : s0.gpr .a0 = q)
    (hw : (⟨q, 57⟩ : Region) ∈ s0.wr) (hd : (⟨q, 57⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 SR, 56⟩) :
    WP isa (.block ((List.range 14).flatMap outStep)) s0 (FinInv q (limb s0.mem b SR) s0 14) := by
  have hS : SR = 0 := rfl
  refine wp_range_flatMap (M := isa) (FinInv q (limb s0.mem b SR) s0) (fun k s hk h => ?_)
    14 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  unfold outStep
  refine lw0_ok hcs (d := SR + 4 * k) (by omega) (by omega) fun t1 v1 => ?_
  have e3 : t1.gpr .a0 = q := by rw [v1.other _ (by decide), h.rest.gpr _ (by decide), h3]
  have hwr : t1.wr = s0.wr := by rw [v1.wr, h.rest.wr]
  refine WP.mono (ByteLoad.storeLE32_ok (by decide) (by decide) (by omega)
    (by rw [e3, hwr]; exact in_base hw (by omega) (by omega))) fun t2 e2 => ?_
  have v2 : Rest [.a5] t1 t2 := by
    rw [e2]
    exact ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩
  have em : t2.mem = s.mem.writeW (q + BitVec.ofNat 64 (4 * k)) ((t1.gpr .a4).setWidth 32) := by
    rw [e2, RegUpd.mem_write, e3]
    show t1.mem.writeW _ _ = _
    rw [v1.mem]
  have hsrc : wd s.mem b (SR + 4 * k) = limb s0.mem b SR k := by
    refine wd_frame h.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine fun x hx hx' => hd x ?_ ?_
    · exact Region.sub_prefix (by omega) x hx'
    · exact Offset.sub b (d := SR + 4 * k) (n := 4) (e := SR) (k := 56) (by omega) (by omega) x hx
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans (v2.mono (by decide))), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.words j hj
    · rw [wd_write_self, toNat_lo32, v1.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
      exact hsrc

/-- **The remainder at `SR`** as the 57 bytes at `out` (`a0`). -/
theorem finish_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) (h3 : s0.gpr .a0 = q)
    (hw : (⟨q, 57⟩ : Region) ∈ s0.wr)
    (hd : (⟨q, 57⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 SR, 56⟩) :
    WP isa (.block scalarFinish) s0 fun t =>
      Rest [.a4, .a5] s0 t ∧ Frame [⟨q, 57⟩] s0.mem t.mem ∧
      Spec.Ed448.bytesAt t.mem q 57 = Spec.Ed448.encodeLE 57 (V s0.mem b SR) := by
  unfold scalarFinish
  refine WP.append (outWords_ok hc h3 hw hd) fun s1 h1 => ?_
  refine wp_li (by decide) fun s2 u2 => ?_
  refine wp_sb (a := q + BitVec.ofNat 64 56) (by decide)
    (by rw [u2.other _ (by decide), h1.rest.gpr _ (by decide), h3])
    (by rw [u2.wr, h1.rest.wr]; exact in_base hw (by decide) (by decide)) fun s3 u3 => WP.block_nil ?_
  have hm3 : s3.mem = s1.mem.writeW (q + BitVec.ofNat 64 56) (0 : BitVec 8) := by
    rw [u3.mem, u2.gpr, u2.mem]; rfl
  refine ⟨h1.rest.trans ((u2.rest (by decide)).trans (u3.rest _)), ?_, ?_⟩
  · rw [hm3]
    exact (h1.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (n := 8 / 8) (by decide) (by decide))
  · have hlt := V_lt s0.mem b SR
    rw [encodeLE_57_zero hlt, show (57 : Nat) = 56 + 1 from rfl, Proof.Ed448.bytesAt_eq,
      Proof.X25519.bytesAt_add, ← Proof.Ed448.bytesAt_eq]
    congr 1
    · have f3 : Frame [⟨q + BitVec.ofNat 64 56, 1⟩] s1.mem s3.mem := by
        rw [hm3]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Region.contains_self _ (8 / 8))
      have e : ∀ j < 14, wd s3.mem q (4 * j) = limb s0.mem b SR j := fun j hj => by
        rw [wd_frame f3 fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact Offset.disjoint q (d := 4 * j) (n := 4) (e := 56) (k := 1) (.inl (by omega)) (by omega) (by omega)]
        exact h1.words j hj
      exact bytesAt_words14 _ _ e
    · show [s3.mem (q + BitVec.ofNat 64 56 + BitVec.ofNat 64 0)] = [0]
      rw [hm3, VG.WriteBytes.writeW8_apply]
      exact congrArg (· :: []) (ite_eq_left (by simp))

end VG.Proof.Ed448.RISCV64
