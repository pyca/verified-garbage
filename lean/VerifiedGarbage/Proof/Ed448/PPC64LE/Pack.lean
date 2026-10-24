module

public import VerifiedGarbage.Impl.Ed448.PPC64LE.Scalar
public import VerifiedGarbage.Proof.X448.PPC64LE.Field
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.X448.PPC64LE.Freeze
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass

/-!
# Ed448 on PPC64LE: remainders to memory outside the working space

`packWords a n` copies the `n` words at `a` of the working space to the
bytes at `r14` (`packWords_ok`), and `packScalar a` the remainder at `a` as
57 bytes: its fourteen words and a zero byte, the encoding of a number below
`2⁴⁴⁸` (`packScalar_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame

/-- After `k` words of `packWords a n` from `s0`. -/
structure PackInv (b q : Addr) (a : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r7] s0 s
  frame : Frame [⟨q, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem q (4 * j) = limb s0.mem b a j

theorem packWords_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) (h14 : s0.gpr .r14 = q) {a n : Nat}
    (ha : a + 4 * n ≤ 4096) (hn : 4 * n < 2 ^ 15)
    (hw : ∀ k < n, InRegions s0.wr (q + BitVec.ofNat 64 (4 * k)) 4)
    (hd : (⟨q, 4 * n⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 4 * n⟩) :
    WP isa (.block (packWords a n)) s0 (PackInv b q a s0 n) := by
  refine wp_range_flatMap (M := isa) (PackInv b q a s0) (fun k s hk h => ?_)
    n (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  unfold packStep
  refine lw0_ok hcs (d := a + 4 * k) (by omega) fun t1 v1 => ?_
  refine wp_sw (a := q + BitVec.ofNat 64 (4 * k)) (by decide) (by omega)
    (by rw [v1.other _ (by decide), h.rest.gpr _ (by decide), h14])
    (by rw [v1.wr, h.rest.wr]; exact hw k hk) fun t2 v2 => WP.block_nil ?_
  have em : t2.mem = s.mem.writeW (q + BitVec.ofNat 64 (4 * k)) ((t1.gpr .r7).setWidth 32) := by
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

/-- **The remainder at `a`** as the 57 bytes at `r14`. -/
theorem packScalar_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) (h14 : s0.gpr .r14 = q) {a : Nat}
    (ha : a + 56 ≤ 4096) (hw : (⟨q, 57⟩ : Region) ∈ s0.wr)
    (hd : (⟨q, 57⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 56⟩) :
    WP isa (.block (packScalar a)) s0 fun t =>
      Rest [.r7] s0 t ∧ Frame [⟨q, 57⟩] s0.mem t.mem ∧
      Spec.Ed448.bytesAt t.mem q 57 = Spec.Ed448.encodeLE 57 (V s0.mem b a) := by
  unfold packScalar
  refine WP.append (packWords_ok hc h14 (n := 14) (by omega) (by decide)
    (fun k hk => in_base hw (by omega) (by omega))
    (hd.sub_left (Region.sub_prefix (by decide)))) fun s1 h1 => ?_
  refine wp_li (by decide) fun s2 u2 => ?_
  refine wp_stb (a := q + BitVec.ofNat 64 56) (by decide) (by decide)
    (by rw [u2.other _ (by decide), h1.rest.gpr _ (by decide), h14])
    (by rw [u2.wr, h1.rest.wr]; exact in_base hw (by decide) (by decide)) fun s3 u3 => WP.block_nil ?_
  have hm3 : s3.mem = s1.mem.writeW (q + BitVec.ofNat 64 56) (0 : BitVec 8) := by
    rw [u3.mem, u2.gpr, u2.mem]; rfl
  refine ⟨h1.rest.trans ((u2.rest (by decide)).trans (u3.rest _)), ?_, ?_⟩
  · rw [hm3]
    exact (h1.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (n := 8 / 8) (by decide) (by decide))
  · have hlt := V_lt s0.mem b a
    rw [encodeLE_57_zero hlt, show (57 : Nat) = 56 + 1 from rfl, Proof.Ed448.bytesAt_eq,
      Proof.X25519.bytesAt_add, ← Proof.Ed448.bytesAt_eq]
    congr 1
    · have f3 : Frame [⟨q + BitVec.ofNat 64 56, 1⟩] s1.mem s3.mem := by
        rw [hm3]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Region.contains_self _ (8 / 8))
      have e : ∀ j < 14, wd s3.mem q (4 * j) = limb s0.mem b a j := fun j hj => by
        rw [wd_frame f3 fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact Offset.disjoint q (d := 4 * j) (n := 4) (e := 56) (k := 1) (.inl (by omega)) (by omega) (by omega)]
        exact h1.outs j hj
      exact bytesAt_words14 _ _ e
    · show [s3.mem (q + BitVec.ofNat 64 56 + BitVec.ofNat 64 0)] = [0]
      rw [hm3, VG.WriteBytes.writeW8_apply]
      exact congrArg (· :: []) (ite_eq_left (by simp))

end VG.Proof.Ed448.PPC64LE
