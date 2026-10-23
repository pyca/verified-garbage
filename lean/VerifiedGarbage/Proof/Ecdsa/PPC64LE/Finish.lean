module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ECDSA on PPC64LE: the results and the restore

What writing a result shares: the bytes of a range apart from the one that
changed (`bytesAt_keep`), a range changed at an offset (`outside_shift`), and
`restore`, which reloads `lr`, `r14` and `r31` from the working space
(`restore_ok`), as on 32-bit ARM (`Proof/Ecdsa/Arm/Finish.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE

/-- The bytes of a range apart from the one that changed. -/
theorem bytesAt_keep {q p : Addr} {len k : Nat} {m m' : Mem} (h : Outside q 0 len m m')
    (hd : Region.Disjoint ⟨p, k⟩ ⟨q, len⟩) (hl : len ≤ 2 ^ 64) (hk : k ≤ 2 ^ 64) :
    Spec.Ecdsa.bytesAt m' p k = Spec.Ecdsa.bytesAt m p k := by
  simp only [Spec.Ecdsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact keep_of_disjoint' h hd hl hi hk

/-- A range changed at `p + d` is one changed at offset `d` of `p`. -/
theorem outside_shift {p : Addr} {d len : Nat} {m m' : Mem}
    (h : Outside (p + BitVec.ofNat 64 d) 0 len m m') (hd : d + len ≤ 2 ^ 64) : Outside p d len m m' :=
  fun x hx => h x (Or.inr (by
    show 0 + len ≤ (x - (p + BitVec.ofNat 64 d)).toNat
    rcases Nat.lt_or_ge (x - (p + BitVec.ofNat 64 d)).toNat len with hlt | hge
    · have := (Offset.lt_iff x p hd).mp hlt
      simp only [ofs] at hx
      omega
    · omega))

theorem mask_bit (b : Bool) : (mask64 (b = true) &&& BitVec.ofNat 64 1 : BitVec 64) = if b then 1 else 0 := by
  cases b <;> decide

theorem restore_eq : Cfg.restore =
    [.load .d .r0 wb Cfg.lrAt, .mtlr .r0, .load .d .r14 wb 0, .load .d .r31 wb 8] := rfl

/-- `lr`, `r14` and `r31` from the working space. -/
theorem restore_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    (hsz : 24 ≤ size) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Rk [.r0, .r14, .r31] s t → t.mem = s.mem → t.lr = word s.mem base Cfg.lrAt →
      t.gpr .r14 = word s.mem base 0 → t.gpr .r31 = word s.mem base 8 → WP isa (.block is) t Q) :
    WP isa (.block (Cfg.restore ++ is)) s Q := by
  rw [restore_eq, List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_step (ld0_ok hs h3 (by decide) (by decide) (by simp only [Cfg.lrAt]; omega)) ?_
  refine wp_step exec_mtlr ?_
  simp only [write_gpr, ite_true]
  have hs₂ : Ws { s.write .r0 (word s.mem base Cfg.lrAt) with lr := word s.mem base Cfg.lrAt } base size :=
    hs.of_wr rfl
  have h3₂ : At { s.write .r0 (word s.mem base Cfg.lrAt) with lr := word s.mem base Cfg.lrAt } base .r3 0 :=
    h3.write (d := .r0) (word s.mem base Cfg.lrAt)
  refine wp_step (ld0_ok hs₂ h3₂ (by decide) (by decide) (by omega)) ?_
  refine wp_step (ld0_ok (hs₂.write .r14 (word s.mem base 0)) (h3₂.write (d := .r14) (word s.mem base 0)) (by decide) (by decide) (by omega)) ?_
  refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ rfl ?_ ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false]
  · simp only [write_lr]
  · simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true]
  · simp only [write_gpr, write_mem, ite_true]

end VG.Proof.Ecdsa.PPC64LE
