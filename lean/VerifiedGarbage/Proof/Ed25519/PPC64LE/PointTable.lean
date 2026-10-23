module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointOps
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Packed
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Packed
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field

/-!
# Ed25519 on PPC64LE: points in tables

A table entry is a point's four coordinates, 128 bytes at an offset `o` of
the working space above the field area (`tableAt`). `pointToTable` with
`r14` at the entry writes the point of slots 0–3 there
(`pointToTable_ok`), and `pointFromTable` reads it into slots 0–3
(`pointFromTable_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE

theorem Ctx8.inW {b : Addr} {s : State} (h : Ctx8 b s) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions s.wr (b + BitVec.ofNat 64 d) n :=
  in_base h.wr hd (by omega)

theorem Ctx8.inR {b : Addr} {s : State} (h : Ctx8 b s) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 d) n :=
  in_base (List.mem_append_right _ h.wr) hd (by omega)

theorem Ctx8.of_rest {b : Addr} {s t : State} {R : List Reg} (h : Ctx8 b s) (hr : Rest R s t)
    (h6 : Reg.r6 ∉ R) : Ctx8 b t :=
  ⟨by rw [hr.gpr _ h6, h.r6], by rw [hr.wr]; exact h.wr⟩

/-- The point at offset `o`, as four elements. -/
def tableAt (m : Mem) (b : Addr) (o : Nat) : Spec.Ed25519.Point :=
  ⟨FS m b o, FS m b (o + 32), FS m b (o + 64), FS m b (o + 96)⟩

section
variable {b : Addr}

/-- After `j` coordinates of `pointToTable` from `s0`. -/
structure ToTableInv (b : Addr) (o : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r7] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 32 * j⟩] s0.mem s.mem
  outs : ∀ i < j, V s.mem b (o + 32 * i) = V s0.mem b (64 + 32 * i)

theorem pointToTable_ok {s : State} (hc : Ctx8 b s) {o : Nat} (h14 : s.gpr .r14 = b + BitVec.ofNat 64 o)
    (ho : 1024 ≤ o) (ho' : o + 128 ≤ 8192) :
    WP isa (.block pointToTable) s fun t =>
      Rest [.r7] s t ∧ Frame [⟨b + BitVec.ofNat 64 o, 128⟩] s.mem t.mem ∧
      tableAt t.mem b o = point (env s.mem b) 0 1 2 3 := by
  refine WP.mono (wp_range_flatMap (M := isa) (ToTableInv b o s) (fun j t hj h => ?_) 4 (Nat.le_refl _) s
    ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => by omega⟩) fun t h => ⟨h.rest, h.frame, ?_⟩
  · have hct : Ctx8 b t := hc.of_rest h.rest (by decide)
    refine WP.mono (packField_ok hct.ctx (q := b + BitVec.ofNat 64 o) (a := 64 + 32 * j) (dst := 32 * j)
      (by rw [h.rest.gpr _ (by decide), h14]) (by omega) (by omega)
      (fun k hk => by rw [Offset.add_add]; exact hct.inW (by omega))
      (by rw [Offset.add_add]; exact Offset.disjoint _ (by omega) (by omega) (by omega))) fun u hu => ?_
    have hf : Frame [⟨b + BitVec.ofNat 64 (o + 32 * j), 32⟩] t.mem u.mem := by
      have := hu.frame; rwa [Offset.add_add] at this
    have hsrc : V t.mem b (64 + 32 * j) = V s.mem b (64 + 32 * j) := by
      unfold V
      exact val32_congr (limb_frame h.frame fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
    refine ⟨h.rest.trans hu.rest, ?_, fun i hi => ?_⟩
    · refine (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)
      · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [← h.outs i hi]
        unfold V
        exact val32_congr (limb_frame hf fun r hr k hk => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
      · rw [← hsrc, V, V]
        refine val32_congr fun k hk => ?_
        have := hu.outs k hk
        rw [wd_shift] at this
        rw [limb, show o + 32 * i + 4 * k = o + (32 * i + 4 * k) by omega, this]
  · simp only [tableAt, point, env, FS]
    have e0 := h.outs 0 (by decide)
    have e1 := h.outs 1 (by decide)
    have e2 := h.outs 2 (by decide)
    have e3 := h.outs 3 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2 e3
    rw [e0, e1, e2, e3]
    rfl

/-- After `j` coordinates of `pointFromTable` from `s0`. -/
structure FromTableInv (b : Addr) (o : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r7] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 64, 32 * j⟩] s0.mem s.mem
  outs : ∀ i < j, V s.mem b (64 + 32 * i) = V s0.mem b (o + 32 * i)

theorem pointFromTable_ok {s : State} (hc : Ctx8 b s) {o : Nat} (h14 : s.gpr .r14 = b + BitVec.ofNat 64 o)
    (ho : 1024 ≤ o) (ho' : o + 128 ≤ 8192) :
    WP isa (.block pointFromTable) s fun t =>
      Rest [.r7] s t ∧ Frame [⟨b + BitVec.ofNat 64 64, 128⟩] s.mem t.mem ∧
      point (env t.mem b) 0 1 2 3 = tableAt s.mem b o ∧ ∀ i : Slot, 4 ≤ i.val → env t.mem b i = env s.mem b i := by
  refine WP.mono (wp_range_flatMap (M := isa) (FromTableInv b o s) (fun j t hj h => ?_) 4 (Nat.le_refl _) s
    ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => by omega⟩) fun t h => ⟨h.rest, h.frame, ?_, fun i hi => ?_⟩
  · have hct : Ctx8 b t := hc.of_rest h.rest (by decide)
    refine WP.mono (unpackField_ok hct.ctx (q := b + BitVec.ofNat 64 o) (o := 64 + 32 * j) (src := 32 * j)
      (by rw [h.rest.gpr _ (by decide), h14]) (by omega) (by omega)
      (fun k hk => by rw [Offset.add_add]; exact hct.inR (by omega))
      (by rw [Offset.add_add]; exact Offset.disjoint _ (by omega) (by omega) (by omega)))
      fun u ⟨ru, fu, lu⟩ => ?_
    have hsrc : V t.mem b (o + 32 * j) = V s.mem b (o + 32 * j) := by
      unfold V
      exact val32_congr (limb_frame h.frame fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega))
    refine ⟨h.rest.trans ru, ?_, fun i hi => ?_⟩
    · refine (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)
      · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [← h.outs i hi]
        unfold V
        exact val32_congr (limb_frame fu fun r hr k hk => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
      · rw [← hsrc, V, V]
        refine val32_congr fun k hk => ?_
        rw [lu k hk, wd_shift, limb, show o + 32 * i + 4 * k = o + (32 * i + 4 * k) by omega]
  · have e0 := h.outs 0 (by decide)
    have e1 := h.outs 1 (by decide)
    have e2 := h.outs 2 (by decide)
    have e3 := h.outs 3 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2 e3
    simp only [tableAt, point, env, FS]
    rw [show offset 0 = 64 from rfl, show offset 1 = 96 from rfl, show offset 2 = 128 from rfl,
      show offset 3 = 160 from rfl, e0, e1, e2, e3]
  · have hs := slot_range i
    unfold env FS V
    refine congrArg _ (val32_congr (limb_frame h.frame fun r hr k hk => ?_))
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by simp only [offset]; omega)) (by omega) (by omega)

end

end VG.Proof.Ed25519.PPC64LE
