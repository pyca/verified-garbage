module

import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Copy
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Spec.MlDsa.Poly
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Copy
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Base
public import VerifiedGarbage.Proof.MlDsa.Sign.Iter
public import VerifiedGarbage.Spec.MlDsa
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.Framework.RelCT

/-! # Immutable canonical polynomials across shared-kernel phases -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr)

structure ReadCache (count S : Nat) (f : Nat → Poly) (s : State) : Prop where
  small : count < 2 ^ 22
  readable : Covers [⟨s.gpr .x21, 1024 * count⟩] (s.rd ++ s.wr)
  writable : ∀ R ∈ s.wr, (⟨s.gpr .x21, 1024 * count⟩ : Region).Disjoint R
  stack : (⟨s.gpr .x21, 1024 * count⟩ : Region).Disjoint (below s.sp S)
  values : ∀ i < count, PolyIs s.mem (pa s (.x21, 1024 * i)) (f i)

theorem ReadCache.inR {count S : Nat} {f : Nat → Poly} {s : State}
    (h : ReadCache count S f s) {i : Nat} (hi : i < count) :
    InRegions (s.rd ++ s.wr) (pa s (.x21, 1024 * i)) 1024 := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .x21) (1024 * count) :=
    h.readable _ _ ⟨_, by simp, Region.contains_self _ _⟩
  exact inRegions_sub hr (by omega) (by have := h.small; omega)

theorem ReadCache.apart_write {count S : Nat} {f : Nat → Poly} {s : State}
    (h : ReadCache count S f s) {p : Addr} {n : Nat} (hp : InRegions s.wr p n) :
    (⟨s.gpr .x21, 1024 * count⟩ : Region).Disjoint ⟨p, n⟩ := by
  obtain ⟨R, hR, hp⟩ := hp
  intro a ha hb
  apply h.writable R hR a ha
  apply hp.byte
  change (a - p).toNat + 1 ≤ n at hb
  omega

theorem ReadCache.slice_sub {count S : Nat} {f : Nat → Poly} {s : State}
    (_h : ReadCache count S f s) {i : Nat} (hi : i < count) :
    Region.Sub ⟨pa s (.x21, 1024 * i), 1024⟩ ⟨s.gpr .x21, 1024 * count⟩ :=
  Offset.sub_base _ (by omega)

theorem ReadCache.step {count S : Nat} {f : Nat → Poly} {s t : State}
    (h : ReadCache count S f s) {ws : List (Ptr × Nat)} (hp : PPostB S s t ws)
    (hw : ∀ w ∈ ws, InRegions s.wr (pa s w.1) w.2) : ReadCache count S f t := by
  have h21 := hp.bs .x21 (by decide)
  have hd : ∀ R ∈ ws.map (toR s) ++ [below s.sp S],
      (⟨s.gpr .x21, 1024 * count⟩ : Region).Disjoint R := by
    intro R hR
    rcases List.mem_append.mp hR with hR | hR
    · obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hR
      exact h.apart_write (hw w hw')
    · obtain rfl := List.mem_singleton.mp hR
      exact h.stack
  refine ⟨h.small, ?_, ?_, ?_, ?_⟩
  · simpa only [h21, hp.rd, hp.wr] using h.readable
  · simpa only [h21, hp.wr] using h.writable
  · simpa only [h21, hp.sp] using h.stack
  · intro i hi
    rw [hp.pa (p := (.x21, 1024 * i)) (show Reg.x21 ∈ keptRegs by decide)]
    exact VG.Proof.MlDsa.Verify.polyIs_frame hp.frame
      (fun R hR => (hd R hR).sub_left (h.slice_sub hi)) (h.values i hi)

theorem ReadCache.exec {count S : Nat} {f : Nat → Poly} {s t : State}
    {code : Prog isa} {tr : List Leak} (h : ReadCache count S f s)
    (he : Exec isa code s tr t) (hd : 16 * code.aarch64Depth ≤ S) (hS : S < 2 ^ 64)
    (h21 : t.gpr .x21 = s.gpr .x21) : ReadCache count S f t := by
  have hf := Frame.below_mono (VG.AArch64.Exec.frameSp he (by omega)) hd hS
  obtain ⟨hr, hw, hsp⟩ := VG.AArch64.Exec.rdwr he
  have hdisj : ∀ R ∈ s.wr ++ [below s.sp S],
      (⟨s.gpr .x21, 1024 * count⟩ : Region).Disjoint R := by
    intro R hR
    rcases List.mem_append.mp hR with hR | hR
    · exact h.writable R hR
    · obtain rfl := List.mem_singleton.mp hR
      exact h.stack
  refine ⟨h.small, ?_, ?_, ?_, ?_⟩
  · simpa only [h21, hr, hw] using h.readable
  · simpa only [h21, hw] using h.writable
  · simpa only [h21, hsp] using h.stack
  · intro i hi
    simp only [pa, h21]
    exact VG.Proof.MlDsa.Verify.polyIs_frame hf
      (fun R hR => (hdisj R hR).sub_left (h.slice_sub hi)) (h.values i hi)

theorem WP.optionalCache {count S : Nat} {f : Nat → Poly} {s : State}
    {code : Prog isa} {post : State → Prop} (hwp : WP isa code s post)
    (hcache : s.gpr .x22 ≠ 0 → ReadCache count S f s)
    (hd : 16 * code.aarch64Depth ≤ S) (hS : S < 2 ^ 64)
    (h21 : ∀ t, post t → t.gpr .x21 = s.gpr .x21)
    (h22 : ∀ t, post t → t.gpr .x22 = s.gpr .x22) :
    WP isa code s fun t => post t ∧ (t.gpr .x22 ≠ 0 → ReadCache count S f t) := by
  obtain ⟨tr, t, he, hp⟩ := hwp
  refine ⟨tr, t, he, hp, ?_⟩
  intro hn
  have hprev : s.gpr .x22 ≠ 0 := by rwa [h22 t hp] at hn
  exact (hcache hprev).exec he hd hS (h21 t hp)

theorem ReadCache.copy_poly {count S : Nat} {f : Nat → Poly} {s : State}
    (cache : ReadCache count S f s) {dst : Ptr} (hd : dst.1 ∈ keptRegs)
    (hw : InRegions s.wr (pa s dst) 1024) {i : Nat} (hi : i < count) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.copy dst (.x21, 1024 * i) 1024) s fun t =>
      PPostB S s t [(dst, 1024)] ∧ t.gpr .x24 = s.gpr .x24 ∧
      ReadCache count S f t ∧ PolyIs t.mem (pa t dst) (f i) := by
  have hsep := (cache.apart_write hw).sub_left (cache.slice_sub hi)
  refine WP.mono (copy_core (n := 64) (by decide) (by decide) hd
    (show Reg.x21 ∈ keptRegs by decide) s (cache.inR hi) hw hsep)
    fun t ⟨hb, hf, hk⟩ => ?_
  have ht : PPostB S s t [(dst, 1024)] := postB_of_keep hk (by decide) hf
  refine ⟨ht, hk.get .x24, cache.step ht ?_, ?_⟩
  · intro w hw'
    obtain rfl := List.mem_singleton.mp hw'
    exact hw
  · rw [ht.pa hd]
    exact VG.Proof.MlDsa.PreparedKey.polyIs_of_copy hb (cache.values i hi)

abbrev cacheCopyHint : VG.Taint.Hint AArch64.Taint.T :=
  .seq (AArch64.Taint.ofRegs [.x0, .x1, .x2, .x21, .x28]) (.block [])
    (.loop (AArch64.Taint.ofRegs [.x0, .x1, .x2, .x21, .x28]) (.block []))

theorem copy_cache_check (od os : Nat) :
    taint.check (AArch64.Taint.ofRegs [.x21, .x28])
      (Impl.MlDsa.AArch64.PreparedKey.copy (.x28, od) (.x21, os) 1024) cacheCopyHint =
      some (AArch64.Taint.ofRegs [.x0, .x1, .x2, .x21, .x28]) := by
  dsimp only [Impl.MlDsa.AArch64.PreparedKey.copy, cacheCopyHint,
    Impl.MlDsa.AArch64.Call.lea, Impl.MlDsa.AArch64.Call.movV]
  simp only [show ¬(1024 : Nat) = 0 by decide, ↓reduceIte]
  (repeat' split) <;> rfl

theorem copy_cache_tr (od os : Nat) :
    RelCT isa (SameIn [.x21, .x28])
      (Impl.MlDsa.AArch64.PreparedKey.copy (.x28, od) (.x21, os) 1024)
      (SameIn [.x21, .x28]) := by
  intro x y tx ty x' y' h ex ey
  have ha : AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x21, .x28]) x y :=
    ⟨h.2, fun r hr => h.1 r (AArch64.Taint.mem_ofRegs.mp hr)⟩
  obtain ⟨ht, hp⟩ := VG.Taint.check_sound (copy_cache_check od os) ha ex ey
  exact ⟨ht, (fun r hr => hp.2 r (by simpa using
    (show r ∈ ([.x0, .x1, .x2, .x21, .x28] : List Reg) by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl <;> simp))), hp.1⟩

end VG.Proof.MlDsa.AArch64.PreparedKey
