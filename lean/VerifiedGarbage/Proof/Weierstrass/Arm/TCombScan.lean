module

import VerifiedGarbage.Proof.Weierstrass.Arm.TCombWord
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Proof.Mont.Arm.Words
public import VerifiedGarbage.Proof.Mont.Words

/-! A row entry is selected one packed word at a time. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

/-- Changes confined to a subrange are a frame within the containing workspace. -/
theorem outside_frame {base : Addr} {o n size : Nat} {m m' : Mem}
    (h : Outside base o n m m') (hle : o+n ≤ size) : Frame [⟨base,size⟩] m m' := by
  intro x hx
  have hn := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn
  apply h
  right
  change o+n ≤ (x-base).toNat
  omega

theorem selectWords_ok (K : TCombCfg) {s : State} {base X : Addr} {size : Nat}
    (hs : Scr s base size) (hX : State.addr (s.gpr .r8)=X)
    (ho : K.Q.x+16*K.L.M.n ≤ size) (hi : 16*K.L.M.n ≤ 4096)
    (fit : X.toNat+16*K.L.M.n ≤ 2^32)
    (hr : InRegions (s.rd ++ s.wr) X (16*K.L.M.n))
    (hd : Region.Disjoint ⟨X,16*K.L.M.n⟩ ⟨base,size⟩)
    (b : Bool) (hc : s.gpr .r10=if b then BitVec.allOnes 32 else 0) :
    ∀ k, k ≤ 4*K.L.M.n →
    WP isa (.block ((List.range k).flatMap K.selectWord)) s fun t =>
      (∀ i<k, w32 t.mem base (K.Q.x+4*i) =
        if b then w32 s.mem X (4*i) else w32 s.mem base (K.Q.x+4*i)) ∧
      Rest [.r4,.r5] s t ∧ Outside base K.Q.x (4*k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => by omega,Rest.refl _ _,Outside.refl _ _ _ _⟩
  | k+1, hk => by
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (selectWords_ok K hs hX ho hi fit hr hd b hc k (by omega))
      fun s₁ ⟨e₁,k₁,O₁⟩ => ?_
    have hs₁ := hs.of_rest k₁ (by decide)
    have hx₁ : State.addr (s₁.gpr .r8)=X := by rw [k₁.gpr .r8 (by decide),hX]
    have hc₁ : s₁.gpr .r10=if b then BitVec.allOnes 32 else 0 := by rw [k₁.gpr .r10 (by decide),hc]
    have hr₁ : InRegions (s₁.rd ++ s₁.wr) (off X (4*k)) 4 := by
      rw [k₁.rd,k₁.wr]
      exact CallLay.inRegions_sub (off := 4*k) (l := 4) hr (by omega) (by omega)
    refine WP.mono (selectWord_ok K (i := k) hs₁ hx₁ (by omega) (by omega) (by omega) hr₁ b hc₁)
      fun s₂ ⟨v₂,k₂,O₂⟩ => ?_
    refine ⟨fun i hii => ?_,k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    by_cases hik : i<k
    · rw [O₂.w32 (by omega) (by have := hs.nowrap; omega),e₁ i hik]
    · have ei : i=k := by omega
      subst i
      have vnat := congrArg BitVec.toNat v₂
      change w32 s₂.mem base (K.Q.x+4*k) = _ at vnat
      have xeq : w32 s₁.mem X (4*k) = w32 s.mem X (4*k) := by
        apply congrArg BitVec.toNat
        exact (outside_frame (size := size) O₁ (by omega)).readW (r := ⟨X,16*K.L.M.n⟩)
          (Offset.contains_base (d := 4*k) (n := 4) (k := 16*K.L.M.n) X (by omega) (by omega))
          (fun r hr' => by rcases List.mem_singleton.mp hr' with rfl; exact hd) (by decide)
      have oeq : w32 s₁.mem base (K.Q.x+4*k) = w32 s.mem base (K.Q.x+4*k) :=
        O₁.w32 (by omega) (by have := hs.nowrap; omega)
      cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] at vnat ⊢ <;>
        rw [vnat] <;> first | exact oeq | exact xeq

end VG.Proof.Weierstrass.Arm.TComb
