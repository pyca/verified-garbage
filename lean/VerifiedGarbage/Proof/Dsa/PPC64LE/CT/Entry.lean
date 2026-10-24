module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Sizes
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFront
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Sizes
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFront
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubSave
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA verification on PPC64LE: constant time of the entry

`entry_rel`: from two states that satisfy the contract with the same public
data (`vdOf`), the entry leaks the same trace and leaves both in the phase
`S0`. The taint analysis treats `scratch`'s address, loaded from the stack,
as secret: the phase `L1` after `loadS` fixes it.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- A call's public data. -/
def vdOf (s : State) : VD :=
  ⟨layOf s, s.gpr .r3, s.gpr .r7, s.gpr .r9, (s.gpr .r10).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .r3) (3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat),
    3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat, 2 * (s.gpr .r6).toNat, none,
    3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat⟩

/-- The public octets name y. -/
def KY (v : VD) : Prop := 3 * v.L.pl + v.L.ql ≤ v.kn

/-- On entry. -/
def C0 (v : VD) (s : State) : Prop := vContract.pre s ∧ vdOf s = v

/-- After `loadS`. -/
def L1 (v : VD) (s : State) : Prop :=
  s.gpr .r11 = v.L.S ∧ s.gpr .r3 = v.key ∧ s.gpr .r5 = BitVec.ofNat 64 v.L.pl ∧
    s.gpr .r6 = BitVec.ofNat 64 v.L.ql ∧ s.gpr .r7 = v.sig ∧ s.gpr .r9 = v.dig ∧
    s.gpr .r10 = BitVec.ofNat 64 v.dl

theorem C0.L1 {v : VD} {s : State} (h : C0 v s) :
    s.gpr .r3 = v.key ∧ s.gpr .r5 = BitVec.ofNat 64 v.L.pl ∧ s.gpr .r6 = BitVec.ofNat 64 v.L.ql ∧
      s.gpr .r7 = v.sig ∧ s.gpr .r9 = v.dig ∧ s.gpr .r10 = BitVec.ofNat 64 v.dl := by
  obtain ⟨-, rfl⟩ := h
  simp [vdOf, layOf]

theorem pins_C0 : Pins C0 [.r3, .r5, .r6, .r7, .r9, .r10] := by
  intro v s₁ s₂ h₁ h₂ r hr
  have a := h₁.L1
  have b := h₂.L1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a.1, b.1]
  · rw [a.2.1, b.2.1]
  · rw [a.2.2.1, b.2.2.1]
  · rw [a.2.2.2.1, b.2.2.2.1]
  · rw [a.2.2.2.2.1, b.2.2.2.2.1]
  · rw [a.2.2.2.2.2, b.2.2.2.2.2]

theorem pins_L1 : Pins L1 [.r11, .r3, .r5, .r6, .r7, .r9, .r10] := by
  intro v s₁ s₂ a b r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a.1, b.1]
  · rw [a.2.1, b.2.1]
  · rw [a.2.2.1, b.2.2.1]
  · rw [a.2.2.2.1, b.2.2.2.1]
  · rw [a.2.2.2.2.1, b.2.2.2.2.1]
  · rw [a.2.2.2.2.2.1, b.2.2.2.2.2.1]
  · rw [a.2.2.2.2.2.2, b.2.2.2.2.2.2]

theorem loadS_L1 {v : VD} {s : State} (h : C0 v s) :
    WP isa (.block [.addSp .r11 96, .load .d .r11 .r11 0]) s (L1 v) := by
  have e := h.L1
  obtain ⟨hp, rfl⟩ := h
  refine WP.mono (Pub.loadS_ok s ⟨stackArgs s, List.mem_append_left _ (by rw [hp.2.1]; simp),
    by simp [Region.Contains]⟩) fun t ⟨⟨a11, _, _⟩, k⟩ => ⟨a11, ?_⟩
  obtain ⟨e3, e5, e6, e7, e9, e10⟩ := e
  exact ⟨(k.gpr .r3 (by decide)).trans e3, (k.gpr .r5 (by decide)).trans e5, (k.gpr .r6 (by decide)).trans e6,
    (k.gpr .r7 (by decide)).trans e7, (k.gpr .r9 (by decide)).trans e9, (k.gpr .r10 (by decide)).trans e10⟩

/-- The contract's buffers apart from `scratch`. -/
theorem pre_src {s : State} {A : Addr} {n k : Nat} (hm : (⟨A, n⟩ : Region) ∈ s.rd)
    (hd : (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩)
    (hn : n < 2 ^ 64) (hk : k ≤ n) {t : State} (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Src t (layOf s) A k :=
  ⟨fun i hi => ⟨_, by rw [hr, hw]; exact List.mem_append_left _ hm, Offset.contains_base _ (by omega) (by omega)⟩,
    fun i hi => Pub.ne_of_disjoint hd (by omega) i (by omega)⟩

theorem front_S0 {v : VD} {s : State} (h : C0 v s) :
    WP isa (.block Verify.entry) s fun t => S0 v t ∧ KY v := by
  obtain ⟨hp, rfl⟩ := h
  have hL := layOf_ok hp
  have hZ := hL.z256
  have hpre := hp
  obtain ⟨-, hrd, -, dKS, dGS, dDS, -, -, -, -, -, -, hkl, hsl, -⟩ := hp
  refine WP.mono (front_ok hpre) fun t ⟨⟨hr, scr, r2, _, out⟩, k⟩ => ?_
  have hK : ∀ {u : State}, u.rd = s.rd → u.wr = s.wr → Src u (layOf s) (s.gpr .r3) (3 * (layOf s).pl + (layOf s).ql) :=
    fun hr hw => pre_src (A := s.gpr .r3) (by rw [hrd]; simp) dKS (s.gpr .r4).isLt
      (by simp only [layOf]; omega) hr hw
  have Out : Outside (layOf s).S 0 (layOf s).Z s.mem t.mem := out.mono (Nat.le_refl _) (by simp only [layOf] at hZ ⊢; omega)
  refine ⟨⟨⟨hL, hr, scr, hK k.rd k.wr,
    pre_src (A := s.gpr .r7) (k := 2 * (layOf s).ql) (by rw [hrd]; simp) dGS (s.gpr .r8).isLt
      (by simp only [layOf]; omega) k.rd k.wr,
    pre_src (A := s.gpr .r9) (k := min (s.gpr .r10).toNat 64) (by rw [hrd]; simp) dDS (s.gpr .r10).isLt
      (Nat.min_le_left _ _) k.rd k.wr,
    (hK rfl rfl).kept Out, hK k.rd k.wr, (fun _ h => nomatch h), (fun h => nomatch h),
    (by simp only [vdOf, layOf]; omega)⟩, r2, fixL_nil t, trivial⟩, Nat.le_refl _⟩

theorem entry_rel : RelCT isa (Two C0) (.block Verify.entry) (Two fun v s => S0 v s ∧ KY v) := by
  refine two_post ?_ fun _ _ h => front_S0 h
  unfold Verify.entry
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun _ _ h => loadS_L1 h)
    (two_taint _ pins_L1 (by taint_decide)))

end VG.Proof.Dsa.PPC64LE
