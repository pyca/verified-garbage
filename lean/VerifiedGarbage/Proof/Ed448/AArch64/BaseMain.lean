import VerifiedGarbage.Proof.Ed448.AArch64.BaseBits
import VerifiedGarbage.Proof.Ed448.AArch64.BaseSetup
import VerifiedGarbage.Proof.Ed448.AArch64.BaseLoop
import VerifiedGarbage.Proof.Ed448.AArch64.BaseEncode
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# Ed448 base-point multiplication on AArch64: the whole function

The contract the proof is written against (the facts of
`Spec.Ed448.scalarBaseContract` it uses, stated for AArch64), and the
correctness of `vg_ed448_scalar_base` against it: the constants and the
scalar's bits, the loop (`R` ends as the reference ladder's point, which
encodes `[k]B` by `BaseLadderOk`), and the encoding; every write but the
result's is in the working space, so the scalar is read unchanged, and `x19`
and `x20` are restored from it.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word Outside Saved ofs workRegs bitRegs far)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv E_outside)
open VG.Impl.X448.AArch64 (BITS slot)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- `vg_ed448_scalar_base(out = x0, scalar = x1, scratch = x2)`. -/
def scalarBaseLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 57⟩] ∧ s.wr = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x0, 57⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
    (⟨s.gpr .x1, 57⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
    (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64
  post s t := bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarBase (bytesAt s.mem (s.gpr .x1) 57)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

/-- A byte of the working space is beyond the output. -/
theorem far_out {base p : Addr} (hd : (⟨p, 57⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 57 ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ 57
  omega

theorem scalarBase_correct (hL : BaseLadderOk) {s : State} (hp : scalarBaseLocal.pre s) :
    WP isa scalarBase s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ scalarBaseLocal.post s t := by
  obtain ⟨hr, hw, hdo, hds, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .x2 = b := ⟨_, rfl⟩
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hbase]; simp
  rw [hbase] at hn hdo hds
  have hkd : ∀ q < 57, 8192 ≤ ofs base (s.gpr .x1 + BitVec.ofNat 64 q) := fun q hq => far hds hq (by decide)
  have hod : ∀ q < 57, 8192 ≤ ofs base (s.gpr .x0 + BitVec.ofNat 64 q) := fun q hq => far hdo hq (by decide)
  rw [scalarBase]
  -- The entry and the constants.
  refine WP.seq (WP.mono (prep_ok hbase hws hn) fun s₁ ⟨hs₁, b₁, sv₁, x20₁, k₁, o₁, pR₁, pB₁, d₁⟩ => ?_)
  -- The scalar's bits.
  have kr : ∀ q < 57, InRegions (s₁.rd ++ s₁.wr) (s.gpr .x1 + BitVec.ofNat 64 q) 1 := fun q hq =>
    ⟨⟨s.gpr .x1, 57⟩, (by rw [k₁.2.1, hr]; simp), Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (bits_ok hs₁ (k₁.1 _ (by decide)) kr hkd)
    fun s₂ ⟨x1₂, g₂, rd₂, wr₂, o₂, bits₂⟩ => ?_)
  have hs₂ : Scr s₂ base := ⟨(g₂ _ (by decide)).trans hs₁.x3, (g₂ _ (by decide)).trans hs₁.mask,
    wr₂ ▸ hs₁.wr, hn⟩
  have e₂ : ∀ i : Fin 22, E s₂.mem base i = E s₁.mem base i := fun i =>
    E_outside o₂ i (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
  have b₂ : BoundedEnv s₂.mem base := fun i j hj => by
    rw [o₂.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) (by omega : j < 16)]
    exact b₁ i j hj
  have kb : bytesAt s₁.mem (s.gpr .x1) 57 = bytesAt s.mem (s.gpr .x1) 57 := by
    rw [VG.Proof.Ed448.bytesAt_eq, VG.Proof.Ed448.bytesAt_eq]
    exact List.map_congr_left fun i hi => o₁ _ (Or.inr (hkd i (List.mem_range.mp hi)))
  rw [kb] at bits₂
  -- The loop.
  refine WP.seq (WP.mono (mulLoop_ok bits₂ hs₂ b₂ (by rw [show pt (E s₂.mem base) 8 9 10 =
      pt (E s₁.mem base) 8 9 10 by simp only [pt, e₂]]; exact pB₁) (by rw [e₂]; exact d₁)
      (by rw [show pt (E s₂.mem base) 0 1 2 = pt (E s₁.mem base) 0 1 2 by simp only [pt, e₂]]; exact pR₁))
    fun s₃ I₃ => ?_)
  -- The encoding.
  have k₃ : Keeps (.x19 :: workRegs) s₂ s₃ := I₃.regs
  have x1₃ : s₃.gpr .x1 = s.gpr .x0 := by
    rw [k₃.1 _ (by decide), x1₂, x20₁]
  have wr₃ : s₃.wr = s.wr := by rw [k₃.2.2, wr₂, k₁.2.2]
  have sv₃ : Saved base s.gpr s₃.mem :=
    (sv₁.outside o₂ (by decide)).outside2 I₃.mem (by decide) (by decide)
  refine WP.mono (encode_ok I₃.scr I₃.bounded x1₃
    (fun j hj => ⟨⟨s.gpr .x0, 57⟩, (by rw [wr₃, hw]; simp), Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => hod j hj) (fun j hj => far_out hdo hj) sv₃) fun t ⟨t19, t20, kt, _, vt⟩ => ?_
  refine ⟨fun r hpres => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hpres
    rcases hpres with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact t19
    · exact t20
    all_goals rw [kt.1 _ (by decide), k₃.1 _ (by decide), g₂ _ (by decide), k₁.1 _ (by decide)]
  · show bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarBase (bytesAt s.mem (s.gpr .x1) 57)
    rw [vt, I₃.rep, Nat.sub_zero, hL _ (decodeLE_below (by rw [bytesAt_eq]; simp [Spec.X25519.bytesAt]))]
    rfl

end VG.Proof.Ed448.AArch64
