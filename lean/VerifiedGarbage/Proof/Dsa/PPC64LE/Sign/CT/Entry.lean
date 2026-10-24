module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Sizes
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Front
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Sizes
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Front
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey

/-!
# DSA signing on PPC64LE: constant time of the entry

`sentry_rel`: from two states that satisfy `sContract` with the same public
data (`svdOf`: the layout, the pointers, the digest's length, the key's
public part and `out`), the entry leaks the same trace and leaves both in the
phase `S0` of the checks of the key, with `out` in the header's word `hOut`
(`SG`). The taint analysis treats `scratch`'s address, loaded from the
stack, as secret: the phase `SL1` after the load fixes it.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- Signing's public data: `out` is given. -/
def SG (v : VD) : Prop := v.out.isSome = true

/-- A call's public data. -/
def svdOf (s : State) : VD :=
  ⟨slayOf s, s.gpr .r5, s.gpr .r8, s.gpr .r10, (stackArg s 0).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .r5) (3 * (s.gpr .r7).toNat + (s.gpr .r9).toNat),
    3 * (s.gpr .r7).toNat + 2 * (s.gpr .r9).toNat, (s.gpr .r9).toNat, some (s.gpr .r3)⟩

/-- On entry. -/
def SC0 (v : VD) (s : State) : Prop := sContract.pre s ∧ svdOf s = v

/-- After the load of `scratch`'s address. -/
def SL1 (v : VD) (s : State) : Prop := s.gpr .r11 = v.L.S

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] :=
  fun _ _ _ _ _ _ h => absurd h List.not_mem_nil

theorem pins_SL1 : Pins SL1 [.r11] := by
  intro v s₁ s₂ a b r hr
  simp only [List.mem_singleton] at hr
  subst hr
  rw [a, b]

/-- The stack's second argument is readable. -/
theorem stack1_in {s : State} (h : sContract.pre s) : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 := by
  obtain ⟨-, hrd, -⟩ := h
  have e1 : stackArgAddr s 1 = stackArgAddr s 0 + BitVec.ofNat 64 8 := by
    simp only [stackArgAddr]; rw [Offset.add_add]
  exact ⟨sStackArgs s, List.mem_append_left _ (by rw [hrd]; simp), by
    simp only [Region.Contains]; rw [e1, Mem.sub_ofNat_toNat _ (by decide)]; decide⟩

theorem sloadS_SL1 {v : VD} {s : State} (h : SC0 v s) :
    WP isa (.block [.addSp .r11 104, .load .d .r11 .r11 0]) s (SL1 v) := by
  obtain ⟨hp, rfl⟩ := h
  exact WP.mono (sloadS_ok s (stack1_in hp)) fun t ⟨⟨a11, _⟩, _⟩ => a11

/-- A buffer of the contract apart from `scratch`. -/
theorem spre_src {s : State} {A : Addr} {n k : Nat} (hm : (⟨A, n⟩ : Region) ∈ s.rd)
    (hd : (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩)
    (hn : n < 2 ^ 64) (hk : k ≤ n) {t : State} (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Src t (slayOf s) A k :=
  ⟨fun i hi => ⟨_, by rw [hr, hw]; exact List.mem_append_left _ hm, Offset.contains_base _ (by omega) (by omega)⟩,
    fun i hi => Pub.ne_of_disjoint hd (by omega) i (by omega)⟩

theorem sfront_S0 {v : VD} {s : State} (h : SC0 v s) :
    WP isa (.block Sign.entry) s fun t => S0 v t ∧ SG v := by
  obtain ⟨hp, rfl⟩ := h
  have hL := slayOf_ok hp
  have hZ := hL.z256
  have hpre := hp
  obtain ⟨-, hrd, -, -, -, -, -, -, dKS, dNS, dDS, -, -, -, -, -, -, -, -, hkl, -⟩ := hp
  refine WP.mono (sfront_ok hpre) fun t ⟨⟨hr, scr, r2, hw, _, out⟩, k⟩ => ?_
  have hK : ∀ {u : State} {n : Nat}, n ≤ 3 * (slayOf s).pl + 2 * (slayOf s).ql → u.rd = s.rd → u.wr = s.wr →
      Src u (slayOf s) (s.gpr .r5) n :=
    fun hn hr hw => spre_src (A := s.gpr .r5) (by rw [hrd]; simp) dKS (s.gpr .r6).isLt
      (by simp only [slayOf] at hn ⊢; omega) hr hw
  have Out : Outside (slayOf s).S 0 (slayOf s).Z s.mem t.mem :=
    out.mono (Nat.le_refl _) (by simp only [slayOf] at hZ ⊢; omega)
  refine ⟨⟨⟨hL, hr, scr, hK (n := 3 * (slayOf s).pl + (slayOf s).ql) (by omega) k.rd k.wr,
    spre_src (A := s.gpr .r8) (k := (slayOf s).ql) (by rw [hrd]; simp) dNS (s.gpr .r9).isLt
      (Nat.le_refl _) k.rd k.wr,
    spre_src (A := s.gpr .r10) (k := min (stackArg s 0).toNat 64) (by rw [hrd]; simp) dDS (stackArg s 0).isLt
      (Nat.min_le_left _ _) k.rd k.wr,
    ((hK (n := 3 * (slayOf s).pl + (slayOf s).ql) (by omega) rfl rfl).kept Out), hK (Nat.le_refl _) k.rd k.wr,
    (fun o ho => by cases ho; exact hw), (fun _ => ⟨rfl, rfl⟩)⟩, r2, fixL_nil t, trivial⟩, rfl⟩

theorem sentry_rel : RelCT isa (Two SC0) (.block Sign.entry) (Two fun v s => S0 v s ∧ SG v) := by
  refine two_post ?_ fun _ _ h => sfront_S0 h
  unfold Sign.entry
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  exact RelCT.block_append (RelCT.seq (two_post (two_taint _ (pins_nil _) (by taint_decide))
    fun _ _ h => sloadS_SL1 h) (two_taint _ pins_SL1 (by taint_decide)))

end VG.Proof.Dsa.PPC64LE
