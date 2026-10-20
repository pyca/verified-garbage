module

import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.Code
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Rt.Step

/-! # Words copied into the working space from readable memory

The loop of `copyIn` (`Impl/Bignum/X86/PrecomputedRt.lean`): `N` words from
`esi`, in a readable region apart from the working space, to `ebp` in it
(`copyLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputedRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt

/-- `[r + d]`, for `r = P + x`, in readable memory. -/
theorem readSrc_rd {s : State} {P : Addr} {L : Nat} (hr : InRegions (s.rd ++ s.wr) P L)
    (hn : P.toNat + L ≤ 2 ^ 32) {r : Reg} {x d : Nat} (hp : PtrAt s P r x) (hd : x + d + 4 ≤ L) :
    readSrc s (.mem (at_ r d)) = some (s.mem.readW (off P (x + d)) 32) := by
  have ea : s.ea (at_ r d) = off P (x + d) := by
    rw [at_, ea_mk, addr_eq (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have hP : P.toNat < 2 ^ 64 := P.isLt
    rw [Nat.mod_eq_of_lt (a := (s.gpr r).toNat) (by have := (s.gpr r).isLt; omega), hp]
    repeat rw [Nat.mod_eq_of_lt (by omega)]
    omega
  show s.load32 (s.ea (at_ r d)) = _
  rw [ea, State.load32, ite_eq_left_iff.mpr fun h => absurd (VG.CallLay.inRegions_sub hr (off := x + d) (l := 4)
    (by omega) (by omega)) h]

/-- Memory apart from the working space keeps its bytes when only a range of it changes. -/
theorem outside_apart {W a : Addr} {L x n : Nat} {m m' : Mem} (O : Outside W x n m m') (hxn : x + n ≤ L)
    (hc : ¬ (⟨W, L⟩ : Region).Contains a 1) : m' a = m a :=
  O a (.inr (by simp only [Region.Contains] at hc; simp only [ofs]; omega))

theorem copyLoop_ok {t₀ : State} {W P : Addr} {L L' : Nat} (hw : Ws t₀ W L)
    (hr : InRegions (t₀.rd ++ t₀.wr) P L') (hn : P.toNat + L' ≤ 2 ^ 32)
    (hap : Region.Disjoint ⟨P, L'⟩ ⟨W, L⟩) {x y N : Nat} (hN : 0 < N)
    (hx : x + 4 * N ≤ L) (hy : y + 4 * N ≤ L') (hebp : PtrAt t₀ W .ebp x) (hesi : PtrAt t₀ P .esi y)
    (hecx : (t₀.gpr .ecx).toNat = 4 * N) :
    WP isa (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 4)]) .ne) t₀
      fun u => Outside W x (4 * N) t₀.mem u.mem ∧ val32 u.mem W x N = val32 t₀.mem P y N ∧
        Keeps [.eax, .ecx, .ebp, .esi] t₀ u := by
  have hwn := hw.nowrap
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ecx, .ebp, .esi] t₀ t ∧ PtrAt t W .ebp (x + 4 * j) ∧
      PtrAt t P .esi (y + 4 * j) ∧ (t.gpr .ecx).toNat = 4 * (N - j) ∧ Outside W x (4 * j) t₀.mem t.mem ∧
      val32 t.mem W x j = val32 t₀.mem P y j) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hesi, by simpa using hecx, Outside.refl _ _ _ _, rfl⟩)
    fun u ⟨K, _, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro j t hj ⟨Kt, ebp, esi, ecx, O, V⟩
  have ht := hw.of_keeps Kt
  have hrt : InRegions (t.rd ++ t.wr) P L' := by rw [Kt.2.1, Kt.2.2]; exact hr
  refine wp_movS (readSrc_rd hrt hn esi (d := 0) (by omega_using [hy, hj])) fun s₁ u₁ _ => ?_
  have ht₁ := ht.of_keeps u₁.keeps
  have ebp₁ : PtrAt s₁ W .ebp (x + 4 * j) := by rw [PtrAt, u₁.other _ (by decide)]; exact ebp
  refine wp_storeS (ea_ptr ht₁ ebp₁ (d := 0) (by omega_using [hx, hj]))
    (ws_write ht₁ (y := x + 4 * j + 0) (n := 4) (by omega_using [hx, hj])) fun s₂ m₂ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => wp_addS rfl fun s₄ u₄ _ => wp_subZ rfl fun s₅ u₅ z₅ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf ecx hj
  have ecx₄ : s₄.gpr .ecx = t.gpr .ecx := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide)]
  -- The source word, unchanged since the start.
  have word : (t.mem.readW (off P (y + 4 * j + 0)) 32).toNat = w32 t₀.mem P (y + 4 * j) := by
    rw [Nat.add_zero]
    refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => outside_apart O (L := L) (by omega_using [hx, hj]) ?_)
    intro hc
    refine hap _ ?_ hc
    rw [Offset.add_add]
    exact Region.contains_ofNat P (by omega_using [hy, hj, hi])
  refine ⟨⟨(((Kt.widen (u₁.keeps.widen (m₂.keeps []))).widen u₃.keeps).widen u₄.keeps).widen u₅.keeps,
    ?_, ?_, by rw [u₅.gpr, ecx₄]; exact c₁, ?_, ?_⟩, by rw [z₅, ecx₄, c₂]⟩
  · rw [PtrAt, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide)]
    exact ptr4 ebp
  · rw [PtrAt, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, m₂.gpr, u₁.other _ (by decide)]
    exact ptr4 esi
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hx, hj, hwn])).mono (by omega_using []) (by omega_using []))
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem, Nat.add_zero, val32_store hwn (by omega_using [hx, hj]), V,
      u₁.gpr, val32_succ t₀.mem P y, ← word, Nat.add_zero]

end VG.Proof.Bignum.X86.PrecomputedRt
