module

import VerifiedGarbage.Proof.Rsa.X86.RvMontFrame
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.MulMod
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.X86.RvMontGeometry
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # Computing Montgomery R squared inside the recovery workspace

`KS.setupR2`: `[mR2]` set to one and doubled modulo `[aN] = m` `128 n`
times (`addMod`, through the arrays from `mAcc`), so `[mR2] = 2^(128 n) mod m`.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.RecoverRt (nar)
open VG.Impl.Rsa.X86.KeyRt (copy addMod)
open VG.Proof.Rsa.X86.Keys

/-- The arrays `addMod` writes through `mAcc`, and its result. -/
abbrev addWrites (o : Nat) : List Nat := [mAcc, mAcc + 1, mAcc + 2, o]

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {m : Nat}

theorem KS.copyMont {o a : Nat} (h : KS g s0 A live AW liveW V ls s) (mr : MR g m s)
    (ho : o < nArr) (ha : a ∈ live) (hoa : o ≠ a) (hom : o ≠ mBase) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (copy nar o a) s fun t =>
      KS g s0 (upd A o (A a)) (o :: live) AW liveW V ls t ∧ MR g m t ∧ Keeps opRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.copy_ok h.rt ho (h.live_lt a ha) hoa) fun t ⟨_, k, e, r, _⟩ => ?_
  rw [kw_nar] at k e
  exact ⟨h.write_w k ho (by simp) (r.mono (by decide)) (e.trans (h.arrs a ha)) hlW (by simp),
    mr.keepD h.ws k (by simpa using hom) (by simp) (by simp), r.mono (by decide)⟩

theorem KS.addMod {o a b n z : Nat} (h : KS g s0 A live AW liveW V ls s) (mr : MR g m s)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hn : n ∈ live) (hz : z ∈ live)
    (hat : a ≠ mAcc) (hnt : n ≠ mAcc) (hnt1 : n ≠ mAcc + 1) (hot : o ≠ mAcc + 2) (hom : o ≠ mBase)
    (hl : ∀ j ∈ live, j = o ∨ j ∉ addWrites o) (hlW : ∀ j ∈ liveW, ∀ i ∈ addWrites o, i / 2 ≠ j)
    (hls : ∀ d ∈ ls, d + 4 ≤ sC ∨ sC + 4 ≤ d)
    (zero : A z = 0) (la : A a < A n) (lb : A b < A n) (big : 2 * A n ≤ 2 ^ (32 * g.w)) :
    WP isa (seqs (addMod nar o a b n z mAcc)) s fun t =>
      KS g s0 (upd A o ((A a + A b) % A n)) (o :: live) AW liveW V ls t ∧ MR g m t ∧
        Keeps opRegs s t ∧ t.gpr .esi = s.gpr .esi := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.addMod_ok h.rt ho (h.live_lt a ha) (h.live_lt b hb)
    (h.live_lt n hn) (h.live_lt z hz) (by decide) hat hnt hnt1 hot) fun t ⟨_, k, r, v⟩ => ?_
  rw [kw_nar] at k v
  rw [h.arrs a ha, h.arrs b hb, h.arrs n hn, h.arrs z hz] at v
  have r' : Keeps opRegs s t := r.mono (by decide)
  have hjs : ∀ j ∈ addWrites o, j < nArr := fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> first | exact ho | decide
  have hjm : ∀ j ∈ addWrites o, j ≠ mBase := fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> first | exact hom | decide
  exact ⟨h.writeK k ho hjs (by decide) r' (v zero la lb big) hl hlW (fun d hd e he => by
      rw [List.mem_singleton] at he; subst he; exact hls d hd),
    mr.keepD h.ws k hjm (by decide) (by decide), r', r.1 _ (by decide)⟩

theorem KS.setupR2 (h : KS g s0 A live AW liveW V ls s) (mr : MR g m s) (hm : 1 < m)
    (hn : aN ∈ live) (vn : A aN = m) (hz : aZ ∈ live) (vz : A aZ = 0) (ho : aOne ∈ live) (vo : A aOne = 1)
    (hl : ∀ j ∈ live, j = mR2 ∨ j ∉ addWrites mR2) (hlW : ∀ j ∈ liveW, ∀ i ∈ addWrites mR2, i / 2 ≠ j)
    (hls : ∀ d ∈ ls, d + 4 ≤ sC ∨ sC + 4 ≤ d) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.setupR2 s fun t =>
      KS g s0 (upd A mR2 (2 ^ (128 * g.n) % m)) (mR2 :: live) AW liveW V ls t ∧ MR g m t := by
  have bound := mr.bound
  have lo := h.lower
  have up := h.upper
  have big : 2 * m ≤ 2 ^ (32 * g.w) := by
    have p := Nat.pow_le_pow_right (n := 2) (by decide) (show 64 * g.n + 1 ≤ 32 * g.w by
      simp only [Geo.w, width]; omega)
    rw [Nat.pow_succ] at p
    omega
  unfold VG.Impl.Rsa.X86.RecoverRt.setupR2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h.copyMont mr (by decide) ho (by decide) (by decide) (fun j hj => hlW j hj mR2 (by simp)))
    fun u ⟨hu, mu, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine VG.Proof.Rsa.X86.KeyRt.bytesB_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hu.rt) hu.rt.lenLe
    fun v K mv e => ?_
  rw [kw_nar] at e
  refine wp_subS rfl fun v1 U1 _ => wp_addS rfl fun v2 U2 _ => wp_addS rfl fun v3 U3 _ =>
    wp_addS rfl fun v4 U4 _ => wp_addS rfl fun v5 U5 _ => WP.block_nil ?_
  have l8 : (8 : BitVec 32).toNat = 8 := rfl
  have e1 : (v1.gpr .esi).toNat = 8 * g.n := by
    rw [U1.gpr, BitVec.toNat_sub, e, l8]; simp only [width]; omega
  have dbl : ∀ {x y : State} {k : Nat}, y.gpr .esi = x.gpr .esi + x.gpr .esi → (x.gpr .esi).toNat = k →
      k < 2 ^ 31 → (y.gpr .esi).toNat = 2 * k := fun hy hx hk => by
    rw [hy, BitVec.toNat_add, hx]; omega
  have e2 := dbl U2.gpr e1 (by omega)
  have e3 := dbl U3.gpr e2 (by omega)
  have e4 := dbl U4.gpr e3 (by omega)
  have e5 := dbl U5.gpr e4 (by omega)
  have c : v5.gpr .esi = BitVec.ofNat 32 (128 * g.n - 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [e5, BitVec.toNat_ofNat]
    omega
  have K5 : Keeps [.esi] u v5 :=
    (((((K.trans U1.keeps).trans U2.keeps).trans U3.keeps).trans U4.keeps).trans U5.keeps)
  have m5 : v5.mem = u.mem := by rw [U5.mem, U4.mem, U3.mem, U2.mem, U1.mem, mv]
  have one : 2 ^ 0 % m = A aOne := by rw [vo, Nat.pow_zero, Nat.mod_eq_of_lt hm]
  have h5 : KS g s0 (upd A mR2 (2 ^ 0 % m)) (mR2 :: live) AW liveW V ls v5 := by
    rw [one]; exact hu.of_rest K5 (by decide) m5
  have mr5 : MR g m v5 := mu.of_eq (by rw [m5]) (by rw [m5])
  refine WP.loop (M := isa) (fun j v => ∃ i, i + j = 128 * g.n ∧ 0 < j ∧
      KS g s0 (upd A mR2 (2 ^ i % m)) (mR2 :: live) AW liveW V ls v ∧ MR g m v ∧
      v.gpr .esi = BitVec.ofNat 32 (128 * g.n - i)) ?_ (128 * g.n) v5
    ⟨0, by omega, by omega, h5, mr5, c⟩
  intro j v ⟨i, hij, hj, hv, mv, cv⟩
  rw [wp_seqs_append (l₁ := VG.Impl.Rsa.X86.KeyRt.addMod nar mR2 mR2 mR2 aN aZ mAcc) (by simp [VG.Impl.Rsa.X86.KeyRt.addMod]) (by simp)]
  refine WP.mono (hv.addMod mv (by decide) List.mem_cons_self List.mem_cons_self
      (List.mem_cons_of_mem _ hn) (List.mem_cons_of_mem _ hz) (by decide) (by decide) (by decide) (by decide)
      (by decide) (fun j hj => (List.mem_cons.mp hj).elim .inl (hl j)) hlW hls
      (by rw [upd_ne _ _ (by decide)]; exact vz)
      (by rw [upd_self, upd_ne _ _ (by decide), vn]; exact Nat.mod_lt _ (by omega))
      (by rw [upd_self, upd_ne _ _ (by decide), vn]; exact Nat.mod_lt _ (by omega))
      (by rw [upd_ne _ _ (by decide), vn]; exact big)) fun t ⟨ht, mt, _, rt⟩ => ?_
  have ey : (upd A mR2 (2 ^ i % m) mR2 + upd A mR2 (2 ^ i % m) mR2) % upd A mR2 (2 ^ i % m) aN =
      2 ^ (i + 1) % m := by
    rw [upd_self, upd_ne _ _ (by decide : aN ≠ mR2), vn, Nat.pow_succ, Nat.mul_two, Nat.add_mod (2 ^ i)]
  rw [ey] at ht
  have ht' : KS g s0 (upd A mR2 (2 ^ (i + 1) % m)) (mR2 :: live) AW liveW V ls t :=
    ht.mono (fun k hk => ⟨List.mem_cons_of_mem _ hk, by
      by_cases e : k = mR2
      · subst e; rw [upd_self, upd_self]
      · rw [upd_ne _ _ e, upd_ne _ _ e, upd_ne _ _ e]⟩) (fun k hk => ⟨hk, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.mono (VG.Proof.Rsa.X86.Div.count_ok t) fun t' ⟨cnt, zf, mem, K'⟩ => ?_
  have esi : t.gpr .esi = v.gpr .esi := rt
  have c' : t'.gpr .esi = BitVec.ofNat 32 (128 * g.n - (i + 1)) := by
    rw [cnt, esi, cv]
    change BitVec.ofNat 32 (128 * g.n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  have h' := ht'.of_rest K' (by decide) mem
  have m' : MR g m t' := mt.of_eq (by rw [mem]) (by rw [mem])
  have z' : t'.zf = some (decide (i + 1 = 128 * g.n)) := by
    rw [zf, ← cnt, c', ofNat_beq_zero (by omega)]
    simp only [show 128 * g.n - (i + 1) = 0 ↔ i + 1 = 128 * g.n by omega]
  by_cases e : i + 1 = 128 * g.n
  · left
    refine ⟨by change t'.zf.map (!·) = some false; simp [z', e], ?_, m'⟩
    rw [← e]; exact h'
  · right
    exact ⟨by change t'.zf.map (!·) = some true; simp [z', e], j - 1, by omega, i + 1, by omega, by omega,
      h', m', c'⟩

end
end VG.Proof.Rsa.X86.Recover
