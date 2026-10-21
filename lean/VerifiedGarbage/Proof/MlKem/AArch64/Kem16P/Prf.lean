module

public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.State
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
public import VerifiedGarbage.Proof.Sha3.AArch64.Hybrid.X3
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics

/-! # The padded block of `PRF₂(r, N)`, written word by word

`prfWords_ok`: `Kem16P.prfWords` writes word `k` of `Noise.seedState`
(`r` from `RB`, then `N` and the suffix, then the final bit) to `D + o + st k`.
`prfBlock_ok`: so the third state at `ST` is `PRF₂(r, N)`'s padded block;
`reinitB_ok`: so is the second state of the pair at `x19`, its first kept. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt wordAddr pairR)
open VG.Spec.Sha3 (stateAt)

/-- Word `k` of `PRF₂(r, N)`'s padded block, `r` at `R`. -/
abbrev pw (m : Mem) (R : Addr) (N k : Nat) : BitVec 64 := (Noise.seedState m R N)[k]!

theorem imm16_eq {v : Nat} (h : v < 65536) : (BitVec.ofNat 16 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : v < 2 ^ 16), Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)]

/-- What `prfWords` keeps after `k` words. -/
def WInv (o st N : Nat) (s : State) (D R : Addr) (W : Region) (k : Nat) (t : State) : Prop :=
  Keep [.x9] s t ∧ Frame [W] s.mem t.mem ∧
    (∀ j < k, t.mem.readW (D + BitVec.ofNat 64 (o + st * j)) 64 = pw s.mem R N j) ∧
    ∀ a : Addr, (∀ j < k, Mem.Sep a 8 (D + BitVec.ofNat 64 (o + st * j)) 8) →
      t.mem.readW a 64 = s.mem.readW a 64

/-- One word's store. -/
theorem store_step {dst : Reg} {o st N k : Nat} {s t : State} {D R : Addr} {W : Region}
    (hd9 : dst ≠ .x9) (hst : 8 ≤ st) (ho : o % 8 = 0) (hs8 : st % 8 = 0) (hlim : o + st * 24 + 8 ≤ 32768)
    (hk : k < 25) (hD : s.gpr dst = D)
    (hW : ∀ k < 25, W.Contains (D + BitVec.ofNat 64 (o + st * k)) 8) (hWin : Covers [W] s.wr)
    (hI : WInv o st N s D R W k t) (hv : t.gpr .x9 = pw s.mem R N k) :
    WP isa (.block [.str .x .x9 dst (o + st * k)]) t (WInv o st N s D R W (k + 1)) := by
  obtain ⟨kt, ft, wt, ot⟩ := hI
  have bnd : ∀ j < 25, o + st * j + 8 ≤ 32768 := fun j hj => by
    have : st * j ≤ st * 24 := Nat.mul_le_mul_left _ (by omega)
    omega
  have hlt := bnd k hk
  refine wp_strx (a := D + BitVec.ofNat 64 (o + st * k)) ⟨by
      rw [Nat.add_mod, ho, Nat.mul_mod, hs8]; simp, by omega⟩
    (by rw [kt.get dst (by simpa using hd9), hD])
    (by rw [kt.wr]; exact hWin _ _ ⟨W, List.mem_singleton_self _, hW k hk⟩) fun u hu => wp_nil ?_
  have hm : u.mem = t.mem.writeW (D + BitVec.ofNat 64 (o + st * k)) (t.gpr .x9) := hu.mem
  have sep : ∀ j < k, Mem.Sep (D + BitVec.ofNat 64 (o + st * j)) 8 (D + BitVec.ofNat 64 (o + st * k)) 8 :=
    fun j hj => sep_off D (.inl (by
      have : st * j + st ≤ st * k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
      omega)) (by have := bnd j (by omega); omega) (by omega)
  refine ⟨kt.trans hu.keep |>.mono (by simp), ?_, fun j hj => ?_, fun a ha => ?_⟩
  · rw [hm]; exact ft.writeW (List.mem_singleton_self _) _ (hW k hk)
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (sep j hj) (by decide)]; exact wt j hj
    · rw [Mem.readW_writeW_self64, hv]
  · rw [hm, Mem.readW_writeW_sep (ha k (Nat.lt_succ_self _)) (by decide)]
    exact ot a fun j hj => ha j (Nat.lt_succ_of_lt hj)

/-- **The 25 words of `PRF₂(r, N)`'s padded block**, `r` at `R`. -/
theorem prfWords_ok {dst : Reg} {o st N : Nat} (hN : N < 256) (hd9 : dst ≠ .x9) (hst : 8 ≤ st)
    (ho : o % 8 = 0) (hs8 : st % 8 = 0) (hlim : o + st * 24 + 8 ≤ 32768)
    {s : State} {D R : Addr} (hD : s.gpr dst = D) (hR : s.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    {W : Region} (hW : ∀ k < 25, W.Contains (D + BitVec.ofNat 64 (o + st * k)) 8)
    (hWin : Covers [W] s.wr) (hRW : W.Disjoint ⟨R, 32⟩) (hRin : Covers [⟨R, 32⟩] (s.rd ++ s.wr)) :
    WP isa (.block (Impl.MlKem.AArch64.Kem16P.prfWords dst (fun k => o + st * k) N)) s
      (WInv o st N s D R W 25) := by
  refine wp_range_flatMap (M := isa) (WInv o st N s D R W) (fun k t hk hI => ?_) 25 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl⟩
  have hget := Noise.seedState_get s.mem R N hk
  unfold Impl.MlKem.AArch64.Kem16P.prfWord
  by_cases h4 : k < 4
  · rw [ite_eq_left h4]
    have kt := hI.1
    have ft := hI.2.1
    have hc : (⟨R, 32⟩ : Region).Contains (R + BitVec.ofNat 64 (8 * k)) 8 :=
      Offset.contains_base R (by omega) (by omega)
    refine wp_ldrx (a := R + BitVec.ofNat 64 (8 * k)) ⟨by
        simp only [Impl.MlKem.AArch64.KEM.RB]; omega, by simp only [Impl.MlKem.AArch64.KEM.RB]; omega⟩
      (by rw [kt.get .x28 (by decide), ← hR, ptr_add])
      (by rw [kt.rd, kt.wr]; exact hRin _ _ ⟨_, List.mem_singleton_self _, hc⟩) fun u hu e => ?_
    refine store_step hd9 hst ho hs8 hlim hk hD hW hWin ?_ ?_
    · obtain ⟨kt, ft, wt, ot⟩ := hI
      exact ⟨(kt.trans hu.keep).mono (by simp), by rw [hu.mem]; exact ft,
        fun j hj => by rw [hu.mem]; exact wt j hj, fun a ha => by rw [hu.mem]; exact ot a ha⟩
    · rw [e, pw, hget, ite_eq_left h4]
      exact ft.readW (r := ⟨R, 32⟩) hc (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hRW.symm) (by decide)
  · rw [ite_eq_right h4]
    have step : ∀ (v : BitVec 64) (i : Instr), (∀ (Q : State → Prop) (is : List Instr) (u : State),
        (∀ u', Only [.x9] u u' → u'.gpr .x9 = v → WP isa (.block is) u' Q) → WP isa (.block (i :: is)) u Q) →
        v = pw s.mem R N k →
        WP isa (.block [i, .str .x .x9 dst (o + st * k)]) t (WInv o st N s D R W (k + 1)) :=
      fun v i hi hv => hi _ _ _ fun u hu e => by
        obtain ⟨kt, ft, wt, ot⟩ := hI
        refine store_step hd9 hst ho hs8 hlim hk hD hW hWin
          ⟨(kt.trans hu.keep).mono (by simp), by rw [hu.mem]; exact ft,
            fun j hj => by rw [hu.mem]; exact wt j hj, fun a ha => by rw [hu.mem]; exact ot a ha⟩ ?_
        rw [e, hv]
    by_cases h4' : k = 4
    · rw [ite_eq_left h4']
      refine step _ _ (fun Q is u k => wp_movz k) ?_
      rw [imm16_eq (by omega), pw, hget, ite_eq_right h4, ite_eq_left h4']
    · rw [ite_eq_right h4']
      by_cases h16 : k = 16
      · rw [ite_eq_left h16]
        refine step 0x8000000000000000 _ (fun Q is u k => wp_x (d := .x9) (by rfl) k) ?_
        rw [pw, hget, ite_eq_right h4, ite_eq_right h4', ite_eq_left h16]
      · rw [ite_eq_right h16]
        refine step _ _ (fun Q is u k => wp_movz k) ?_
        rw [pw, hget, ite_eq_right h4, ite_eq_right h4', ite_eq_right h16]; rfl

/-- **The third state at `ST` set to `PRF₂(r, N)`'s padded block.** -/
theorem prfBlock_ok {N : Nat} (hN : N < 256) {s : State} {R : Addr}
    (hR : s.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hWin : Covers [VG.Proof.Sha3.AArch64.Hybrid.X3.stR (s.gpr .x28)] s.wr)
    (hRW : (VG.Proof.Sha3.AArch64.Hybrid.X3.stR (s.gpr .x28)).Disjoint ⟨R, 32⟩)
    (hRin : Covers [⟨R, 32⟩] (s.rd ++ s.wr)) :
    WP isa (.block (Impl.MlKem.AArch64.Kem16P.prfBlock N)) s fun t =>
      Keep [.x9] s t ∧ Frame [VG.Proof.Sha3.AArch64.Hybrid.X3.stR (s.gpr .x28)] s.mem t.mem ∧
      stateAt t.mem (s.gpr .x28) = Noise.seedState s.mem R N := by
  have hc : ∀ k < 25, (VG.Proof.Sha3.AArch64.Hybrid.X3.stR (s.gpr .x28)).Contains
      (s.gpr .x28 + BitVec.ofNat 64 (0 + 8 * k)) 8 := fun k hk =>
    Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (prfWords_ok (o := 0) (st := 8) hN (by decide) (by decide) (by decide) (by decide)
    (by decide) rfl hR hc hWin hRW hRin) fun t ⟨kt, ft, wt, _⟩ => ⟨kt, ft, ?_⟩
  refine Vector.ext fun i hi => ?_
  have := wt i hi
  rw [Nat.zero_add] at this
  simp only [stateAt, Vector.getElem_ofFn]
  rw [this, pw, getElem!_pos _ i hi]

/-- **The second state of the pair at `p` set to `PRF₂(r, N)`'s padded block**, the first kept. -/
theorem reinitB_ok {N : Nat} (hN : N < 256) {s : State} {p R : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x19 = p) (hR : s.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (pair : PairAt s.mem p A B)
    (hWin : Covers [pairR p] s.wr) (hRW : (pairR p).Disjoint ⟨R, 32⟩)
    (hRin : Covers [⟨R, 32⟩] (s.rd ++ s.wr)) :
    WP isa (.block (Impl.MlKem.AArch64.Kem16P.reinitB N)) s fun t =>
      Keep [.x9] s t ∧ Frame [pairR p] s.mem t.mem ∧ PairAt t.mem p A (Noise.seedState s.mem R N) := by
  have hc : ∀ k < 25, (pairR p).Contains (p + BitVec.ofNat 64 (8 + 16 * k)) 8 := fun k hk =>
    Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (prfWords_ok (o := 8) (st := 16) hN (by decide) (by decide) (by decide) (by decide)
    (by decide) hp hR hc hWin hRW hRin) fun t ⟨kt, ft, wt, ot⟩ => ⟨kt, ft, fun i hi => ?_⟩
  have hlo : t.mem.readW (wordAddr p i) 64 = s.mem.readW (wordAddr p i) 64 :=
    ot _ fun j hj => sep_off p (by
      rcases Nat.lt_or_ge j i with h | h
      · exact .inr (by omega)
      · exact .inl (by omega)) (by omega) (by omega)
  have hhi : wordAddr p i + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 + 16 * i) := by
    rw [wordAddr, ptr_add, Nat.add_comm]
  rw [read16_dwords, hlo, hhi, wt i hi, pw]
  have h0 := pair i hi
  rw [read16_dwords] at h0
  have e0 := congrArg (fun v => vdword v 0) h0
  simp only [vdword_ofVDwords_0] at e0
  rw [e0, getElem!_pos _ i hi]

end VG.Proof.MlKem.AArch64.Kem16P
