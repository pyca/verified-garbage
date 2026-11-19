module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Squeeze
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Squeeze
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.State
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Absorb
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.TCB.AArch64.Isa

/-! ### `MlKem.AArch64.Kem16P.Slot`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Kem16P.Prf`, which this module and modules that import it used -/

section

/-! # The padded block of `PRF₂(r, N)`, written word by word

`prfWords_ok`: `Kem16P.prfWords` writes word `k` of `Noise.seedState`
(`r` from `sd`, then `N` and the suffix, then the final bit) to `D + o + st k`.
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
  rw [Nat.mod_eq_of_lt (by omega_using [h] : v < 2 ^ 16), Nat.mod_eq_of_lt (by omega_using [h] : v < 2 ^ 64)]

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
    have : st * j ≤ st * 24 := Nat.mul_le_mul_left _ (by omega_using [hj])
    omega_using [hlim, this]
  have hlt := bnd k hk
  refine wp_strx (a := D + BitVec.ofNat 64 (o + st * k)) ⟨by
      rw [Nat.add_mod, ho, Nat.mul_mod, hs8]; simp, by omega_using [hlt]⟩
    (by rw [kt.get dst (by simpa using hd9), hD])
    (by rw [kt.wr]; exact hWin _ _ ⟨W, List.mem_singleton_self _, hW k hk⟩) fun u hu => wp_nil ?_
  have hm : u.mem = t.mem.writeW (D + BitVec.ofNat 64 (o + st * k)) (t.gpr .x9) := hu.mem
  have sep : ∀ j < k, Mem.Sep (D + BitVec.ofNat 64 (o + st * j)) 8 (D + BitVec.ofNat 64 (o + st * k)) 8 :=
    fun j hj => sep_off D (.inl (by
      have : st * j + st ≤ st * k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
      omega_using [hst, this])) (by have := bnd j (by omega_using [hk, hj]); omega_using [this]) (by omega_using [hlt])
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
    {s : State} {D R : Addr} {sd : Nat} (hsd : sd % 8 = 0) (hsd' : sd + 32 ≤ 32768) (hD : s.gpr dst = D)
    (hR : s.gpr .x28 + BitVec.ofNat 64 sd = R)
    {W : Region} (hW : ∀ k < 25, W.Contains (D + BitVec.ofNat 64 (o + st * k)) 8)
    (hWin : Covers [W] s.wr) (hRW : W.Disjoint ⟨R, 32⟩) (hRin : Covers [⟨R, 32⟩] (s.rd ++ s.wr)) :
    WP isa (.block (Impl.MlKem.AArch64.Kem16P.prfWords sd dst (fun k => o + st * k) N)) s
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
      Offset.contains_base R (by omega_using [h4]) (by omega_using [hk])
    refine wp_ldrx (a := R + BitVec.ofNat 64 (8 * k)) ⟨by omega_using [hsd], by omega_using [hsd', h4]⟩
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
      rw [imm16_eq (by omega_using [hN]), pw, hget, ite_eq_right h4, ite_eq_left h4']
    · rw [ite_eq_right h4']
      by_cases h16 : k = 16
      · rw [ite_eq_left h16]
        refine step 0x8000000000000000 _ (fun Q is u k => wp_x (d := .x9) (by rfl) k) ?_
        rw [pw, hget, ite_eq_right h4, ite_eq_right h4', ite_eq_left h16]
      · rw [ite_eq_right h16]
        refine step _ _ (fun Q is u k => wp_movz k) ?_
        rw [pw, hget, ite_eq_right h4, ite_eq_right h4', ite_eq_right h16]; rfl

/-- **The third state at `ST` set to `PRF₂(r, N)`'s padded block.** -/
theorem prfBlock_ok {N : Nat} (hN : N < 256) {s : State} {R : Addr} {sd : Nat}
    (hR : s.gpr .x28 + BitVec.ofNat 64 sd = R) (hsd : sd % 8 = 0 := by decide)
    (hsd' : sd + 32 ≤ 32768 := by decide)
    (hWin : Covers [VG.Proof.Sha3.AArch64.Hybrid.X3.stR (s.gpr .x28)] s.wr)
    (hRW : (VG.Proof.Sha3.AArch64.Hybrid.X3.stR (s.gpr .x28)).Disjoint ⟨R, 32⟩)
    (hRin : Covers [⟨R, 32⟩] (s.rd ++ s.wr)) :
    WP isa (.block (Impl.MlKem.AArch64.Kem16P.prfBlock sd N)) s fun t =>
      Keep [.x9] s t ∧ Frame [VG.Proof.Sha3.AArch64.Hybrid.X3.stR (s.gpr .x28)] s.mem t.mem ∧
      stateAt t.mem (s.gpr .x28) = Noise.seedState s.mem R N := by
  have hc : ∀ k < 25, (VG.Proof.Sha3.AArch64.Hybrid.X3.stR (s.gpr .x28)).Contains
      (s.gpr .x28 + BitVec.ofNat 64 (0 + 8 * k)) 8 := fun k hk =>
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  refine WP.mono (prfWords_ok (o := 0) (st := 8) hN (by decide) (by decide) (by decide) (by decide)
    (by decide) hsd hsd' rfl hR hc hWin hRW hRin) fun t ⟨kt, ft, wt, _⟩ => ⟨kt, ft, ?_⟩
  refine Vector.ext fun i hi => ?_
  have := wt i hi
  rw [Nat.zero_add] at this
  simp only [stateAt, Vector.getElem_ofFn]
  rw [this, pw, getElem!_pos _ i hi]

/-- **The second state of the pair at `p` set to `PRF₂(r, N)`'s padded block**, the first kept. -/
theorem reinitB_ok {N : Nat} (hN : N < 256) {s : State} {p R : Addr} {A B : Spec.Sha3.State} {sd : Nat}
    (hp : s.gpr .x19 = p) (hR : s.gpr .x28 + BitVec.ofNat 64 sd = R)
    (pair : PairAt s.mem p A B)
    (hWin : Covers [pairR p] s.wr) (hRW : (pairR p).Disjoint ⟨R, 32⟩)
    (hRin : Covers [⟨R, 32⟩] (s.rd ++ s.wr)) (hsd : sd % 8 = 0 := by decide) (hsd' : sd + 32 ≤ 32768 := by decide) :
    WP isa (.block (Impl.MlKem.AArch64.Kem16P.reinitB sd N)) s fun t =>
      Keep [.x9] s t ∧ Frame [pairR p] s.mem t.mem ∧ PairAt t.mem p A (Noise.seedState s.mem R N) := by
  have hc : ∀ k < 25, (pairR p).Contains (p + BitVec.ofNat 64 (8 + 16 * k)) 8 := fun k hk =>
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  refine WP.mono (prfWords_ok (o := 8) (st := 16) hN (by decide) (by decide) (by decide) (by decide)
    (by decide) hsd hsd' hp hR hc hWin hRW hRin) fun t ⟨kt, ft, wt, ot⟩ => ⟨kt, ft, fun i hi => ?_⟩
  have hlo : t.mem.readW (wordAddr p i) 64 = s.mem.readW (wordAddr p i) 64 :=
    ot _ fun j hj => sep_off p (by
      rcases Nat.lt_or_ge j i with h | h
      · exact .inr (by omega_using [h])
      · exact .inl (by omega_using [h])) (by omega_using [hi]) (by omega_using [hj])
  have hhi : wordAddr p i + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 + 16 * i) := by
    rw [wordAddr, ptr_add, Nat.add_comm]
  rw [read16_dwords, hlo, hhi, wt i hi, pw]
  have h0 := pair i hi
  rw [read16_dwords] at h0
  have e0 := congrArg (fun v => vdword v 0) h0
  simp only [vdword_ofVDwords_0] at e0
  rw [e0, getElem!_pos _ i hi]

end VG.Proof.MlKem.AArch64.Kem16P

end

end

/-! # A main squeeze computing `PRF₂(r, N)` in the third state

`prfOut_ok`: the first 16 words of the third state to buffer `N`.
`slotPrf_ok`: `PRF₂(r, N)`'s padded block into the third state, the `x3` call,
both SHAKE128 states' 21 words to their stream buffers, and the first 128
bytes of the third state to buffer `N` (`Rate128`, which `Noise.output_prf`
takes to `PRF₂`'s output). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P
variable {sha3 : Bool}

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR outAddr)
open VG.Proof.Sha3.AArch64.Neon.X2 (callR)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (rateR21 Rate21)
open VG.Proof.MlKem.AArch64.Noise (rateR Rate128)
open VG.Proof.MlKem.AArch64.Hybrid (clobbered stepRegs step3Writes frame)
open VG.Spec.Sha3 (stateAt keccakF)

theorem rate21_frame {m m' : Mem} {p : Addr} {A : Spec.Sha3.State} {rs : List Region}
    (h : Rate21 m p A) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (rateR21 p).Disjoint r) : Rate21 m' p A :=
  fun i hi => by
    show m'.readW (p + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [hf.readW (r := rateR21 p) (Offset.contains_base p (by omega_using [hi]) (by omega_using [hi])) hd (by decide)]
    exact h i hi

/-- **The first 16 words of the third state at `st` to buffer `N`.** -/
theorem prfOut_ok (bt N : Nat) {s : State} {st Bf : Addr} {S : Spec.Sha3.State}
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff bt N < 65536)
    (h28 : s.gpr .x28 = st) (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff bt N) = Bf)
    (hS : stateAt s.mem st = S) (hin : Covers [stR st] (s.rd ++ s.wr)) (hout : Covers [rateR Bf] s.wr)
    (hd : (stR st).Disjoint (rateR Bf)) :
    WP isa (.block (Impl.MlKem.AArch64.Kem16P.prfOut bt N)) s fun t =>
      Keep [.x2, .x9] s t ∧ Frame [rateR Bf] s.mem t.mem ∧ Rate128 t.mem Bf S := by
  unfold Impl.MlKem.AArch64.Kem16P.prfOut
  refine wp_ptrTo (by decide) hbo fun s₁ h₁ e₁ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) (fun k (t : State) =>
      Keep [.x2, .x9] s t ∧ t.gpr .x2 = Bf ∧ Frame [rateR Bf] s.mem t.mem ∧
        ∀ j < k, t.mem.readW (outAddr Bf j) 64 = S[j]!)
    (fun k t hk ⟨kt, xt, ft, wt⟩ => ?_) 16 (Nat.le_refl _) s₁
    ⟨h₁.keep.mono (by simp), by rw [e₁, h28, hB], by rw [h₁.mem]; exact Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩) fun t ⟨kt, _, ft, wt⟩ => ⟨kt, ft, wt⟩
  have hc : (stR st).Contains (st + BitVec.ofNat 64 (Impl.MlKem.AArch64.KEM.ST + 8 * k)) 8 :=
    Offset.contains_base st (by simp only [Impl.MlKem.AArch64.KEM.ST]; omega_using [hk]) (by simp only [Impl.MlKem.AArch64.KEM.ST]; omega_using [hk])
  have hbc : (rateR Bf).Contains (outAddr Bf k) 8 := Offset.contains_base Bf (by omega_using [hk]) (by omega_using [hk])
  refine wp_ldrx (a := st + BitVec.ofNat 64 (Impl.MlKem.AArch64.KEM.ST + 8 * k))
    ⟨by simp only [Impl.MlKem.AArch64.KEM.ST]; omega_using [], by simp only [Impl.MlKem.AArch64.KEM.ST]; omega_using [hk]⟩
    (by rw [kt.get .x28 (by decide), h28])
    (by rw [kt.rd, kt.wr]; exact hin _ _ ⟨_, List.mem_singleton_self _, hc⟩) fun u hu e => ?_
  refine wp_strx (a := outAddr Bf k) ⟨by omega_using [], by omega_using [hk]⟩ (by rw [hu.get .x2 (by decide), xt]; rfl)
    (by rw [hu.wr, kt.wr]; exact hout _ _ ⟨_, List.mem_singleton_self _, hbc⟩) fun v hv => wp_nil ?_
  have hm : v.mem = u.mem.writeW (outAddr Bf k) (u.gpr .x9) := hv.mem
  have hv9 : u.gpr .x9 = S[k]! := by
    rw [e, ft.readW hc (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide), ← hS]
    simp only [stateAt, Impl.MlKem.AArch64.KEM.ST, Nat.zero_add]
    rw [getElem!_pos _ k (by omega_using [hk]), Vector.getElem_ofFn]
  refine ⟨(kt.trans (hu.keep.trans hv.keep)).mono (by simp), by rw [hv.gpr, hu.get .x2 (by decide), xt], ?_,
    fun j hj => ?_⟩
  · rw [hm, hu.mem]; exact ft.writeW (List.mem_singleton_self _) _ hbc
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [show outAddr Bf j = Bf + BitVec.ofNat 64 (8 * j) from rfl,
        show outAddr Bf k = Bf + BitVec.ofNat 64 (8 * k) from rfl,
        Mem.readW_writeW_sep (sep_off Bf (.inl (by omega_using [hj])) (by omega_arith) (by omega_using [hk])) (by decide), hu.mem]
      exact wt j hj
    · rw [Mem.readW_writeW_self64, hv9]

/-- What a PRF slot needs of its memory: a main squeeze's, `r` at `R`, and buffer `N` at `Bf`. -/
structure SlotLay (p a b st R Bf : Addr) (s : State) : Prop where
  cov : Covers [pairR p, stR st, callR (p + 1536)] s.wr
  hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (Proof.Sha3.AArch64.Neon.wordAddr p i) 16
  hwa : ∀ i < 21, InRegions s.wr (outAddr a i) 8
  hwb : ∀ i < 21, InRegions s.wr (outAddr b i) 8
  sp : 128 ≤ s.sp.toNat
  dAB : (rateR21 a).Disjoint (rateR21 b)
  dPA : (pairR p).Disjoint (rateR21 a)
  dPB : (pairR p).Disjoint (rateR21 b)
  dPS : (pairR p).Disjoint (stR st)
  dPC : (pairR p).Disjoint (callR (p + 1536))
  dSC : (stR st).Disjoint (callR (p + 1536))
  dSA : (stR st).Disjoint (rateR21 a)
  dSB : (stR st).Disjoint (rateR21 b)
  fP : (frame s.sp).Disjoint (pairR p)
  fS : (frame s.sp).Disjoint (stR st)
  fC : (frame s.sp).Disjoint (callR (p + 1536))
  rin : Covers [⟨R, 32⟩] (s.rd ++ s.wr)
  dSR : (stR st).Disjoint ⟨R, 32⟩
  bout : Covers [rateR Bf] s.wr
  dSF : (stR st).Disjoint (rateR Bf)
  dAF : (rateR21 a).Disjoint (rateR Bf)
  dBF : (rateR21 b).Disjoint (rateR Bf)
  dPF : (pairR p).Disjoint (rateR Bf)

/-- **A main squeeze computing `PRF₂(r, N)` in the third state.** -/
theorem slotPrf_ok (sd bt : Nat) {N : Nat} (hN : N < 256)
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff bt N < 65536) {s : State} {p a b st R Bf : Addr}
    {A B : Spec.Sha3.State}
    (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = a) (h21 : s.gpr .x21 = b) (h28 : s.gpr .x28 = st)
    (hR : st + BitVec.ofNat 64 sd = R) (hsd : sd % 8 = 0) (hsd' : sd + 32 ≤ 32768)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff bt N) = Bf)
    (pair : PairAt s.mem p A B) (hl : SlotLay p a b st R Bf s) :
    WP isa (Impl.MlKem.AArch64.Kem16P.slotPrf sha3 sd bt N) s fun t =>
      Keep stepRegs s t ∧
      Frame (step3Writes p a b st s.sp ++ [rateR Bf]) s.mem t.mem ∧
      PairAt t.mem p (keccakF A) (keccakF B) ∧
      Rate21 t.mem a (keccakF A) ∧ Rate21 t.mem b (keccakF B) ∧
      t.gpr .x20 = a + 168 ∧ t.gpr .x21 = b + 168 ∧
      Rate128 t.mem Bf (keccakF (Noise.seedState s.mem R N)) := by
  unfold Impl.MlKem.AArch64.Kem16P.slotPrf
  refine WP.seq (WP.mono (prfBlock_ok hN (by rw [h28]; exact hR) (hsd := hsd) (hsd' := hsd')
    (by rw [h28]; exact Hybrid.covers_mono hl.cov (by simp)) (by rw [h28]; exact hl.dSR) hl.rin)
    fun u ⟨ku, fu, su⟩ => ?_)
  rw [h28] at fu su
  have pu : PairAt u.mem p A B :=
    VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame pair fu (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hl.dPS)
  refine WP.seq (WP.mono (Hybrid.x3call_ok (sha3 := sha3) (q := p + 1536) (S := Noise.seedState s.mem R N)
    (by rw [ku.get .x19, h19]) rfl (by rw [ku.get .x28, h28]) pu su hl.dPS hl.dPC hl.dSC
    (by rw [ku.sp]; exact hl.sp) (by rw [ku.sp]; exact hl.fP) (by rw [ku.sp]; exact hl.fS)
    (by rw [ku.sp]; exact hl.fC) (by rw [ku.wr]; exact hl.cov)) fun v ⟨kv, fv, pv, sv⟩ => ?_)
  rw [ku.sp] at fv
  have kuv := ku.trans kv
  rw [WP.block_append_iff]
  refine WP.mono (Hybrid.tail_ok (by rw [kuv.get .x19, h19]) (by rw [kuv.get .x20, h20])
    (by rw [kuv.get .x21, h21]) pv
    (fun i hi => by rw [kuv.rd, kuv.wr]; exact hl.hin i hi)
    (fun i hi => by rw [kuv.wr]; exact hl.hwa i hi) (fun i hi => by rw [kuv.wr]; exact hl.hwb i hi)
    hl.dAB hl.dPA hl.dPB) fun w ⟨kw, fw, aw, bw, w20, w21⟩ => ?_
  have svt : ∀ r ∈ [rateR21 a, rateR21 b], (stR st).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl; exact hl.dSA; exact hl.dSB
  have sw : stateAt w.mem st = keccakF (Noise.seedState s.mem R N) := by
    rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame fw svt, sv]
  have kuw := kuv.trans kw
  refine WP.mono (prfOut_ok bt N hbo (by rw [kuw.get .x28, h28]) hB sw
    (by rw [kuw.rd, kuw.wr]; exact Covers.right (Hybrid.covers_mono hl.cov (by simp)))
    (by rw [kuw.wr]; exact hl.bout) hl.dSF) fun t ⟨kt, ft, rt⟩ => ?_
  have fpt : ∀ r ∈ [rateR Bf], (pairR p).Disjoint r := by
    intro r hr; rw [List.mem_singleton.mp hr]; exact hl.dPF
  refine ⟨(kuw.trans kt).mono (by simp [stepRegs, clobbered]), ?_, ?_,
    rate21_frame aw ft (fun r hr => by rw [List.mem_singleton.mp hr]; exact hl.dAF),
    rate21_frame bw ft (fun r hr => by rw [List.mem_singleton.mp hr]; exact hl.dBF),
    by rw [kt.get .x20 (by decide), w20], by rw [kt.get .x21 (by decide), w21], rt⟩
  · refine (((fu.mono (by simp [step3Writes])).trans (fv.mono (by simp [step3Writes]))).trans
      (fw.mono (by simp [step3Writes]))).trans (ft.mono (by simp))
  · exact VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame
      (VG.Proof.Sha3.AArch64.Hybrid.X3.pairAt_frame pv fw (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl; exact hl.dPA; exact hl.dPB)) ft fpt

end VG.Proof.MlKem.AArch64.Kem16P

end

end

/-!
# The three main squeezes of a pair computing PRF outputs

As `Hybrid/Squeeze.lean`, with `Kem16P.stepP` for `Hybrid.stepM`: the
first `m` main squeezes compute `PRF₂(r, N₀ + k)` in the third state
(`slotPrf_ok`) into the buffers from `B₀`, 168 bytes apart (`PrfBufs`), `r` at
`R`. `startP_ok`: with the pair's initialization before them.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P
variable {sha3 : Bool}

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR wordAddr outAddr)
open VG.Proof.Sha3.AArch64.Neon.X2 (callR)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (rateR21 Rate21 Blocks blockAt streamR block_sub)
open VG.Proof.MlKem.AArch64.Noise (rateR Rate128)
open VG.Proof.MlKem.AArch64.Hybrid (stepRegs step3Writes frame squeezeWrites startWrites
  blockAt_eq outAddr_eq in_scratch cov_scratch extend_blocks3 startRegs3)
open VG.Proof.Sha3 (iterF iterF_succ)
open VG.Spec.Sha3 (stateAt bytesAt keccakF)

/-- The three buffers of a pair's PRF outputs. -/
def bufR (B₀ : Addr) : Region := ⟨B₀, 504⟩

/-- Buffer `k` from `B₀`. -/
abbrev bufAt (B₀ : Addr) (k : Nat) : Addr := B₀ + BitVec.ofNat 64 (168 * k)

/-- The first `n` PRF outputs from `N₀`, `r` at `R` in `mR`, in their buffers from `B₀`. -/
def PrfBufs (m : Mem) (B₀ : Addr) (mR : Mem) (R : Addr) (N₀ n : Nat) : Prop :=
  ∀ k < n, Rate128 m (bufAt B₀ k) (keccakF (Noise.seedState mR R (N₀ + k)))

theorem PrfBufs.frame {m m' mR : Mem} {B₀ R : Addr} {N₀ n : Nat} (h : PrfBufs m B₀ mR R N₀ n)
    (hn : n ≤ 3) {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (bufR B₀).Disjoint r) :
    PrfBufs m' B₀ mR R N₀ n := fun k hk i hi => by
  have hc : (bufR B₀).Contains (outAddr (bufAt B₀ k) i) 8 := by
    show (bufR B₀).Contains (B₀ + BitVec.ofNat 64 (168 * k) + BitVec.ofNat 64 (8 * i)) 8
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base B₀ (by omega_arith) (by omega_arith)
  rw [hf.readW hc hd (by decide)]
  exact h k hk i hi

/-- What a PRF pair's squeezes may write. -/
def squeezeWritesP (p st sp B₀ : Addr) : List Region := squeezeWrites p st sp ++ [bufR B₀]

/-- What a PRF pair's start may write. -/
def startWritesP (p st sp B₀ : Addr) : List Region := startWrites p st sp ++ [bufR B₀]

/-- What the pair's memory is. -/
structure SqLayP (p st R B₀ : Addr) (s : State) : Prop where
  scratch : Covers [⟨p, 2048⟩] s.wr
  state : Covers [stR st] s.wr
  sp : 128 ≤ s.sp.toNat
  dSP : (stR st).Disjoint ⟨p, 2048⟩
  fP : (frame s.sp).Disjoint ⟨p, 2048⟩
  fS : (frame s.sp).Disjoint (stR st)
  rin : Covers [⟨R, 32⟩] (s.rd ++ s.wr)
  dSR : (stR st).Disjoint ⟨R, 32⟩
  dPR : (Region.mk p 2048).Disjoint ⟨R, 32⟩
  fR : (frame s.sp).Disjoint ⟨R, 32⟩
  bout : Covers [bufR B₀] s.wr
  dSF : (stR st).Disjoint (bufR B₀)
  dPF : (Region.mk p 2048).Disjoint (bufR B₀)
  fF : (frame s.sp).Disjoint (bufR B₀)
  dRF : (Region.mk R 32).Disjoint (bufR B₀)

theorem SqLayP.frame {p st R B₀ : Addr} {s t : State} (h : SqLayP p st R B₀ s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp) : SqLayP p st R B₀ t := by
  refine ⟨?_, ?_, ?_, h.dSP, ?_, ?_, ?_, h.dSR, h.dPR, ?_, ?_, h.dSF, h.dPF, ?_, h.dRF⟩ <;>
    simp only [hr, hw, hsp]
  exacts [h.scratch, h.state, h.sp, h.fP, h.fS, h.rin, h.fR, h.bout, h.fF]

theorem buf_sub (B₀ : Addr) {k : Nat} (hk : k < 3) : Region.Sub (rateR (bufAt B₀ k)) (bufR B₀) :=
  Offset.sub_base B₀ (by omega_arith)

theorem SqLayP.slotLay {p st R B₀ : Addr} {s : State} (h : SqLayP p st R B₀ s) {k : Nat} (hk : k < 3) :
    SlotLay p (blockAt (p + 400) k) (blockAt (p + 904) k) st R (bufAt B₀ k) s := by
  have ea : blockAt (p + 400) k = p + BitVec.ofNat 64 (400 + 168 * k) := blockAt_eq p 400 k
  have eb : blockAt (p + 904) k = p + BitVec.ofNat 64 (904 + 168 * k) := blockAt_eq p 904 k
  have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
    fun h => Offset.sub_base p h
  have subP : Region.Sub (pairR p) ⟨p, 2048⟩ := Region.sub_prefix (by decide : 400 ≤ 2048)
  have bs := buf_sub B₀ hk
  rw [ea, eb]
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, h.sp,
    Offset.disjoint p (by omega_arith) (by omega_arith) (by omega_arith),
    Offset.base_disjoint p (by omega_arith) (by omega_arith), Offset.base_disjoint p (by omega_arith) (by omega_arith),
    (h.dSP.sub_right subP).symm, Offset.base_disjoint p (e := 1536) (n := 136) (by decide) (by decide),
    h.dSP.sub_right (sub (o := 1536) (n := 136) (by decide)), h.dSP.sub_right (sub (by omega_arith)),
    h.dSP.sub_right (sub (by omega_arith)), h.fP.sub_right subP, h.fS,
    h.fP.sub_right (sub (o := 1536) (n := 136) (by decide)), h.rin, h.dSR,
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton_self _, 168 * k, rfl, by simp only [rateR, bufR]; omega_arith⟩).trans h.bout,
    h.dSF.sub_right bs, (h.dPF.sub_left (sub (by omega_arith))).sub_right bs,
    (h.dPF.sub_left (sub (by omega_arith))).sub_right bs, (h.dPF.sub_left subP).sub_right bs⟩
  · refine Covers.cons ?_ (Covers.cons (Hybrid.covers_mono h.state (by simp)) (Covers.cons ?_ Covers.nil))
    · simpa only [BitVec.add_zero, pairR] using cov_scratch (o := 0) (n := 400) h.scratch (by decide)
    · exact cov_scratch (o := 1536) (n := 136) h.scratch (by decide)
  · exact Covers.right (cov_scratch h.scratch (o := 16 * i) (n := 16) (by omega_arith)) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  · rw [outAddr_eq]; exact in_scratch h.scratch (by omega_arith)
  · rw [outAddr_eq]; exact in_scratch h.scratch (by omega_arith)

theorem rate128_frame {m m' : Mem} {p : Addr} {A : Spec.Sha3.State} {rs : List Region}
    (h : Rate128 m p A) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (rateR p).Disjoint r) : Rate128 m' p A :=
  fun i hi => by
    show m'.readW (p + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [hf.readW (r := rateR p) (Offset.contains_base p (by omega_arith) (by omega_arith)) hd (by decide)]
    exact h i hi

theorem seedState_frame {m m' : Mem} {R : Addr} {N : Nat} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (Region.mk R 32).Disjoint r) : Noise.seedState m' R N = Noise.seedState m R N := by
  apply Vector.ext; intro i hi
  simp only [Noise.seedState, Vector.getElem_ofFn]
  split
  · rw [hf.readW (r := ⟨R, 32⟩) (Offset.contains_base R (by omega_arith) (by omega_arith)) hd (by decide)]
  · rfl

/-- `Hybrid.extend_blocks3`, with the writes `Bs` too. -/
theorem extend_blocksP {m m' : Mem} {p a b st sp : Addr} {A : Spec.Sha3.State} {k : Nat} (hk : k < 3)
    {Bs : List Region} (old : Blocks m a k A) (new : Rate21 m' (blockAt a k) (iterF (k + 1) A))
    (hf : Frame (step3Writes p (blockAt a k) (blockAt b k) st sp ++ Bs) m m')
    (hpa : (pairR p).Disjoint (streamR a)) (hab : (streamR a).Disjoint (streamR b))
    (hwa : (callR (p + 1536)).Disjoint (streamR a)) (hsa : (stR st).Disjoint (streamR a))
    (hfa : (frame sp).Disjoint (streamR a)) (hBa : ∀ r ∈ Bs, (streamR a).Disjoint r) :
    Blocks m' a (k + 1) A := by
  intro j hj
  by_cases he : j = k
  · subst j; exact new
  · have hjk : j < k := by omega_arith
    intro i hi
    have hc : (rateR21 (blockAt a j)).Contains (outAddr (blockAt a j) i) 8 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    rw [hf.readW hc (by
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · simp only [step3Writes, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
          · exact (hpa.sub_right (block_sub a (by omega_arith))).symm
          · exact Offset.disjoint a (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
          · exact (hab.sub_left (block_sub a (by omega_arith))).sub_right (block_sub b hk)
          · exact (hwa.sub_right (block_sub a (by omega_arith))).symm
          · exact (hsa.sub_right (block_sub a (by omega_arith))).symm
          · exact (hfa.sub_right (block_sub a (by omega_arith))).symm
        · exact (hBa r hr).sub_left (block_sub a (by omega_arith))) (by decide)]
    exact old j hjk i hi

/-- After `k` of the three main squeezes, the first `m` computing PRF outputs from `N₀`. -/
structure SInvP (initial : State) (p st R B₀ : Addr) (A B : Spec.Sha3.State) (N₀ m k : Nat) (s : State) : Prop where
  keep : Keep stepRegs initial s
  pair : PairAt s.mem p (iterF k A) (iterF k B)
  ptr : s.gpr .x19 = p
  pa : s.gpr .x20 = blockAt (p + 400) k
  pb : s.gpr .x21 = blockAt (p + 904) k
  frame : Frame (squeezeWritesP p st initial.sp B₀) initial.mem s.mem
  oa : Blocks s.mem (p + 400) k A
  ob : Blocks s.mem (p + 904) k B
  prf : PrfBufs s.mem B₀ initial.mem R N₀ (min k m)

/-- A main squeeze computing no PRF output. -/
theorem plainP_ok {s : State} {p st R B₀ : Addr} {A B : Spec.Sha3.State} {k : Nat} (hk : k < 3)
    (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = blockAt (p + 400) k) (h21 : s.gpr .x21 = blockAt (p + 904) k)
    (pair : PairAt s.mem p A B) (hl : SqLayP p st R B₀ s) :
    WP isa (Impl.MlKem.AArch64.Hybrid.plainStep sha3) s fun t =>
      Keep stepRegs s t ∧
      Frame (step3Writes p (blockAt (p + 400) k) (blockAt (p + 904) k) st s.sp) s.mem t.mem ∧
      PairAt t.mem p (keccakF A) (keccakF B) ∧
      Rate21 t.mem (blockAt (p + 400) k) (keccakF A) ∧ Rate21 t.mem (blockAt (p + 904) k) (keccakF B) ∧
      t.gpr .x20 = blockAt (p + 400) k + 168 ∧ t.gpr .x21 = blockAt (p + 904) k + 168 := by
  have sl := hl.slotLay hk
  have hc := Paired.squeezeBlock_ok (sha3 := sha3) (rp := .x19) (ra := .x20) (rb := .x21) h19 h20 h21 (by rw [h19]; rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) pair sl.hin sl.hwa sl.hwb sl.dAB sl.dPA sl.dPB sl.dPC
    (Hybrid.covers_mono sl.cov (by simp))
  unfold Impl.MlKem.AArch64.Hybrid.plainStep Impl.MlKem.AArch64.Hybrid.squeezeTail
  apply WP.seq
  refine WP.mono (WP.seq_iff.mp hc) fun u hu => ?_
  rw [WP.block_append_iff]
  refine WP.mono hu fun v ⟨kv, pv, av, bv, fv, vv⟩ => ?_
  refine wp_addImm (by decide) fun v1 h1 e1 => wp_addImm (by decide) fun t h2 e2 => wp_nil ?_
  have hv : Keep Paired.blockRegs s v := ⟨kv.gpr, kv.rd, kv.wr, kv.sp, vv⟩
  have ot : Only [.x20, .x21] v t := (h1.trans h2).mono (by simp)
  have hm : t.mem = v.mem := ot.mem
  refine ⟨(hv.trans ot.keep).mono (by simp [stepRegs, Hybrid.clobbered, Paired.blockRegs, VG.Proof.Sha3.AArch64.Neon.X2.volatile]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact fv.mono (by simp [step3Writes])
  · rw [hm]; exact pv
  · rw [hm]; exact av
  · rw [hm]; exact bv
  · rw [h2.get .x20 (by decide), e1, kv.gpr .x20 (by decide), h20]; rfl
  · rw [e2, h1.get .x21 (by decide), kv.gpr .x21 (by decide), h21]; rfl

/-- One of the three main squeezes. -/
theorem pstep_ok (sd bt : Nat) {initial s : State} {p st R B₀ : Addr}
    {A B : Spec.Sha3.State} {N₀ m k : Nat} (hk : k < 3) (hN : N₀ + 2 < 256)
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff bt (N₀ + 2) < 65536)
    (hl : SqLayP p st R B₀ initial) (h28 : initial.gpr .x28 = st)
    (hR : st + BitVec.ofNat 64 sd = R) (hsd : sd % 8 = 0) (hsd' : sd + 32 ≤ 32768)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff bt N₀) = B₀)
    (h : SInvP initial p st R B₀ A B N₀ m k s) :
    WP isa (Impl.MlKem.AArch64.Kem16P.stepP sha3 sd bt N₀ m k) s (SInvP initial p st R B₀ A B N₀ m (k + 1)) := by
  have hls : SqLayP p st R B₀ s := hl.frame h.keep.rd h.keep.wr h.keep.sp
  have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
    fun h => Offset.sub_base p h
  have bs := buf_sub B₀ hk
  have dBW : ∀ r ∈ step3Writes p (blockAt (p + 400) k) (blockAt (p + 904) k) st initial.sp,
      (bufR B₀).Disjoint r := by
    intro r hr; simp only [step3Writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hl.dPF.sub_left (Region.sub_prefix (by decide : 400 ≤ 2048))).symm
    · show Region.Disjoint _ ⟨blockAt (p + BitVec.ofNat 64 400) k, 168⟩
      rw [blockAt_eq]; exact (hl.dPF.sub_left (sub (by omega_arith))).symm
    · show Region.Disjoint _ ⟨blockAt (p + BitVec.ofNat 64 904) k, 168⟩
      rw [blockAt_eq]; exact (hl.dPF.sub_left (sub (by omega_arith))).symm
    · exact (hl.dPF.sub_left (sub (o := 1536) (n := 136) (by decide))).symm
    · exact hl.dSF.symm
    · exact hl.fF.symm
  have next : ∀ {t : State} (Bs : List Region), (∀ r ∈ Bs, r = rateR (bufAt B₀ k)) →
      Keep stepRegs s t → Frame (step3Writes p (blockAt (p + 400) k)
      (blockAt (p + 904) k) st s.sp ++ Bs) s.mem t.mem →
      PairAt t.mem p (keccakF (iterF k A)) (keccakF (iterF k B)) →
      Rate21 t.mem (blockAt (p + 400) k) (keccakF (iterF k A)) →
      Rate21 t.mem (blockAt (p + 904) k) (keccakF (iterF k B)) →
      t.gpr .x20 = blockAt (p + 400) k + 168 → t.gpr .x21 = blockAt (p + 904) k + 168 →
      (k < m → Rate128 t.mem (bufAt B₀ k) (keccakF (Noise.seedState initial.mem R (N₀ + k)))) →
      SInvP initial p st R B₀ A B N₀ m (k + 1) t := by
    intro t Bs hBs kt ft pt at' bt t20 t21 rt
    rw [h.keep.sp] at ft
    have ft3 : Frame (step3Writes p (blockAt (p + 400) k) (blockAt (p + 904) k) st initial.sp ++ [bufR B₀])
        s.mem t.mem := ft.sub fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨bufR B₀, by simp, by rw [hBs r hr]; exact bs⟩
    have fsub : Frame (squeezeWritesP p st initial.sp B₀) s.mem t.mem := by
      refine ft3.sub fun r hr => ?_
      simp only [step3Writes, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      · exact ⟨pairR p, by simp [squeezeWritesP, squeezeWrites], fun _ h => h⟩
      · exact ⟨streamR (p + 400), by simp [squeezeWritesP, squeezeWrites], block_sub _ hk⟩
      · exact ⟨streamR (p + 904), by simp [squeezeWritesP, squeezeWrites], block_sub _ hk⟩
      · exact ⟨callR (p + 1536), by simp [squeezeWritesP, squeezeWrites], fun _ h => h⟩
      · exact ⟨stR st, by simp [squeezeWritesP, squeezeWrites], fun _ h => h⟩
      · exact ⟨frame initial.sp, by simp [squeezeWritesP, squeezeWrites], fun _ h => h⟩
      · exact ⟨bufR B₀, by simp [squeezeWritesP], fun _ h => h⟩
    have dP : ∀ {o : Nat}, o + 504 ≤ 2048 → (frame initial.sp).Disjoint (streamR (p + BitVec.ofNat 64 o)) :=
      fun h => hl.fP.sub_right (sub h)
    have hBs' : ∀ {o : Nat}, o + 504 ≤ 2048 → ∀ r ∈ Bs, (streamR (p + BitVec.ofNat 64 o)).Disjoint r :=
      fun ho r hr => by rw [hBs r hr]; exact (hl.dPF.sub_left (sub ho)).sub_right bs
    refine ⟨(h.keep.trans kt).mono (fun r hr => by rcases List.mem_append.mp hr with h | h <;> exact h), ?_,
      (kt.get .x19).trans h.ptr, ?_, ?_, h.frame.trans fsub, ?_, ?_, fun j hj => ?_⟩
    · simpa only [iterF_succ] using pt
    · rw [t20]; show (p + 400 + BitVec.ofNat 64 (168 * k)) + BitVec.ofNat 64 168 = p + 400 + BitVec.ofNat 64 (168 * (k + 1))
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 168 * k + 168 = 168 * (k + 1) by omega_arith]
    · rw [t21]; show (p + 904 + BitVec.ofNat 64 (168 * k)) + BitVec.ofNat 64 168 = p + 904 + BitVec.ofNat 64 (168 * (k + 1))
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 168 * k + 168 = 168 * (k + 1) by omega_arith]
    · exact extend_blocksP hk h.oa (by simpa only [iterF_succ] using at') ft
        (Offset.base_disjoint p (by decide) (by decide)) (Offset.disjoint p (by decide) (by decide) (by decide))
        (Offset.disjoint p (by decide) (by decide) (by decide)) (hl.dSP.sub_right (sub (by decide)))
        (dP (by decide)) (hBs' (by decide))
    · refine extend_blocksP hk h.ob (by simpa only [iterF_succ] using bt) (ft.mono ?_)
        (Offset.base_disjoint p (by decide) (by decide))
        (Offset.disjoint p (d := 400) (n := 504) (e := 904) (k := 504) (by decide) (by decide) (by decide)).symm
        (Offset.disjoint p (by decide) (by decide) (by decide)) (hl.dSP.sub_right (sub (by decide)))
        (dP (by decide)) (hBs' (by decide))
      intro r hr; simp only [step3Writes, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h | h | h | h) | h <;> simp [h]
    · by_cases hjk : j < min k m
      · refine rate128_frame (h.prf j hjk) ft fun r hr => ?_
        have hj3 : j < 3 := by omega_arith
        rcases List.mem_append.mp hr with hr | hr
        · exact (dBW r hr).sub_left (buf_sub B₀ hj3)
        · rw [hBs r hr]
          exact Offset.disjoint B₀ (by omega_arith) (by omega_arith) (by omega_arith)
      · have hjk' : j = k := by omega_arith
        subst hjk'
        exact rt (by omega_arith)
  unfold Impl.MlKem.AArch64.Kem16P.stepP
  split
  · rename_i hkm
    have hbk : Impl.MlKem.AArch64.Kem16P.bufOff bt (N₀ + k) < 65536 := by
      simp only [Impl.MlKem.AArch64.Kem16P.bufOff] at hbo ⊢; omega_arith
    have hBk : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff bt (N₀ + k)) = bufAt B₀ k := by
      rw [← hB, bufAt, BitVec.add_assoc, ← BitVec.ofNat_add]
      simp only [Impl.MlKem.AArch64.Kem16P.bufOff]
      rw [show bt + 168 * N₀ + 168 * k = bt + 168 * (N₀ + k) by
        rw [Nat.mul_add, Nat.add_assoc]]
    refine WP.mono (slotPrf_ok (sha3 := sha3) sd bt (N := N₀ + k) (by omega_arith) hbk h.ptr h.pa h.pb
      (by rw [h.keep.get .x28, h28]) hR hsd hsd' hBk h.pair (hls.slotLay hk))
      fun t ⟨kt, ft, pt, at', bt, t20, t21, rt⟩ =>
        next [rateR (bufAt B₀ k)] (fun r hr => List.mem_singleton.mp hr) kt ft pt at' bt t20 t21 fun _ => ?_
    rw [seedState_frame h.frame (fun r hr => ?_)] at rt
    · exact rt
    simp only [squeezeWritesP, squeezeWrites, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    · exact (hl.dPR.sub_left (Region.sub_prefix (by decide : 400 ≤ 2048))).symm
    · exact (hl.dPR.sub_left (sub (by decide))).symm
    · exact (hl.dPR.sub_left (sub (by decide))).symm
    · exact (hl.dPR.sub_left (sub (o := 1536) (n := 136) (by decide))).symm
    · exact hl.dSR.symm
    · exact hl.fR.symm
    · exact hl.dRF
  · rename_i hkm
    refine WP.mono (plainP_ok (sha3 := sha3) hk h.ptr h.pa h.pb h.pair hls) fun t ⟨kt, ft, pt, at', bt, t20, t21⟩ =>
      next [] (fun r hr => absurd hr (List.not_mem_nil)) kt (by simpa using ft) pt at' bt t20 t21
        fun hkm' => absurd hkm' hkm

/-- **The three main squeezes** of a pair, the first `m` computing PRF outputs from `N₀`. -/
theorem squeezeP_ok (sd bt : Nat) {s : State} {p st R B₀ : Addr}
    {A B : Spec.Sha3.State} {N₀ m : Nat} (hN : N₀ + 2 < 256)
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff bt (N₀ + 2) < 65536)
    (hl : SqLayP p st R B₀ s) (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = p + 400)
    (h21 : s.gpr .x21 = p + 904) (h28 : s.gpr .x28 = st)
    (hR : st + BitVec.ofNat 64 sd = R) (hsd : sd % 8 = 0) (hsd' : sd + 32 ≤ 32768)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff bt N₀) = B₀)
    (pair : PairAt s.mem p A B) :
    WP isa (.seq (Impl.MlKem.AArch64.Kem16P.stepP sha3 sd bt N₀ m 0)
      (.seq (Impl.MlKem.AArch64.Kem16P.stepP sha3 sd bt N₀ m 1) (Impl.MlKem.AArch64.Kem16P.stepP sha3 sd bt N₀ m 2))) s
      (SInvP s p st R B₀ A B N₀ m 3) := by
  have h0 : SInvP s p st R B₀ A B N₀ m 0 s :=
    ⟨Keep.refl _ _, pair, h19, by rw [h20]; exact (BitVec.add_zero _).symm,
      by rw [h21]; exact (BitVec.add_zero _).symm, Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j hj => absurd hj (by simp)⟩
  refine WP.seq (WP.mono (pstep_ok (sha3 := sha3) sd bt (k := 0) (by decide) hN hbo hl h28 hR hsd hsd' hB h0) fun t ht => ?_)
  refine WP.seq (WP.mono (pstep_ok (sha3 := sha3) sd bt (k := 1) (by decide) hN hbo hl h28 hR hsd hsd' hB ht) fun u hu => ?_)
  exact pstep_ok (sha3 := sha3) sd bt (k := 2) (by decide) hN hbo hl h28 hR hsd hsd' hB hu

/-- **A PRF pair's initialization and main squeezes** (as `Hybrid.startM_ok`). -/
theorem startP_ok (L : Impl.MlKem.AArch64.KemLay) (sd bt : Nat) {s : State}
    {p seed st R B₀ : Addr} {sb ss a b N₀ m : Nat} (hN : N₀ + 2 < 256)
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff bt (N₀ + 2) < 65536)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0)
    (hp : s.gpr .x28 + BitVec.ofNat 64 ss = p) (ha : s.gpr .x28 + BitVec.ofNat 64 sb = seed)
    (hin : ∀ j < 4, InRegions (s.rd ++ s.wr) (seed + BitVec.ofNat 64 (8 * j)) 8)
    (hsep : (Region.mk seed 32).Disjoint ⟨p, 2048⟩)
    (hl : SqLayP p st R B₀ s) (h28 : s.gpr .x28 = st)
    (hR : st + BitVec.ofNat 64 sd = R) (hsd : sd % 8 = 0) (hsd' : sd + 32 ≤ 32768)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff bt N₀) = B₀) :
    WP isa (.seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a b L.k))
      (.seq (Impl.MlKem.AArch64.Kem16P.stepP sha3 sd bt N₀ m 0)
        (.seq (Impl.MlKem.AArch64.Kem16P.stepP sha3 sd bt N₀ m 1) (Impl.MlKem.AArch64.Kem16P.stepP sha3 sd bt N₀ m 2)))) s
      fun t =>
      Keep startRegs3 s t ∧ Frame (startWritesP p st s.sp B₀) s.mem t.mem ∧ Noise.Saved p s t.mem ∧
      t.gpr .x19 = p ∧
      PairAt t.mem p (iterF 3 (Paired.seedState s.mem seed a L.k)) (iterF 3 (Paired.seedState s.mem seed b L.k)) ∧
      Blocks t.mem (p + 400) 3 (Paired.seedState s.mem seed a L.k) ∧
      Blocks t.mem (p + 904) 3 (Paired.seedState s.mem seed b L.k) ∧
      PrfBufs t.mem B₀ s.mem R N₀ (min 3 m) := by
  have hc := hl.scratch
  have iw {o l : Nat} (h : o + l ≤ 2048) := Noise.inScratch hc h (by decide)
  have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
    fun h => Offset.sub_base p h
  refine WP.seq (WP.mono (Paired.init_ok hss hsb h8b hp ha hin
    (fun j hj => iw (by omega_arith)) (fun j hj => iw (by omega_arith))
    (hsep.sub_right (Offset.sub_base p (by decide)))
    (hsep.sub_right (Region.sub_prefix (by decide : 400 ≤ 2048)))
    (Offset.disjoint_base p (by decide) (by decide))) fun u ⟨ku, fu, sv, h19, h20, h21, h22, pair⟩ => ?_)
  have fi : Frame [⟨p, 2048⟩] s.mem u.mem := fu.sub (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨p, 2048⟩, by simp, Offset.sub_base p (by decide)⟩
    · exact ⟨⟨p, 2048⟩, by simp, Region.sub_prefix (by decide : 400 ≤ 2048)⟩)
  refine WP.mono (squeezeP_ok (sha3 := sha3) sd bt hN hbo (hl.frame ku.rd ku.wr ku.sp) h19 h20 h21
    (by rw [ku.get .x28]; exact h28) hR hsd hsd' hB pair) fun t ht => ?_
  have hsR : ∀ {N : Nat}, Noise.seedState u.mem R N = Noise.seedState s.mem R N := fun {_} =>
    seedState_frame fi (fun r hr => by rw [List.mem_singleton.mp hr]; exact hl.dPR.symm)
  refine ⟨ku.trans ht.keep, ?_, ?_, ht.ptr, ht.pair, ht.oa, ht.ob, fun k hk => ?_⟩
  · have ft := ht.frame
    rw [ku.sp] at ft
    refine (fi.mono (by simp [startWritesP, startWrites])).trans (ft.sub fun r hr => ?_)
    simp only [squeezeWritesP, squeezeWrites, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    · exact ⟨⟨p, 2048⟩, by simp [startWritesP, startWrites], Region.sub_prefix (by decide : 400 ≤ 2048)⟩
    · exact ⟨⟨p, 2048⟩, by simp [startWritesP, startWrites], sub (o := 400) (n := 504) (by decide)⟩
    · exact ⟨⟨p, 2048⟩, by simp [startWritesP, startWrites], sub (o := 904) (n := 504) (by decide)⟩
    · exact ⟨⟨p, 2048⟩, by simp [startWritesP, startWrites], sub (o := 1536) (n := 136) (by decide)⟩
    · exact ⟨stR st, by simp [startWritesP, startWrites], fun _ h => h⟩
    · exact ⟨frame s.sp, by simp [startWritesP, startWrites], fun _ h => h⟩
    · exact ⟨bufR B₀, by simp [startWritesP], fun _ h => h⟩
  · apply sv.frame ht.frame
    intro r hr; simp only [squeezeWritesP, squeezeWrites, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    · exact Offset.disjoint_base p (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact (hl.dSP.sub_right (sub (o := 1800) (n := 48) (by decide))).symm
    · rw [ku.sp]; exact (hl.fP.sub_right (sub (o := 1800) (n := 48) (by decide))).symm
    · exact (hl.dPF.sub_left (sub (o := 1800) (n := 48) (by decide)))
  · have := ht.prf k hk
    rwa [hsR] at this

end VG.Proof.MlKem.AArch64.Kem16P
