module

public import VerifiedGarbage.Proof.Ecdh.AArch64.Main
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.P384.EcdhDouble
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
import VerifiedGarbage.Proof.Ecdh.AArch64.MulJ4
import VerifiedGarbage.Proof.Ecdh.AArch64.WithMul
import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.AbiOnce
public import VerifiedGarbage.Impl.Ecdh.P384.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Main
meta import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
meta import VerifiedGarbage.Proof.Ecdh.AArch64.MulJ4
meta import VerifiedGarbage.Proof.Ecdh.AArch64.WithMul
meta import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Lit
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.AbiOnce
meta import VerifiedGarbage.Impl.Ecdh.P384.AArch64
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
public import VerifiedGarbage.Impl.P384.EcdhMadd
import VerifiedGarbage.Proof.P384.Ops
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
meta import VerifiedGarbage.Impl.P384.EcdhMadd
meta import VerifiedGarbage.Proof.P384.Ops
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Impl.P384.EcdhSelect
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
meta import VerifiedGarbage.Impl.P384.EcdhSelect
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
meta import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
meta import VerifiedGarbage.Proof.Weierstrass.InverseContract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.P384
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.EcKey.P384
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import VerifiedGarbage.Spec.Ecdh.P384
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved

/-! ### `Ecdh.AArch64.P384.Contract`, which only this module used -/

section

/-!
# ECDH over P-384 on AArch64: the contract the proof is written against

The facts of `Spec.Ecdh.P384.exchangeApi`'s contract for AArch64, by name:
`vg_ecdh_p384(out = x0, d = x1, peer = x2, scratch = x3)`, the result in
`w0`.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P384

open VG VG.AArch64 Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.P384.curve (ofBytes (bytesAt m d 48)) (bytesAt m peer 97)

def ecdhAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 48⟩
    let d : Region := ⟨s.gpr .x1, 48⟩
    let peer : Region := ⟨s.gpr .x2, 97⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧
      out.Disjoint peer ∧ d.Disjoint scratch ∧ peer.Disjoint scratch ∧
      (s.gpr .x0).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match ex s.mem (s.gpr .x1) (s.gpr .x2) with
    | some z => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 48 = z
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 48 = List.replicate 48 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 48⟩, ⟨0x3000, 97⟩]
  wr := [⟨0x1000, 48⟩, ⟨0x8000, 8192⟩]

theorem implies :
    ecdhAArch64.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst AArch64.abi) := by
  exact
    { pre := by
        sig_implies_pre [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
        simp only [ecdhAArch64, ex, Spec.P384.curve] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
      sat := by
        sig_implies_sat [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, satState] [satState] using satState }

end VG.Proof.Ecdh.AArch64.P384

end

end

/-! ### `P384.EcdhSelect`, which only this module used -/

section

/-!
# P-384's table entry for ECDH's window, selected by vectors

`sel_ok`: the selection (`Impl/P384/EcdhSelect.lean`) does what the window's
must (`SelOk`). The accumulators hold `(0 : R : 0)` at the start (`start_ok`),
and after `q` entries of the table still do unless the magnitude is among
`1 … q`, when they hold its entry (`entry_ok`, `scan_ok`); so the words stored
are the magnitude's (`words_ok`).
-/

@[expose] public section

namespace VG.Proof.P384.EcdhSelect
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P384.EcdhDouble
open VG.Impl.P384.EcdhSelect
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- The registers of the selection are apart. -/
theorem bank_ok : GOk bank 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Word `j` of `(0 : R : 0)`. -/
def zeroW (j : Nat) : BitVec 64 := if 6 ≤ j ∧ j < 12 then wordOf K.one (j - 6) else 0

/-- What accumulator `i` starts as. -/
def zeroV (i : Nat) : BitVec 128 := ofVDwords (zeroW (2 * i)) (zeroW (2 * i + 1))

theorem vdword_zeroV : ∀ j < 18, vdword (zeroV (j / 2)) (j % 2) = zeroW j := by decide +kernel

/-- The magnitude and `1` in the lanes, and the count zero. -/
theorem count_ok (s : State) : WP isa (.block count) s fun t =>
    t.gpr .x5 = 1 ∧ t.v .v19 = dup2 (s.gpr .x2) ∧ t.v .v28 = dup2 1 ∧ t.v bank.idx = dup2 0 ∧
      VKeep [.x5] [.v19, .v28, bank.idx] s t := by
  apply WP.of_runBlock
  simp only [count, show bank.idx = .v30 from rfl, runBlock_cons, runStep_some, runBlock_nil, exec, reduceVOpEval, Option.map_some,
    show 16 * 0 < Size.x.bits from by decide, RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.gpr_write,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, trivial, by decide, by decide, fun r hr => ?_, rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setV, RegUpd.gpr_write, hr, ite_false]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.v_setV, RegUpd.v_write, hr.1, hr.2.1, hr.2.2, ite_false]

private theorem zero_words :
    ofVDwords ((1 : BitVec 64) - (1 : BitVec 64) <<< 32) ((1 : BitVec 64) <<< 32 - 1) = zeroV 3 ∧
      setLane 0 64 0 (1 : BitVec 64) = zeroV 4 ∧ ∀ i < 9, i ≠ 3 → i ≠ 4 → zeroV i = 0 := by
  decide +kernel

private theorem acc_34 : ∀ i < 9, (acc i = .v3 ↔ i = 3) ∧ (acc i = .v4 ↔ i = 4) ∧ acc i ∈ bank.acc := by
  decide

theorem start_ok {s : State} (h5 : s.gpr .x5 = 1) : WP isa (.block start) s fun t =>
    (∀ i < 9, t.v (acc i) = zeroV i) ∧ VKeep [.x4, .x6] bank.acc s t := by
  rw [start, WP.block_append_iff]
  refine WP.mono (movisV_ok s bank.acc) fun a ⟨z, k⟩ => ?_
  have a5 : a.gpr .x5 = 1 := by rw [k.gpr _ List.not_mem_nil, h5]
  have z3 : a.v .v3 = 0 := z _ (by decide)
  have z4 : a.v .v4 = 0 := z _ (by decide)
  obtain ⟨w3, w4, w0⟩ := zero_words
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, reduceVOpEval, Option.map_some,
    Size.bits, show (32 : Nat) < 64 from by decide, Nat.zero_lt_two, Nat.one_lt_two, RegUpd.v_setV,
    RegUpd.gpr_setV, RegUpd.gpr_write, RegUpd.v_write, BitVec.setWidth_eq, a5, z3, z4, setLane_two, w3, w4,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi => ?_, fun r hr => ?_, k.mem, k.rd, k.wr, k.sp, fun r hr => ?_⟩
  · obtain ⟨e3, e4, hm⟩ := acc_34 i hi
    simp only [e3, e4]
    split
    · rename_i h; rw [h]
    · split
      · rename_i h; rw [h]
      · rename_i h4 h3; rw [z _ hm, w0 i hi h3 h4]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setV, RegUpd.gpr_write, hr.1, hr.2, ite_false]
    exact k.gpr _ List.not_mem_nil
  · have n3 : r ≠ .v3 := fun e => hr (by rw [e]; decide)
    have n4 : r ≠ .v4 := fun e => hr (by rw [e]; decide)
    simp only [RegUpd.v_setV, RegUpd.v_write, n3, n4, ite_false]
    exact k.v _ hr

/-- Pair `i` of entry `m + 1`. -/
abbrev pairAt (s : State) (m i : Nat) : BitVec 128 :=
  s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (K.tbl + 144 * m + 16 * i)) 16

/-- Entry `m + 1`: into the accumulators if it is the magnitude `a`'s. -/
theorem entry_ok {s : State} {base : Addr} {a m : Nat} (hs : Scr s base 8192) (ha : a ≤ 8) (hm : m < 8)
    (hi : s.v bank.idx = dup2 (BitVec.ofNat 64 m)) (h28 : s.v .v28 = dup2 1)
    (h19 : s.v .v19 = dup2 (BitVec.ofNat 64 a)) :
    WP isa (.block (entry m)) s fun t =>
      t.v bank.idx = dup2 (BitVec.ofNat 64 (m + 1)) ∧
      (∀ i < 9, t.v (acc i) = if a = m + 1 then pairAt s m i else s.v (acc i)) ∧
      VKeep [] bank.wr s t := by
  have hG := bank_ok
  have hK : K.tbl = 4240 := by decide
  rw [entry]
  simp only [List.cons_append, List.nil_append]
  refine wp_vop (d := bank.idx) (x := dup2 (BitVec.ofNat 64 (m + 1)))
    (by simp only [reduceVOpEval, hi, h28, map2_dup2, BitVec.ofNat_add]; rfl) ?_
  refine wp_vop (d := bank.mask) (x := if a = m + 1 then BitVec.allOnes 128 else 0)
    (by simp only [reduceVOpEval, RegUpd.v_setV_self,
      RegUpd.v_setV_of_ne _ _ (show VReg.v19 ≠ bank.idx by decide), h19, cmeq_dup2,
      ofNat_eq_iff (a := a) (m := m + 1) (by omega_using [ha]) (by omega_using [hm])]) ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldsV_ok 9 hG (tb := .x0) (o := K.tbl + 144 * m)
    (s := (s.setV bank.idx (dup2 (BitVec.ofNat 64 (m + 1)))).setV bank.mask
      (if a = m + 1 then BitVec.allOnes 128 else 0))
    (by omega_using [hK, hm]) (by omega_using [hK])
    (fun i hi => by
      show InRegions (s.rd ++ s.wr) (s.gpr .x0 + _) 16
      rw [hs.x0]
      exact ⟨_, List.mem_append_right _ hs.wr, hs.contains (by omega_using [hK, hm, hi]) (by decide)⟩)
    9 (Nat.le_refl _)) fun u ⟨l, ku⟩ => ?_
  refine WP.mono (bselsV_ok 9 hG (s := u) 9 (Nat.le_refl _)) fun t ⟨b, kt⟩ => ?_
  have nl : ∀ r, (∀ i < 9, bank.ld.getD i .v20 ≠ r) → r ∉ (List.range 9).map fun i => bank.ld.getD i .v20 :=
    fun _ h => not_mem_map_range h
  have na : ∀ r, (∀ i < 9, bank.acc.getD i .v0 ≠ r) → r ∉ (List.range 9).map fun i => bank.acc.getD i .v0 :=
    fun _ h => not_mem_map_range h
  refine ⟨?_, fun i hi' => ?_, ?_⟩
  · rw [kt.v _ (na _ (by decide)), ku.v _ (nl _ (by decide)),
      RegUpd.v_setV_of_ne _ _ (show bank.idx ≠ bank.mask by decide), RegUpd.v_setV_self]
  · have um : u.v bank.mask = if a = m + 1 then BitVec.allOnes 128 else 0 := by
      rw [ku.v _ (nl _ (by decide)), RegUpd.v_setV_self]
    have ua : u.v (bank.acc.getD i .v0) = s.v (bank.acc.getD i .v0) := by
      rw [ku.v _ (nl _ fun j hj e => hG.acc_ld i hi' j hj e.symm),
        RegUpd.v_setV_of_ne _ _ fun e => hG.acc_o i hi' (by rw [e]; simp),
        RegUpd.v_setV_of_ne _ _ fun e => hG.acc_o i hi' (by rw [e]; simp)]
    have e := b i hi'
    rw [ua, l i hi', um, bit_mask] at e
    exact e
  · have w1 : VKeep [] bank.wr s (s.setV bank.idx (dup2 (BitVec.ofNat 64 (m + 1)))) :=
      VKeep.setV' _ _ (by decide)
    exact ((w1.trans (VKeep.setV' _ _ (by decide))).trans
      (ku.mono (fun _ h => h) (map_range_sub hG.ld_wr))).trans
      (kt.mono (fun _ h => h) (map_range_sub hG.acc_wr))

private theorem acc_wr : ∀ i < 9, acc i ∉ [VReg.v19, .v28, bank.idx] := by decide

/-- Every entry. -/
theorem scan_ok {s : State} {base : Addr} {a : Nat} (hs : Scr s base 8192) (ha : a ≤ 8)
    (hi : s.v bank.idx = dup2 0) (h28 : s.v .v28 = dup2 1) (h19 : s.v .v19 = dup2 (BitVec.ofNat 64 a)) :
    WP isa (.block ((List.range 8).flatMap entry)) s fun t =>
      (∀ i < 9, t.v (acc i) = if a = 0 then s.v (acc i) else pairAt s (a - 1) i) ∧
      VKeep [] bank.wr s t := by
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8)
    (fun q t => t.v bank.idx = dup2 (BitVec.ofNat 64 q) ∧
      (∀ i < 9, t.v (acc i) = if 1 ≤ a ∧ a ≤ q then pairAt s (a - 1) i else s.v (acc i)) ∧
      VKeep [] bank.wr s t) (fun q t hq ⟨ti, ta, k⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨hi, fun i _ => by rw [ite_eq_right (by omega_using [])], VKeep.refl _ _ _⟩) fun t ⟨_, ta, k⟩ => ⟨fun i hi => ?_, k⟩
  · refine WP.mono (entry_ok (hs.of_keeps k.keeps List.not_mem_nil) ha hq ti
      (by rw [k.v _ (by decide), h28]) (by rw [k.v _ (by decide), h19]))
      fun u ⟨ui, ua, ku⟩ => ⟨ui, fun i hi => ?_, k.trans ku⟩
    rw [ua i hi, ta i hi]
    have hp : pairAt t q i = pairAt s q i := by
      show t.mem.read (t.gpr .x0 + _) 16 = _
      rw [k.mem, k.gpr _ List.not_mem_nil]
    by_cases h1 : a = q + 1
    · rw [ite_eq_left h1, ite_eq_left (by omega_using [h1]), hp, show a - 1 = q by omega_using [h1]]
    · rw [ite_eq_right h1]
      by_cases h2 : 1 ≤ a ∧ a ≤ q
      · rw [ite_eq_left h2, ite_eq_left (by omega_using [h2])]
      · rw [ite_eq_right h2, ite_eq_right (by omega_using [h1, h2])]
  · rw [ta i hi]
    by_cases h : a = 0
    · rw [ite_eq_left h, ite_eq_right (by omega_using [h])]
    · rw [ite_eq_right h, ite_eq_left (by omega_using [h, ha])]

private theorem wr_sub : (∀ r ∈ [Reg.x2, .x4, .x16], r ∈ combClob 6) ∧
    (∀ r ∈ [Reg.x2, .x3, .x4, .x9], r ∈ combClob 6) ∧ (∀ r ∈ [Reg.x5], r ∈ combClob 6) ∧
    ∀ r ∈ [Reg.x4, .x6], r ∈ combClob 6 := by decide

/-- `wordsVal_of_shifts`, of a number of at most `k` bits. -/
private theorem wordsVal_of_shifts' {m : Mem} {base : Addr} {o n x k : Nat} (hx : x < 2 ^ k) (hk : k ≤ 64 * n)
    (h : ∀ j < n, word m base (o + 8 * j) = BitVec.ofNat 64 (x >>> (64 * j))) : wordsVal m base o n = x :=
  wordsVal_of_shifts m base o n x (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hk)) h

/-- The coordinates' words at `K.E.x`, from those of `j < 18`. -/
theorem coord_ok {m m' : Mem} {base : Addr} {a : Nat} (c : Nat) (hc : c < 3)
    (h : ∀ j < 18, word m' base (1024 + 8 * j) =
      if a = 0 then zeroW j else word m base (4240 + 144 * (a - 1) + 8 * j)) :
    wordsVal m' base (1024 + 48 * c) 6 =
      if a = 0 then (if c = 1 then K.one else 0) else wordsVal m base (tblSlot K c (a - 1)) 6 := by
  have hj : ∀ j < 6, word m' base (1024 + 48 * c + 8 * j) =
      if a = 0 then zeroW (6 * c + j) else word m base (4240 + 144 * (a - 1) + 48 * c + 8 * j) := by
    intro j hj
    have := h (6 * c + j) (by omega_using [hc, hj])
    rw [show 1024 + 8 * (6 * c + j) = 1024 + 48 * c + 8 * j by omega_using [],
      show 4240 + 144 * (a - 1) + 8 * (6 * c + j) = 4240 + 144 * (a - 1) + 48 * c + 8 * j by omega_using []] at this
    exact this
  by_cases ha : a = 0
  · simp only [ha, ↓reduceIte] at hj ⊢
    have hz : ∀ c < 3, (if c = 1 then K.one else 0) < 2 ^ 129 ∧ ∀ j < 6, zeroW (6 * c + j) =
        BitVec.ofNat 64 ((if c = 1 then K.one else 0) >>> (64 * j)) := by decide +kernel
    exact wordsVal_of_shifts' (hz c hc).1 (by decide)
      fun j h' => by rw [hj j h', (hz c hc).2 j h']
  · simp only [ha, ↓reduceIte] at hj ⊢
    have ht : tblSlot K c (a - 1) = 4240 + 144 * (a - 1) + 48 * c := by
      have h1 : K.tbl = 4240 := by decide
      have h2 : K.M.n = 6 := rfl
      rw [tblSlot, h1, h2]
    rw [ht]
    exact wordsVal_of_words _ _ _ _ _ _ hj

/-- P-384's selection, as the window's. -/
theorem sel_ok : SelOk K 8192 (WinCfg.selOf K (some Impl.P384.EcdhSelect.sel)) := by
  intro base k i s hL hA hs hi hx hbits
  have hmag := mag_le (nib_lt k i)
  have hKs : K.tbl = 4240 ∧ K.E.x = 1024 ∧ K.E.y = 1072 ∧ K.E.z = 1120 ∧ K.M.n = 6 := by decide
  obtain ⟨hKt, hKx, hKy, hKz, hKn⟩ := hKs
  obtain ⟨c1, c2, c3, c4⟩ := wr_sub
  show WP isa (.block Impl.P384.EcdhSelect.sel) s _
  rw [Impl.P384.EcdhSelect.sel, WP.block_append_iff]
  refine WP.mono (nibble_ok hs K.bits (k := k) (j := i) (N := 4 * K.J) (by omega_using [hi]) hL.bits hA.bits4 hx
    hbits) fun s₁ ⟨x₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (magnitude_ok s₁ (nib_lt k i) x₁) fun s₂ ⟨x₂, _, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (count_ok s₂) fun s₃ ⟨x₃, a₃, b₃, i₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (start_ok x₃) fun s₄ ⟨z₄, k₄⟩ => ?_
  have K₄ : Keeps (combClob 6) s s₄ := (((k₁.mono c1).trans (k₂.mono c2)).trans
    (k₃.keeps.mono c3)).trans (k₄.keeps.mono c4)
  have hx0 : Reg.x0 ∉ combClob 6 := by decide
  have hs₄ := hs.of_keeps K₄ hx0
  rw [WP.block_append_iff]
  refine WP.mono (scan_ok hs₄ hmag (by rw [k₄.v _ (by decide), i₃]) (by rw [k₄.v _ (by decide), b₃])
    (by rw [k₄.v _ (by decide), a₃, x₂])) fun s₅ ⟨v₅, k₅⟩ => ?_
  have K₅ := K₄.trans (k₅.keeps.mono fun _ h => absurd h List.not_mem_nil)
  refine WP.mono (qstoresV_ok acc (o := K.E.x) (hs.of_keeps K₅ hx0) (by rw [hKx]) 9
    (by rw [hKx]; decide)) fun t ⟨w, kt, _, O⟩ => ?_
  have hw : ∀ j < 18, word t.mem base (1024 + 8 * j) = if mag (nib k i) = 0 then zeroW j else
      word s.mem base (4240 + 144 * (mag (nib k i) - 1) + 8 * j) := by
    intro j hj
    have e := w j hj
    rw [hKx] at e
    rw [e, v₅ _ (by omega_using [hj])]
    by_cases h : mag (nib k i) = 0
    · rw [ite_eq_left h, ite_eq_left h, z₄ _ (by omega_using [hj]), vdword_zeroV j hj]
    · rw [ite_eq_right h, ite_eq_right h, pairAt, vdword_read16 _ _ (by omega_using []), hs₄.x0, K₄.mem,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat, hKt]
      exact congrArg (word s.mem base) (by omega_using [])
  have hc := fun c hc => coord_ok c hc hw
  have KR : KeepRegs (combClob 6) s t := (Keeps.regs K₅).trans (kt.mono fun _ h => absurd h List.not_mem_nil)
  refine ⟨KR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact KR.gpr _ hx0
  · rw [kt.gpr _ List.not_mem_nil, k₅.gpr _ List.not_mem_nil, k₄.gpr _ (by decide), k₃.gpr _ (by decide),
      k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  · rw [← K₅.mem]
    refine fun x hx => O x ?_
    rw [hKn, hKx, hKy, hKz] at hx
    have h1 := hx (1024, 48) (by decide)
    have h2 := hx (1072, 48) (by decide)
    have h3 := hx (1120, 48) (by decide)
    rw [hKx]
    omega_using [h1, h2, h3]
  · have := hc 0 (by decide)
    rw [hKx, hKn]; exact this
  · have := hc 1 (by decide)
    rw [hKy, hKn]; exact this
  · have := hc 2 (by decide)
    rw [hKz, hKn]; exact this

end VG.Proof.P384.EcdhSelect

end

end

/-! ### `P384.EcdhMadd`, which only this module used -/

section

/-!
# P-384's inline mixed addition

`madd_ok`: the inline mixed addition (`Impl/P384/EcdhMadd.lean`) does what
the window's must (`MaddSpec`), as `ofN_ok` shows of the field program's: its
operations are `fprog_ok`'s, on the slots the field program uses.
-/

@[expose] public section

-- Powers of two up to `2^384` are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.P384.EcdhMadd
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P384.EcdhDouble
open VG.Impl.P384.EcdhMadd
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.P384.Ops (clobX ProgKeepX)
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open Spec.Weierstrass

/-- The inline mixed addition, as the window's. -/
theorem madd_ok {C : Curve} (hC : C.p = p384) {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) : MaddSpec K C base size (.block madd) := by
  intro E s hI
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oE := pt_other (K := K) (p := K.E) (Or.inr (Or.inl rfl))
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  have sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    List.mem_append_right (winRo K) (h x hx)
  have w1 := winJ_sl oD (sl _ oR) (sl _ oE)
  have hAp := hL.rcbApart_D (Or.inr rfl)
  rw [madd, maddJ_eq]
  refine WP.mono (Ops.fprog_ok hC hL.lay hA.al hp _ hI (fun op hop x hx => w1.1 x (ofN_slots op hop x hx))
    (readsOk_mono (ofN_readsOk maddJN_ok _ _ _ _) fun x hx => hx)) fun s' ⟨k, I⟩ => ?_
  have hw : ∀ w ∈ (ofN maddJN K.S K.R K.E K.D).map FOp.out, w ∈ rcbW K.S K.D := fun w hw => by
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out maddJN_ok op hop
  refine ⟨⟨fun r hr => k.gpr r fun h => hr (by
      have : ∀ r ∈ clobX, r ∈ clob K.M.n ++ winSaved K.M.n := by decide
      exact this r h), k.rd, k.wr, k.sp⟩,
    (ProgKeepX.mono k hw).unch.mono fun w hw => ?_, _, I.sub fun x hx => ?_,
    fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ ofN_out maddJN_ok op hop),
    (congrArg₂ Prod.mk (ofN_run maddJN_ok hAp E 6)
      (congrArg₂ Prod.mk (ofN_run maddJN_ok hAp E 7) (ofN_run maddJN_ok hAp E 8))).trans (maddJN_run _)⟩
  · simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact Or.inl ⟨y, w1.2.1 y hy, rfl⟩
    · exact Or.inr rfl
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem maddJN_ok hx)
    · exact Or.inl hx

/-- P-384's inline mixed addition, as the window's. -/
theorem maddOk {C : Curve} (hC : C.p = p384) (hL : WinLay K 8192) (hA : WinA K)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (base : Addr) : MaddOk K C base 8192 (some (.block madd)) := by
  intro m hm
  cases hm
  exact madd_ok hC hL hA hp

end VG.Proof.P384.EcdhMadd

end

end

/-!
# ECDH over P-384 on AArch64: `Verified`

P-384 is a curve the proof supports (`p384_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P384.law` and `invSound_of_toM`), and of prime order
(`Proof.P384.primeOrder`), so the windows with a Jacobian accumulator compute `[d]P` (`mulJ4_ok`) and
`exchangeWith_ok'` gives the contract's postcondition; `x19`–`x25` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter,
so not even the peer's key (which the contract would let leak) affects timing.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P384

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P384

theorem pre_of {s : State} (h : ecdhAArch64.pre s) : EPre p384 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost p384 s s') : ecdhAArch64.post s s' := by
  unfold EPost at h
  dsimp only [ecdhAArch64]
  revert h
  generalize hq : ex s.mem (s.gpr .x1) (s.gpr .x2) = q
  rw [show Spec.Ecdh.exchange p384.C (dk p384 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1 + 2 * p384.C.len)) = ex s.mem (s.gpr .x1) (s.gpr .x2) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_a64 (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) (s : State) (hs : ecdhAArch64.pre s) :
    ∃ t s', Exec isa exchangeP384 s t s' ∧ abiPreserved s s' ∧ ecdhAArch64.post s s' := by
  -- In steps: elaborated in one term, the unifier would compare P-384's
  -- terms before the literals' facts are known.
  have ha : AbiOk exchangeP384 := by lit_decide
  have hmc : CallsKeep (Impl.Ecdh.AArch64.Cfg.middle p384) :=
    callsKeep_ofK (c := Impl.Ecdh.AArch64.Cfg.middle p384) (by lit_decide)
  have hmu : KeepsUntouched (Impl.Ecdh.AArch64.Cfg.middle p384) :=
    keepsUntouched_ofK (c := Impl.Ecdh.AArch64.Cfg.middle p384) (by lit_decide)
  have hm : Ecdh.AArch64.MulOk p384 (Cfg.mulJ4 p384
      (some (Impl.P384.EcdhDouble.callRD, Impl.P384.EcdhDouble.callDR))
      (some (.block Impl.P384.EcdhMadd.madd)) (some Impl.P384.EcdhSelect.sel)) :=
    Ecdh.AArch64.mulJ4_ok (p384_ok hI) hL hO rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (P384.EcdhDouble.dblsOk P384.EcdhDouble.p384_C_p (Ecdh.AArch64.winLayQ (p384_ok hI)) (Ecdh.AArch64.winAQ (p384_ok hI))
        (Weierstrass.unitMod_pow_two (p384_ok hI).p_odd _))
      (P384.EcdhMadd.maddOk P384.EcdhDouble.p384_C_p (Ecdh.AArch64.winLayQ (p384_ok hI))
        (Ecdh.AArch64.winAQ (p384_ok hI)) (Weierstrass.unitMod_pow_two (p384_ok hI).p_odd _))
      P384.EcdhSelect.sel_ok
  obtain ⟨t, s', he, hsv, -, hpost⟩ :=
    Ecdh.AArch64.exchangeWith_ok' (p384_ok hI) hL hm (by decide +kernel) hmc hmu (pre_of hs)
  exact ⟨t, s', he, abiPreserved_ofK he ha hsv, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhAArch64.pre ecdhAArch64.pub exchangeP384 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩) (by taint_decide)

theorem ecdh_verified (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) :
    Verified AArch64.target exchangeP384
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst AArch64.abi) :=
  Verified.of_correct (ecdh_a64 hL hI hO) ecdh_ct implies


/-- ECDH over P-384 as it is emitted, its cleanup included
(`Impl.Ecdh.AArch64.Fn.exchangeP384`), meets its contract in constant time and
returns without secret residue. -/
theorem exchange_scrubbed (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) :
    VerifiedScrubbed AArch64.target VG.Impl.Ecdh.AArch64.Fn.exchangeP384
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst AArch64.abi) 32 :=
  VG.AArch64.Scrub.verifiedScrubbedAll (api := Spec.Ecdh.P384.exchangeApi)
    { code := exchangeP384, verified := ecdh_verified hL hI hO } _
    (VG.Proof.EcKey.AArch64.Scrub.exchangeOk _) (by dsimp only; lit_decide)

end VG.Proof.Ecdh.AArch64.P384
