import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Backend
import VerifiedGarbage.Impl.Argon2.AArch64.HPrime
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Spec.Argon2
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Copy`. -/
section

/-! # H′: copying digest bytes -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem copyByte_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x2) 1)
    (hw : InRegions s.wr (s.gpr .x22) 1) :
    WP isa (.block copyByte) s fun t =>
      t.mem = s.mem.writeW (s.gpr .x22) (s.mem (s.gpr .x2)) ∧
      t.gpr .x2 = s.gpr .x2 + 1 ∧ t.gpr .x22 = s.gpr .x22 + 1 ∧
      t.gpr .x8 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x8 → r ≠ .x3 → r ≠ .x2 → r ≠ .x22 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [copyByte, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, show (0 : Nat) % 1 = 0 ∧ 0 < 4096 * 1 from by decide,
    show (1 : Nat) < 4096 from by decide, Size.bits, BitVec.add_zero, State.load, State.store, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hr, hw, and_self, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left',
    BitVec.setWidth_eq]
  refine ⟨?_, rfl, rfl, rfl,
    fun r h1 h2 h3 h4 => by simp only [h1, h2, h3, h4, ite_false], trivial⟩
  unfold Mem.writeW
  congr 1
  ext i hi
  simp [VG.Proof.MdStream.AArch64.read_one]

open VG.WriteBytes
open VG.Spec.Blake2 (bytesAt)

/-- The prefix already copied, with every other register preserved. -/
structure CopyI (s₀ : State) (src dst : Addr) (k j : Nat) (s : State) : Prop where
  bound : j ≤ k
  source : s.gpr .x2 = src + BitVec.ofNat 64 j
  destination : s.gpr .x22 = dst + BitVec.ofNat 64 j
  count : s.gpr .x8 = BitVec.ofNat 64 (k - j)
  other : ∀ r, r ≠ .x8 → r ≠ .x3 → r ≠ .x2 → r ≠ .x22 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.WriteBytes.writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)

theorem copyLoop_ok (s₀ : State) (src dst : Addr) (k : Nat)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 64)
    (hs : s₀.gpr .x2 = src) (hd : s₀.gpr .x22 = dst)
    (hn : s₀.gpr .x8 = BitVec.ofNat 64 k)
    (hr : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < k, InRegions s₀.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : Region.Disjoint ⟨src, k⟩ ⟨dst, k⟩) :
    WP isa (.loop (.block copyByte) (.nonzero .x .x8)) s₀ (VG.Proof.Argon2.AArch64.HPrime.CopyI s₀ src dst k k) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = k - j ∧ j < k ∧ VG.Proof.Argon2.AArch64.HPrime.CopyI s₀ src dst k j s)
    ?_ k s₀ ⟨0, by omega, hk, by omega, by simpa using hs, by simpa using hd,
      by simpa using hn, fun _ _ _ _ _ => rfl, rfl, rfl, by rw [List.take_zero, VG.WriteBytes.writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hlen : (bytesAt s₀.mem src k).length = k := by simp [bytesAt]
  have htake : ((bytesAt s₀.mem src k).take j).length = j := by
    rw [List.length_take, hlen, Nat.min_eq_left (by omega)]
  have hb : s.mem (src + BitVec.ofNat 64 j) = s₀.mem (src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    apply (VG.WriteBytes.writeBytes_frame s₀.mem dst _ (R := ⟨dst, k⟩)
      (by simpa only [BitVec.add_zero, htake] using
        (Offset.contains_base dst (k := k) (d := 0) (n := j) (by omega) (by decide)))).bytes
        (R := ⟨src, k⟩) _ (show k ≤ 2 ^ 64 by omega) hj
    simpa using hsep
  have hr' : InRegions (s.rd ++ s.wr) (s.gpr .x2) 1 := by
    rw [h.rd, h.wr, h.source]; exact hr j hj
  have hw' : InRegions s.wr (s.gpr .x22) 1 := by
    rw [h.wr, h.destination]; exact hw j hj
  refine (VG.Proof.Argon2.AArch64.HPrime.copyByte_ok s hr' hw').mono ?_
  rintro t ⟨hm, hs', hd', hn', ho, hrd, hwr⟩
  have hc : BitVec.ofNat 64 (k - j) - 1 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega : 1 ≤ k - j)]
    congr 1
  have hi : VG.Proof.Argon2.AArch64.HPrime.CopyI s₀ src dst k (j + 1) t := by
    refine ⟨by omega, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, hrd.trans h.rd, hwr.trans h.wr, ?_⟩
    · rw [hs', h.source, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hd', h.destination, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hn', h.count, hc]
    · exact (ho r h1 h2 h3 h4).trans (h.other r h1 h2 h3 h4)
    · have hj' : j < (bytesAt s₀.mem src k).length := by omega
      rw [hm, h.source, h.destination, hb, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [htake]; omega), htake]
      refine congrArg (fun b => (VG.WriteBytes.writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)).writeW
        (dst + BitVec.ofNat 64 j) b) ?_
      simp only [bytesAt, List.getElem_map, List.getElem_range]
  have hz' : (t.gpr .x8 == 0) = decide (k - (j + 1) = 0) := by
    rw [hi.count]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have ht := congrArg BitVec.toNat he
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k - (j + 1) < 2 ^ 64),
        show (0 : BitVec 64).toNat = 0 from rfl] using ht
    · intro he; rw [he]; rfl
  by_cases he : j + 1 = k
  · refine .inl ⟨?_, he ▸ hi⟩
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, bne, hz', show k - (j + 1) = 0 by omega, decide_true, Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega, j + 1, rfl, by omega, hi⟩
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, bne, hz', show k - (j + 1) ≠ 0 by omega, decide_false, Bool.not_false]

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Init`. -/
section

/-! # H′: initializing an unkeyed BLAKE2b computation -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure InitArgs (s t : State) : Prop where
  state : t.gpr .x0 = s.gpr .x24
  key : t.gpr .x2 = s.gpr .x24 + 832
  keylen : t.gpr .x3 = 0
  other : ∀ r, r ≠ .x0 → r ≠ .x2 → r ≠ .x3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem initArgs_ok (s : State) : WP isa (.block initArgs) s (VG.Proof.Argon2.AArch64.HPrime.InitArgs s) := by
  apply WP.of_runBlock
  simp only [initArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    show (0 : Nat) < 4096 from by decide, show (832 : Nat) < 4096 from by decide,
    show (16 * 0 : Nat) < 64 from by decide, State.read, Size.bits,
    BitVec.setWidth_eq, BitVec.add_zero,
    ite_true, ite_false, reduceCtorEq, RegUpd.gpr_write, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]

/-- Narrow the callee's permissions to its state and empty key. -/
theorem init_call_hyps (s u : State) (hu : VG.Proof.Argon2.AArch64.HPrime.InitArgs s u)
    (hlen : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr) :
    (Proof.Blake2.initAArch64 Spec.Blake2.b).pre
      (u.callEntry.withRegions [⟨s.gpr .x24 + 832, 0⟩] [⟨s.gpr .x24, 192⟩]) ∧
    Covers [⟨s.gpr .x24 + 832, 0⟩, ⟨s.gpr .x24, 192⟩] (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .x24, 192⟩] u.wr := by
  have hlen' : u.gpr .x1 = s.gpr .x1 := hu.other _ (by decide) (by decide) (by decide)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun _ hr => State.callEntry_gpr u hr
  have hp : (Proof.Blake2.initAArch64 Spec.Blake2.b).pre
      (u.callEntry.withRegions [⟨s.gpr .x24 + 832, 0⟩] [⟨s.gpr .x24, 192⟩]) := by
    simp only [Proof.Blake2.initAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g .x0 (by decide), g .x2 (by decide), g .x3 (by decide),
      g .x1 (by decide), hu.state, hu.key, hu.keylen, hlen']
    refine ⟨rfl, rfl, ?_, hlen.1, hlen.2, by decide⟩
    exact (Offset.base_disjoint (s.gpr .x24) (e := 832) (n := 0) (k := 192) (by decide) (by decide)).symm
  have cover : Covers [⟨s.gpr .x24 + 832, 0⟩, ⟨s.gpr .x24, 192⟩] (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .x24, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), ?_⟩
    rcases hr with rfl | rfl
    · exact ⟨832, rfl, by change 832 ≤ 16384; decide⟩
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
  have writes : Covers [⟨s.gpr .x24, 192⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨s.gpr .x24, 16384⟩, hu.wr.symm ▸ hwr, 0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
  exact ⟨hp, cover, writes⟩

theorem init_ok (v : Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr) :
    WP isa (init v.hash) s fun t =>
      Spec.Blake2.Repr Spec.Blake2.b (Spec.Blake2.init Spec.Blake2.b (s.gpr .x1).toNat 0)
        t.mem (s.gpr .x24) [] ∧
      (∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ Frame [⟨s.gpr .x24, 192⟩] s.mem t.mem := by
  unfold init
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.initArgs_ok s).mono fun u hu => ?_)
  have hlen' : u.gpr .x1 = s.gpr .x1 := hu.other _ (by decide) (by decide) (by decide)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun _ hr => State.callEntry_gpr u hr
  obtain ⟨hp, cover, writes⟩ := VG.Proof.Argon2.AArch64.HPrime.init_call_hyps s u hu hlen hwr
  refine WP.call (k := Proof.Blake2.initAArch64 Spec.Blake2.b)
    v.initCorrect hp cover writes ?_ v.ok.initNoFrames
  intro t rd wr sp frame cs keep post
  have post' := post
  simp only [Proof.Blake2.initAArch64, State.withRegions_gpr, State.withRegions_mem,
    g .x0 (by decide), g .x1 (by decide), g .x2 (by decide), g .x3 (by decide),
    hu.state, hu.key, hu.keylen, hlen', Spec.Blake2.bytesAt, Spec.Blake2.keyBlock] at post'
  refine ⟨post', fun r hr h30 => (cs r hr h30).trans ?_, rd.trans hu.rd, wr.trans hu.wr,
    sp.trans hu.sp, ?_⟩
  · have hn : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · simpa only [hu.mem] using frame

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Update`. -/
section

/-! # H′: absorbing bytes with the selected BLAKE2b backend -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

structure UpdateArgs (s t : State) : Prop where
  state : t.gpr .x0 = s.gpr .x24
  scratch : t.gpr .x4 = s.gpr .x24 + 192
  other : ∀ r, r ≠ .x0 → r ≠ .x4 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem updateArgs_ok (s : State) : WP isa (.block updateArgs) s (VG.Proof.Argon2.AArch64.HPrime.UpdateArgs s) := by
  apply WP.of_runBlock
  simp only [updateArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    show (0 : Nat) < 4096 from by decide, show (192 : Nat) < 4096 from by decide,
    State.read, Size.bits, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write, h1, h2, ite_false]

/-- The narrowed streaming call, without assumptions about message contents. -/
theorem update_call_hyps (s u : State) (hu : VG.Proof.Argon2.AArch64.HPrime.UpdateArgs s u)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] (s.rd ++ s.wr))
    (dataState : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 192⟩)
    (dataScratch : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x24 + 192, 576⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackData : (below s.sp 16).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩) :
    (Proof.Blake2.updateAArch64 b).pre (u.callEntry.withRegions
      [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩]) ∧
    Covers ([⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ++
      [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩] u.wr := by
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp := hu.sp
  have src : u.gpr .x2 = s.gpr .x2 := hu.other _ (by decide) (by decide)
  have len : u.gpr .x3 = s.gpr .x3 := hu.other _ (by decide) (by decide)
  have subState : Region.Sub ⟨s.gpr .x24, 192⟩ ⟨s.gpr .x24, 16384⟩ := Region.sub_prefix (by decide)
  have subScratch : Region.Sub ⟨s.gpr .x24 + 192, 576⟩ ⟨s.gpr .x24, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have hp : (Proof.Blake2.updateAArch64 b).pre (u.callEntry.withRegions
      [⟨s.gpr .x2, (s.gpr .x3).toNat⟩]
      [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩]) := by
    simp only [Proof.Blake2.updateAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g .x0 (by decide), g .x2 (by decide),
      g .x3 (by decide), g .x4 (by decide), State.callEntry_sp, State.withRegions_sp,
      hu.state, hu.scratch, src, len, sp]
    exact ⟨trivial, rfl, Offset.base_disjoint _ (by decide) (by decide), dataState, dataScratch,
      hsp, stackWork.sub_right subState, stackData, stackWork.sub_right subScratch⟩
  have writes : Covers [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .x24, 16384⟩, hu.wr.symm ▸ hwr, ?_⟩
    rcases hr with rfl | rfl
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
    · exact ⟨192, rfl, by change 192 + 576 ≤ 16384; decide⟩
  have cover : Covers ([⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ++
      [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩]) (u.rd ++ u.wr) := by
    intro a n ⟨r, hr, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · rw [hu.rd, hu.wr]; exact hdata a n ⟨r, hr, hc⟩
    · obtain ⟨r', hr', hc'⟩ := writes a n ⟨r, hr, hc⟩
      exact ⟨r', List.mem_append_right _ hr', hc'⟩
  exact ⟨hp, cover, writes⟩

theorem update_ok (v : Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .x24) d)
    (count : s.gpr .x1 = BitVec.ofNat 64 d.length)
    (bound : d.length + (s.gpr .x3).toNat < 2 ^ 64)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] (s.rd ++ s.wr))
    (dataState : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 192⟩)
    (dataScratch : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x24 + 192, 576⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackData : (below s.sp 16).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩) :
    WP isa (update v.hash) s fun t =>
      Repr b h0 t.mem (s.gpr .x24) (d ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ∧
      (∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 192, 576⟩, below s.sp 16] s.mem t.mem := by
  unfold update
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.updateArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp := hu.sp
  have src : u.gpr .x2 = s.gpr .x2 := hu.other _ (by decide) (by decide)
  have len : u.gpr .x3 = s.gpr .x3 := hu.other _ (by decide) (by decide)
  have cnt : u.gpr .x1 = s.gpr .x1 := hu.other _ (by decide) (by decide)
  obtain ⟨hp, cover, writes⟩ := VG.Proof.Argon2.AArch64.HPrime.update_call_hyps s u hu hsp hwr hdata dataState dataScratch stackWork stackData
  have repr' : Repr b h0 u.callEntry.mem (s.gpr .x24) d := by
    simpa only [State.callEntry_mem, hu.mem] using repr
  have bytes : bytesAt u.callEntry.mem (s.gpr .x2) (s.gpr .x3).toNat =
      bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat := by
    rw [State.callEntry_mem, hu.mem]
  refine WP.callF (k := Proof.Blake2.updateAArch64 b) v.updateCorrect hp cover writes ?_
    (by rw [v.ok.updateDepth]; decide)
  intro t rd wr sp' frame cs post
  simp only [Proof.Blake2.updateAArch64, State.withRegions_gpr, State.withRegions_mem,
    g .x0 (by decide), g .x1 (by decide),
    g .x2 (by decide), g .x3 (by decide),
    hu.state, src, len, cnt] at post
  have result := post h0 d repr' count bound
  rw [bytes] at result
  refine ⟨result, fun r hr h30 => (cs r hr h30).trans ?_, rd.trans hu.rd, wr.trans hu.wr, sp'.trans hu.sp, ?_⟩
  · have hn : r ≠ .x0 ∧ r ≠ .x4 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2
  · simpa only [v.ok.updateDepth, sp, hu.mem, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Finalize`. -/
section

/-! # H′: finishing a BLAKE2b hash -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

structure FinalizeArgs (s t : State) : Prop where
  state : t.gpr .x0 = s.gpr .x24
  digest : t.gpr .x2 = s.gpr .x24 + 768
  scratch : t.gpr .x3 = s.gpr .x24 + 192
  other : ∀ r, r ≠ .x0 → r ≠ .x2 → r ≠ .x3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem finalizeArgs_ok (s : State) : WP isa (.block finalizeArgs) s (VG.Proof.Argon2.AArch64.HPrime.FinalizeArgs s) := by
  apply WP.of_runBlock
  simp only [finalizeArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    show (0 : Nat) < 4096 from by decide, show (192 : Nat) < 4096 from by decide,
    show (768 : Nat) < 4096 from by decide,
    State.read, Size.bits, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]

/-- The narrowed finalization call, independently of the represented message. -/
theorem finalize_call_hyps (s u : State) (hu : VG.Proof.Argon2.AArch64.HPrime.FinalizeArgs s u)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    (Proof.Blake2.finalizeAArch64 b).pre (u.callEntry.withRegions []
      [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩, ⟨s.gpr .x24 + 192, 576⟩]) ∧
    Covers ([] ++ [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩,
      ⟨s.gpr .x24 + 192, 576⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩, ⟨s.gpr .x24 + 192, 576⟩] u.wr := by
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp := hu.sp
  have subState : Region.Sub ⟨s.gpr .x24, 192⟩ ⟨s.gpr .x24, 16384⟩ := Region.sub_prefix (by decide)
  have subDigest : Region.Sub ⟨s.gpr .x24 + 768, 64⟩ ⟨s.gpr .x24, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have subScratch : Region.Sub ⟨s.gpr .x24 + 192, 576⟩ ⟨s.gpr .x24, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have hp : (Proof.Blake2.finalizeAArch64 b).pre (u.callEntry.withRegions []
      [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩, ⟨s.gpr .x24 + 192, 576⟩]) := by
    simp only [Proof.Blake2.finalizeAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g .x0 (by decide), g .x2 (by decide),
      g .x3 (by decide), State.callEntry_sp, State.withRegions_sp, hu.state, hu.digest, hu.scratch, sp]
    exact ⟨trivial, rfl, Offset.base_disjoint _ (by decide) (by decide),
      Offset.base_disjoint _ (by decide) (by decide), (Offset.disjoint _ (by decide) (by decide) (by decide)).symm,
      hsp, stackWork.sub_right subState, stackWork.sub_right subDigest,
      stackWork.sub_right subScratch⟩
  have writes : Covers [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩, ⟨s.gpr .x24 + 192, 576⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .x24, 16384⟩, hu.wr.symm ▸ hwr, ?_⟩
    rcases hr with rfl | rfl | rfl
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
    · exact ⟨768, rfl, by change 768 + 64 ≤ 16384; decide⟩
    · exact ⟨192, rfl, by change 192 + 576 ≤ 16384; decide⟩
  have cover : Covers ([] ++ [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩,
      ⟨s.gpr .x24 + 192, 576⟩]) (u.rd ++ u.wr) := by
    intro a n h
    obtain ⟨r, hr, hc⟩ := writes a n h
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  exact ⟨hp, cover, writes⟩

theorem finalize_ok (v : Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .x24) d)
    (count : s.gpr .x1 = BitVec.ofNat 64 d.length) (bound : d.length < 2 ^ 64)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (finalize v.hash) s fun t =>
      bytesAt t.mem (s.gpr .x24 + 768) 64 = Spec.Blake2.finalHash b h0 d ∧
      (∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨s.gpr .x24, 192⟩, ⟨s.gpr .x24 + 768, 64⟩,
        ⟨s.gpr .x24 + 192, 576⟩, below s.sp 16] s.mem t.mem := by
  unfold finalize
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.finalizeArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp := hu.sp
  have cnt : u.gpr .x1 = s.gpr .x1 := hu.other _ (by decide) (by decide) (by decide)
  obtain ⟨hp, cover, writes⟩ := VG.Proof.Argon2.AArch64.HPrime.finalize_call_hyps s u hu hsp hwr stackWork
  have repr' : Repr b h0 u.callEntry.mem (s.gpr .x24) d := by
    simpa only [State.callEntry_mem, hu.mem] using repr
  refine WP.callF (k := Proof.Blake2.finalizeAArch64 b) v.finalizeCorrect hp cover writes ?_
    (by rw [v.ok.finalizeDepth]; decide)
  intro t rd wr sp' frame cs post
  simp only [Proof.Blake2.finalizeAArch64, State.withRegions_gpr, State.withRegions_mem,
    g .x0 (by decide), g .x1 (by decide),
    g .x2 (by decide), hu.state, hu.digest, cnt] at post
  refine ⟨post h0 d repr' bound count, fun r hr h30 => (cs r hr h30).trans ?_, rd.trans hu.rd, wr.trans hu.wr, sp'.trans hu.sp, ?_⟩
  · have hn : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · simpa only [v.ok.finalizeDepth, sp, hu.mem, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Fixed`. -/
section

/-! # H′: arguments for a fixed workspace buffer -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure FixedArgs (s t : State) (offset size : Nat) : Prop where
  count : t.gpr .x1 = 0
  data : t.gpr .x2 = s.gpr .x24 + BitVec.ofNat 64 offset
  size : t.gpr .x3 = BitVec.ofNat 64 size
  other : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem fixedArgs_ok (s : State) (offset size : Nat) (ho : offset < 4096) (hn : size < 2 ^ 16) :
    WP isa (.block (fixedArgs offset size)) s fun t => VG.Proof.Argon2.AArch64.HPrime.FixedArgs s t offset size := by
  have hsize : (BitVec.ofNat 16 size).setWidth 64 = BitVec.ofNat 64 size := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (by omega : size < 2 ^ 64)]
  apply WP.of_runBlock
  simp only [fixedArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    show (0 : Nat) < 4096 from by decide, show (16 * 0 : Nat) < 64 from by decide,
    ho, State.read, Size.bits, Nat.mul_zero, BitVec.setWidth_eq, BitVec.shiftLeft_zero, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  · exact hsize
  · simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Frame`. -/
section

/-! # H′: the memory changed by hashing a workspace buffer -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64

/-- Join the hash's individual writable buffers into its first 832 bytes. -/
theorem workspace_frame {m m' : Mem} (p sp : Addr) (rs : List (Nat × Nat)) (stack : Nat)
    (bounds : ∀ r ∈ rs, r.1 + r.2 ≤ 832) (depth : stack ≤ 16)
    (h : Frame (rs.map (fun r => ⟨p + BitVec.ofNat 64 r.1, r.2⟩) ++ [below sp stack]) m m') :
    Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply h.sub
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact ⟨_, List.mem_cons_self .., Offset.sub_base p (bounds q hq)⟩
  · simp only [List.mem_singleton] at hr; subst r
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), below_sub depth (by decide)⟩

theorem init_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩] m m') : Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply h.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨p, 832⟩, List.mem_cons_self .., Region.sub_prefix (by decide)⟩

theorem update_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩, ⟨p + 192, 576⟩, below sp 16] m m') :
    Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply VG.Proof.Argon2.AArch64.HPrime.workspace_frame p sp [(0, 192), (192, 576)] 16 (by decide) (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.add_zero,
    show BitVec.ofNat 64 192 = (192 : Addr) from rfl] using h

theorem finalize_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩, ⟨p + 768, 64⟩, ⟨p + 192, 576⟩, below sp 16] m m') :
    Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply VG.Proof.Argon2.AArch64.HPrime.workspace_frame p sp [(0, 192), (768, 64), (192, 576)] 16 (by decide) (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.add_zero,
    show BitVec.ofNat 64 192 = (192 : Addr) from rfl,
    show BitVec.ofNat 64 768 = (768 : Addr) from rfl] using h

/-- The caller's registers and permissions, and its saved registers above
832, survive every hash operation. -/
structure Keeps (s t : State) : Prop where
  regs : ∀ r ∈ preserved, r ≠ .x30 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16] s.mem t.mem

theorem Keeps.x24 {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.Keeps s t) : t.gpr .x24 = s.gpr .x24 :=
  h.regs _ (by decide) (by decide)

theorem Keeps.trans {s t u : State} (h : VG.Proof.Argon2.AArch64.HPrime.Keeps s t) (h' : VG.Proof.Argon2.AArch64.HPrime.Keeps t u) : VG.Proof.Argon2.AArch64.HPrime.Keeps s u where
  regs r hr h30 := (h'.regs r hr h30).trans (h.regs r hr h30)
  rd := h'.rd.trans h.rd
  wr := h'.wr.trans h.wr
  sp := h'.sp.trans h.sp
  frame := h.frame.trans (by simpa only [h.x24, h.sp] using h'.frame)

theorem Keeps.bytes {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.Keeps s t) (r : Region) (bound : r.len ≤ 2 ^ 64)
    (work : r.Disjoint ⟨s.gpr .x24, 832⟩) (stack : r.Disjoint (below s.sp 16)) :
    Spec.Blake2.bytesAt t.mem r.base r.len = Spec.Blake2.bytesAt s.mem r.base r.len := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := r) _ bound hi
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact work
  · exact stack

theorem Keeps.prefix {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.Keeps s t)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    Spec.Blake2.bytesAt t.mem (s.gpr .x24 + 832) 4 =
      Spec.Blake2.bytesAt s.mem (s.gpr .x24 + 832) 4 :=
  h.bytes ⟨s.gpr .x24 + 832, 4⟩ (show 4 ≤ 2 ^ 64 by decide)
    (Offset.base_disjoint _ (e := 832) (n := 4) (k := 832) (by decide) (by decide)).symm
    (stackWork.sub_right (Offset.sub_base _ (by decide : 832 + 4 ≤ 16384))).symm

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Absorb`. -/
section

/-! # H′: absorbing the length prefix or previous digest -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem absorbFixed_ok (v : Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (offset size : Nat)
    (offsetUpper : offset < 4096)
    (hsp : 16 ≤ s.sp.toNat)
    (offsetLower : 768 ≤ offset) (sizeBound : offset + size ≤ 16384)
    (repr : Repr b h0 s.mem (s.gpr .x24) [])
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (absorbFixed v.hash offset size) s fun t =>
      Repr b h0 t.mem (s.gpr .x24) (bytesAt s.mem (s.gpr .x24 + BitVec.ofNat 64 offset) size) ∧
      VG.Proof.Argon2.AArch64.HPrime.Keeps s t := by
  unfold absorbFixed
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.fixedArgs_ok s offset size offsetUpper (by omega)).mono fun u hu => ?_)
  have p : u.gpr .x24 = s.gpr .x24 := hu.other _ (by decide) (by decide) (by decide)
  have sp := hu.sp
  have len : (u.gpr .x3).toNat = size := by
    rw [hu.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have wr : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [p, hu.wr]; exact hwr
  have hr : Repr b h0 u.mem (u.gpr .x24) [] := by rw [hu.mem, p]; exact repr
  have hc : u.gpr .x1 = BitVec.ofNat 64 ([] : List Byte).length := hu.count
  have hb : ([] : List Byte).length + (u.gpr .x3).toNat < 2 ^ 64 := by simp only [List.length_nil, Nat.zero_add, len]; omega
  have cover : Covers [⟨u.gpr .x2, (u.gpr .x3).toNat⟩] (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .x24, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), offset, hu.data, ?_⟩
    change offset + (u.gpr .x3).toNat ≤ 16384
    rw [len]; exact sizeBound
  have ds : (⟨u.gpr .x2, (u.gpr .x3).toNat⟩ : Region).Disjoint ⟨u.gpr .x24, 192⟩ := by
    rw [hu.data, len, p]
    exact (Offset.base_disjoint _ (by omega) (by omega)).symm
  have dw : (⟨u.gpr .x2, (u.gpr .x3).toNat⟩ : Region).Disjoint ⟨u.gpr .x24 + 192, 576⟩ := by
    rw [hu.data, len, p]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega) (by omega) (by decide)
  have sw : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
    rw [sp, p]; exact stackWork
  have sd : (below u.sp 16).Disjoint ⟨u.gpr .x2, (u.gpr .x3).toNat⟩ := by
    rw [sp, hu.data, len]
    exact stackWork.sub_right (Offset.sub_base _ sizeBound)
  refine (VG.Proof.Argon2.AArch64.HPrime.update_ok v u h0 [] hr hc hb (by rw [sp]; exact hsp) wr cover ds dw sw sd).mono ?_
  rintro t ⟨repr', regs, rd, wr', sp', frame⟩
  simp only [p, hu.data, len, hu.mem, List.nil_append] at repr'
  refine ⟨repr', fun r hr h30 => (regs r hr h30).trans ?_, rd.trans hu.rd, wr'.trans hu.wr, sp'.trans hu.sp, ?_⟩
  · have hn : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · simpa only [p, sp, hu.mem] using VG.Proof.Argon2.AArch64.HPrime.update_frame (u.gpr .x24) u.sp frame

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Length`. -/
section

/-! # H′: selecting the first digest length -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov wp_subImm wp_lsr wp_movz Upd)

/-- A bounded public output length can be compared using the high bit of
its subtraction, without adding flag-based branches to the ISA. -/
theorem below65 (x : BitVec 64) (hx : x.toNat < 2 ^ 32) :
    (x - 65) >>> (63 : Nat) = if x.toNat < 65 then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  by_cases h : x.toNat < 65
  · rw [ite_eq_left h, BitVec.toNat_sub_of_lt (by rw [BitVec.lt_def]; exact h)]
    simp only [show (65 : BitVec 64).toNat = 65 from rfl,
      show (1 : BitVec 64).toNat = 1 from rfl, Nat.reducePow]
    omega
  · rw [ite_eq_right h, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact Nat.le_of_not_gt h)]
    simp only [show (65 : BitVec 64).toNat = 65 from rfl,
      show (0 : BitVec 64).toNat = 0 from rfl]
    omega

theorem Keeps.of_upd {s t : State} {d : Reg} {v : BitVec 64}
    (h : Upd s t d v) (hd : d ∉ preserved) : VG.Proof.Argon2.AArch64.HPrime.Keeps s t := by
  refine ⟨fun r hr _ => h.other r ?_, h.rd, h.wr, h.sp, ?_⟩
  · intro he; subst r; exact hd hr
  · rw [h.mem]; exact Frame.refl _ _

theorem chooseLength_ok (s : State) (hb : (s.gpr .x23).toNat < 2 ^ 32) :
    WP isa chooseLength s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 (min (s.gpr .x23).toNat 64) ∧ VG.Proof.Argon2.AArch64.HPrime.Keeps s t := by
  unfold chooseLength
  refine WP.seq (wp_mov fun a ha => wp_subImm (by decide) fun b hb' =>
    wp_lsr (by decide) fun u hu => WP.block_nil ?_)
  have ku : VG.Proof.Argon2.AArch64.HPrime.Keeps s u :=
    (Keeps.of_upd ha (by decide)).trans
      ((Keeps.of_upd hb' (by decide)).trans (Keeps.of_upd hu (by decide)))
  have n : u.gpr .x1 = s.gpr .x23 := by
    rw [hu.other _ (by decide), hb'.other _ (by decide), ha.gpr]
  have comparison : u.gpr .x9 = if (s.gpr .x23).toNat < 65 then 1 else 0 := by
    rw [hu.gpr, hb'.gpr, ha.gpr]
    exact VG.Proof.Argon2.AArch64.HPrime.below65 _ hb
  have flag : isa.eval (.nonzero .x .x9) u = some (decide ((s.gpr .x23).toNat < 65)) := by
    by_cases hn : (s.gpr .x23).toNat < 65 <;>
      simp [eval, State.read, comparison, hn]
  refine WP.ite (decide ((s.gpr .x23).toNat < 65)) flag ?_ ?_
  · intro h
    have hn : (s.gpr .x23).toNat ≤ 64 := by have := of_decide_eq_true h; omega
    apply WP.block_nil
    refine ⟨?_, ku⟩
    rw [n, Nat.min_eq_left hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro h
    have hn : 64 ≤ (s.gpr .x23).toNat := by have := of_decide_eq_false h; omega
    refine wp_movz fun t ht => WP.block_nil ?_
    refine ⟨?_, ku.trans (Keeps.of_upd ht (by decide))⟩
    rw [Nat.min_eq_right hn]; exact ht.gpr

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Compare`. -/
section

/-! # H′: a bounded public length comparison -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64
open VG.Proof.MdStream.AArch64 (wp_subImm wp_lsr)

structure Compared (s t : State) : Prop where
  value : t.gpr .x9 = if (s.gpr .x23).toNat < 65 then 1 else 0
  other : ∀ r, r ≠ .x9 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem compare_ok (s : State) (hb : (s.gpr .x23).toNat < 2 ^ 32) :
    WP isa (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63]) s (VG.Proof.Argon2.AArch64.HPrime.Compared s) := by
  refine wp_subImm (by decide) fun a ha => wp_lsr (by decide) fun t ht => WP.block_nil ?_
  refine ⟨?_, fun r hr => (ht.other r hr).trans (ha.other r hr), ht.mem.trans ha.mem,
    ht.rd.trans ha.rd, ht.wr.trans ha.wr, ht.sp.trans ha.sp⟩
  rw [ht.gpr, ha.gpr]
  exact VG.Proof.Argon2.AArch64.HPrime.below65 _ hb

theorem Compared.keeps {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.Compared s t) : VG.Proof.Argon2.AArch64.HPrime.Keeps s t := by
  refine ⟨fun r hr _ => h.other r ?_, h.rd, h.wr, h.sp, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [h.mem]; exact Frame.refl _ _

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Output`. -/
section

/-! # H′: emitting a digest or its 32-byte prefix -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov wp_addImm wp_movz wp_subImm)
open VG.Spec.Blake2 (bytesAt)
open VG.WriteBytes

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytesAt_take (m : Mem) (p : Addr) (n k : Nat) (hn : n ≤ k) :
    (bytesAt m p k).take n = bytesAt m p n := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left hn]

structure Copied (s : State) (k : Nat) (t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + BitVec.ofNat 64 k
  other : ∀ r, r ≠ .x8 → r ≠ .x3 → r ≠ .x2 → r ≠ .x22 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .x22) (bytesAt s.mem (s.gpr .x24 + 768) k)

theorem copy_ok (s : State) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 64)
    (count : s.gpr .x8 = BitVec.ofNat 64 k)
    (work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < k, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .x24 + 768, k⟩ : Region).Disjoint ⟨s.gpr .x22, k⟩) :
    WP isa copy s (VG.Proof.Argon2.AArch64.HPrime.Copied s k) := by
  unfold copy
  refine WP.seq (wp_mov fun a ha => wp_addImm (by decide) fun u hu => WP.block_nil ?_)
  have src : u.gpr .x2 = s.gpr .x24 + 768 := by rw [hu.gpr, ha.gpr]; rfl
  have other : ∀ r, r ≠ .x2 → u.gpr r = s.gpr r := fun r hr =>
    (hu.other r hr).trans (ha.other r hr)
  have mem : u.mem = s.mem := hu.mem.trans ha.mem
  have rd : u.rd = s.rd := hu.rd.trans ha.rd
  have wr : u.wr = s.wr := hu.wr.trans ha.wr
  have read : ∀ i < k, InRegions (u.rd ++ u.wr)
      (s.gpr .x24 + 768 + BitVec.ofNat 64 i) 1 := by
    intro i hi'
    rw [rd, wr, BitVec.add_assoc,
      show (768 : Addr) = BitVec.ofNat 64 768 from rfl, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_append_right _ work,
      Offset.contains_base _ (by omega : 768 + i + 1 ≤ 16384) (by omega)⟩
  have loop := VG.Proof.Argon2.AArch64.HPrime.copyLoop_ok u _ _ k lo (by omega) src (other .x22 (by decide))
    ((other .x8 (by decide)).trans count) read
    (by intro i hi'; rw [wr]; exact out i hi') sep
  obtain ⟨tr, t, he, ht⟩ := loop
  refine ⟨tr, t, he, ht.destination,
    fun r h1 h2 h3 h4 => (ht.other r h1 h2 h3 h4).trans (other r h3),
    ht.rd.trans rd, ht.wr.trans wr, (VG.AArch64.Exec.sp he).trans (hu.sp.trans ha.sp), ?_⟩
  rw [ht.mem, mem, List.take_of_length_le]
  simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl]

theorem Copied.frame {s t : State} {k : Nat} (h : VG.Proof.Argon2.AArch64.HPrime.Copied s k t) :
    Frame [⟨s.gpr .x22, k⟩] s.mem t.mem := by
  rw [h.mem]
  apply VG.WriteBytes.writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .x22) (d := 0) (n := k) (k := k) (by omega) (by decide)

structure Emitted (s t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + 32
  remaining : t.gpr .x23 = s.gpr .x23 - 32
  other : ∀ r, r ≠ .x8 → r ≠ .x3 → r ≠ .x2 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .x22) (bytesAt s.mem (s.gpr .x24 + 768) 32)

theorem emitPrefix_ok (s : State)
    (work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .x24 + 768, 32⟩ : Region).Disjoint ⟨s.gpr .x22, 32⟩) :
    WP isa emitPrefix s (VG.Proof.Argon2.AArch64.HPrime.Emitted s) := by
  unfold emitPrefix
  refine WP.seq (wp_movz fun a ha => WP.block_nil ?_)
  have base : a.gpr .x24 = s.gpr .x24 := ha.other _ (by decide)
  have dst : a.gpr .x22 = s.gpr .x22 := ha.other _ (by decide)
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact work
  have outA : ∀ i < 32, InRegions a.wr (a.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact out
  have sepA : (⟨a.gpr .x24 + 768, 32⟩ : Region).Disjoint ⟨a.gpr .x22, 32⟩ := by
    rw [base, dst]; exact sep
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.copy_ok a 32 (by decide) (by decide) ha.gpr workA outA sepA).mono ?_)
  intro u hu
  refine wp_subImm (by decide) fun t ht => WP.block_nil ?_
  refine ⟨?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ht.rd.trans (hu.rd.trans ha.rd),
    ht.wr.trans (hu.wr.trans ha.wr), ht.sp.trans (hu.sp.trans ha.sp), ?_⟩
  · rw [ht.other _ (by decide), hu.output, dst]; rfl
  · rw [ht.gpr, hu.other _ (by decide) (by decide) (by decide) (by decide), ha.other _ (by decide)]
    rfl
  · exact (ht.other r h5).trans ((hu.other r h1 h2 h3 h4).trans (ha.other r h1))
  · rw [ht.mem, hu.mem, ha.mem, base, dst]

theorem Emitted.frame {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.Emitted s t) :
    Frame [⟨s.gpr .x22, 32⟩] s.mem t.mem := by
  rw [h.mem]
  apply VG.WriteBytes.writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .x22) (d := 0) (n := 32) (k := 32) (by decide) (by decide)

theorem Emitted.digest {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.Emitted s t)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, 32⟩) :
    bytesAt t.mem (s.gpr .x24 + 768) 64 = bytesAt s.mem (s.gpr .x24 + 768) 64 := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .x24 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Chain`. -/
section

/-! Merged from `Proof.Argon2.AArch64.HPrime.Next`. -/
section
/-! # H′: hashing the previous 64-byte digest -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.AArch64 (wp_movz)

theorem next_ok (v : Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (next v.hash) s fun t =>
      (bytesAt t.mem (s.gpr .x24 + 768) 64).take (s.gpr .x1).toNat =
        Spec.Argon2.H (s.gpr .x1).toNat (bytesAt s.mem (s.gpr .x24 + 768) 64) ∧ VG.Proof.Argon2.AArch64.HPrime.Keeps s t := by
  unfold next
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.init_ok v s hlen hwr).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, spA, frameA⟩
  have ka : VG.Proof.Argon2.AArch64.HPrime.Keeps s a := ⟨regsA, rdA, wrA, spA, VG.Proof.Argon2.AArch64.HPrime.init_frame _ _ frameA⟩
  have digest : bytesAt a.mem (a.gpr .x24 + 768) 64 = bytesAt s.mem (s.gpr .x24 + 768) 64 := by
    rw [ka.x24]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply frameA.bytes (R := ⟨s.gpr .x24 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (Offset.base_disjoint _ (e := 768) (n := 64) (k := 192) (by decide) (by decide)).symm
  have reprA' : Repr b (Spec.Blake2.init b (s.gpr .x1).toNat 0) a.mem (a.gpr .x24) [] := by
    rw [ka.x24]; exact reprA
  have wrA' : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [ka.x24, ka.wr]; exact hwr
  have swA : (below a.sp 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ka.x24, ka.sp]; exact stackWork
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.absorbFixed_ok v a _ 768 64 (by decide) (by rw [ka.sp]; exact hsp) (by decide) (by decide) reprA' wrA' swA).mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .x1).toNat 0) u.mem (u.gpr .x24)
      (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    rw [ku.x24]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_movz fun w hw => WP.block_nil ?_)
  have kw : VG.Proof.Argon2.AArch64.HPrime.Keeps u w := by
    refine ⟨fun r hr _ => ?_, hw.rd, hw.wr, hw.sp, ?_⟩
    · have hn : r ≠ .x1 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hw.other r hn
    · rw [hw.mem]; exact Frame.refl _ _
  have ksw := ksu.trans kw
  have reprW : Repr b (Spec.Blake2.init b (s.gpr .x1).toNat 0) w.mem (w.gpr .x24)
      (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    rw [hw.mem, kw.x24]; exact reprU'
  have length : (bytesAt s.mem (s.gpr .x24 + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have count : w.gpr .x1 = BitVec.ofNat 64 (bytesAt s.mem (s.gpr .x24 + 768) 64).length := by
    rw [length]; exact hw.gpr
  have bound : (bytesAt s.mem (s.gpr .x24 + 768) 64).length < 2 ^ 64 := by rw [length]; decide
  have wrW : (⟨w.gpr .x24, 16384⟩ : Region) ∈ w.wr := by rw [ksw.x24, ksw.wr]; exact hwr
  have swW : (below w.sp 16).Disjoint ⟨w.gpr .x24, 16384⟩ := by
    rw [ksw.x24, ksw.sp]; exact stackWork
  refine (VG.Proof.Argon2.AArch64.HPrime.finalize_ok v w _ _ reprW count bound (by rw [ksw.sp]; exact hsp) wrW swW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, spT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, spT, VG.Proof.Argon2.AArch64.HPrime.finalize_frame _ _ frameT⟩⟩
  have result := congrArg (List.take (s.gpr .x1).toNat) out
  rw [ksw.x24] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.ChainStep`. -/
section
/-! # H′: one hash-and-prefix iteration -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_movz)
open VG.Spec.Blake2 (bytesAt)

structure ChainStep (s t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + 32
  remaining : t.gpr .x23 = s.gpr .x23 - 32
  regs : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16, ⟨s.gpr .x22, 32⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .x24 + 768) 64 =
    Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .x24 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .x22) 32 =
    (Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .x24 + 768) 64)).take 32
  comparison : t.gpr .x9 = if (s.gpr .x23 - 32).toNat < 65 then 1 else 0

theorem chainStep_ok (v : Backend) (s : State)
    (hsp : 16 ≤ s.sp.toNat)
    (remainingBound : 32 ≤ (s.gpr .x23).toNat ∧ (s.gpr .x23).toNat < 2 ^ 32)
    (work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, 32⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (.seq (.block [.movz .x .x1 64 0])
      (.seq (next v.hash) (.seq emitPrefix (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63]))))
      s (VG.Proof.Argon2.AArch64.HPrime.ChainStep s) := by
  refine WP.seq (wp_movz fun a ha => WP.block_nil ?_)
  have ka : VG.Proof.Argon2.AArch64.HPrime.Keeps s a := Keeps.of_upd ha (by decide)
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [ka.x24, ka.wr]; exact work
  have stackA : (below a.sp 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ka.x24, ka.sp]; exact stackWork
  have lengthA : (a.gpr .x1).toNat = 64 := by rw [ha.gpr]; rfl
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.next_ok v a (by rw [lengthA]; decide) (by rw [ka.sp]; exact hsp) workA stackA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .x22 = s.gpr .x22 := ksu.regs _ (by decide) (by decide)
  have digestU : bytesAt u.mem (s.gpr .x24 + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    simpa only [lengthA, ka.x24, ha.mem, VG.Proof.Argon2.AArch64.HPrime.bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ksu.x24, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .x24 + 768, 32⟩ : Region).Disjoint ⟨u.gpr .x22, 32⟩ := by
    rw [ksu.x24, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.emitPrefix_ok u workU outU sepU).mono ?_)
  intro w hw
  have remainingW : (w.gpr .x23).toNat < 2 ^ 32 := by
    rw [hw.remaining, ksu.regs _ (by decide) (by decide),
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact remainingBound.1)]
    exact Nat.lt_of_le_of_lt (Nat.sub_le ..) remainingBound.2
  refine (VG.Proof.Argon2.AArch64.HPrime.compare_ok w remainingW).mono fun t compared => ?_
  have gt := compared.other
  have mt := compared.mem
  have rt := compared.rd
  have wt := compared.wr
  have fw : Frame [⟨s.gpr .x22, 32⟩] u.mem w.mem := by
    rw [← dstU]; exact hw.frame
  refine ⟨?_, ?_, fun r hr h30 h14 h15 => ?_, rt.trans (hw.rd.trans ksu.rd),
    wt.trans (hw.wr.trans ksu.wr), compared.sp.trans (hw.sp.trans ksu.sp), ?_, ?_, ?_, ?_⟩
  · rw [gt _ (by decide), hw.output, dstU]
  · rw [gt _ (by decide), hw.remaining, ksu.regs _ (by decide) (by decide)]
  · have h9 : r ≠ .x9 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gt r h9]
    have hrax : r ≠ .x8 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrcx : r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrdx : r ≠ .x2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hw.other r hrax hrcx hrdx h14 h15).trans (ksu.regs r hr h30)
  · rw [mt]
    apply Frame.trans (ksu.frame.sub ?_) (fw.sub ?_)
    · intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    · intro r hr
      exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [mt, ← digestU]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply fw.bytes (R := ⟨s.gpr .x24 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  · rw [mt, hw.mem, dstU, ksu.x24, ← digestU, VG.Proof.Argon2.AArch64.HPrime.bytesAt_take _ _ 32 64 (by decide)]
    exact VG.Proof.Argon2.AArch64.HPrime.bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
  · rw [compared.value, hw.remaining, ksu.regs _ (by decide) (by decide)]

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: repeating the hash-and-prefix iteration -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

structure ChainResult (s : State) (n : Nat) (t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + BitVec.ofNat 64 (32 * n)
  remaining : t.gpr .x23 = s.gpr .x23 - BitVec.ofNat 64 (32 * n)
  regs : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16, ⟨s.gpr .x22, 32 * n⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .x24 + 768) 64 =
    chainDigest n (bytesAt s.mem (s.gpr .x24 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .x22) (32 * n) =
    chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)

theorem ChainResult.refl (s : State) : VG.Proof.Argon2.AArch64.HPrime.ChainResult s 0 s :=
  ⟨by simp, by simp, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

theorem ChainResult.cons {s u t : State} {n : Nat} (step : VG.Proof.Argon2.AArch64.HPrime.ChainStep s u)
    (tail : VG.Proof.Argon2.AArch64.HPrime.ChainResult u n t) (bound : 32 * (n + 1) < 2 ^ 64)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, 32 * (n + 1)⟩)
    (stackOut : (below s.sp 16).Disjoint ⟨s.gpr .x22, 32 * (n + 1)⟩) :
    VG.Proof.Argon2.AArch64.HPrime.ChainResult s (n + 1) t := by
  have base := step.regs .x24 (by decide) (by decide) (by decide) (by decide)
  have sp := step.sp
  have sum : 32 * (n + 1) = 32 + 32 * n := by omega
  have sumBV : BitVec.ofNat 64 (32 * (n + 1)) = 32 + BitVec.ofNat 64 (32 * n) := by
    rw [sum, BitVec.ofNat_add]; rfl
  have tf : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
      ⟨s.gpr .x22 + 32, 32 * n⟩] u.mem t.mem := by
    rw [← base, ← sp, ← step.output]; exact tail.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ 32 * (n + 1))
      (h : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
        ⟨s.gpr .x22 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .x24, 832⟩, below s.sp 16, ⟨s.gpr .x22, 32 * (n + 1)⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ hk⟩
  refine ⟨?_, ?_, fun r hr h30 h1 h2 => (tail.regs r hr h30 h1 h2).trans (step.regs r hr h30 h1 h2),
    tail.rd.trans step.rd, tail.wr.trans step.wr, tail.sp.trans step.sp, ?_, ?_, ?_⟩
  · rw [tail.output, step.output, sumBV, BitVec.add_assoc]
  · rw [tail.remaining, step.remaining, sumBV, BitVec.sub_sub]
  · exact (extend 0 32 (by omega) (by simpa only [BitVec.add_zero] using step.frame)).trans
      (extend 32 (32 * n) (by omega) tf)
  · rw [← base, tail.digest, base, step.digest]
    rfl
  · have before : bytesAt t.mem (s.gpr .x22) 32 = bytesAt u.mem (s.gpr .x22) 32 := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .x22, 32⟩) _ (show 32 ≤ 2 ^ 64 by decide) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left
          (Region.sub_prefix (by omega))
      · exact stackOut.symm.sub_left (Region.sub_prefix (by omega))
      · exact Offset.base_disjoint _ (e := 32) (n := 32 * n) (k := 32) (by decide) (by omega)
    rw [sum, Proof.Blake2.bytesAt_add, before, step.bytes,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl, ← step.output, tail.bytes,
      base, step.digest]
    rfl

theorem chain_ok (v : Backend) (n lastLen : Nat) (s : State)
    (positive : 1 ≤ n) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (bound : 32 * n + lastLen < 2 ^ 32)
    (hsp : 16 ≤ s.sp.toNat)
    (count : s.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen))
    (work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32 * n, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, 32 * n⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackOut : (below s.sp 16).Disjoint ⟨s.gpr .x22, 32 * n⟩) :
    WP isa (chain v.hash) s (VG.Proof.Argon2.AArch64.HPrime.ChainResult s n) := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    have out32 : ∀ i < 32, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1 :=
      fun i hi => out i (by omega)
    have sep32 := sep.sub_right (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega))
    obtain ⟨trace, u, run, step⟩ := VG.Proof.Argon2.AArch64.HPrime.chainStep_ok v s hsp
      (by rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) work out32 sep32 stackWork
    have base := step.regs .x24 (by decide) (by decide) (by decide) (by decide)
    have sp := step.sp
    have countU : u.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen) := by
      rw [step.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        Offset.ofNat_sub_ofNat (by omega : 32 ≤ 32 * (n + 1) + lastLen)]
      rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega]
    have compareU : u.gpr .x9 = if 32 * n + lastLen < 65 then 1 else 0 := by
      rw [step.comparison, ← step.remaining, countU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    cases n with
    | zero =>
      have flag : isa.eval (.zero .x .x9) u = some false := by
        simp [eval, State.read, compareU, show lastLen < 65 by omega]
      exact ⟨_, u, .loopExit run flag, (ChainResult.refl u).cons step (by omega) sep stackOut⟩
    | succ n =>
      have workU : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [base, step.wr]; exact work
      have outU : ∀ i < 32 * (n + 1), InRegions u.wr (u.gpr .x22 + BitVec.ofNat 64 i) 1 := by
        intro i hi
        rw [step.wr, step.output, BitVec.add_assoc,
          show (32 : Addr) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
        exact out (32 + i) (by omega)
      have suffix : Region.Sub ⟨u.gpr .x22, 32 * (n + 1)⟩ ⟨s.gpr .x22, 32 * (n + 1 + 1)⟩ := by
        rw [step.output]
        exact Offset.sub_base _ (by omega : 32 + 32 * (n + 1) ≤ 32 * (n + 1 + 1))
      have sepU : (⟨u.gpr .x24, 16384⟩ : Region).Disjoint ⟨u.gpr .x22, 32 * (n + 1)⟩ := by
        rw [base]; exact sep.sub_right suffix
      have swU : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
        rw [sp, base]; exact stackWork
      have soU : (below u.sp 16).Disjoint ⟨u.gpr .x22, 32 * (n + 1)⟩ := by
        rw [sp]; exact stackOut.sub_right suffix
      obtain ⟨trace', t, run', result⟩ := ih u (by omega) (by omega) (by rw [sp]; exact hsp) countU workU outU sepU swU soU
      have flag : isa.eval (.zero .x .x9) u = some true := by
        simp [eval, State.read, compareU, show ¬ 32 * (n + 1) + lastLen < 65 by omega]
      exact ⟨_, t, .loopNext run flag run', result.cons step (by omega) sep stackOut⟩

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Contract`. -/
section

/-! # H′: a local ARM64 contract -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64

def inputR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
def outputR (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
def workR (s : State) : Region := ⟨s.gpr .x4, 16384⟩
def stackR (s : State) : Region := below s.sp 16

def localContract : Contract isa where
  pre s := s.rd = [VG.Proof.Argon2.AArch64.HPrime.inputR s] ∧ s.wr = [VG.Proof.Argon2.AArch64.HPrime.outputR s, VG.Proof.Argon2.AArch64.HPrime.workR s] ∧
    (s.gpr .x1).toNat < 2 ^ 32 ∧ 1 ≤ (s.gpr .x3).toNat ∧ (s.gpr .x3).toNat < 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧
    (VG.Proof.Argon2.AArch64.HPrime.inputR s).Disjoint (VG.Proof.Argon2.AArch64.HPrime.workR s) ∧ (VG.Proof.Argon2.AArch64.HPrime.outputR s).Disjoint (VG.Proof.Argon2.AArch64.HPrime.workR s) ∧
    (VG.Proof.Argon2.AArch64.HPrime.stackR s).Disjoint (VG.Proof.Argon2.AArch64.HPrime.inputR s) ∧ (VG.Proof.Argon2.AArch64.HPrime.stackR s).Disjoint (VG.Proof.Argon2.AArch64.HPrime.outputR s) ∧ (VG.Proof.Argon2.AArch64.HPrime.stackR s).Disjoint (VG.Proof.Argon2.AArch64.HPrime.workR s)
  post s t := Spec.Blake2.bytesAt t.mem (s.gpr .x2) (s.gpr .x3).toNat =
    Spec.Argon2.hPrime (s.gpr .x3).toNat (Spec.Blake2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s t := s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4 ∧ s.sp = t.sp

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x2000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x9000
  c := false
  v _ := 0
  unknowns _ := 0
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 1⟩, ⟨0x4000, 16384⟩]

theorem contract_implies : localContract.Implies (Spec.Argon2.hPrimeContract AArch64.abi 16) := by
  sig_implies [Spec.Argon2.hPrimeContract, Spec.Argon2.hPrimeSig, VG.Proof.Argon2.AArch64.HPrime.localContract,
    VG.Proof.Argon2.AArch64.HPrime.inputR, VG.Proof.Argon2.AArch64.HPrime.outputR, VG.Proof.Argon2.AArch64.HPrime.workR, VG.Proof.Argon2.AArch64.HPrime.stackR, below, AArch64.abi, AArch64.argRegs] [satState] using VG.Proof.Argon2.AArch64.HPrime.satState

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Space`. -/
section

/-! Merged from `Proof.Argon2.AArch64.HPrime.Written`. -/
section
/-! # H′: composing output fragments -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64
open VG.Spec.Blake2 (bytesAt)

/-- An output fragment, allowing hashing in the workspace between writes. -/
structure Written (s : State) (xs : List Byte) (t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + BitVec.ofNat 64 xs.length
  regs : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16, ⟨s.gpr .x22, xs.length⟩] s.mem t.mem
  bytes : bytesAt t.mem (s.gpr .x22) xs.length = xs

theorem Written.x24 {s t : State} {xs : List Byte} (h : VG.Proof.Argon2.AArch64.HPrime.Written s xs t) :
    t.gpr .x24 = s.gpr .x24 := h.regs _ (by decide) (by decide) (by decide) (by decide)

theorem Written.of_keeps {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.Keeps s t) : VG.Proof.Argon2.AArch64.HPrime.Written s [] t := by
  refine ⟨?_, fun r hr h30 _ _ => h.regs r hr h30, h.rd, h.wr, h.sp, ?_, rfl⟩
  · exact (h.regs .x22 (by decide) (by decide)).trans (BitVec.add_zero _).symm
  · exact h.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩

theorem Written.before_keeps {s u t : State} {xs : List Byte} (h : VG.Proof.Argon2.AArch64.HPrime.Written u xs t)
    (k : VG.Proof.Argon2.AArch64.HPrime.Keeps s u) : VG.Proof.Argon2.AArch64.HPrime.Written s xs t := by
  have dst := k.regs .x22 (by decide) (by decide)
  refine ⟨by rw [h.output, dst], fun r hr h30 h1 h2 => (h.regs r hr h30 h1 h2).trans (k.regs r hr h30),
    h.rd.trans k.rd, h.wr.trans k.wr, h.sp.trans k.sp, ?_, ?_⟩
  · have before : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
        ⟨s.gpr .x22, xs.length⟩] s.mem u.mem :=
      k.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    exact before.trans (by simpa only [dst, k.x24, k.sp] using h.frame)
  · rw [← dst]; exact h.bytes

theorem Written.of_copied {s t : State} {k : Nat} (h : VG.Proof.Argon2.AArch64.HPrime.Copied s k t) (hk : k < 2 ^ 64) :
    VG.Proof.Argon2.AArch64.HPrime.Written s (bytesAt s.mem (s.gpr .x24 + 768) k) t := by
  have len : (bytesAt s.mem (s.gpr .x24 + 768) k).length = k := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr _ h14 _ => ?_, h.rd, h.wr, h.sp, ?_, ?_⟩
  · have h1 : r ≠ .x8 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h3 : r ≠ .x2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h1 h2 h3 h14
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [h.mem]
    exact VG.Proof.Argon2.AArch64.HPrime.bytesAt_writeBytes _ _ _ (by rw [len]; exact hk)

theorem Written.of_emitted {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.Emitted s t) :
    VG.Proof.Argon2.AArch64.HPrime.Written s (bytesAt s.mem (s.gpr .x24 + 768) 32) t := by
  have len : (bytesAt s.mem (s.gpr .x24 + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr _ h14 h15 => ?_, h.rd, h.wr, h.sp, ?_, ?_⟩
  · have h1 : r ≠ .x8 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h3 : r ≠ .x2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h1 h2 h3 h14 h15
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [h.mem]
    exact VG.Proof.Argon2.AArch64.HPrime.bytesAt_writeBytes _ _ _ (by rw [len]; decide)

theorem Written.of_chain {s t : State} {n : Nat} (h : VG.Proof.Argon2.AArch64.HPrime.ChainResult s n t) :
    VG.Proof.Argon2.AArch64.HPrime.Written s (Proof.Argon2.chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)) t := by
  refine ⟨?_, h.regs, h.rd, h.wr, h.sp, ?_, ?_⟩
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.output
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.frame
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.bytes

theorem Written.trans {s u t : State} {xs ys : List Byte} (first : VG.Proof.Argon2.AArch64.HPrime.Written s xs u)
    (last : VG.Proof.Argon2.AArch64.HPrime.Written u ys t) (bound : xs.length + ys.length < 2 ^ 64)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, xs.length + ys.length⟩)
    (stack : (below s.sp 16).Disjoint ⟨s.gpr .x22, xs.length + ys.length⟩) :
    VG.Proof.Argon2.AArch64.HPrime.Written s (xs ++ ys) t := by
  have tf : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
      ⟨s.gpr .x22 + BitVec.ofNat 64 xs.length, ys.length⟩] u.mem t.mem := by
    rw [← first.x24, ← first.sp, ← first.output]; exact last.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ xs.length + ys.length)
      (h : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
        ⟨s.gpr .x22 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
        ⟨s.gpr .x22, (xs ++ ys).length⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ (by simpa only [List.length_append] using hk)⟩
  refine ⟨?_, fun r hr h30 h1 h2 => (last.regs r hr h30 h1 h2).trans (first.regs r hr h30 h1 h2),
    last.rd.trans first.rd, last.wr.trans first.wr, last.sp.trans first.sp, ?_, ?_⟩
  · rw [last.output, first.output, List.length_append, BitVec.ofNat_add, BitVec.add_assoc]
  · exact (extend 0 xs.length (by omega) (by simpa only [BitVec.add_zero] using first.frame)).trans
      (extend xs.length ys.length (by omega) tf)
  · have before : bytesAt t.mem (s.gpr .x22) xs.length = bytesAt u.mem (s.gpr .x22) xs.length := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .x22, xs.length⟩) _ (show xs.length ≤ 2 ^ 64 by omega) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Region.sub_prefix (by omega))
      · exact stack.symm.sub_left (Region.sub_prefix (by omega))
      · exact Offset.base_disjoint _ (by omega) (by omega)
    rw [List.length_append, Proof.Blake2.bytesAt_add, before, first.bytes, ← first.output, last.bytes]

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: permissions and separation at an output cursor -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov)
open VG.Spec.Blake2 (bytesAt)

structure Space (s : State) (n : Nat) : Prop where
  bound : n < 2 ^ 32
  spBound : 16 ≤ s.sp.toNat
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  out : ∀ i < n, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1
  sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, n⟩
  stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩
  stackOut : (below s.sp 16).Disjoint ⟨s.gpr .x22, n⟩

theorem Space.advance {s t : State} {xs : List Byte} {n k : Nat}
    (h : VG.Proof.Argon2.AArch64.HPrime.Space s n) (written : VG.Proof.Argon2.AArch64.HPrime.Written s xs t) (size : xs.length + k ≤ n) : VG.Proof.Argon2.AArch64.HPrime.Space t k := by
  have suffix : Region.Sub ⟨t.gpr .x22, k⟩ ⟨s.gpr .x22, n⟩ := by
    rw [written.output]; exact Offset.sub_base _ size
  refine ⟨by have := h.bound; omega, by rw [written.sp]; exact h.spBound, ?_, ?_, ?_, ?_, ?_⟩
  · rw [written.wr, written.x24]; exact h.work
  · intro i hi
    rw [written.wr, written.output, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.out (xs.length + i) (by omega)
  · rw [written.x24]; exact h.sep.sub_right suffix
  · rw [written.x24, written.sp]; exact h.stackWork
  · rw [written.sp]; exact h.stackOut.sub_right suffix

theorem Space.keeps {s t : State} {n : Nat} (h : VG.Proof.Argon2.AArch64.HPrime.Space s n) (k : VG.Proof.Argon2.AArch64.HPrime.Keeps s t) : VG.Proof.Argon2.AArch64.HPrime.Space t n :=
  h.advance (Written.of_keeps k) (by simp only [List.length_nil, Nat.zero_add, Nat.le_refl])

theorem Space.prefix {s : State} {n k : Nat} (h : VG.Proof.Argon2.AArch64.HPrime.Space s n) (hk : k ≤ n) : VG.Proof.Argon2.AArch64.HPrime.Space s k := by
  refine ⟨by have := h.bound; omega, h.spBound, h.work, fun i hi => h.out i (by omega),
    h.sep.sub_right (Region.sub_prefix hk), h.stackWork, h.stackOut.sub_right (Region.sub_prefix hk)⟩

theorem Space.join {s u t : State} {xs ys : List Byte} {n : Nat} (h : VG.Proof.Argon2.AArch64.HPrime.Space s n)
    (first : VG.Proof.Argon2.AArch64.HPrime.Written s xs u) (last : VG.Proof.Argon2.AArch64.HPrime.Written u ys t) (size : xs.length + ys.length ≤ n) :
    VG.Proof.Argon2.AArch64.HPrime.Written s (xs ++ ys) t :=
  first.trans last (by have := h.bound; omega)
    (h.sep.sub_right (Region.sub_prefix size)) (h.stackOut.sub_right (Region.sub_prefix size))

theorem copyRemaining_ok (s : State) (n : Nat) (space : VG.Proof.Argon2.AArch64.HPrime.Space s n)
    (lo : 1 ≤ n) (hi : n ≤ 64) (count : s.gpr .x23 = BitVec.ofNat 64 n) :
    WP isa copyRemaining s fun t => VG.Proof.Argon2.AArch64.HPrime.Written s (bytesAt s.mem (s.gpr .x24 + 768) n) t := by
  unfold copyRemaining
  refine WP.seq (wp_mov fun a ha => WP.block_nil ?_)
  have base := ha.other .x24 (by decide)
  have dst := ha.other .x22 (by decide)
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact space.work
  have outA : ∀ i < n, InRegions a.wr (a.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact space.out
  have sepA : (⟨a.gpr .x24 + 768, n⟩ : Region).Disjoint ⟨a.gpr .x22, n⟩ := by
    rw [base, dst]; exact space.sep.sub_left (Offset.sub_base _ (by omega : 768 + n ≤ 16384))
  refine (VG.Proof.Argon2.AArch64.HPrime.copy_ok a n lo hi (ha.gpr.trans count) workA outA sepA).mono ?_
  intro t ht
  have result := Written.of_copied ht (by have := space.bound; omega)
  refine ⟨?_, fun r hr h30 h1 h2 => ?_, result.rd.trans ha.rd, result.wr.trans ha.wr, result.sp.trans ha.sp, ?_, ?_⟩
  · simpa only [dst, ha.mem, base] using result.output
  · have hrax : r ≠ .x8 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (result.regs r hr h30 h1 h2).trans (ha.other r hrax)
  · simpa only [base, dst, ha.mem, ha.sp] using result.frame
  · simpa only [base, dst, ha.mem] using result.bytes

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Input`. -/
section

/-! # H′: arguments for the caller's input -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure InputArgs (s t : State) : Prop where
  count : t.gpr .x1 = 4
  data : t.gpr .x2 = s.gpr .x20
  size : t.gpr .x3 = s.gpr .x21
  other : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem inputArgs_ok (s : State) : WP isa (.block inputArgs) s (VG.Proof.Argon2.AArch64.HPrime.InputArgs s) := by
  apply WP.of_runBlock
  simp only [inputArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    show (0 : Nat) < 4096 from by decide, show (16 * 0 : Nat) < 64 from by decide,
    State.read, Size.bits, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]

theorem InputArgs.keeps {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.InputArgs s t) : VG.Proof.Argon2.AArch64.HPrime.Keeps s t := by
  refine ⟨fun r hr _ => ?_, h.rd, h.wr, h.sp, ?_⟩
  · have hn : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r hn.1 hn.2.1 hn.2.2
  · rw [h.mem]; exact Frame.refl _ _

open VG.Spec.Blake2 (b Repr bytesAt)

theorem absorbInput_ok (v : Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (headBytes : List Byte) (prefixLen : headBytes.length = 4)
    (repr : Repr b h0 s.mem (s.gpr .x24) headBytes) (len : (s.gpr .x21).toNat < 2 ^ 32)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .x20, (s.gpr .x21).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .x20, (s.gpr .x21).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackData : (below s.sp 16).Disjoint ⟨s.gpr .x20, (s.gpr .x21).toNat⟩) :
    WP isa (absorbInput v.hash) s fun t =>
      Repr b h0 t.mem (s.gpr .x24) (headBytes ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat) ∧
      VG.Proof.Argon2.AArch64.HPrime.Keeps s t := by
  unfold absorbInput
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.inputArgs_ok s).mono fun u hu => ?_)
  have ku := hu.keeps
  have repr' : Repr b h0 u.mem (u.gpr .x24) headBytes := by rw [hu.mem, ku.x24]; exact repr
  have count : u.gpr .x1 = BitVec.ofNat 64 headBytes.length := by rw [prefixLen]; exact hu.count
  have bound : headBytes.length + (u.gpr .x3).toNat < 2 ^ 64 := by rw [prefixLen, hu.size]; omega
  have wr : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ku.x24, ku.wr]; exact hwr
  have cover : Covers [⟨u.gpr .x2, (u.gpr .x3).toNat⟩] (u.rd ++ u.wr) := by
    rw [hu.data, hu.size, hu.rd, hu.wr]; exact hdata
  have ds : (⟨u.gpr .x2, (u.gpr .x3).toNat⟩ : Region).Disjoint ⟨u.gpr .x24, 192⟩ := by
    rw [hu.data, hu.size, ku.x24]
    exact dataWork.sub_right (Region.sub_prefix (by decide))
  have dw : (⟨u.gpr .x2, (u.gpr .x3).toNat⟩ : Region).Disjoint ⟨u.gpr .x24 + 192, 576⟩ := by
    rw [hu.data, hu.size, ku.x24]
    exact dataWork.sub_right (Offset.sub_base _ (by decide))
  have sw : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
    rw [ku.x24, ku.sp]; exact stackWork
  have sd : (below u.sp 16).Disjoint ⟨u.gpr .x2, (u.gpr .x3).toNat⟩ := by
    rw [hu.data, hu.size, ku.sp]; exact stackData
  refine (VG.Proof.Argon2.AArch64.HPrime.update_ok v u h0 headBytes repr' count bound (by rw [ku.sp]; exact hsp) wr cover ds dw sw sd).mono ?_
  rintro t ⟨result, regs, rd, wr', sp', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', sp', VG.Proof.Argon2.AArch64.HPrime.update_frame _ _ frame⟩⟩
  simpa only [ku.x24, hu.mem, hu.data, hu.size] using result

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Setup`. -/
section

/-! # H′: saving the caller and writing the length prefix -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

/-- Save the seven caller registers and then the four-byte length prefix. -/
def setupMem (s : State) : Mem :=
  (saved.foldl (fun m rd => m.writeW (s.gpr .x4 + BitVec.ofNat 64 rd.2) (s.gpr rd.1)) s.mem).writeW
    (s.gpr .x4 + 832) ((s.gpr .x3).setWidth 32)

theorem setupMem_frame (s : State) :
    Frame [⟨s.gpr .x4 + 832, 64⟩] s.mem (VG.Proof.Argon2.AArch64.HPrime.setupMem s) := by
  have store {m : Mem} (h : Frame [⟨s.gpr .x4 + 832, 64⟩] s.mem m)
      (d w : Nat) (v : BitVec w) (lo : 832 ≤ d) (hi : d + w / 8 ≤ 896) :
      Frame [⟨s.gpr .x4 + 832, 64⟩] s.mem (m.writeW (s.gpr .x4 + BitVec.ofNat 64 d) v) :=
    h.writeW (List.mem_singleton_self _) v (Offset.contains _ lo hi (by decide))
  unfold VG.Proof.Argon2.AArch64.HPrime.setupMem VG.Impl.Argon2.AArch64.HPrime.saved
  simp only [List.foldl_cons, List.foldl_nil]
  apply store (d := 832) (w := 32) _ _ (by decide) (by decide)
  apply store (d := 880) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 888) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 872) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 864) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 856) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 848) (w := 64) _ _ (by decide) (by decide)
  exact store (Frame.refl _ _) 840 64 _ (by decide) (by decide)

theorem setupMem_prefix (s : State) :
    Spec.Blake2.bytesAt (VG.Proof.Argon2.AArch64.HPrime.setupMem s) (s.gpr .x4 + 832) 4 =
      Spec.Argon2.le32 (s.gpr .x3).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl)]
  unfold VG.Proof.Argon2.AArch64.HPrime.setupMem
  rw [Mem.readW_writeW_self32]
  rfl

theorem setupMem_saved (s : State) (r : Reg) (d : Nat) (hr : (r, d) ∈ VG.Impl.Argon2.AArch64.HPrime.saved) :
    (VG.Proof.Argon2.AArch64.HPrime.setupMem s).readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 = s.gpr r := by
  have skip64 (m : Mem) (v : BitVec 64) (d e : Nat)
      (sep : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
      (m.writeW (s.gpr .x4 + BitVec.ofNat 64 e) v).readW
        (s.gpr .x4 + BitVec.ofNat 64 d) 64 = m.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 :=
    Mem.readW_writeW_sep (Offset.sep _ sep hd he) (by decide)
  have skip32 (m : Mem) (v : BitVec 32) (d : Nat) (lo : 836 ≤ d) (hi : d + 8 ≤ 2 ^ 64) :
      (m.writeW (s.gpr .x4 + 832) v).readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 =
        m.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 :=
    Mem.readW_writeW_sep (Offset.sep _ (Or.inr lo) hi (by decide)) (by decide)
  simp only [VG.Impl.Argon2.AArch64.HPrime.saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp (disch := decide) only [VG.Proof.Argon2.AArch64.HPrime.setupMem, VG.Impl.Argon2.AArch64.HPrime.saved, List.foldl_cons, List.foldl_nil,
      skip32, skip64, Mem.readW_writeW_self64]

structure Setup (s t : State) : Prop where
  workspace : t.gpr .x24 = s.gpr .x4
  input : t.gpr .x20 = s.gpr .x0
  length : t.gpr .x21 = s.gpr .x1
  output : t.gpr .x22 = s.gpr .x2
  remaining : t.gpr .x23 = s.gpr .x3
  other : ∀ r, r ≠ .x24 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  mem : t.mem = VG.Proof.Argon2.AArch64.HPrime.setupMem s
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem setup_ok (s : State) (hw : (⟨s.gpr .x4, 16384⟩ : Region) ∈ s.wr) :
    WP isa (.block VG.Impl.Argon2.AArch64.HPrime.setup) s (VG.Proof.Argon2.AArch64.HPrime.Setup s) := by
  have write (d n : Nat) (h : d + n ≤ 16384) :
      InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 d) n :=
    ⟨_, hw, Offset.contains_base _ h (by omega)⟩
  have w832 := write 832 4 (by decide)
  have w840 := write 840 8 (by decide)
  have w848 := write 848 8 (by decide)
  have w856 := write 856 8 (by decide)
  have w864 := write 864 8 (by decide)
  have w872 := write 872 8 (by decide)
  have w888 := write 888 8 (by decide)
  have w880 := write 880 8 (by decide)
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.HPrime.setup, VG.Impl.Argon2.AArch64.HPrime.saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    show (840 : Nat) % 8 = 0 ∧ 840 < 4096 * 8 from by decide,
    show (848 : Nat) % 8 = 0 ∧ 848 < 4096 * 8 from by decide,
    show (856 : Nat) % 8 = 0 ∧ 856 < 4096 * 8 from by decide,
    show (864 : Nat) % 8 = 0 ∧ 864 < 4096 * 8 from by decide,
    show (872 : Nat) % 8 = 0 ∧ 872 < 4096 * 8 from by decide,
    show (880 : Nat) % 8 = 0 ∧ 880 < 4096 * 8 from by decide,
    show (888 : Nat) % 8 = 0 ∧ 888 < 4096 * 8 from by decide,
    show (832 : Nat) % 4 = 0 ∧ 832 < 4096 * 4 from by decide,
    show (0 : Nat) < 4096 from by decide,
    and_self, Nat.reduceMul, BitVec.setWidth_eq, Size.bits, Size.bytes, BitVec.add_zero, State.store, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    w832, w840, w848, w856, w864, w872, w880, w888, reduceCtorEq, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun r h1 h2 h3 h4 h5 => ?_, ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, h1, h2, h3, h4, h5, ite_false]
  · rfl

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Correct`. -/
section

/-! Merged from `Proof.Argon2.AArch64.HPrime.Restore`. -/
section
/-! # H′: restoring the caller's registers -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem saved_read {m m' : Mem} (p sp : Addr)
    (frame : Frame [⟨p, 832⟩, below sp 16] m m')
    (stack : (below sp 16).Disjoint ⟨p, 16384⟩)
    (d : Nat) (lo : 832 ≤ d) (hi : d + 8 ≤ 16384) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 := by
  apply frame.readW (r := ⟨p + BitVec.ofNat 64 d, 8⟩) ?_ ?_ (by decide)
  · simpa only [BitVec.add_zero] using
      Offset.contains_base (p + BitVec.ofNat 64 d) (d := 0) (n := 8) (k := 8) (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (Offset.base_disjoint p lo (by omega)).symm
    · exact (stack.sub_right (Offset.sub_base p hi)).symm

theorem restore_ok (original s : State) (base : s.gpr .x24 = original.gpr .x4)
    (extra : ∀ r ∈ [.x25, .x26, .x27, .x28], s.gpr r = original.gpr r)
    (readable : (⟨original.gpr .x4, 16384⟩ : Region) ∈ s.rd ++ s.wr)
    (values : ∀ r d, (r, d) ∈ saved →
      s.mem.readW (original.gpr .x4 + BitVec.ofNat 64 d) 64 = original.gpr r) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ preserved, t.gpr r = original.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have read (d : Nat) (h : d + 8 ≤ 16384) :
      InRegions (s.rd ++ s.wr) (original.gpr .x4 + BitVec.ofNat 64 d) 8 :=
    ⟨_, readable, Offset.contains_base _ h (by omega)⟩
  have r840 := read 840 (by decide)
  have r848 := read 848 (by decide)
  have r856 := read 856 (by decide)
  have r864 := read 864 (by decide)
  have r872 := read 872 (by decide)
  have r888 := read 888 (by decide)
  have r880 := read 880 (by decide)
  have v840 := values .x19 840 (by decide)
  have v848 := values .x20 848 (by decide)
  have v856 := values .x21 856 (by decide)
  have v864 := values .x22 864 (by decide)
  have v872 := values .x23 872 (by decide)
  have v888 := values .x30 888 (by decide)
  have v880 := values .x24 880 (by decide)
  simp only [Mem.readW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq] at v840 v848 v856 v864 v872 v880 v888
  apply WP.of_runBlock
  simp only [restore, saved, List.map_cons, List.map_nil, runBlock_cons,
    runStep_some, runBlock_nil, exec, addr,
    show (840 : Nat) % 8 = 0 ∧ 840 < 4096 * 8 from by decide,
    show (848 : Nat) % 8 = 0 ∧ 848 < 4096 * 8 from by decide,
    show (856 : Nat) % 8 = 0 ∧ 856 < 4096 * 8 from by decide,
    show (864 : Nat) % 8 = 0 ∧ 864 < 4096 * 8 from by decide,
    show (872 : Nat) % 8 = 0 ∧ 872 < 4096 * 8 from by decide,
    show (880 : Nat) % 8 = 0 ∧ 880 < 4096 * 8 from by decide,
    show (888 : Nat) % 8 = 0 ∧ 888 < 4096 * 8 from by decide,
    and_self, Nat.reduceMul, BitVec.setWidth_eq, Size.bits, Size.bytes,
    State.load,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    base, r840, r848, r856, r864, r872, r880, r888,
    reduceCtorEq, ite_true, ite_false, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [reduceCtorEq, ite_true, ite_false,
      v840, v848, v856, v864, v872, v880, v888]
  all_goals exact extra _ (by decide)

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.First`. -/
section
/-! Merged from `Proof.Argon2.AArch64.HPrime.FinishInput`. -/
section
/-! # H′: finalizing the prefixed input -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.AArch64 (wp_mov wp_addImm)

theorem finishInput_ok (v : Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .x24) d)
    (length : d.length = 4 + (s.gpr .x21).toNat) (bound : (s.gpr .x21).toNat < 2 ^ 32)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (finishInput v.hash) s fun t =>
      bytesAt t.mem (s.gpr .x24 + 768) 64 = Spec.Blake2.finalHash b h0 d ∧ VG.Proof.Argon2.AArch64.HPrime.Keeps s t := by
  unfold finishInput
  refine WP.seq (wp_mov fun a ha => wp_addImm (by decide) fun u hu => WP.block_nil ?_)
  have ku : VG.Proof.Argon2.AArch64.HPrime.Keeps s u := by
    refine ⟨fun r hr _ => ?_, hu.rd.trans ha.rd, hu.wr.trans ha.wr, hu.sp.trans ha.sp, ?_⟩
    · have hn : r ≠ .x1 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hu.other r hn).trans (ha.other r hn)
    · rw [hu.mem, ha.mem]; exact Frame.refl _ _
  have repr' : Repr b h0 u.mem (u.gpr .x24) d := by rw [hu.mem, ha.mem, ku.x24]; exact repr
  have count : u.gpr .x1 = BitVec.ofNat 64 d.length := by
    rw [hu.gpr, ha.gpr, length, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.add_comm _ _
  have len : d.length < 2 ^ 64 := by rw [length]; omega
  have wr : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ku.x24, ku.wr]; exact hwr
  have sw : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
    rw [ku.x24, ku.sp]; exact stackWork
  refine (VG.Proof.Argon2.AArch64.HPrime.finalize_ok v u h0 d repr' count len (by rw [ku.sp]; exact hsp) wr sw).mono ?_
  rintro t ⟨out, regs, rd, wr', sp', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', sp', VG.Proof.Argon2.AArch64.HPrime.finalize_frame _ _ frame⟩⟩
  simpa only [ku.x24] using out

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: the hash of the length prefix and input -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem first_ok (v : Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .x23).toNat ∧ (s.gpr .x23).toNat < 2 ^ 32)
    (len : (s.gpr .x21).toNat < 2 ^ 32)
    (headBytes : bytesAt s.mem (s.gpr .x24 + 832) 4 = Spec.Argon2.le32 (s.gpr .x23).toNat)
    (hsp : 16 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .x20, (s.gpr .x21).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .x20, (s.gpr .x21).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩)
    (stackData : (below s.sp 16).Disjoint ⟨s.gpr .x20, (s.gpr .x21).toNat⟩) :
    WP isa (first v.hash) s fun t =>
      (bytesAt t.mem (s.gpr .x24 + 768) 64).take (min (s.gpr .x23).toNat 64) =
        Spec.Argon2.H (min (s.gpr .x23).toNat 64)
          (Spec.Argon2.le32 (s.gpr .x23).toNat ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat) ∧
      VG.Proof.Argon2.AArch64.HPrime.Keeps s t := by
  unfold first
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.chooseLength_ok s hlen.2).mono ?_)
  rintro a ⟨lengthA, ka⟩
  have na : (a.gpr .x1).toNat = min (s.gpr .x23).toNat 64 := by
    rw [lengthA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have wrA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [ka.x24, ka.wr]; exact hwr
  have swA : (below a.sp 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ka.x24, ka.sp]; exact stackWork
  have lenA : 1 ≤ (a.gpr .x1).toNat ∧ (a.gpr .x1).toNat ≤ 64 := by rw [na]; omega
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.init_ok v a lenA wrA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  have ku : VG.Proof.Argon2.AArch64.HPrime.Keeps a u := ⟨regsU, rdU, wrU, spU, VG.Proof.Argon2.AArch64.HPrime.init_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (min (s.gpr .x23).toNat 64) 0) u.mem (u.gpr .x24) [] := by
    rw [ku.x24]; simpa only [na] using reprU
  have wrU' : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ksu.x24, ksu.wr]; exact hwr
  have swU : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
    rw [ksu.x24, ksu.sp]; exact stackWork
  have headU : bytesAt u.mem (u.gpr .x24 + 832) 4 = Spec.Argon2.le32 (s.gpr .x23).toNat := by
    rw [ksu.x24, ksu.prefix stackWork]; exact headBytes
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.absorbFixed_ok v u _ 832 4 (by decide) (by rw [ksu.sp]; exact hsp) (by decide) (by decide) reprU' wrU' swU).mono ?_)
  rintro w ⟨reprW, kw⟩
  have ksw := ksu.trans kw
  have r12 : w.gpr .x20 = s.gpr .x20 := ksw.regs _ (by decide) (by decide)
  have r13 : w.gpr .x21 = s.gpr .x21 := ksw.regs _ (by decide) (by decide)
  have headLen : (Spec.Argon2.le32 (s.gpr .x23).toNat).length = 4 := by
    simp only [Spec.Argon2.le32, Spec.Blake2.wordBytes, List.length_map, List.length_range]
  have reprW' : Repr b (Spec.Blake2.init b (min (s.gpr .x23).toNat 64) 0) w.mem (w.gpr .x24)
      (Spec.Argon2.le32 (s.gpr .x23).toNat) := by
    rw [kw.x24]
    simpa only [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, headU] using reprW
  have wrW : (⟨w.gpr .x24, 16384⟩ : Region) ∈ w.wr := by rw [ksw.x24, ksw.wr]; exact hwr
  have dataW : Covers [⟨w.gpr .x20, (w.gpr .x21).toNat⟩] (w.rd ++ w.wr) := by
    rw [r12, r13, ksw.rd, ksw.wr]; exact hdata
  have dwW : (⟨w.gpr .x20, (w.gpr .x21).toNat⟩ : Region).Disjoint ⟨w.gpr .x24, 16384⟩ := by
    rw [r12, r13, ksw.x24]; exact dataWork
  have swW : (below w.sp 16).Disjoint ⟨w.gpr .x24, 16384⟩ := by
    rw [ksw.sp, ksw.x24]; exact stackWork
  have sdW : (below w.sp 16).Disjoint ⟨w.gpr .x20, (w.gpr .x21).toNat⟩ := by
    rw [ksw.sp, r12, r13]; exact stackData
  have inputW : bytesAt w.mem (w.gpr .x20) (w.gpr .x21).toNat =
      bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat := by
    rw [r12, r13]
    exact ksw.bytes _ (show (s.gpr .x21).toNat ≤ 2 ^ 64 by omega)
      (dataWork.sub_right (Region.sub_prefix (by decide))) stackData.symm
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.absorbInput_ok v w _ _ headLen reprW' (by rw [r13]; exact len)
    (by rw [ksw.sp]; exact hsp) wrW dataW dwW swW sdW).mono ?_)
  rintro x ⟨reprX, kx⟩
  have ksx := ksw.trans kx
  have reprX' : Repr b (Spec.Blake2.init b (min (s.gpr .x23).toNat 64) 0) x.mem (x.gpr .x24)
      (Spec.Argon2.le32 (s.gpr .x23).toNat ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat) := by
    rw [kx.x24]; simpa only [inputW] using reprX
  have r13X : x.gpr .x21 = s.gpr .x21 := ksx.regs _ (by decide) (by decide)
  have length : (Spec.Argon2.le32 (s.gpr .x23).toNat ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat).length =
      4 + (x.gpr .x21).toNat := by
    rw [List.length_append, headLen, r13X]
    simp only [bytesAt, List.length_map, List.length_range]
  have wrX : (⟨x.gpr .x24, 16384⟩ : Region) ∈ x.wr := by rw [ksx.x24, ksx.wr]; exact hwr
  have swX : (below x.sp 16).Disjoint ⟨x.gpr .x24, 16384⟩ := by
    rw [ksx.sp, ksx.x24]; exact stackWork
  refine (VG.Proof.Argon2.AArch64.HPrime.finishInput_ok v x _ _ reprX' length (by rw [r13X]; exact len) (by rw [ksx.sp]; exact hsp) wrX swX).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, ksx.trans kt⟩
  have result := congrArg (List.take (min (s.gpr .x23).toNat 64)) out
  rw [ksx.x24] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.Finish`. -/
section
/-! Merged from `Proof.Argon2.AArch64.HPrime.Extend`. -/
section
/-! # H′: the prefixes and final digest of a long output -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem maybeChain_ok (v : Backend) (n lastLen : Nat) (s : State)
    (space : VG.Proof.Argon2.AArch64.HPrime.Space s (32 * n + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen))
    (comparison : s.gpr .x9 = if 32 * n + lastLen < 65 then 1 else 0) :
    WP isa (.ite (.nonzero .x .x9) (.block []) (chain v.hash)) s (VG.Proof.Argon2.AArch64.HPrime.ChainResult s n) := by
  refine WP.ite (decide (32 * n + lastLen < 65)) (by by_cases h : 32 * n + lastLen < 65 <;>
    simp [eval, State.read, comparison, h]) ?_ ?_
  · intro h
    have hn : n = 0 := by have := of_decide_eq_true h; omega
    subst n
    exact WP.block_nil (ChainResult.refl s)
  · intro h
    have hn : 1 ≤ n := by have := of_decide_eq_false h; omega
    have p := space.prefix (show 32 * n ≤ 32 * n + lastLen by omega)
    exact VG.Proof.Argon2.AArch64.HPrime.chain_ok v n lastLen s hn last space.bound space.spBound count p.work p.out p.sep p.stackWork p.stackOut

theorem extendDigest_ok (v : Backend) (n lastLen : Nat) (s : State)
    (space : VG.Proof.Argon2.AArch64.HPrime.Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .x23 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (extendDigest v.hash) s fun t =>
      VG.Proof.Argon2.AArch64.HPrime.Written s ((bytesAt s.mem (s.gpr .x24 + 768) 64).take 32 ++
        chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)) t ∧
      (bytesAt t.mem (s.gpr .x24 + 768) 64).take lastLen =
        Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .x24 + 768) 64)) ∧
      t.gpr .x23 = BitVec.ofNat 64 lastLen := by
  unfold extendDigest
  have short := space.prefix (show 32 ≤ 32 * (n + 1) + lastLen by omega)
  have sep32 := short.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.emitPrefix_ok s short.work short.out sep32).mono ?_)
  intro a ha
  have wa := Written.of_emitted ha
  have lenA : (bytesAt s.mem (s.gpr .x24 + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have spaceA : VG.Proof.Argon2.AArch64.HPrime.Space a (32 * n + lastLen) := space.advance wa (by rw [lenA]; omega)
  have countA : a.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen) := by
    rw [ha.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
      Offset.ofNat_sub_ofNat (by omega : 32 ≤ 32 * (n + 1) + lastLen)]
    rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega]
  have digestA : bytesAt a.mem (a.gpr .x24 + 768) 64 = bytesAt s.mem (s.gpr .x24 + 768) 64 := by
    rw [wa.x24]; exact ha.digest short.sep
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.compare_ok a (by rw [countA, BitVec.toNat_ofNat,
                                   Nat.mod_eq_of_lt (by have := spaceA.bound; omega)]; exact spaceA.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  have countU : u.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen) :=
    (compared.other _ (by decide)).trans countA
  have compareU : u.gpr .x9 = if 32 * n + lastLen < 65 then 1 else 0 := by
    rw [compared.value, countA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceA.bound; omega)]
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.maybeChain_ok v n lastLen u (spaceA.keeps ku) last countU compareU).mono ?_)
  intro w hw
  have ww := (Written.of_chain hw).before_keeps ku
  have digestU : bytesAt u.mem (u.gpr .x24 + 768) 64 = bytesAt s.mem (s.gpr .x24 + 768) 64 := by
    rw [compared.mem, ku.x24]; exact digestA
  have ww' : VG.Proof.Argon2.AArch64.HPrime.Written a (chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)) w := by
    simpa only [digestU] using ww
  have wsw := space.join wa ww' (by rw [lenA, Proof.Argon2.chainPrefixes_length]; omega)
  have produced : ((bytesAt s.mem (s.gpr .x24 + 768) 32) ++
      chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)).length = 32 * (n + 1) := by
    rw [List.length_append, lenA, Proof.Argon2.chainPrefixes_length]; omega
  have spaceW : VG.Proof.Argon2.AArch64.HPrime.Space w lastLen := space.advance wsw (by rw [produced])
  have countW : w.gpr .x23 = BitVec.ofNat 64 lastLen := by
    rw [hw.remaining, countU, Offset.ofNat_sub_ofNat (by omega : 32 * n ≤ 32 * n + lastLen)]
    rw [Nat.add_sub_cancel_left]
  have digestW : bytesAt w.mem (w.gpr .x24 + 768) 64 =
      chainDigest n (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    rw [hw.regs .x24 (by decide) (by decide) (by decide) (by decide), hw.digest, digestU]
  refine WP.seq (wp_mov fun x hx => WP.block_nil ?_)
  have kx : VG.Proof.Argon2.AArch64.HPrime.Keeps w x := Keeps.of_upd hx (by decide)
  have spaceX := spaceW.keeps kx
  have lenX : (x.gpr .x1).toNat = lastLen := by
    rw [hx.gpr, countW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceW.bound; omega)]
  refine (VG.Proof.Argon2.AArch64.HPrime.next_ok v x (by rw [lenX]; omega) spaceX.spBound spaceX.work spaceX.stackWork).mono ?_
  rintro t ⟨dt, kt⟩
  have wwt := Written.of_keeps (kx.trans kt)
  have written := space.join wsw wwt (by rw [produced, List.length_nil]; omega)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.append_nil, VG.Proof.Argon2.AArch64.HPrime.bytesAt_take _ _ 32 64 (by decide)] using written
  · rw [lenX, kx.x24, hx.mem, digestW, wsw.x24] at dt
    exact dt
  · rw [kt.regs _ (by decide) (by decide), kx.regs _ (by decide) (by decide)]; exact countW

theorem longOutput_ok (v : Backend) (n lastLen : Nat) (s : State)
    (space : VG.Proof.Argon2.AArch64.HPrime.Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .x23 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (.seq (extendDigest v.hash) copyRemaining) s fun t =>
      VG.Proof.Argon2.AArch64.HPrime.Written s (Spec.Argon2.longHash lastLen (n + 1) (bytesAt s.mem (s.gpr .x24 + 768) 64)) t := by
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.extendDigest_ok v n lastLen s space last count).mono ?_)
  rintro u ⟨written, digest, remaining⟩
  have len : ((bytesAt s.mem (s.gpr .x24 + 768) 64).take 32 ++
      chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)).length = 32 * (n + 1) := by
    simp only [List.length_append, List.length_take, bytesAt, List.length_map,
      List.length_range, Proof.Argon2.chainPrefixes_length]
    omega
  have spaceU : VG.Proof.Argon2.AArch64.HPrime.Space u lastLen := space.advance written (by rw [len])
  refine (VG.Proof.Argon2.AArch64.HPrime.copyRemaining_ok u lastLen spaceU (by omega) last.2 remaining).mono ?_
  intro t copied
  have out : bytesAt u.mem (u.gpr .x24 + 768) lastLen =
      Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .x24 + 768) 64)) := by
    rw [written.x24, ← VG.Proof.Argon2.AArch64.HPrime.bytesAt_take _ _ lastLen 64 last.2]; exact digest
  have all := space.join written copied (by
    rw [len]; simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl])
  rw [out, ← Proof.Argon2.longHash_chain] at all
  exact all

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: emitting the complete short or long output -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem finishOutput_ok (v : Backend) (s : State) (n : Nat) (input : List Byte)
    (space : VG.Proof.Argon2.AArch64.HPrime.Space s n) (positive : 1 ≤ n) (count : s.gpr .x23 = BitVec.ofNat 64 n)
    (digest : (bytesAt s.mem (s.gpr .x24 + 768) 64).take (min n 64) =
      Spec.Argon2.H (min n 64) (Spec.Argon2.le32 n ++ input)) :
    WP isa (finishOutput v.hash) s (VG.Proof.Argon2.AArch64.HPrime.Written s (Spec.Argon2.hPrime n input)) := by
  unfold finishOutput
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.compare_ok s (by rw [count, BitVec.toNat_ofNat,
                                   Nat.mod_eq_of_lt (by have := space.bound; omega)]; exact space.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  have countU : u.gpr .x23 = BitVec.ofNat 64 n := (compared.other _ (by decide)).trans count
  have compareU : u.gpr .x9 = if n < 65 then 1 else 0 := by
    rw [compared.value, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := space.bound; omega)]
  apply WP.seq
  refine WP.ite (decide (n < 65)) (by by_cases h : n < 65 <;> simp [eval, State.read, compareU, h]) ?_ ?_
  · intro h
    have short : n ≤ 64 := by have := of_decide_eq_true h; omega
    apply WP.block_nil
    refine (VG.Proof.Argon2.AArch64.HPrime.copyRemaining_ok u n (space.keeps ku) positive short countU).mono ?_
    intro t ht
    have result := ht.before_keeps ku
    have value : bytesAt u.mem (u.gpr .x24 + 768) n = Spec.Argon2.hPrime n input := by
      rw [compared.mem, ku.x24, ← VG.Proof.Argon2.AArch64.HPrime.bytesAt_take _ _ n 64 short]
      simpa only [Nat.min_eq_left short, Spec.Argon2.hPrime, ite_eq_left short] using digest
    rw [value] at result
    exact result
  · intro h
    have long : 64 < n := by have := of_decide_eq_false h; omega
    let r := (n + 31) / 32 - 2
    let lastLen := n - 32 * r
    have bounds : 1 ≤ r ∧ 33 ≤ lastLen ∧ lastLen ≤ 64 ∧ 32 * r + lastLen = n :=
      Proof.Argon2.longHash_bounds n long
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
    change r = q + 1 at hq
    have size : 32 * (q + 1) + lastLen = n := by rw [← hq]; exact bounds.2.2.2
    have spaceU : VG.Proof.Argon2.AArch64.HPrime.Space u (32 * (q + 1) + lastLen) := by rw [size]; exact space.keeps ku
    have countLong : u.gpr .x23 = BitVec.ofNat 64 (32 * (q + 1) + lastLen) := by rw [size]; exact countU
    apply WP.seq_iff.mp
    refine (VG.Proof.Argon2.AArch64.HPrime.longOutput_ok v q lastLen u spaceU ⟨bounds.2.1, bounds.2.2.1⟩ countLong).mono ?_
    intro t ht
    have result := ht.before_keeps ku
    have digestU : bytesAt u.mem (u.gpr .x24 + 768) 64 =
        Spec.Argon2.H 64 (Spec.Argon2.le32 n ++ input) := by
      rw [compared.mem, ku.x24]
      simpa only [Nat.min_eq_right (show 64 ≤ n by omega), VG.Proof.Argon2.AArch64.HPrime.bytesAt_take _ _ 64 64 (by decide)] using digest
    have value : Spec.Argon2.longHash lastLen (q + 1) (bytesAt u.mem (u.gpr .x24 + 768) 64) =
        Spec.Argon2.hPrime n input := by
      rw [digestU, ← hq, Spec.Argon2.hPrime, ite_eq_right (show ¬ n ≤ 64 by omega)]
    rw [value] at result
    exact result

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: functional correctness of the complete ARM64 program -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem code_wp (v : Backend) (s : State) (pre : localContract.pre s) :
    WP isa (code v.hash) s fun t => localContract.post s t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      Frame [VG.Proof.Argon2.AArch64.HPrime.outputR s, VG.Proof.Argon2.AArch64.HPrime.workR s, VG.Proof.Argon2.AArch64.HPrime.stackR s] s.mem t.mem := by
  obtain ⟨rd, wr, len, lo, hi, hsp, dw, ow, sd, so, sw⟩ := pre
  have work : (VG.Proof.Argon2.AArch64.HPrime.workR s) ∈ s.wr := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unfold code
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.setup_ok s work).mono ?_)
  intro a ha
  have sp := ha.sp
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by
    rw [ha.workspace, ha.wr]; exact work
  have dataA : Covers [⟨a.gpr .x20, (a.gpr .x21).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.input, ha.length, ha.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  have dwA : (⟨a.gpr .x20, (a.gpr .x21).toNat⟩ : Region).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ha.input, ha.length, ha.workspace]; exact dw
  have swA : (below (a.sp) 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [sp, ha.workspace]; exact sw
  have sdA : (below (a.sp) 16).Disjoint ⟨a.gpr .x20, (a.gpr .x21).toNat⟩ := by
    rw [sp, ha.input, ha.length]; exact sd
  have inputA : bytesAt a.mem (a.gpr .x20) (a.gpr .x21).toNat =
      bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat := by
    rw [ha.input, ha.length, ha.mem]
    apply Proof.Blake2.bytesAt_congr
    intro i hi'
    apply (VG.Proof.Argon2.AArch64.HPrime.setupMem_frame s).bytes (R := VG.Proof.Argon2.AArch64.HPrime.inputR s) _ (show (s.gpr .x1).toNat ≤ 2 ^ 64 by omega) hi'
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact dw.sub_right (Offset.sub_base _ (by decide : 832 + 64 ≤ 16384))
  have headA : bytesAt a.mem (a.gpr .x24 + 832) 4 = Spec.Argon2.le32 (a.gpr .x23).toNat := by
    rw [ha.mem, ha.workspace, ha.remaining]; exact VG.Proof.Argon2.AArch64.HPrime.setupMem_prefix s
  have spaceA : VG.Proof.Argon2.AArch64.HPrime.Space a (s.gpr .x3).toNat := by
    refine ⟨hi, by rw [sp]; exact hsp, workA, ?_, ?_, swA, ?_⟩
    · intro i hi'
      rw [ha.wr, ha.output, wr]
      exact ⟨VG.Proof.Argon2.AArch64.HPrime.outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
    · rw [ha.workspace, ha.output]; exact ow.symm
    · rw [sp, ha.output]; exact so
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.first_ok v a (by rw [ha.remaining]; exact ⟨lo, hi⟩)
    (by rw [ha.length]; exact len) headA (by rw [sp]; exact hsp) workA dataA dwA swA sdA).mono ?_)
  rintro b ⟨digestB, kb⟩
  have spaceB := spaceA.keeps kb
  have countB : b.gpr .x23 = BitVec.ofNat 64 (s.gpr .x3).toNat := by
    rw [kb.regs _ (by decide) (by decide), ha.remaining, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have digestB' : (bytesAt b.mem (b.gpr .x24 + 768) 64).take (min (s.gpr .x3).toNat 64) =
      Spec.Argon2.H (min (s.gpr .x3).toNat 64)
        (Spec.Argon2.le32 (s.gpr .x3).toNat ++ bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) := by
    rw [kb.x24]
    simpa only [ha.remaining, inputA] using digestB
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.finishOutput_ok v b (s.gpr .x3).toNat
    (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) spaceB lo countB digestB').mono ?_)
  intro x hx
  have baseB : b.gpr .x24 = s.gpr .x4 := kb.x24.trans ha.workspace
  have spB : b.sp = s.sp := kb.sp.trans sp
  have dstB : b.gpr .x22 = s.gpr .x2 := (kb.regs _ (by decide) (by decide)).trans ha.output
  have wrX : x.wr = s.wr := hx.wr.trans (kb.wr.trans ha.wr)
  have frame : Frame [⟨s.gpr .x4, 832⟩, VG.Proof.Argon2.AArch64.HPrime.stackR s, VG.Proof.Argon2.AArch64.HPrime.outputR s] a.mem x.mem := by
    have fb : Frame [⟨s.gpr .x4, 832⟩, VG.Proof.Argon2.AArch64.HPrime.stackR s, VG.Proof.Argon2.AArch64.HPrime.outputR s] a.mem b.mem := by
      apply kb.frame.sub
      intro r hr
      rw [ha.workspace, sp] at hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    exact fb.trans (by simpa only [baseB, spB, dstB, VG.Proof.Argon2.AArch64.HPrime.stackR, VG.Proof.Argon2.AArch64.HPrime.outputR, Proof.Argon2.hPrime_length] using hx.frame)
  have values : ∀ r d, (r, d) ∈ saved →
      x.mem.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hr
    have bounds : ∀ rd ∈ saved, 832 ≤ rd.2 ∧ rd.2 + 8 ≤ 16384 := by decide
    obtain ⟨dlo, dhi⟩ := bounds (r, d) hr
    have keep : x.mem.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 =
        a.mem.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 := by
      apply frame.readW (r := ⟨s.gpr .x4 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact (Offset.base_disjoint _ dlo (by omega)).symm
      · exact (sw.sub_right (Offset.sub_base _ dhi)).symm
      · exact (ow.sub_right (Offset.sub_base _ dhi)).symm
    rw [keep, ha.mem]; exact VG.Proof.Argon2.AArch64.HPrime.setupMem_saved s r d hr
  have baseX := hx.x24.trans baseB
  have spX := hx.sp.trans spB
  have readable : VG.Proof.Argon2.AArch64.HPrime.workR s ∈ x.rd ++ x.wr := List.mem_append_right _ (wrX.symm ▸ work)
  refine (VG.Proof.Argon2.AArch64.HPrime.restore_ok s x baseX (by
    intro r hr
    have hp : r ∈ preserved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h30 : r ≠ .x30 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h22 : r ≠ .x22 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h23 : r ≠ .x23 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [hx.regs r hp h30 h22 h23, kb.regs r hp h30]
    exact ha.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) h22 h23) readable values).mono ?_
  rintro t ⟨regs, mem, _, _⟩
  refine ⟨?_, regs, ?_⟩
  · change bytesAt t.mem (s.gpr .x2) (s.gpr .x3).toNat = _
    rw [mem]
    simpa only [dstB, Proof.Argon2.hPrime_length] using hx.bytes
  · rw [mem]
    have setupFrame : Frame [VG.Proof.Argon2.AArch64.HPrime.outputR s, VG.Proof.Argon2.AArch64.HPrime.workR s, VG.Proof.Argon2.AArch64.HPrime.stackR s] s.mem a.mem := by
      rw [ha.mem]
      apply (VG.Proof.Argon2.AArch64.HPrime.setupMem_frame s).sub
      intro r hr
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨VG.Proof.Argon2.AArch64.HPrime.workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        Offset.sub_base _ (by decide : 832 + 64 ≤ 16384)⟩
    apply setupFrame.trans
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Argon2.AArch64.HPrime.workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.Argon2.AArch64.HPrime.stackR s, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
    · exact ⟨VG.Proof.Argon2.AArch64.HPrime.outputR s, List.mem_cons_self .., fun _ h => h⟩

theorem code_keepsV (v : Backend) : (code v.hash).allInstrs keepsV = true := by
  simp only [code, setup, saved, first, chooseLength, Impl.Argon2.AArch64.HPrime.init,
    initArgs, absorbFixed, fixedArgs, Impl.Argon2.AArch64.HPrime.update, updateArgs,
    absorbInput, inputArgs, finishInput, Impl.Argon2.AArch64.HPrime.finalize, finalizeArgs,
    finishOutput, extendDigest, emitPrefix, copy, copyByte, chain, next, copyRemaining,
    restore, Code.allInstrs]
  rw [v.initV, v.updateV, v.finalizeV]
  decide +kernel

theorem code_correct (v : Backend) (s : State) (pre : localContract.pre s) :
    ∃ tr t, Exec isa (code v.hash) s tr t ∧ abiPreserved s t ∧ localContract.post s t := by
  obtain ⟨tr, t, run, post, regs, _⟩ := VG.Proof.Argon2.AArch64.HPrime.code_wp v s pre
  exact ⟨tr, t, run, ⟨regs, VG.AArch64.Exec.sp run,
    VG.AArch64.Exec.preservedV run (VG.Proof.Argon2.AArch64.HPrime.code_keepsV v)⟩, post⟩

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT`. -/
section

/-! # Composition helpers for ARM64 H′ timing proofs -/

namespace VG.AArch64

theorem RelCT.taintRegs {τ : Taint.T} {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ s₁ s₂, P s₁ s₂ → Taint.Agree τ s₁ s₂) (rs : List Reg) {hc : VG.Taint.Hint Taint.T}
    (h : ((taint.check τ c hc).map fun τ' => (RegSet.ofList rs).subset τ') = some true) :
    RelCT isa P c fun s t => s.sp = t.sp ∧ ∀ r ∈ rs, s.gpr r = t.gpr r := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (hp _ _ hP) e₁ e₂
  exact ⟨ht, ha.1, fun r hr => ha.2 r (RegSet.mem_of_subset hs (RegSet.mem_ofList.mpr hr))⟩

end VG.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.FixedCT`. -/
section

/-! Merged from `Proof.Argon2.AArch64.HPrime.UpdateCT`. -/
section
/-! # H′: constant time of a BLAKE2b update -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure UpdateReady (s : State) : Prop where
  spBound : 16 ≤ s.sp.toNat
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  data : Covers [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] (s.rd ++ s.wr)
  dataState : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 192⟩
  dataScratch : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨s.gpr .x24 + 192, 576⟩
  stackWork : (below (s.sp) 16).Disjoint ⟨s.gpr .x24, 16384⟩
  stackData : (below (s.sp) 16).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩

theorem update_keeps (v : Backend) (s : State) (h : VG.Proof.Argon2.AArch64.HPrime.UpdateReady s) :
    WP isa (update v.hash) s (VG.Proof.Argon2.AArch64.HPrime.Keeps s) := by
  unfold update
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.updateArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := VG.Proof.Argon2.AArch64.HPrime.update_call_hyps s u hu h.spBound h.work h.data
    h.dataState h.dataScratch h.stackWork h.stackData
  refine WP.callF (k := Proof.Blake2.updateAArch64 Spec.Blake2.b) v.updateCorrect
    pre cover writes ?_ (by rw [v.ok.updateDepth]; decide)
  intro t rd wr sp frame regs _
  refine ⟨fun r hr h30 => ?_, rd.trans hu.rd, wr.trans hu.wr, sp.trans hu.sp, ?_⟩
  · have hn : r ≠ .x0 ∧ r ≠ .x4 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (regs r hr h30).trans (hu.other r hn.1 hn.2)
  · apply VG.Proof.Argon2.AArch64.HPrime.update_frame
    simpa only [v.ok.updateDepth, hu.sp, hu.mem,
      List.cons_append, List.nil_append] using frame

theorem update_rel (v : Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.Argon2.AArch64.HPrime.UpdateReady s₁ ∧ VG.Proof.Argon2.AArch64.HPrime.UpdateReady s₂ ∧
      s₁.gpr .x24 = s₂.gpr .x24 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (update v.hash) fun _ _ => True := by
  have args := (RelCT.taint (A := VG.AArch64.taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨(hP _ _ hp).2.2.2.2.2.2, by simp [Taint.ofRegs]⟩) (c := .block updateArgs) (by taint_decide)).wpDep
    (F := VG.Proof.Argon2.AArch64.HPrime.UpdateArgs) fun s₁ s₂ _ => ⟨VG.Proof.Argon2.AArch64.HPrime.updateArgs_ok s₁, VG.Proof.Argon2.AArch64.HPrime.updateArgs_ok s₂⟩
  have call := RelCT.callEx (n := v.hash.updateName) (k := Proof.Blake2.updateAArch64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ VG.Proof.Argon2.AArch64.HPrime.UpdateArgs σ₁ s₁ ∧ VG.Proof.Argon2.AArch64.HPrime.UpdateArgs σ₂ s₂)
    v.updateCorrect v.updateCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, data, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := VG.Proof.Argon2.AArch64.HPrime.update_call_hyps σ₁ s₁ h₁ p₁.spBound p₁.work p₁.data
        p₁.dataState p₁.dataScratch p₁.stackWork p₁.stackData
      obtain ⟨pre₂, cover₂, writes₂⟩ := VG.Proof.Argon2.AArch64.HPrime.update_call_hyps σ₂ s₂ h₂ p₂.spBound p₂.work p₂.data
        p₂.dataState p₂.dataScratch p₂.stackWork p₂.stackData
      have sp' : s₁.sp = s₂.sp := h₁.sp.trans (sp.trans h₂.sp.symm)
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂⟩
      simp only [Proof.Blake2.updateAArch64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), State.callEntry_sp, State.withRegions_sp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), count],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), data],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), len],
        by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.RelatedCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.HPrime.InitCT`. -/
section
/-! # H′: constant time of BLAKE2b initialization -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure InitReady (s : State) : Prop where
  length : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.sp) 8).Disjoint ⟨s.gpr .x24, 192⟩

theorem init_keeps (v : Backend) (s : State) (h : VG.Proof.Argon2.AArch64.HPrime.InitReady s) :
    WP isa (init v.hash) s (VG.Proof.Argon2.AArch64.HPrime.Keeps s) :=
  (VG.Proof.Argon2.AArch64.HPrime.init_ok v s h.length h.work).mono fun _ ⟨_, regs, rd, wr, sp, frame⟩ =>
    ⟨regs, rd, wr, sp, VG.Proof.Argon2.AArch64.HPrime.init_frame _ _ frame⟩

theorem init_rel (v : Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.Argon2.AArch64.HPrime.InitReady s₁ ∧ VG.Proof.Argon2.AArch64.HPrime.InitReady s₂ ∧
      s₁.gpr .x24 = s₂.gpr .x24 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (init v.hash) fun _ _ => True := by
  have args := (RelCT.taint (A := VG.AArch64.taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨(hP _ _ hp).2.2.2.2, by simp [Taint.ofRegs]⟩) (c := .block initArgs) (by taint_decide)).wpDep
    (F := VG.Proof.Argon2.AArch64.HPrime.InitArgs) fun s₁ s₂ _ => ⟨VG.Proof.Argon2.AArch64.HPrime.initArgs_ok s₁, VG.Proof.Argon2.AArch64.HPrime.initArgs_ok s₂⟩
  have call := RelCT.callEx (n := v.hash.initName) (k := Proof.Blake2.initAArch64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ VG.Proof.Argon2.AArch64.HPrime.InitArgs σ₁ s₁ ∧ VG.Proof.Argon2.AArch64.HPrime.InitArgs σ₂ s₂)
    v.initCorrect v.initCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := VG.Proof.Argon2.AArch64.HPrime.init_call_hyps σ₁ s₁ h₁ p₁.length p₁.work
      obtain ⟨pre₂, cover₂, writes₂⟩ := VG.Proof.Argon2.AArch64.HPrime.init_call_hyps σ₂ s₂ h₂ p₂.length p₂.work
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂⟩
      · simp only [Proof.Blake2.initAArch64, State.withRegions_gpr,
          State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
          State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
          State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
          State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs)]
        exact ⟨by rw [h₁.state, h₂.state, base],
          by rw [h₁.other _ (by decide) (by decide) (by decide),
            h₂.other _ (by decide) (by decide) (by decide), len],
          by rw [h₁.key, h₂.key, base], by rw [h₁.keylen, h₂.keylen], h₁.sp.trans (sp.trans h₂.sp.symm)⟩
  exact args.seq call

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.FinalizeCT`. -/
section
/-! # H′: constant time of BLAKE2b finalization -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure FinalizeReady (s : State) : Prop where
  spBound : 16 ≤ s.sp.toNat
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.sp) 16).Disjoint ⟨s.gpr .x24, 16384⟩

theorem FinalizeReady.keeps {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.FinalizeReady s) (k : VG.Proof.Argon2.AArch64.HPrime.Keeps s t) : VG.Proof.Argon2.AArch64.HPrime.FinalizeReady t := by
  refine ⟨by rw [k.sp]; exact h.spBound, ?_, ?_⟩
  · rw [k.wr, k.x24]; exact h.work
  · rw [k.sp, k.x24]; exact h.stack

theorem finalize_keeps (v : Backend) (s : State) (h : VG.Proof.Argon2.AArch64.HPrime.FinalizeReady s) :
    WP isa (finalize v.hash) s (VG.Proof.Argon2.AArch64.HPrime.Keeps s) := by
  unfold finalize
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.finalizeArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := VG.Proof.Argon2.AArch64.HPrime.finalize_call_hyps s u hu h.spBound h.work h.stack
  refine WP.callF (k := Proof.Blake2.finalizeAArch64 Spec.Blake2.b) v.finalizeCorrect
    pre cover writes ?_ (by rw [v.ok.finalizeDepth]; decide)
  intro t rd wr sp frame regs _
  refine ⟨fun r hr h30 => ?_, rd.trans hu.rd, wr.trans hu.wr, sp.trans hu.sp, ?_⟩
  · have hn : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (regs r hr h30).trans (hu.other r hn.1 hn.2.1 hn.2.2)
  · apply VG.Proof.Argon2.AArch64.HPrime.finalize_frame
    simpa only [v.ok.finalizeDepth, hu.sp, hu.mem,
      List.cons_append, List.nil_append] using frame

theorem finalize_rel (v : Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.Argon2.AArch64.HPrime.FinalizeReady s₁ ∧ VG.Proof.Argon2.AArch64.HPrime.FinalizeReady s₂ ∧
      s₁.gpr .x24 = s₂.gpr .x24 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp) :
    RelCT isa P (finalize v.hash) fun _ _ => True := by
  have args := (RelCT.taint (A := VG.AArch64.taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨(hP _ _ hp).2.2.2.2, by simp [Taint.ofRegs]⟩) (c := .block finalizeArgs) (by taint_decide)).wpDep
    (F := VG.Proof.Argon2.AArch64.HPrime.FinalizeArgs) fun s₁ s₂ _ => ⟨VG.Proof.Argon2.AArch64.HPrime.finalizeArgs_ok s₁, VG.Proof.Argon2.AArch64.HPrime.finalizeArgs_ok s₂⟩
  have call := RelCT.callEx (n := v.hash.finalizeName) (k := Proof.Blake2.finalizeAArch64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ VG.Proof.Argon2.AArch64.HPrime.FinalizeArgs σ₁ s₁ ∧ VG.Proof.Argon2.AArch64.HPrime.FinalizeArgs σ₂ s₂)
    v.finalizeCorrect v.finalizeCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := VG.Proof.Argon2.AArch64.HPrime.finalize_call_hyps σ₁ s₁ h₁ p₁.spBound p₁.work p₁.stack
      obtain ⟨pre₂, cover₂, writes₂⟩ := VG.Proof.Argon2.AArch64.HPrime.finalize_call_hyps σ₂ s₂ h₂ p₂.spBound p₂.work p₂.stack
      have sp' : s₁.sp = s₂.sp := h₁.sp.trans (sp.trans h₂.sp.symm)
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂⟩
      simp only [Proof.Blake2.finalizeAArch64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), State.callEntry_sp, State.withRegions_sp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), count],
        by rw [h₁.digest, h₂.digest, base], by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.BlocksCT`. -/
section
/-! # H′: constant time of public argument handling and copying -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

def publicRegs : List Reg := [.x24, .x20, .x21, .x22, .x23]
def AgreeRegs (rs : List Reg) (s t : State) : Prop :=
  s.sp = t.sp ∧ ∀ r ∈ rs, s.gpr r = t.gpr r

theorem AgreeRegs.taint {rs : List Reg} {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.AgreeRegs rs s t) :
    AArch64.Taint.Agree (Taint.ofRegs rs) s t :=
  ⟨h.1, fun r hr => h.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem publicRegs_callee : ∀ r ∈ VG.Proof.Argon2.AArch64.HPrime.publicRegs, r ∈ preserved := by decide

theorem publicRegs_not_link : ∀ r ∈ VG.Proof.Argon2.AArch64.HPrime.publicRegs, r ≠ .x30 := by decide

theorem setup_rel :
    RelCT isa (VG.Proof.Argon2.AArch64.HPrime.AgreeRegs [.x0, .x1, .x2, .x3, .x4]) (.block setup)
      (VG.Proof.Argon2.AArch64.HPrime.AgreeRegs VG.Proof.Argon2.AArch64.HPrime.publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ hp => hp.taint) VG.Proof.Argon2.AArch64.HPrime.publicRegs (by taint_decide)

theorem chooseLength_rel : RelCT isa (VG.Proof.Argon2.AArch64.HPrime.AgreeRegs VG.Proof.Argon2.AArch64.HPrime.publicRegs) chooseLength
    (VG.Proof.Argon2.AArch64.HPrime.AgreeRegs (.x1 :: VG.Proof.Argon2.AArch64.HPrime.publicRegs)) :=
  RelCT.taintRegs (τ := Taint.ofRegs VG.Proof.Argon2.AArch64.HPrime.publicRegs)
    (fun _ _ hp => hp.taint) (.x1 :: VG.Proof.Argon2.AArch64.HPrime.publicRegs) (by taint_decide)

theorem copy_rel : RelCT isa (VG.Proof.Argon2.AArch64.HPrime.AgreeRegs (.x8 :: VG.Proof.Argon2.AArch64.HPrime.publicRegs)) copy (VG.Proof.Argon2.AArch64.HPrime.AgreeRegs VG.Proof.Argon2.AArch64.HPrime.publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs (.x8 :: VG.Proof.Argon2.AArch64.HPrime.publicRegs))
    (fun _ _ hp => hp.taint) VG.Proof.Argon2.AArch64.HPrime.publicRegs (by taint_decide)

theorem emitPrefix_rel : RelCT isa (VG.Proof.Argon2.AArch64.HPrime.AgreeRegs VG.Proof.Argon2.AArch64.HPrime.publicRegs) emitPrefix (VG.Proof.Argon2.AArch64.HPrime.AgreeRegs VG.Proof.Argon2.AArch64.HPrime.publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs VG.Proof.Argon2.AArch64.HPrime.publicRegs)
    (fun _ _ hp => hp.taint) VG.Proof.Argon2.AArch64.HPrime.publicRegs (by taint_decide)

theorem copyRemaining_rel : RelCT isa (VG.Proof.Argon2.AArch64.HPrime.AgreeRegs VG.Proof.Argon2.AArch64.HPrime.publicRegs) copyRemaining (VG.Proof.Argon2.AArch64.HPrime.AgreeRegs VG.Proof.Argon2.AArch64.HPrime.publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs VG.Proof.Argon2.AArch64.HPrime.publicRegs)
    (fun _ _ hp => hp.taint) VG.Proof.Argon2.AArch64.HPrime.publicRegs (by taint_decide)

theorem restore_rel : RelCT isa (VG.Proof.Argon2.AArch64.HPrime.AgreeRegs [.x24]) (.block restore) fun _ _ => True :=
  RelCT.taint (A := VG.AArch64.taint) (Taint.ofRegs [.x24]) (fun _ _ hp => hp.taint)
    (by taint_decide)

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: retaining public caller state across hash calls -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

/-- Caller conditions that survive hashing in the workspace. -/
structure Stable (F : State → Prop) : Prop where
  ready : ∀ s, F s → VG.Proof.Argon2.AArch64.HPrime.FinalizeReady s
  keeps : ∀ s t, F s → VG.Proof.Argon2.AArch64.HPrime.Keeps s t → F t

def Related (F : State → Prop) (s t : State) : Prop := F s ∧ F t ∧ VG.Proof.Argon2.AArch64.HPrime.AgreeRegs VG.Proof.Argon2.AArch64.HPrime.publicRegs s t

theorem Related.keeps {F : State → Prop} (stable : VG.Proof.Argon2.AArch64.HPrime.Stable F) {s₁ s₂ t₁ t₂ : State}
    (h : VG.Proof.Argon2.AArch64.HPrime.Related F s₁ s₂) (k₁ : VG.Proof.Argon2.AArch64.HPrime.Keeps s₁ t₁) (k₂ : VG.Proof.Argon2.AArch64.HPrime.Keeps s₂ t₂) : VG.Proof.Argon2.AArch64.HPrime.Related F t₁ t₂ := by
  refine ⟨stable.keeps _ _ h.1 k₁, stable.keeps _ _ h.2.1 k₂,
    k₁.sp.trans (h.2.2.1.trans k₂.sp.symm), fun r hr => ?_⟩
  rw [k₁.regs _ (VG.Proof.Argon2.AArch64.HPrime.publicRegs_callee r hr) (VG.Proof.Argon2.AArch64.HPrime.publicRegs_not_link r hr), k₂.regs _ (VG.Proof.Argon2.AArch64.HPrime.publicRegs_callee r hr) (VG.Proof.Argon2.AArch64.HPrime.publicRegs_not_link r hr)]
  exact h.2.2.2 r hr

theorem keeps_rel {F : State → Prop} (stable : VG.Proof.Argon2.AArch64.HPrime.Stable F) {P : State → State → Prop} {c : Prog isa}
    (ct : RelCT isa P c fun _ _ => True)
    (wp : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ (VG.Proof.Argon2.AArch64.HPrime.Keeps s₁) ∧ WP isa c s₂ (VG.Proof.Argon2.AArch64.HPrime.Keeps s₂))
    (pre : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.Argon2.AArch64.HPrime.Related F s₁ s₂) : RelCT isa P c (VG.Proof.Argon2.AArch64.HPrime.Related F) :=
  (ct.wpDep wp).mono (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, k₁, k₂⟩ =>
    (pre _ _ hp).keeps stable k₁ k₂

theorem stable_init_rel (v : Backend) {F : State → Prop} (stable : VG.Proof.Argon2.AArch64.HPrime.Stable F) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related F s₁ s₂ ∧
      (1 ≤ (s₁.gpr .x1).toNat ∧ (s₁.gpr .x1).toNat ≤ 64) ∧ s₁.gpr .x1 = s₂.gpr .x1)
      (init v.hash) (VG.Proof.Argon2.AArch64.HPrime.Related F) := by
  have ready (s : State) (hs : F s) (len : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 64) :
      VG.Proof.Argon2.AArch64.HPrime.InitReady s := by
    have h := stable.ready s hs
    exact ⟨len, h.work, (h.stack.sub_left (below_sub (by decide) (by decide))).sub_right
      (Region.sub_prefix (by decide))⟩
  apply VG.Proof.Argon2.AArch64.HPrime.keeps_rel stable (VG.Proof.Argon2.AArch64.HPrime.init_rel v ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨ready s₁ h.1 len, ready s₂ h.2.1 (by rw [← eq]; exact len),
      h.2.2.2 _ (by decide), eq, h.2.2.1⟩
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨VG.Proof.Argon2.AArch64.HPrime.init_keeps v s₁ (ready s₁ h.1 len),
      VG.Proof.Argon2.AArch64.HPrime.init_keeps v s₂ (ready s₂ h.2.1 (by rw [← eq]; exact len))⟩

theorem stable_finalize_rel (v : Backend) {F : State → Prop} (stable : VG.Proof.Argon2.AArch64.HPrime.Stable F) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related F s₁ s₂ ∧ s₁.gpr .x1 = s₂.gpr .x1)
      (finalize v.hash) (VG.Proof.Argon2.AArch64.HPrime.Related F) := by
  apply VG.Proof.Argon2.AArch64.HPrime.keeps_rel stable (VG.Proof.Argon2.AArch64.HPrime.finalize_rel v ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, count⟩
    exact ⟨stable.ready _ h.1, stable.ready _ h.2.1,
      h.2.2.2 _ (by decide), count, h.2.2.1⟩
  · intro s₁ s₂ ⟨h, _⟩
    exact ⟨VG.Proof.Argon2.AArch64.HPrime.finalize_keeps v s₁ (stable.ready _ h.1), VG.Proof.Argon2.AArch64.HPrime.finalize_keeps v s₂ (stable.ready _ h.2.1)⟩

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: constant time of hashing a fixed workspace buffer -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem FixedArgs.keeps {s t : State} {offset size : Nat} (h : VG.Proof.Argon2.AArch64.HPrime.FixedArgs s t offset size) : VG.Proof.Argon2.AArch64.HPrime.Keeps s t := by
  refine ⟨fun r hr _ => ?_, h.rd, h.wr, h.sp, ?_⟩
  · have hn : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r hn.1 hn.2.1 hn.2.2
  · rw [h.mem]; exact Frame.refl _ _

theorem fixed_ready {s t : State} {offset size : Nat} (ready : VG.Proof.Argon2.AArch64.HPrime.FinalizeReady s)
    (h : VG.Proof.Argon2.AArch64.HPrime.FixedArgs s t offset size) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    VG.Proof.Argon2.AArch64.HPrime.UpdateReady t := by
  have k := h.keeps
  have len : (t.gpr .x3).toNat = size := by
    rw [h.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨(ready.keeps k).spBound, (ready.keeps k).work, ?_, ?_, ?_, (ready.keeps k).stack, ?_⟩
  · apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .x24, 16384⟩, List.mem_append_right _ (k.wr.symm ▸ ready.work), offset, h.data, ?_⟩
    change offset + (t.gpr .x3).toNat ≤ 16384
    rw [len]; exact hi
  · rw [h.data, len, k.x24]
    exact (Offset.base_disjoint _ (by omega) (by omega)).symm
  · rw [h.data, len, k.x24]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega) (by omega) (by decide)
  · rw [k.sp, h.data, len]
    exact ready.stack.sub_right (Offset.sub_base _ hi)

theorem absorbFixed_keeps (v : Backend) (s : State) (offset size : Nat)
    (ready : VG.Proof.Argon2.AArch64.HPrime.FinalizeReady s) (offsetBound : offset < 4096) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    WP isa (absorbFixed v.hash offset size) s (VG.Proof.Argon2.AArch64.HPrime.Keeps s) := by
  unfold absorbFixed
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.fixedArgs_ok s offset size offsetBound (by omega)).mono fun u hu => ?_)
  exact (VG.Proof.Argon2.AArch64.HPrime.update_keeps v u (VG.Proof.Argon2.AArch64.HPrime.fixed_ready ready hu lo hi)).mono fun _ h => hu.keeps.trans h

theorem absorbFixed_rel (v : Backend) (offset size : Nat)
    (offsetBound : offset < 4096) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384)
    (ct : ∃ hint, (taint.check (Taint.ofRegs []) (.block (fixedArgs offset size)) hint).isSome = true)
    {F : State → Prop} (stable : VG.Proof.Argon2.AArch64.HPrime.Stable F) :
    RelCT isa (VG.Proof.Argon2.AArch64.HPrime.Related F) (absorbFixed v.hash offset size) (VG.Proof.Argon2.AArch64.HPrime.Related F) := by
  obtain ⟨_, ct⟩ := ct
  have args := (RelCT.taint (A := VG.AArch64.taint) (P := VG.Proof.Argon2.AArch64.HPrime.Related F) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩) (c := .block (fixedArgs offset size))
    ct).wpDep (F := fun s t => VG.Proof.Argon2.AArch64.HPrime.FixedArgs s t offset size)
    fun s₁ s₂ _ => ⟨VG.Proof.Argon2.AArch64.HPrime.fixedArgs_ok s₁ offset size offsetBound (by omega),
      VG.Proof.Argon2.AArch64.HPrime.fixedArgs_ok s₂ offset size offsetBound (by omega)⟩
  have call := VG.Proof.Argon2.AArch64.HPrime.update_rel v (P := fun s₁ s₂ => True ∧
      ∃ σ₁ σ₂, VG.Proof.Argon2.AArch64.HPrime.Related F σ₁ σ₂ ∧ VG.Proof.Argon2.AArch64.HPrime.FixedArgs σ₁ s₁ offset size ∧ VG.Proof.Argon2.AArch64.HPrime.FixedArgs σ₂ s₂ offset size)
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      have base := hp.2.2.2 .x24 (by decide)
      have sp := hp.2.2.1
      exact ⟨VG.Proof.Argon2.AArch64.HPrime.fixed_ready (stable.ready _ hp.1) h₁ lo hi, VG.Proof.Argon2.AArch64.HPrime.fixed_ready (stable.ready _ hp.2.1) h₂ lo hi,
        by rw [h₁.keeps.x24, h₂.keeps.x24, base], by rw [h₁.count, h₂.count],
        by rw [h₁.data, h₂.data, base], by rw [h₁.size, h₂.size], by rw [h₁.keeps.sp, h₂.keeps.sp, sp]⟩
  exact VG.Proof.Argon2.AArch64.HPrime.keeps_rel stable (args.seq call)
    (fun s₁ s₂ hp => ⟨VG.Proof.Argon2.AArch64.HPrime.absorbFixed_keeps v s₁ offset size (stable.ready _ hp.1) offsetBound lo hi,
      VG.Proof.Argon2.AArch64.HPrime.absorbFixed_keeps v s₂ offset size (stable.ready _ hp.2.1) offsetBound lo hi⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Verified`. -/
section

/-! Merged from `Proof.Argon2.AArch64.HPrime.OutputCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.HPrime.NextCT`. -/
section
/-! # H′: constant time of hashing the previous digest -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_movz)

theorem count64_ok (s : State) : WP isa (.block [.movz .x .x1 64 0]) s fun t =>
    VG.Proof.Argon2.AArch64.HPrime.Keeps s t ∧ t.gpr .x1 = 64 := by
  refine wp_movz fun t ht => WP.block_nil ⟨?_, ht.gpr⟩
  refine ⟨fun r hr _ => ?_, ht.rd, ht.wr, ht.sp, ?_⟩
  · have hn : r ≠ .x1 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ht.other r hn
  · rw [ht.mem]; exact Frame.refl _ _

theorem count64_rel {F : State → Prop} (stable : VG.Proof.Argon2.AArch64.HPrime.Stable F) :
    RelCT isa (VG.Proof.Argon2.AArch64.HPrime.Related F) (.block [.movz .x .x1 64 0])
      (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related F s₁ s₂ ∧ s₁.gpr .x1 = s₂.gpr .x1) := by
  have ct := (RelCT.taint (A := VG.AArch64.taint) (P := VG.Proof.Argon2.AArch64.HPrime.Related F) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩) (c := .block [.movz .x .x1 64 0])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨VG.Proof.Argon2.AArch64.HPrime.count64_ok s₁, VG.Proof.Argon2.AArch64.HPrime.count64_ok s₂⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, k₁, k₂⟩ =>
    ⟨hp.keeps stable k₁.1 k₂.1, k₁.2.trans k₂.2.symm⟩

theorem next_rel (v : Backend) {F : State → Prop} (stable : VG.Proof.Argon2.AArch64.HPrime.Stable F) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related F s₁ s₂ ∧
      (1 ≤ (s₁.gpr .x1).toNat ∧ (s₁.gpr .x1).toNat ≤ 64) ∧ s₁.gpr .x1 = s₂.gpr .x1)
      (next v.hash) (VG.Proof.Argon2.AArch64.HPrime.Related F) :=
  (VG.Proof.Argon2.AArch64.HPrime.stable_init_rel v stable).seq
    ((VG.Proof.Argon2.AArch64.HPrime.absorbFixed_rel v 768 64 (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩ stable).seq
      ((VG.Proof.Argon2.AArch64.HPrime.count64_rel stable).seq (VG.Proof.Argon2.AArch64.HPrime.stable_finalize_rel v stable)))

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.InputCT`. -/
section
/-! # H′: public input bounds and constant-time absorption -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

structure OutputReady (s : State) : Prop where
  space : VG.Proof.Argon2.AArch64.HPrime.Space s (s.gpr .x23).toNat
  positive : 1 ≤ (s.gpr .x23).toNat
  bound : (s.gpr .x23).toNat < 2 ^ 32

theorem output_stable : VG.Proof.Argon2.AArch64.HPrime.Stable VG.Proof.Argon2.AArch64.HPrime.OutputReady where
  ready _ h := ⟨h.space.spBound, h.space.work, h.space.stackWork⟩
  keeps s t h k := by
    have n := k.regs .x23 (by decide) (by decide)
    refine ⟨?_, ?_, ?_⟩
    · rw [n]; exact h.space.keeps k
    · rw [n]; exact h.positive
    · rw [n]; exact h.bound

structure FirstReady (s : State) : Prop extends VG.Proof.Argon2.AArch64.HPrime.OutputReady s where
  length : (s.gpr .x21).toNat < 2 ^ 32
  data : Covers [⟨s.gpr .x20, (s.gpr .x21).toNat⟩] (s.rd ++ s.wr)
  dataWork : (⟨s.gpr .x20, (s.gpr .x21).toNat⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩
  stackData : (below s.sp 16).Disjoint ⟨s.gpr .x20, (s.gpr .x21).toNat⟩

theorem first_stable : VG.Proof.Argon2.AArch64.HPrime.Stable VG.Proof.Argon2.AArch64.HPrime.FirstReady where
  ready _ h := output_stable.ready _ h.toOutputReady
  keeps s t h k := by
    have ptr := k.regs .x20 (by decide) (by decide)
    have len := k.regs .x21 (by decide) (by decide)
    refine ⟨output_stable.keeps s t h.toOutputReady k, ?_, ?_, ?_, ?_⟩
    · rw [len]; exact h.length
    · rw [ptr, len, k.rd, k.wr]; exact h.data
    · rw [ptr, len, k.x24]; exact h.dataWork
    · rw [ptr, len, k.sp]; exact h.stackData

theorem input_ready {s t : State} (ready : VG.Proof.Argon2.AArch64.HPrime.FirstReady s) (h : VG.Proof.Argon2.AArch64.HPrime.InputArgs s t) : VG.Proof.Argon2.AArch64.HPrime.UpdateReady t := by
  have k := h.keeps
  refine ⟨(first_stable.ready _ (first_stable.keeps _ _ ready k)).spBound,
    (first_stable.ready _ (first_stable.keeps _ _ ready k)).work, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.data, h.size, h.rd, h.wr]; exact ready.data
  · rw [h.data, h.size, k.x24]; exact ready.dataWork.sub_right (Region.sub_prefix (by decide))
  · rw [h.data, h.size, k.x24]; exact ready.dataWork.sub_right (Offset.sub_base _ (by decide))
  · rw [k.x24, k.sp]; exact ready.space.stackWork
  · rw [h.data, h.size, k.sp]; exact ready.stackData

theorem absorbInput_keeps (v : Backend) (s : State) (h : VG.Proof.Argon2.AArch64.HPrime.FirstReady s) :
    WP isa (absorbInput v.hash) s (VG.Proof.Argon2.AArch64.HPrime.Keeps s) := by
  unfold absorbInput
  refine WP.seq ((VG.Proof.Argon2.AArch64.HPrime.inputArgs_ok s).mono fun u hu => ?_)
  exact (VG.Proof.Argon2.AArch64.HPrime.update_keeps v u (VG.Proof.Argon2.AArch64.HPrime.input_ready h hu)).mono fun _ ht => hu.keeps.trans ht

theorem absorbInput_rel (v : Backend) :
    RelCT isa (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.FirstReady) (absorbInput v.hash) (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.FirstReady) := by
  have args := (RelCT.taint (A := VG.AArch64.taint) (P := VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.FirstReady) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩) (c := .block inputArgs) (by taint_decide)).wpDep
    (F := VG.Proof.Argon2.AArch64.HPrime.InputArgs) fun s₁ s₂ _ => ⟨VG.Proof.Argon2.AArch64.HPrime.inputArgs_ok s₁, VG.Proof.Argon2.AArch64.HPrime.inputArgs_ok s₂⟩
  have call := VG.Proof.Argon2.AArch64.HPrime.update_rel v (P := fun s₁ s₂ => True ∧
      ∃ σ₁ σ₂, VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.FirstReady σ₁ σ₂ ∧ VG.Proof.Argon2.AArch64.HPrime.InputArgs σ₁ s₁ ∧ VG.Proof.Argon2.AArch64.HPrime.InputArgs σ₂ s₂)
    fun _ _ ⟨_, _, _, hp, h₁, h₂⟩ => by
      exact ⟨VG.Proof.Argon2.AArch64.HPrime.input_ready hp.1 h₁, VG.Proof.Argon2.AArch64.HPrime.input_ready hp.2.1 h₂,
        by rw [h₁.keeps.x24, h₂.keeps.x24]; exact hp.2.2.2 _ (by decide),
        by rw [h₁.count, h₂.count],
        by rw [h₁.data, h₂.data]; exact hp.2.2.2 _ (by decide),
        by rw [h₁.size, h₂.size]; exact hp.2.2.2 _ (by decide),
        by rw [h₁.keeps.sp, h₂.keeps.sp]; exact hp.2.2.1⟩
  exact VG.Proof.Argon2.AArch64.HPrime.keeps_rel VG.Proof.Argon2.AArch64.HPrime.first_stable (args.seq call)
    (fun s₁ s₂ hp => ⟨VG.Proof.Argon2.AArch64.HPrime.absorbInput_keeps v s₁ hp.1, VG.Proof.Argon2.AArch64.HPrime.absorbInput_keeps v s₂ hp.2.1⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.FirstCT`. -/
section
/-! # H′: constant time of the initial length-prefixed hash -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov wp_addImm)

theorem chooseFirst_rel : RelCT isa (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.FirstReady) chooseLength
    (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.FirstReady s₁ s₂ ∧
      (1 ≤ (s₁.gpr .x1).toNat ∧ (s₁.gpr .x1).toNat ≤ 64) ∧ s₁.gpr .x1 = s₂.gpr .x1) := by
  have ct := (chooseLength_rel.mono (P' := VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.FirstReady)
    (fun _ _ hp => hp.2.2) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨VG.Proof.Argon2.AArch64.HPrime.chooseLength_ok s₁ hp.1.bound, VG.Proof.Argon2.AArch64.HPrime.chooseLength_ok s₂ hp.2.1.bound⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨pub, s₁, s₂, hp, ⟨len₁, k₁⟩, ⟨_, k₂⟩⟩
  refine ⟨hp.keeps VG.Proof.Argon2.AArch64.HPrime.first_stable k₁ k₂, ?_, pub.2 _ (List.mem_cons_self ..)⟩
  rw [len₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : min (s₁.gpr .x23).toNat 64 < 2 ^ 64)]
  have := hp.1.positive
  omega

theorem inputCount_ok (s : State) :
    WP isa (.block [.addImm .x .x1 .x21 0, .addImm .x .x1 .x1 4]) s fun t =>
      VG.Proof.Argon2.AArch64.HPrime.Keeps s t ∧ t.gpr .x1 = s.gpr .x21 + 4 := by
  refine wp_mov fun a ha => wp_addImm (by decide) fun t ht => WP.block_nil ⟨?_, ?_⟩
  · refine ⟨fun r hr _ => ?_, ht.rd.trans ha.rd, ht.wr.trans ha.wr, ht.sp.trans ha.sp, ?_⟩
    · have hn : r ≠ .x1 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (ht.other r hn).trans (ha.other r hn)
    · rw [ht.mem, ha.mem]; exact Frame.refl _ _
  · rw [ht.gpr, ha.gpr]; rfl

theorem inputCount_rel :
    RelCT isa (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.FirstReady) (.block [.addImm .x .x1 .x21 0, .addImm .x .x1 .x1 4])
      (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.FirstReady s₁ s₂ ∧ s₁.gpr .x1 = s₂.gpr .x1) := by
  have ct := (RelCT.taint (A := VG.AArch64.taint) (P := VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.FirstReady) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩)
    (c := .block [.addImm .x .x1 .x21 0, .addImm .x .x1 .x1 4]) (by taint_decide)).wpDep
    (fun s₁ s₂ _ => ⟨VG.Proof.Argon2.AArch64.HPrime.inputCount_ok s₁, VG.Proof.Argon2.AArch64.HPrime.inputCount_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, hp, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩
  refine ⟨hp.keeps VG.Proof.Argon2.AArch64.HPrime.first_stable k₁ k₂, ?_⟩
  rw [c₁, c₂, hp.2.2.2 .x21 (by decide)]

theorem first_rel (v : Backend) :
    RelCT isa (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.FirstReady) (first v.hash) (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.FirstReady) :=
  chooseFirst_rel.seq ((VG.Proof.Argon2.AArch64.HPrime.stable_init_rel v VG.Proof.Argon2.AArch64.HPrime.first_stable).seq
    ((VG.Proof.Argon2.AArch64.HPrime.absorbFixed_rel v 832 4 (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩ VG.Proof.Argon2.AArch64.HPrime.first_stable).seq
    ((VG.Proof.Argon2.AArch64.HPrime.absorbInput_rel v).seq (inputCount_rel.seq (VG.Proof.Argon2.AArch64.HPrime.stable_finalize_rel v VG.Proof.Argon2.AArch64.HPrime.first_stable)))))

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: public output counters and prefix emission -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

def LoopReady (s : State) : Prop := VG.Proof.Argon2.AArch64.HPrime.OutputReady s ∧ 65 ≤ (s.gpr .x23).toNat

theorem loop_stable : VG.Proof.Argon2.AArch64.HPrime.Stable VG.Proof.Argon2.AArch64.HPrime.LoopReady where
  ready _ h := output_stable.ready _ h.1
  keeps s t h k := ⟨output_stable.keeps s t h.1 k,
    by rw [k.regs .x23 (by decide) (by decide)]; exact h.2⟩

theorem sub32_nat (v : BitVec 64) (h : 32 ≤ v.toNat) : (v - 32).toNat = v.toNat - 32 := by
  have eq : v - 32 = BitVec.ofNat 64 (v.toNat - 32) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl] using (Offset.ofNat_sub_ofNat (w := 64) h)
  rw [eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.isLt; omega)]

theorem Emitted.ready {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.Emitted s t) (pre : VG.Proof.Argon2.AArch64.HPrime.LoopReady s) : VG.Proof.Argon2.AArch64.HPrime.OutputReady t := by
  have count : (t.gpr .x23).toNat = (s.gpr .x23).toNat - 32 := by
    rw [h.remaining, VG.Proof.Argon2.AArch64.HPrime.sub32_nat _ (by have := pre.2; omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [count]
    apply pre.1.space.advance (Written.of_emitted h)
    simp only [Spec.Blake2.bytesAt, List.length_map, List.length_range]
    have := pre.2
    omega
  · rw [count]; have := pre.2; omega
  · rw [count]; have := pre.1.bound; omega

theorem emit_ready (v : State) (h : VG.Proof.Argon2.AArch64.HPrime.LoopReady v) : WP isa emitPrefix v (VG.Proof.Argon2.AArch64.HPrime.Emitted v) := by
  have space := h.1.space.prefix (show 32 ≤ (v.gpr .x23).toNat by have := h.2; omega)
  exact VG.Proof.Argon2.AArch64.HPrime.emitPrefix_ok v space.work space.out
    (space.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384)))

theorem emit_rel : RelCT isa (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.LoopReady) emitPrefix (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady) := by
  have ct := (emitPrefix_rel.mono (P' := VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.LoopReady)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨VG.Proof.Argon2.AArch64.HPrime.emit_ready s₁ hp.1, VG.Proof.Argon2.AArch64.HPrime.emit_ready s₂ hp.2.1⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨pub, _, _, hp, h₁, h₂⟩ =>
    ⟨h₁.ready hp.1, h₂.ready hp.2.1, pub⟩

theorem count64_init_rel {F : State → Prop} (stable : VG.Proof.Argon2.AArch64.HPrime.Stable F) :
    RelCT isa (VG.Proof.Argon2.AArch64.HPrime.Related F) (.block [.movz .x .x1 64 0])
      (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related F s₁ s₂ ∧
        (1 ≤ (s₁.gpr .x1).toNat ∧ (s₁.gpr .x1).toNat ≤ 64) ∧ s₁.gpr .x1 = s₂.gpr .x1) := by
  have ct := (VG.Proof.Argon2.AArch64.HPrime.count64_rel stable).wpDep (fun s₁ s₂ _ => ⟨VG.Proof.Argon2.AArch64.HPrime.count64_ok s₁, VG.Proof.Argon2.AArch64.HPrime.count64_ok s₂⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨⟨hp, eq⟩, _, _, _, ⟨_, len⟩, _⟩ =>
    ⟨hp, by rw [len]; decide, eq⟩

theorem compare_rel (stable : VG.Proof.Argon2.AArch64.HPrime.Stable VG.Proof.Argon2.AArch64.HPrime.OutputReady) :
    RelCT isa (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady) (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63])
      (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady s₁ s₂ ∧ s₁.gpr .x9 = s₂.gpr .x9 ∧
        s₁.gpr .x9 = if (s₁.gpr .x23).toNat < 65 then 1 else 0) := by
  have ct := (RelCT.taint (A := VG.AArch64.taint) (P := VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.2.2.1, by simp [Taint.ofRegs]⟩)
    (c := .block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63])
    (by taint_decide)).wpDep (fun s₁ s₂ hp => ⟨VG.Proof.Argon2.AArch64.HPrime.compare_ok s₁ hp.1.bound, VG.Proof.Argon2.AArch64.HPrime.compare_ok s₂ hp.2.1.bound⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, hp, h₁, h₂⟩
  have k₁ := h₁.keeps
  have k₂ := h₂.keeps
  refine ⟨hp.keeps stable k₁ k₂, ?_, ?_⟩
  · rw [h₁.value, h₂.value, hp.2.2.2 .x23 (by decide)]
  · rw [k₁.regs .x23 (by decide) (by decide)]; exact h₁.value

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.FinishCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.HPrime.ChainCT`. -/
section
/-! # H′: constant time of the long-output loop -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem chainBody_rel (v : Backend) :
    RelCT isa (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.LoopReady)
      (.seq (.block [.movz .x .x1 64 0])
        (.seq (next v.hash) (.seq emitPrefix (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63]))))
      (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady s₁ s₂ ∧ s₁.gpr .x9 = s₂.gpr .x9 ∧
        s₁.gpr .x9 = if (s₁.gpr .x23).toNat < 65 then 1 else 0) :=
  (VG.Proof.Argon2.AArch64.HPrime.count64_init_rel VG.Proof.Argon2.AArch64.HPrime.loop_stable).seq ((VG.Proof.Argon2.AArch64.HPrime.next_rel v VG.Proof.Argon2.AArch64.HPrime.loop_stable).seq
    (emit_rel.seq (VG.Proof.Argon2.AArch64.HPrime.compare_rel VG.Proof.Argon2.AArch64.HPrime.output_stable)))

theorem chainStep_ready (v : Backend) (s : State) (h : VG.Proof.Argon2.AArch64.HPrime.LoopReady s) :
    WP isa (.seq (.block [.movz .x .x1 64 0])
      (.seq (next v.hash) (.seq emitPrefix (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63])))) s (VG.Proof.Argon2.AArch64.HPrime.ChainStep s) := by
  have space := h.1.space.prefix (show 32 ≤ (s.gpr .x23).toNat by have := h.2; omega)
  exact VG.Proof.Argon2.AArch64.HPrime.chainStep_ok v s space.spBound ⟨by have := h.2; omega, h.1.bound⟩ space.work space.out space.sep space.stackWork

theorem chain_rel (v : Backend) :
    RelCT isa (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.LoopReady) (chain v.hash)
      (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64) := by
  let I := fun n s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.LoopReady s₁ s₂ ∧ (s₁.gpr .x23).toNat = n
  have step (n : Nat) := ((VG.Proof.Argon2.AArch64.HPrime.chainBody_rel v).mono (P' := I n)
    (fun _ _ h => h.1) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨VG.Proof.Argon2.AArch64.HPrime.chainStep_ready v s₁ hp.1.1, VG.Proof.Argon2.AArch64.HPrime.chainStep_ready v s₂ hp.1.2.1⟩)
  have loops (n : Nat) : RelCT isa (I n) (chain v.hash)
      (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64) := by
    unfold chain
    apply RelCT.loop (M := isa) I ?_ n
    intro m
    apply (step m).mono (fun _ _ h => h)
    rintro t₁ t₂ ⟨⟨ready, cf, value⟩, s₁, s₂, hp, h₁, _⟩
    refine ⟨by simp only [eval, State.read, cf], ?_, ?_⟩
    · intro flag
      refine ⟨ready, ?_⟩
      by_contra h
      have hn : ¬ (t₁.gpr .x23).toNat < 65 := by omega
      simp [eval, State.read, value, hn] at flag
    intro flag
    have lo : 65 ≤ (t₁.gpr .x23).toNat := by
      by_contra h
      have lt : (t₁.gpr .x23).toNat < 65 := by omega
      simp [eval, State.read, value, lt] at flag
    have remain : (t₁.gpr .x23).toNat = (s₁.gpr .x23).toNat - 32 := by
      rw [h₁.remaining, VG.Proof.Argon2.AArch64.HPrime.sub32_nat _ (by have := hp.1.1.2; omega)]
    refine ⟨(t₁.gpr .x23).toNat, ?_, ⟨⟨ready.1, lo⟩, ⟨ready.2.1, ?_⟩, ready.2.2⟩, rfl⟩
    · have before : 65 ≤ (s₁.gpr .x23).toNat := hp.1.1.2
      have count : (s₁.gpr .x23).toNat = m := hp.2
      omega
    · rw [← ready.2.2.2 .x23 (by decide)]; exact lo
  exact (RelCT.exists_ loops).mono (fun s₁ _ h => ⟨(s₁.gpr .x23).toNat, h, rfl⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # H′: constant time of the final hash and output -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov)

def OutputCompared (s t : State) : Prop := VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady s t ∧ s.gpr .x9 = t.gpr .x9 ∧
  s.gpr .x9 = if (s.gpr .x23).toNat < 65 then 1 else 0

theorem OutputCompared.short {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.OutputCompared s t) (flag : isa.eval (.nonzero .x .x9) s = some true) :
    (s.gpr .x23).toNat ≤ 64 := by
  by_contra hn
  have n : ¬ (s.gpr .x23).toNat < 65 := by omega
  simp [eval, State.read, h.2.2, n] at flag

theorem OutputCompared.long {s t : State} (h : VG.Proof.Argon2.AArch64.HPrime.OutputCompared s t) (flag : isa.eval (.nonzero .x .x9) s = some false) :
    VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.LoopReady s t := by
  have n : 65 ≤ (s.gpr .x23).toNat := by
    by_contra hn
    have n : (s.gpr .x23).toNat < 65 := by omega
    simp [eval, State.read, h.2.2, n] at flag
  exact ⟨⟨h.1.1, n⟩, ⟨h.1.2.1, by rw [← h.1.2.2.2 .x23 (by decide)]; exact n⟩, h.1.2.2⟩

theorem maybeChain_rel (v : Backend) :
    RelCT isa VG.Proof.Argon2.AArch64.HPrime.OutputCompared (.ite (.nonzero .x .x9) (.block []) (chain v.hash))
      (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64) :=
  RelCT.ite (fun _ _ h => by simp only [eval, State.read, h.2.1])
    (RelCT.block_nil fun _ _ ⟨h, flag⟩ => ⟨h.1, h.short flag⟩)
    ((VG.Proof.Argon2.AArch64.HPrime.chain_rel v).mono (fun _ _ ⟨h, flag⟩ => h.long flag) (fun _ _ h => h))

theorem lastCount_ok (s : State) : WP isa (.block [.addImm .x .x1 .x23 0]) s fun t =>
    VG.Proof.Argon2.AArch64.HPrime.Keeps s t ∧ t.gpr .x1 = s.gpr .x23 := by
  refine wp_mov fun t ht => WP.block_nil ⟨?_, ht.gpr⟩
  exact Keeps.of_upd ht (by decide)

theorem lastCount_rel :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64)
      (.block [.addImm .x .x1 .x23 0])
      (fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady s₁ s₂ ∧
        (1 ≤ (s₁.gpr .x1).toNat ∧ (s₁.gpr .x1).toNat ≤ 64) ∧ s₁.gpr .x1 = s₂.gpr .x1) := by
  let P := fun s₁ s₂ => VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady s₁ s₂ ∧ (s₁.gpr .x23).toNat ≤ 64
  have ct := (RelCT.taint (A := VG.AArch64.taint) (P := P) (Taint.ofRegs [])
    (fun _ _ hp => ⟨hp.1.2.2.1, by simp [Taint.ofRegs]⟩) (c := .block [.addImm .x .x1 .x23 0])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨VG.Proof.Argon2.AArch64.HPrime.lastCount_ok s₁, VG.Proof.Argon2.AArch64.HPrime.lastCount_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, ⟨hp, bound⟩, ⟨k₁, n₁⟩, ⟨k₂, n₂⟩⟩
  exact ⟨hp.keeps VG.Proof.Argon2.AArch64.HPrime.output_stable k₁ k₂, by rw [n₁]; exact ⟨hp.1.positive, bound⟩,
    by rw [n₁, n₂]; exact hp.2.2.2 _ (by decide)⟩

theorem extendDigest_rel (v : Backend) :
    RelCT isa (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.LoopReady) (extendDigest v.hash) (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady) :=
  emit_rel.seq ((VG.Proof.Argon2.AArch64.HPrime.compare_rel VG.Proof.Argon2.AArch64.HPrime.output_stable).seq
    ((VG.Proof.Argon2.AArch64.HPrime.maybeChain_rel v).seq (lastCount_rel.seq (VG.Proof.Argon2.AArch64.HPrime.next_rel v VG.Proof.Argon2.AArch64.HPrime.output_stable))))

theorem finishOutput_rel (v : Backend) :
    RelCT isa (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady) (finishOutput v.hash) (VG.Proof.Argon2.AArch64.HPrime.AgreeRegs VG.Proof.Argon2.AArch64.HPrime.publicRegs) := by
  have branches : RelCT isa VG.Proof.Argon2.AArch64.HPrime.OutputCompared (.ite (.nonzero .x .x9) (.block []) (extendDigest v.hash)) (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady) :=
    RelCT.ite (fun _ _ h => by simp only [eval, State.read, h.2.1])
      (RelCT.block_nil fun _ _ h => h.1.1)
      ((VG.Proof.Argon2.AArch64.HPrime.extendDigest_rel v).mono (fun _ _ ⟨h, flag⟩ => h.long flag) (fun _ _ h => h))
  exact (VG.Proof.Argon2.AArch64.HPrime.compare_rel VG.Proof.Argon2.AArch64.HPrime.output_stable).seq (branches.seq
    (copyRemaining_rel.mono (fun _ _ h => h.2.2) (fun _ _ h => h)))

end VG.Proof.Argon2.AArch64.HPrime
end

/-! Merged from `Proof.Argon2.AArch64.HPrime.CT`. -/
section
/-! # H′: constant time of the complete ARM64 program -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem setup_work (s : State) (h : localContract.pre s) :
    (⟨s.gpr .x4, 16384⟩ : Region) ∈ s.wr := by
  rw [h.2.1]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem setup_ready {s t : State} (h : localContract.pre s) (ht : VG.Proof.Argon2.AArch64.HPrime.Setup s t) : VG.Proof.Argon2.AArch64.HPrime.FirstReady t := by
  obtain ⟨rd, wr, len, lo, hi, hsp, dw, ow, sd, so, sw⟩ := h
  have sp := ht.sp
  have space : VG.Proof.Argon2.AArch64.HPrime.Space t (s.gpr .x3).toNat := by
    refine ⟨hi, by rw [sp]; exact hsp, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ht.workspace, ht.wr, wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · intro i hi'
      rw [ht.wr, ht.output, wr]
      exact ⟨VG.Proof.Argon2.AArch64.HPrime.outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
    · rw [ht.workspace, ht.output]; exact ow.symm
    · rw [sp, ht.workspace]; exact sw
    · rw [sp, ht.output]; exact so
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [ht.remaining]; exact space
  · rw [ht.remaining]; exact lo
  · rw [ht.remaining]; exact hi
  · rw [ht.length]; exact len
  · rw [ht.input, ht.length, ht.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · rw [ht.input, ht.length, ht.workspace]; exact dw
  · rw [sp, ht.input, ht.length]; exact sd

theorem code_ct (v : Backend) :
    ConstantTime isa localContract.pre localContract.pub (code v.hash) := by
  let P := fun s₁ s₂ => localContract.pre s₁ ∧ localContract.pre s₂ ∧ localContract.pub s₁ s₂
  have setupCT := (setup_rel.mono (P' := P) (fun s₁ s₂ hp => by
      obtain ⟨di, si, dx, cx, r8, sp⟩ := hp.2.2
      refine ⟨sp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨VG.Proof.Argon2.AArch64.HPrime.setup_ok s₁ (VG.Proof.Argon2.AArch64.HPrime.setup_work s₁ hp.1), VG.Proof.Argon2.AArch64.HPrime.setup_ok s₂ (VG.Proof.Argon2.AArch64.HPrime.setup_work s₂ hp.2.1)⟩)
  have start : RelCT isa P (.block setup) (VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.FirstReady) :=
    setupCT.mono (fun _ _ h => h) fun _ _ ⟨pub, _, _, hp, h₁, h₂⟩ =>
      ⟨VG.Proof.Argon2.AArch64.HPrime.setup_ready hp.1 h₁, VG.Proof.Argon2.AArch64.HPrime.setup_ready hp.2.1 h₂, pub⟩
  have firstCT := (VG.Proof.Argon2.AArch64.HPrime.first_rel v).mono (fun _ _ h => h)
    (fun _ _ h => (show VG.Proof.Argon2.AArch64.HPrime.Related VG.Proof.Argon2.AArch64.HPrime.OutputReady _ _ from ⟨h.1.toOutputReady, h.2.1.toOutputReady, h.2.2⟩))
  have restoreCT := restore_rel.mono (P' := VG.Proof.Argon2.AArch64.HPrime.AgreeRegs VG.Proof.Argon2.AArch64.HPrime.publicRegs) (fun _ _ hp => by
      refine ⟨hp.1, fun r hr => ?_⟩
      simp only [List.mem_singleton] at hr; subst r
      exact hp.2 _ (by decide)) (fun _ _ h => h)
  exact (start.seq (firstCT.seq ((VG.Proof.Argon2.AArch64.HPrime.finishOutput_rel v).seq restoreCT))).constantTime

end VG.Proof.Argon2.AArch64.HPrime
end

/-! # Verified ARM64 H′ for every supplied BLAKE2b backend -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

theorem verified (v : Backend) :
    Verified AArch64.target (code v.hash) (Spec.Argon2.hPrimeContract AArch64.abi 16) :=
  Verified.of_correct (VG.Proof.Argon2.AArch64.HPrime.code_correct v) (VG.Proof.Argon2.AArch64.HPrime.code_ct v) VG.Proof.Argon2.AArch64.HPrime.contract_implies

theorem spSafe (v : Backend) : (code v.hash).all (fun i => !isa.writesSp i) = true := by
  induction code v.hash <;> simp_all [Code.all]

end VG.Proof.Argon2.AArch64.HPrime

end
