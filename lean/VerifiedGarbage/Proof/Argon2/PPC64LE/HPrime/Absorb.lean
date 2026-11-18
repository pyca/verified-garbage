module

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Frame
import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
public import VerifiedGarbage.Impl.Argon2.PPC64LE.HPrime
public import VerifiedGarbage.Impl.MdStream.PPC64LE
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Verified
import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Blake2
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline

/-! ### `Argon2.PPC64LE.HPrime.Calls`, which this module and modules that import it used -/

section

/-! # H′ on PPC64LE: calling the BLAKE2b streaming functions -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (Upd wp_mov wp_addi wp_li)
open VG.Spec.Blake2 (b Repr bytesAt)

theorem init_noFrames : initCode.noFrames = true := by lit_decide
theorem update_fdepth : (Impl.Blake2.PPC64LE.Stream.update b).fdepth = 1 := by lit_decide
theorem finalize_fdepth : (Impl.Blake2.PPC64LE.Stream.finalize b).fdepth = 1 := by lit_decide
theorem update_pushFrames : pushFrames (Impl.Blake2.PPC64LE.Stream.update b) = true := by lit_decide
theorem finalize_pushFrames : pushFrames (Impl.Blake2.PPC64LE.Stream.finalize b) = true := by lit_decide

/-- A register other than those of `ws` is not in `preserved`. -/
theorem preserved_ne {r : Reg} (hr : r ∈ preserved) {d : Reg} (hd : d ∉ preserved := by decide) :
    r ≠ d := fun h => hd (h ▸ hr)

/-! ## `init` -/

structure InitArgs (s t : State) : Prop where
  state : t.gpr .r3 = s.gpr .r31
  key : t.gpr .r5 = s.gpr .r31 + 832
  keylen : t.gpr .r6 = 0
  other : ∀ r, r ≠ .r3 → r ≠ .r5 → r ≠ .r6 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem initArgs_ok (s : State) :
    WP isa (.block initArgs) s (InitArgs s) :=
  wp_mov fun a ha => wp_addi (by decide) fun c hc => wp_li (by decide) fun t ht => WP.block_nil
    ⟨by rw [ht.other _ (by decide), hc.other _ (by decide), ha.gpr],
      by rw [ht.other _ (by decide), hc.gpr, ha.other _ (by decide)]; rfl,
      ht.gpr,
      fun r h1 h2 h3 => by rw [ht.other _ h3, hc.other _ h2, ha.other _ h1],
      by rw [ht.mem, hc.mem, ha.mem], by rw [ht.rd, hc.rd, ha.rd], by rw [ht.wr, hc.wr, ha.wr],
      by rw [ht.sp, hc.sp, ha.sp]⟩

/-- Narrow the callee's permissions to its state and empty key. -/
theorem init_call_hyps (s u : State) (hu : InitArgs s u)
    (hlen : 1 ≤ (s.gpr .r4).toNat ∧ (s.gpr .r4).toNat ≤ 64)
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr) :
    (Proof.Blake2.initPPC64LE b).pre
      (u.callEntry.withRegions [⟨s.gpr .r31 + 832, 0⟩] [⟨s.gpr .r31, 192⟩]) ∧
    Covers ([⟨s.gpr .r31 + 832, 0⟩] ++ [⟨s.gpr .r31, 192⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .r31, 192⟩] u.wr := by
  have hlen' : u.gpr .r4 = s.gpr .r4 := hu.other _ (by decide) (by decide) (by decide)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun _ hr => State.callEntry_gpr u hr
  have hp : (Proof.Blake2.initPPC64LE b).pre
      (u.callEntry.withRegions [⟨s.gpr .r31 + 832, 0⟩] [⟨s.gpr .r31, 192⟩]) := by
    simp only [Proof.Blake2.initPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g .r3 (by decide), g .r5 (by decide), g .r6 (by decide),
      g .r4 (by decide), hu.state, hu.key, hu.keylen, hlen']
    refine ⟨rfl, rfl, ?_, hlen.1, hlen.2, by decide⟩
    exact (Offset.base_disjoint (s.gpr .r31) (e := 832) (n := 0) (k := 192) (by decide) (by decide)).symm
  have cover : Covers ([⟨s.gpr .r31 + 832, 0⟩] ++ [⟨s.gpr .r31, 192⟩]) (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .r31, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), ?_⟩
    rcases hr with rfl | rfl
    · exact ⟨832, rfl, by change 832 ≤ 16384; decide⟩
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
  have writes : Covers [⟨s.gpr .r31, 192⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨s.gpr .r31, 16384⟩, hu.wr.symm ▸ hwr, 0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
  exact ⟨hp, cover, writes⟩

theorem init_ok (s : State)
    (hlen : 1 ≤ (s.gpr .r4).toNat ∧ (s.gpr .r4).toNat ≤ 64)
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr) :
    WP isa init s fun t =>
      Repr b (Spec.Blake2.init b (s.gpr .r4).toNat 0) t.mem (s.gpr .r31) [] ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ Frame [⟨s.gpr .r31, 192⟩] s.mem t.mem := by
  unfold init
  refine WP.seq ((initArgs_ok s).mono fun u hu => ?_)
  have hlen' : u.gpr .r4 = s.gpr .r4 := hu.other _ (by decide) (by decide) (by decide)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun _ hr => State.callEntry_gpr u hr
  obtain ⟨hp, cover, writes⟩ := init_call_hyps s u hu hlen hwr
  refine WP.call (k := Proof.Blake2.initPPC64LE b)
    Proof.Blake2.PPC64LE.Stream.initB_correct hp cover writes ?_ init_noFrames
  intro t rd wr sp frame cs _ post
  simp only [Proof.Blake2.initPPC64LE, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide), g .r6 (by decide),
    hu.state, hu.key, hu.keylen, hlen', Spec.Blake2.bytesAt, Spec.Blake2.keyBlock] at post
  refine ⟨post, fun r hr => (cs r hr).trans ?_, rd.trans hu.rd, wr.trans hu.wr,
    sp.trans hu.sp, by simpa only [hu.mem] using frame⟩
  exact hu.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr)

/-! ## `update` -/

structure UpdateArgs (s t : State) : Prop where
  state : t.gpr .r3 = s.gpr .r31
  scratch : t.gpr .r7 = s.gpr .r31 + 192
  other : ∀ r, r ≠ .r3 → r ≠ .r7 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem updateArgs_ok (s : State) :
    WP isa (.block updateArgs) s (UpdateArgs s) :=
  wp_mov fun a ha => wp_addi (by decide) fun t ht => WP.block_nil
    ⟨by rw [ht.other _ (by decide), ha.gpr], by rw [ht.gpr, ha.other _ (by decide)]; rfl,
      fun r h1 h2 => by rw [ht.other _ h2, ha.other _ h1],
      by rw [ht.mem, ha.mem], by rw [ht.rd, ha.rd], by rw [ht.wr, ha.wr], by rw [ht.sp, ha.sp]⟩

/-- The narrowed update call, without assumptions about message contents. -/
theorem update_call_hyps (s u : State) (hu : UpdateArgs s u)
    (hsp : 48 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .r5, (s.gpr .r6).toNat⟩] (s.rd ++ s.wr))
    (dataState : (⟨s.gpr .r5, (s.gpr .r6).toNat⟩ : Region).Disjoint ⟨s.gpr .r31, 192⟩)
    (dataScratch : (⟨s.gpr .r5, (s.gpr .r6).toNat⟩ : Region).Disjoint ⟨s.gpr .r31 + 192, 576⟩)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩)
    (stackData : (below s.sp 48).Disjoint ⟨s.gpr .r5, (s.gpr .r6).toNat⟩) :
    (Proof.Blake2.updatePPC64LE b).pre (u.callEntry.withRegions
      [⟨s.gpr .r5, (s.gpr .r6).toNat⟩] [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 192, 576⟩]) ∧
    Covers ([⟨s.gpr .r5, (s.gpr .r6).toNat⟩] ++
      [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 192, 576⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 192, 576⟩] u.wr := by
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have src : u.gpr .r5 = s.gpr .r5 := hu.other _ (by decide) (by decide)
  have len : u.gpr .r6 = s.gpr .r6 := hu.other _ (by decide) (by decide)
  have subState : Region.Sub ⟨s.gpr .r31, 192⟩ ⟨s.gpr .r31, 16384⟩ := Region.sub_prefix (by decide)
  have subScratch : Region.Sub ⟨s.gpr .r31 + 192, 576⟩ ⟨s.gpr .r31, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have hp : (Proof.Blake2.updatePPC64LE b).pre (u.callEntry.withRegions
      [⟨s.gpr .r5, (s.gpr .r6).toNat⟩] [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 192, 576⟩]) := by
    simp only [Proof.Blake2.updatePPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g .r3 (by decide), g .r5 (by decide), g .r6 (by decide), g .r7 (by decide),
      State.callEntry_sp, State.withRegions_sp, hu.state, hu.scratch, src, len, hu.sp]
    exact ⟨trivial, rfl, Offset.base_disjoint _ (by decide) (by decide), dataState, dataScratch,
      hsp, stackWork.sub_right subState, stackData, stackWork.sub_right subScratch⟩
  have writes : Covers [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 192, 576⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .r31, 16384⟩, hu.wr.symm ▸ hwr, ?_⟩
    rcases hr with rfl | rfl
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
    · exact ⟨192, rfl, by change 192 + 576 ≤ 16384; decide⟩
  have cover : Covers ([⟨s.gpr .r5, (s.gpr .r6).toNat⟩] ++
      [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 192, 576⟩]) (u.rd ++ u.wr) := by
    intro a n ⟨r, hr, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · rw [hu.rd, hu.wr]; exact hdata a n ⟨r, hr, hc⟩
    · obtain ⟨r', hr', hc'⟩ := writes a n ⟨r, hr, hc⟩
      exact ⟨r', List.mem_append_right _ hr', hc'⟩
  exact ⟨hp, cover, writes⟩

theorem update_ok (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .r31) d)
    (count : s.gpr .r4 = BitVec.ofNat 64 d.length)
    (bound : d.length + (s.gpr .r6).toNat < 2 ^ 64)
    (hsp : 48 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .r5, (s.gpr .r6).toNat⟩] (s.rd ++ s.wr))
    (dataState : (⟨s.gpr .r5, (s.gpr .r6).toNat⟩ : Region).Disjoint ⟨s.gpr .r31, 192⟩)
    (dataScratch : (⟨s.gpr .r5, (s.gpr .r6).toNat⟩ : Region).Disjoint ⟨s.gpr .r31 + 192, 576⟩)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩)
    (stackData : (below s.sp 48).Disjoint ⟨s.gpr .r5, (s.gpr .r6).toNat⟩) :
    WP isa update s fun t =>
      Repr b h0 t.mem (s.gpr .r31) (d ++ bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 192, 576⟩, below s.sp 48] s.mem t.mem := by
  unfold update
  refine WP.seq ((updateArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have src : u.gpr .r5 = s.gpr .r5 := hu.other _ (by decide) (by decide)
  have len : u.gpr .r6 = s.gpr .r6 := hu.other _ (by decide) (by decide)
  have cnt : u.gpr .r4 = s.gpr .r4 := hu.other _ (by decide) (by decide)
  obtain ⟨hp, cover, writes⟩ := update_call_hyps s u hu hsp hwr hdata dataState dataScratch stackWork stackData
  have repr' : Repr b h0 u.callEntry.mem (s.gpr .r31) d := by
    simpa only [State.callEntry_mem, hu.mem] using repr
  refine WP.callF (k := Proof.Blake2.updatePPC64LE b) Proof.Blake2.PPC64LE.Stream.updateB_correct
    hp cover writes ?_ (by rw [update_fdepth]; decide) update_pushFrames
  intro t rd wr sp' frame cs post
  simp only [Proof.Blake2.updatePPC64LE, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide), g .r6 (by decide),
    hu.state, src, len, cnt, hu.mem] at post
  refine ⟨post h0 d repr count bound, fun r hr => (cs r hr).trans ?_, rd.trans hu.rd,
    wr.trans hu.wr, sp'.trans hu.sp, ?_⟩
  · exact hu.other r (preserved_ne hr) (preserved_ne hr)
  · have e : 48 * (Impl.Blake2.PPC64LE.Stream.update b).fdepth = 48 := by lit_decide
    simpa only [e, hu.sp, hu.mem, List.cons_append, List.nil_append] using frame

/-! ## `finalize` -/

structure FinalizeArgs (s t : State) : Prop where
  state : t.gpr .r3 = s.gpr .r31
  digest : t.gpr .r5 = s.gpr .r31 + 768
  scratch : t.gpr .r6 = s.gpr .r31 + 192
  other : ∀ r, r ≠ .r3 → r ≠ .r5 → r ≠ .r6 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem finalizeArgs_ok (s : State) :
    WP isa (.block finalizeArgs) s (FinalizeArgs s) :=
  wp_mov fun a ha => wp_addi (by decide) fun c hc => wp_addi (by decide) fun t ht => WP.block_nil
    ⟨by rw [ht.other _ (by decide), hc.other _ (by decide), ha.gpr],
      by rw [ht.other _ (by decide), hc.gpr, ha.other _ (by decide)]; rfl,
      by rw [ht.gpr, hc.other _ (by decide), ha.other _ (by decide)]; rfl,
      fun r h1 h2 h3 => by rw [ht.other _ h3, hc.other _ h2, ha.other _ h1],
      by rw [ht.mem, hc.mem, ha.mem], by rw [ht.rd, hc.rd, ha.rd], by rw [ht.wr, hc.wr, ha.wr],
      by rw [ht.sp, hc.sp, ha.sp]⟩

/-- The narrowed finalization call, independently of the represented message. -/
theorem finalize_call_hyps (s u : State) (hu : FinalizeArgs s u)
    (hsp : 48 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩) :
    (Proof.Blake2.finalizePPC64LE b).pre (u.callEntry.withRegions []
      [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 768, 64⟩, ⟨s.gpr .r31 + 192, 576⟩]) ∧
    Covers ([] ++ [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 768, 64⟩,
      ⟨s.gpr .r31 + 192, 576⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 768, 64⟩, ⟨s.gpr .r31 + 192, 576⟩] u.wr := by
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have subState : Region.Sub ⟨s.gpr .r31, 192⟩ ⟨s.gpr .r31, 16384⟩ := Region.sub_prefix (by decide)
  have subDigest : Region.Sub ⟨s.gpr .r31 + 768, 64⟩ ⟨s.gpr .r31, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have subScratch : Region.Sub ⟨s.gpr .r31 + 192, 576⟩ ⟨s.gpr .r31, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have hp : (Proof.Blake2.finalizePPC64LE b).pre (u.callEntry.withRegions []
      [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 768, 64⟩, ⟨s.gpr .r31 + 192, 576⟩]) := by
    simp only [Proof.Blake2.finalizePPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g .r3 (by decide), g .r5 (by decide), g .r6 (by decide),
      State.callEntry_sp, State.withRegions_sp, hu.state, hu.digest, hu.scratch, hu.sp]
    exact ⟨trivial, rfl, Offset.base_disjoint _ (by decide) (by decide),
      Offset.base_disjoint _ (by decide) (by decide), (Offset.disjoint _ (by decide) (by decide) (by decide)).symm,
      hsp, stackWork.sub_right subState, stackWork.sub_right subDigest,
      stackWork.sub_right subScratch⟩
  have writes : Covers [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 768, 64⟩, ⟨s.gpr .r31 + 192, 576⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .r31, 16384⟩, hu.wr.symm ▸ hwr, ?_⟩
    rcases hr with rfl | rfl | rfl
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
    · exact ⟨768, rfl, by change 768 + 64 ≤ 16384; decide⟩
    · exact ⟨192, rfl, by change 192 + 576 ≤ 16384; decide⟩
  have cover : Covers ([] ++ [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 768, 64⟩,
      ⟨s.gpr .r31 + 192, 576⟩]) (u.rd ++ u.wr) := by
    intro a n h
    obtain ⟨r, hr, hc⟩ := writes a n h
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  exact ⟨hp, cover, writes⟩

theorem finalize_ok (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .r31) d)
    (count : s.gpr .r4 = BitVec.ofNat 64 d.length) (bound : d.length < 2 ^ 64)
    (hsp : 48 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩) :
    WP isa finalize s fun t =>
      bytesAt t.mem (s.gpr .r31 + 768) 64 = Spec.Blake2.finalHash b h0 d ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨s.gpr .r31, 192⟩, ⟨s.gpr .r31 + 768, 64⟩,
        ⟨s.gpr .r31 + 192, 576⟩, below s.sp 48] s.mem t.mem := by
  unfold finalize
  refine WP.seq ((finalizeArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have cnt : u.gpr .r4 = s.gpr .r4 := hu.other _ (by decide) (by decide) (by decide)
  obtain ⟨hp, cover, writes⟩ := finalize_call_hyps s u hu hsp hwr stackWork
  have repr' : Repr b h0 u.callEntry.mem (s.gpr .r31) d := by
    simpa only [State.callEntry_mem, hu.mem] using repr
  refine WP.callF (k := Proof.Blake2.finalizePPC64LE b) Proof.Blake2.PPC64LE.Stream.finalizeB_correct
    hp cover writes ?_ (by rw [finalize_fdepth]; decide) finalize_pushFrames
  intro t rd wr sp' frame cs post
  simp only [Proof.Blake2.finalizePPC64LE, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide),
    hu.state, hu.digest, cnt, hu.mem] at post
  refine ⟨post h0 d repr bound count, fun r hr => (cs r hr).trans ?_, rd.trans hu.rd, wr.trans hu.wr,
    sp'.trans hu.sp, ?_⟩
  · exact hu.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr)
  · have e : 48 * (Impl.Blake2.PPC64LE.Stream.finalize b).fdepth = 48 := by lit_decide
    simpa only [e, hu.sp, hu.mem, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.PPC64LE.HPrime

end

end

/-! # H′ on PPC64LE: absorbing the length prefix, the previous digest or the input -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE VG.Impl.Argon2.PPC64LE.HPrime
open VG.Proof.MdStream.PPC64LE (Upd wp_mov wp_addi wp_li)
open VG.Spec.Blake2 (b Repr bytesAt)

/-! ## A fixed workspace buffer -/

structure FixedArgs (s t : State) (offset size : Nat) : Prop where
  count : t.gpr .r4 = 0
  data : t.gpr .r5 = s.gpr .r31 + BitVec.ofNat 64 offset
  size : t.gpr .r6 = BitVec.ofNat 64 size
  other : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem fixedArgs_ok (s : State) (offset size : Nat) (ho : offset < 2 ^ 15) (hn : size < 2 ^ 15) :
    WP isa (.block (fixedArgs offset size)) s fun t =>
      FixedArgs s t offset size :=
  wp_li (by decide) fun a ha => wp_addi ho fun c hc => wp_li hn fun t ht => WP.block_nil
    ⟨by rw [ht.other _ (by decide), hc.other _ (by decide), ha.gpr]; rfl,
      by rw [ht.other _ (by decide), hc.gpr, ha.other _ (by decide)],
      ht.gpr,
      fun r h1 h2 h3 => by rw [ht.other _ h3, hc.other _ h2, ha.other _ h1],
      by rw [ht.mem, hc.mem, ha.mem], by rw [ht.rd, hc.rd, ha.rd], by rw [ht.wr, hc.wr, ha.wr],
      by rw [ht.sp, hc.sp, ha.sp]⟩

theorem absorbFixed_ok (s : State)
    (h0 : Spec.Blake2.HashValue 64) (offset size : Nat)
    (offsetUpper : offset < 2 ^ 15)
    (hsp : 48 ≤ s.sp.toNat)
    (offsetLower : 768 ≤ offset) (sizeBound : offset + size ≤ 16384)
    (repr : Repr b h0 s.mem (s.gpr .r31) [])
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩) :
    WP isa (absorbFixed offset size) s fun t =>
      Repr b h0 t.mem (s.gpr .r31) (bytesAt s.mem (s.gpr .r31 + BitVec.ofNat 64 offset) size) ∧
      Keeps s t := by
  unfold absorbFixed
  refine WP.seq ((fixedArgs_ok s offset size offsetUpper (by omega_using [sizeBound])).mono fun u hu => ?_)
  have p : u.gpr .r31 = s.gpr .r31 := hu.other _ (by decide) (by decide) (by decide)
  have sp := hu.sp
  have len : (u.gpr .r6).toNat = size := by
    rw [hu.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [sizeBound])]
  have wr : (⟨u.gpr .r31, 16384⟩ : Region) ∈ u.wr := by rw [p, hu.wr]; exact hwr
  have hr : Repr b h0 u.mem (u.gpr .r31) [] := by rw [hu.mem, p]; exact repr
  have hc : u.gpr .r4 = BitVec.ofNat 64 ([] : List Byte).length := hu.count
  have hb : ([] : List Byte).length + (u.gpr .r6).toNat < 2 ^ 64 := by
    simp only [List.length_nil, Nat.zero_add, len]; omega_using [sizeBound]
  have cover : Covers [⟨u.gpr .r5, (u.gpr .r6).toNat⟩] (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .r31, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), offset, hu.data, ?_⟩
    change offset + (u.gpr .r6).toNat ≤ 16384
    rw [len]; exact sizeBound
  have ds : (⟨u.gpr .r5, (u.gpr .r6).toNat⟩ : Region).Disjoint ⟨u.gpr .r31, 192⟩ := by
    rw [hu.data, len, p]
    exact (Offset.base_disjoint _ (by omega_using [offsetLower]) (by omega_using [sizeBound])).symm
  have dw : (⟨u.gpr .r5, (u.gpr .r6).toNat⟩ : Region).Disjoint ⟨u.gpr .r31 + 192, 576⟩ := by
    rw [hu.data, len, p]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega_using [offsetLower]) (by omega_using [sizeBound]) (by decide)
  have sw : (below u.sp 48).Disjoint ⟨u.gpr .r31, 16384⟩ := by
    rw [sp, p]; exact stackWork
  have sd : (below u.sp 48).Disjoint ⟨u.gpr .r5, (u.gpr .r6).toNat⟩ := by
    rw [sp, hu.data, len]
    exact stackWork.sub_right (Offset.sub_base _ sizeBound)
  refine (update_ok u h0 [] hr hc hb (by rw [sp]; exact hsp) wr cover ds dw sw sd).mono ?_
  rintro t ⟨repr', regs, rd, wr', sp', frame⟩
  simp only [p, hu.data, len, hu.mem, List.nil_append] at repr'
  refine ⟨repr', fun r hr => (regs r hr).trans ?_, rd.trans hu.rd, wr'.trans hu.wr, sp'.trans hu.sp, ?_⟩
  · exact hu.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr)
  · simpa only [p, sp, hu.mem] using update_frame (u.gpr .r31) u.sp frame

/-! ## The caller's input -/

structure InputArgs (s t : State) : Prop where
  count : t.gpr .r4 = 4
  data : t.gpr .r5 = s.gpr .r27
  size : t.gpr .r6 = s.gpr .r28
  other : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem inputArgs_ok (s : State) :
    WP isa (.block inputArgs) s (InputArgs s) :=
  wp_li (by decide) fun a ha => wp_mov fun c hc => wp_mov fun t ht => WP.block_nil
    ⟨by rw [ht.other _ (by decide), hc.other _ (by decide), ha.gpr]; rfl,
      by rw [ht.other _ (by decide), hc.gpr, ha.other _ (by decide)],
      by rw [ht.gpr, hc.other _ (by decide), ha.other _ (by decide)],
      fun r h1 h2 h3 => by rw [ht.other _ h3, hc.other _ h2, ha.other _ h1],
      by rw [ht.mem, hc.mem, ha.mem], by rw [ht.rd, hc.rd, ha.rd], by rw [ht.wr, hc.wr, ha.wr],
      by rw [ht.sp, hc.sp, ha.sp]⟩

theorem InputArgs.keeps {s t : State} (h : InputArgs s t) : Keeps s t := by
  refine ⟨fun r hr => h.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr),
    h.rd, h.wr, h.sp, ?_⟩
  rw [h.mem]; exact Frame.refl _ _

theorem absorbInput_ok (s : State)
    (h0 : Spec.Blake2.HashValue 64) (headBytes : List Byte) (prefixLen : headBytes.length = 4)
    (repr : Repr b h0 s.mem (s.gpr .r31) headBytes) (len : (s.gpr .r28).toNat < 2 ^ 32)
    (hsp : 48 ≤ s.sp.toNat)
    (hwr : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .r27, (s.gpr .r28).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .r27, (s.gpr .r28).toNat⟩ : Region).Disjoint ⟨s.gpr .r31, 16384⟩)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩)
    (stackData : (below s.sp 48).Disjoint ⟨s.gpr .r27, (s.gpr .r28).toNat⟩) :
    WP isa absorbInput s fun t =>
      Repr b h0 t.mem (s.gpr .r31) (headBytes ++ bytesAt s.mem (s.gpr .r27) (s.gpr .r28).toNat) ∧
      Keeps s t := by
  unfold absorbInput
  refine WP.seq ((inputArgs_ok s).mono fun u hu => ?_)
  have ku := hu.keeps
  have repr' : Repr b h0 u.mem (u.gpr .r31) headBytes := by rw [hu.mem, ku.r31]; exact repr
  have count : u.gpr .r4 = BitVec.ofNat 64 headBytes.length := by rw [prefixLen]; exact hu.count
  have bound : headBytes.length + (u.gpr .r6).toNat < 2 ^ 64 := by rw [prefixLen, hu.size]; omega_using [len]
  have wr : (⟨u.gpr .r31, 16384⟩ : Region) ∈ u.wr := by rw [ku.r31, ku.wr]; exact hwr
  have cover : Covers [⟨u.gpr .r5, (u.gpr .r6).toNat⟩] (u.rd ++ u.wr) := by
    rw [hu.data, hu.size, hu.rd, hu.wr]; exact hdata
  have ds : (⟨u.gpr .r5, (u.gpr .r6).toNat⟩ : Region).Disjoint ⟨u.gpr .r31, 192⟩ := by
    rw [hu.data, hu.size, ku.r31]
    exact dataWork.sub_right (Region.sub_prefix (by decide))
  have dw : (⟨u.gpr .r5, (u.gpr .r6).toNat⟩ : Region).Disjoint ⟨u.gpr .r31 + 192, 576⟩ := by
    rw [hu.data, hu.size, ku.r31]
    exact dataWork.sub_right (Offset.sub_base _ (by decide))
  have sw : (below u.sp 48).Disjoint ⟨u.gpr .r31, 16384⟩ := by
    rw [ku.r31, ku.sp]; exact stackWork
  have sd : (below u.sp 48).Disjoint ⟨u.gpr .r5, (u.gpr .r6).toNat⟩ := by
    rw [hu.data, hu.size, ku.sp]; exact stackData
  refine (update_ok u h0 headBytes repr' count bound (by rw [ku.sp]; exact hsp) wr cover ds dw sw sd).mono ?_
  rintro t ⟨result, regs, rd, wr', sp', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', sp', update_frame _ _ frame⟩⟩
  simpa only [ku.r31, hu.mem, hu.data, hu.size] using result

end VG.Proof.Argon2.PPC64LE.HPrime
