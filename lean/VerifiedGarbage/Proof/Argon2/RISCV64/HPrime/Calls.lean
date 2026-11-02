module

import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Frame
public import VerifiedGarbage.Impl.Argon2.RISCV64.HPrime
public import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Common
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Verified
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.CT
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Update
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Finalize
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Spec.Blake2
public import VerifiedGarbage.Proof.Framework.Block

/-! # H′ on RISC-V: calling the BLAKE2b streaming functions

The `_scratch` functions use no stack, so each call writes only the
workspace buffers it is given. -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64 VG.Impl.Argon2.RISCV64.HPrime
open VG.RISCV64.Wp (Upd wp_mv wp_addi wp_li)
open VG.Spec.Blake2 (b Repr bytesAt)

theorem init_noFrames : initCode.noFrames = true := by lit_decide
theorem update_noFrames : updateCode.noFrames = true := by lit_decide
theorem finalize_noFrames : finalizeCode.noFrames = true := by lit_decide

/-- A register other than those of `ws` is not in `preserved`. -/
theorem preserved_ne {r : Reg} (hr : r ∈ preserved) {d : Reg} (hd : d ∉ preserved := by decide) :
    r ≠ d := fun h => hd (h ▸ hr)

theorem init_callee (st : State) (hs : (Proof.Blake2.initRISCV64 b).pre st) :
    ∃ t s', Exec isa initCode st t s' ∧ abiPreserved st s' ∧ (Proof.Blake2.initRISCV64 b).post st s' :=
  Proof.Blake2.RISCV64.Stream.init_correct (z := .d) Proof.Blake2.RISCV64.Stream.okB st hs

theorem update_callee (st : State) (hs : (Proof.Blake2.updateRISCV64 b).pre st) :
    ∃ t s', Exec isa updateCode st t s' ∧ abiPreserved st s' ∧ (Proof.Blake2.updateRISCV64 b).post st s' :=
  Proof.Blake2.RISCV64.Stream.Update.correct Proof.Blake2.RISCV64.Stream.okB
    Proof.Blake2.RISCV64.Stream.calleeB hs

theorem finalize_callee (st : State) (hs : (Proof.Blake2.finalizeRISCV64 b).pre st) :
    ∃ t s', Exec isa finalizeCode st t s' ∧ abiPreserved st s' ∧
      (Proof.Blake2.finalizeRISCV64 b).post st s' :=
  Proof.Blake2.RISCV64.Stream.Finalize.correct Proof.Blake2.RISCV64.Stream.okB
    Proof.Blake2.RISCV64.Stream.calleeB hs

/-! ## `init` -/

structure InitArgs (s t : State) : Prop where
  state : t.gpr .a0 = s.gpr .s4
  key : t.gpr .a2 = s.gpr .s4 + 832
  keylen : t.gpr .a3 = 0
  other : ∀ r, r ≠ .a0 → r ≠ .a2 → r ≠ .a3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem initArgs_ok (s : State) :
    WP isa (.block initArgs) s (InitArgs s) :=
  wp_mv fun a ha => wp_addi (by decide) fun c hc => wp_li (by decide) fun t ht => WP.block_nil
    ⟨by rw [ht.other _ (by decide), hc.other _ (by decide), ha.gpr],
      by rw [ht.other _ (by decide), hc.gpr, ha.other _ (by decide)]; rfl,
      ht.gpr,
      fun r h1 h2 h3 => by rw [ht.other _ h3, hc.other _ h2, ha.other _ h1],
      by rw [ht.mem, hc.mem, ha.mem], by rw [ht.rd, hc.rd, ha.rd], by rw [ht.wr, hc.wr, ha.wr],
      by rw [ht.sp, hc.sp, ha.sp]⟩

/-- Narrow the callee's permissions to its state and empty key. -/
theorem init_call_hyps (s u : State) (hu : InitArgs s u)
    (hlen : 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 64)
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr) :
    (Proof.Blake2.initRISCV64 b).pre
      (u.callEntry.withRegions [⟨s.gpr .s4 + 832, 0⟩] [⟨s.gpr .s4, 192⟩]) ∧
    Covers ([⟨s.gpr .s4 + 832, 0⟩] ++ [⟨s.gpr .s4, 192⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .s4, 192⟩] u.wr := by
  have hlen' : u.gpr .a1 = s.gpr .a1 := hu.other _ (by decide) (by decide) (by decide)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun _ hr => State.callEntry_gpr u hr
  have hp : (Proof.Blake2.initRISCV64 b).pre
      (u.callEntry.withRegions [⟨s.gpr .s4 + 832, 0⟩] [⟨s.gpr .s4, 192⟩]) := by
    simp only [Proof.Blake2.initRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g .a0 (by decide), g .a2 (by decide), g .a3 (by decide),
      g .a1 (by decide), hu.state, hu.key, hu.keylen, hlen']
    refine ⟨rfl, rfl, ?_, hlen.1, hlen.2, by decide⟩
    exact (Offset.base_disjoint (s.gpr .s4) (e := 832) (n := 0) (k := 192) (by decide) (by decide)).symm
  have cover : Covers ([⟨s.gpr .s4 + 832, 0⟩] ++ [⟨s.gpr .s4, 192⟩]) (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .s4, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), ?_⟩
    rcases hr with rfl | rfl
    · exact ⟨832, rfl, by change 832 ≤ 16384; decide⟩
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
  have writes : Covers [⟨s.gpr .s4, 192⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨s.gpr .s4, 16384⟩, hu.wr.symm ▸ hwr, 0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
  exact ⟨hp, cover, writes⟩

theorem init_ok (s : State)
    (hlen : 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 64)
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr) :
    WP isa init s fun t =>
      Repr b (Spec.Blake2.init b (s.gpr .a1).toNat 0) t.mem (s.gpr .s4) [] ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ Frame [⟨s.gpr .s4, 192⟩] s.mem t.mem := by
  unfold init
  refine WP.seq ((initArgs_ok s).mono fun u hu => ?_)
  have hlen' : u.gpr .a1 = s.gpr .a1 := hu.other _ (by decide) (by decide) (by decide)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun _ hr => State.callEntry_gpr u hr
  obtain ⟨hp, cover, writes⟩ := init_call_hyps s u hu hlen hwr
  refine WP.call (k := Proof.Blake2.initRISCV64 b) init_callee hp cover writes ?_ init_noFrames
  intro t rd wr sp frame cs _ post
  simp only [Proof.Blake2.initRISCV64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide),
    hu.state, hu.key, hu.keylen, hlen', Spec.Blake2.bytesAt, Spec.Blake2.keyBlock] at post
  refine ⟨post, fun r hr => (cs r hr).trans ?_, rd.trans hu.rd, wr.trans hu.wr,
    sp.trans hu.sp, by simpa only [hu.mem] using frame⟩
  exact hu.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr)

/-! ## `update` -/

structure UpdateArgs (s t : State) : Prop where
  state : t.gpr .a0 = s.gpr .s4
  scratch : t.gpr .a4 = s.gpr .s4 + 192
  other : ∀ r, r ≠ .a0 → r ≠ .a4 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem updateArgs_ok (s : State) :
    WP isa (.block updateArgs) s (UpdateArgs s) :=
  wp_mv fun a ha => wp_addi (by decide) fun t ht => WP.block_nil
    ⟨by rw [ht.other _ (by decide), ha.gpr], by rw [ht.gpr, ha.other _ (by decide)]; rfl,
      fun r h1 h2 => by rw [ht.other _ h2, ha.other _ h1],
      by rw [ht.mem, ha.mem], by rw [ht.rd, ha.rd], by rw [ht.wr, ha.wr], by rw [ht.sp, ha.sp]⟩

/-- The narrowed update call, without assumptions about message contents. -/
theorem update_call_hyps (s u : State) (hu : UpdateArgs s u)
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .a2, (s.gpr .a3).toNat⟩] (s.rd ++ s.wr))
    (dataState : (⟨s.gpr .a2, (s.gpr .a3).toNat⟩ : Region).Disjoint ⟨s.gpr .s4, 192⟩)
    (dataScratch : (⟨s.gpr .a2, (s.gpr .a3).toNat⟩ : Region).Disjoint ⟨s.gpr .s4 + 192, 576⟩) :
    (Proof.Blake2.updateRISCV64 b).pre (u.callEntry.withRegions
      [⟨s.gpr .a2, (s.gpr .a3).toNat⟩] [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 192, 576⟩]) ∧
    Covers ([⟨s.gpr .a2, (s.gpr .a3).toNat⟩] ++
      [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 192, 576⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 192, 576⟩] u.wr := by
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have src : u.gpr .a2 = s.gpr .a2 := hu.other _ (by decide) (by decide)
  have len : u.gpr .a3 = s.gpr .a3 := hu.other _ (by decide) (by decide)
  have hp : (Proof.Blake2.updateRISCV64 b).pre (u.callEntry.withRegions
      [⟨s.gpr .a2, (s.gpr .a3).toNat⟩] [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 192, 576⟩]) := by
    simp only [Proof.Blake2.updateRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g .a0 (by decide), g .a2 (by decide), g .a3 (by decide), g .a4 (by decide),
      hu.state, hu.scratch, src, len]
    exact ⟨trivial, rfl, Offset.base_disjoint _ (by decide) (by decide), dataState, dataScratch⟩
  have writes : Covers [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 192, 576⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .s4, 16384⟩, hu.wr.symm ▸ hwr, ?_⟩
    rcases hr with rfl | rfl
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
    · exact ⟨192, rfl, by change 192 + 576 ≤ 16384; decide⟩
  have cover : Covers ([⟨s.gpr .a2, (s.gpr .a3).toNat⟩] ++
      [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 192, 576⟩]) (u.rd ++ u.wr) := by
    intro a n ⟨r, hr, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · rw [hu.rd, hu.wr]; exact hdata a n ⟨r, hr, hc⟩
    · obtain ⟨r', hr', hc'⟩ := writes a n ⟨r, hr, hc⟩
      exact ⟨r', List.mem_append_right _ hr', hc'⟩
  exact ⟨hp, cover, writes⟩

theorem update_ok (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .s4) d)
    (count : s.gpr .a1 = BitVec.ofNat 64 d.length)
    (bound : d.length + (s.gpr .a3).toNat < 2 ^ 64)
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .a2, (s.gpr .a3).toNat⟩] (s.rd ++ s.wr))
    (dataState : (⟨s.gpr .a2, (s.gpr .a3).toNat⟩ : Region).Disjoint ⟨s.gpr .s4, 192⟩)
    (dataScratch : (⟨s.gpr .a2, (s.gpr .a3).toNat⟩ : Region).Disjoint ⟨s.gpr .s4 + 192, 576⟩) :
    WP isa update s fun t =>
      Repr b h0 t.mem (s.gpr .s4) (d ++ bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 192, 576⟩] s.mem t.mem := by
  unfold update
  refine WP.seq ((updateArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have src : u.gpr .a2 = s.gpr .a2 := hu.other _ (by decide) (by decide)
  have len : u.gpr .a3 = s.gpr .a3 := hu.other _ (by decide) (by decide)
  have cnt : u.gpr .a1 = s.gpr .a1 := hu.other _ (by decide) (by decide)
  obtain ⟨hp, cover, writes⟩ := update_call_hyps s u hu hwr hdata dataState dataScratch
  refine WP.call (k := Proof.Blake2.updateRISCV64 b) update_callee hp cover writes ?_ update_noFrames
  intro t rd wr sp' frame cs _ post
  simp only [Proof.Blake2.updateRISCV64, Proof.Blake2.updatePost, State.withRegions_gpr,
    State.withRegions_mem, State.callEntry_mem, g .a0 (by decide), g .a1 (by decide),
    g .a2 (by decide), g .a3 (by decide), hu.state, src, len, cnt, hu.mem] at post
  refine ⟨post h0 d repr count bound, fun r hr => (cs r hr).trans ?_, rd.trans hu.rd,
    wr.trans hu.wr, sp'.trans hu.sp, by simpa only [hu.mem] using frame⟩
  exact hu.other r (preserved_ne hr) (preserved_ne hr)

/-! ## `finalize` -/

structure FinalizeArgs (s t : State) : Prop where
  state : t.gpr .a0 = s.gpr .s4
  digest : t.gpr .a2 = s.gpr .s4 + 768
  scratch : t.gpr .a3 = s.gpr .s4 + 192
  other : ∀ r, r ≠ .a0 → r ≠ .a2 → r ≠ .a3 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem finalizeArgs_ok (s : State) :
    WP isa (.block finalizeArgs) s (FinalizeArgs s) :=
  wp_mv fun a ha => wp_addi (by decide) fun c hc => wp_addi (by decide) fun t ht => WP.block_nil
    ⟨by rw [ht.other _ (by decide), hc.other _ (by decide), ha.gpr],
      by rw [ht.other _ (by decide), hc.gpr, ha.other _ (by decide)]; rfl,
      by rw [ht.gpr, hc.other _ (by decide), ha.other _ (by decide)]; rfl,
      fun r h1 h2 h3 => by rw [ht.other _ h3, hc.other _ h2, ha.other _ h1],
      by rw [ht.mem, hc.mem, ha.mem], by rw [ht.rd, hc.rd, ha.rd], by rw [ht.wr, hc.wr, ha.wr],
      by rw [ht.sp, hc.sp, ha.sp]⟩

/-- The narrowed finalization call, independently of the represented message. -/
theorem finalize_call_hyps (s u : State) (hu : FinalizeArgs s u)
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr) :
    (Proof.Blake2.finalizeRISCV64 b).pre (u.callEntry.withRegions []
      [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 768, 64⟩, ⟨s.gpr .s4 + 192, 576⟩]) ∧
    Covers ([] ++ [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 768, 64⟩,
      ⟨s.gpr .s4 + 192, 576⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 768, 64⟩, ⟨s.gpr .s4 + 192, 576⟩] u.wr := by
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have hp : (Proof.Blake2.finalizeRISCV64 b).pre (u.callEntry.withRegions []
      [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 768, 64⟩, ⟨s.gpr .s4 + 192, 576⟩]) := by
    simp only [Proof.Blake2.finalizeRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g .a0 (by decide), g .a2 (by decide), g .a3 (by decide),
      hu.state, hu.digest, hu.scratch]
    exact ⟨trivial, rfl, Offset.base_disjoint _ (by decide) (by decide),
      Offset.base_disjoint _ (by decide) (by decide), (Offset.disjoint _ (by decide) (by decide) (by decide)).symm⟩
  have writes : Covers [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 768, 64⟩, ⟨s.gpr .s4 + 192, 576⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .s4, 16384⟩, hu.wr.symm ▸ hwr, ?_⟩
    rcases hr with rfl | rfl | rfl
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
    · exact ⟨768, rfl, by change 768 + 64 ≤ 16384; decide⟩
    · exact ⟨192, rfl, by change 192 + 576 ≤ 16384; decide⟩
  have cover : Covers ([] ++ [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 768, 64⟩,
      ⟨s.gpr .s4 + 192, 576⟩]) (u.rd ++ u.wr) := by
    intro a n h
    obtain ⟨r, hr, hc⟩ := writes a n h
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  exact ⟨hp, cover, writes⟩

theorem finalize_ok (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .s4) d)
    (count : s.gpr .a1 = BitVec.ofNat 64 d.length) (bound : d.length < 2 ^ 64)
    (hwr : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr) :
    WP isa finalize s fun t =>
      bytesAt t.mem (s.gpr .s4 + 768) 64 = Spec.Blake2.finalHash b h0 d ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨s.gpr .s4, 192⟩, ⟨s.gpr .s4 + 768, 64⟩, ⟨s.gpr .s4 + 192, 576⟩] s.mem t.mem := by
  unfold finalize
  refine WP.seq ((finalizeArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have cnt : u.gpr .a1 = s.gpr .a1 := hu.other _ (by decide) (by decide) (by decide)
  obtain ⟨hp, cover, writes⟩ := finalize_call_hyps s u hu hwr
  refine WP.call (k := Proof.Blake2.finalizeRISCV64 b) finalize_callee hp cover writes ?_
    finalize_noFrames
  intro t rd wr sp' frame cs _ post
  simp only [Proof.Blake2.finalizeRISCV64, Proof.Blake2.finalizePost, State.withRegions_gpr,
    State.withRegions_mem, State.callEntry_mem, g .a0 (by decide), g .a1 (by decide),
    g .a2 (by decide), hu.state, hu.digest, cnt, hu.mem] at post
  refine ⟨post h0 d repr bound count, fun r hr => (cs r hr).trans ?_, rd.trans hu.rd, wr.trans hu.wr,
    sp'.trans hu.sp, by simpa only [hu.mem] using frame⟩
  exact hu.other r (preserved_ne hr) (preserved_ne hr) (preserved_ne hr)

end VG.Proof.Argon2.RISCV64.HPrime
