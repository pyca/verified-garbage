module

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Backend
public import VerifiedGarbage.Proof.Argon2.HPrime
public import VerifiedGarbage.Proof.MdStream.AArch64.Common
public import VerifiedGarbage.Impl.Argon2.AArch64.HPrime
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.Proof.Blake2.Stream
public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Argon2.AArch64.HPrime.Update`, which this module and modules that import it used -/

section

/-! # H′: absorbing bytes with the selected BLAKE2b backend -/

@[expose] public section

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

theorem updateArgs_ok (s : State) : WP isa (.block updateArgs) s (UpdateArgs s) := by
  apply WP.of_runBlock
  simp only [updateArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    show (0 : Nat) < 4096 from by decide, show (192 : Nat) < 4096 from by decide,
    State.read, Size.bits, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write, h1, h2, ite_false]

/-- The narrowed streaming call, without assumptions about message contents. -/
theorem update_call_hyps (s u : State) (hu : UpdateArgs s u)
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
  refine WP.seq ((updateArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp := hu.sp
  have src : u.gpr .x2 = s.gpr .x2 := hu.other _ (by decide) (by decide)
  have len : u.gpr .x3 = s.gpr .x3 := hu.other _ (by decide) (by decide)
  have cnt : u.gpr .x1 = s.gpr .x1 := hu.other _ (by decide) (by decide)
  obtain ⟨hp, cover, writes⟩ := update_call_hyps s u hu hsp hwr hdata dataState dataScratch stackWork stackData
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

end

/-! ### `Argon2.AArch64.HPrime.Fixed`, which this module and modules that import it used -/

section

/-! # H′: arguments for a fixed workspace buffer -/

@[expose] public section

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
    WP isa (.block (fixedArgs offset size)) s fun t => FixedArgs s t offset size := by
  have hsize : (BitVec.ofNat 16 size).setWidth 64 = BitVec.ofNat 64 size := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (by omega_using [hn] : size < 2 ^ 64)]
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

end

/-! ### `Argon2.AArch64.HPrime.Frame`, which this module and modules that import it used -/

section

/-! # H′: the memory changed by hashing a workspace buffer -/

@[expose] public section

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
  apply workspace_frame p sp [(0, 192), (192, 576)] 16 (by decide) (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.add_zero,
    show BitVec.ofNat 64 192 = (192 : Addr) from rfl] using h

theorem finalize_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩, ⟨p + 768, 64⟩, ⟨p + 192, 576⟩, below sp 16] m m') :
    Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply workspace_frame p sp [(0, 192), (768, 64), (192, 576)] 16 (by decide) (by decide)
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

theorem Keeps.x24 {s t : State} (h : Keeps s t) : t.gpr .x24 = s.gpr .x24 :=
  h.regs _ (by decide) (by decide)

theorem Keeps.trans {s t u : State} (h : Keeps s t) (h' : Keeps t u) : Keeps s u where
  regs r hr h30 := (h'.regs r hr h30).trans (h.regs r hr h30)
  rd := h'.rd.trans h.rd
  wr := h'.wr.trans h.wr
  sp := h'.sp.trans h.sp
  frame := h.frame.trans (by simpa only [h.x24, h.sp] using h'.frame)

theorem Keeps.bytes {s t : State} (h : Keeps s t) (r : Region) (bound : r.len ≤ 2 ^ 64)
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

theorem Keeps.prefix {s t : State} (h : Keeps s t)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    Spec.Blake2.bytesAt t.mem (s.gpr .x24 + 832) 4 =
      Spec.Blake2.bytesAt s.mem (s.gpr .x24 + 832) 4 :=
  h.bytes ⟨s.gpr .x24 + 832, 4⟩ (show 4 ≤ 2 ^ 64 by decide)
    (Offset.base_disjoint _ (e := 832) (n := 4) (k := 832) (by decide) (by decide)).symm
    (stackWork.sub_right (Offset.sub_base _ (by decide : 832 + 4 ≤ 16384))).symm

end VG.Proof.Argon2.AArch64.HPrime

end

end

/-! ### `Argon2.AArch64.HPrime.Init`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.HPrime.Finalize`, which the modules that import this one used -/

section

/-! # H′: finishing a BLAKE2b hash -/

@[expose] public section

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

theorem finalizeArgs_ok (s : State) : WP isa (.block finalizeArgs) s (FinalizeArgs s) := by
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
theorem finalize_call_hyps (s u : State) (hu : FinalizeArgs s u)
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
  refine WP.seq ((finalizeArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp := hu.sp
  have cnt : u.gpr .x1 = s.gpr .x1 := hu.other _ (by decide) (by decide) (by decide)
  obtain ⟨hp, cover, writes⟩ := finalize_call_hyps s u hu hsp hwr stackWork
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

end

/-! # H′: initializing an unkeyed BLAKE2b computation -/

@[expose] public section

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

theorem initArgs_ok (s : State) : WP isa (.block initArgs) s (InitArgs s) := by
  apply WP.of_runBlock
  simp only [initArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    show (0 : Nat) < 4096 from by decide, show (832 : Nat) < 4096 from by decide,
    show (16 * 0 : Nat) < 64 from by decide, State.read, Size.bits,
    BitVec.setWidth_eq, BitVec.add_zero,
    ite_true, ite_false, reduceCtorEq, RegUpd.gpr_write, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]

/-- Narrow the callee's permissions to its state and empty key. -/
theorem init_call_hyps (s u : State) (hu : InitArgs s u)
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
  refine WP.seq ((initArgs_ok s).mono fun u hu => ?_)
  have hlen' : u.gpr .x1 = s.gpr .x1 := hu.other _ (by decide) (by decide) (by decide)
  have g : ∀ r, r ∉ linkRegs → u.callEntry.gpr r = u.gpr r := fun _ hr => State.callEntry_gpr u hr
  obtain ⟨hp, cover, writes⟩ := init_call_hyps s u hu hlen hwr
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

end

/-! ### `Argon2.AArch64.HPrime.Setup`, which this module and modules that import it used -/

section

/-! # H′: saving the caller and writing the length prefix -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

/-- Save the seven caller registers and then the four-byte length prefix. -/
def setupMem (s : State) : Mem :=
  (saved.foldl (fun m rd => m.writeW (s.gpr .x4 + BitVec.ofNat 64 rd.2) (s.gpr rd.1)) s.mem).writeW
    (s.gpr .x4 + 832) ((s.gpr .x3).setWidth 32)

theorem setupMem_frame (s : State) :
    Frame [⟨s.gpr .x4 + 832, 64⟩] s.mem (setupMem s) := by
  have store {m : Mem} (h : Frame [⟨s.gpr .x4 + 832, 64⟩] s.mem m)
      (d w : Nat) (v : BitVec w) (lo : 832 ≤ d) (hi : d + w / 8 ≤ 896) :
      Frame [⟨s.gpr .x4 + 832, 64⟩] s.mem (m.writeW (s.gpr .x4 + BitVec.ofNat 64 d) v) :=
    h.writeW (List.mem_singleton_self _) v (Offset.contains _ lo hi (by decide))
  unfold setupMem saved
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
    Spec.Blake2.bytesAt (setupMem s) (s.gpr .x4 + 832) 4 =
      Spec.Argon2.le32 (s.gpr .x3).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl)]
  unfold setupMem
  rw [Mem.readW_writeW_self32]
  rfl

theorem setupMem_saved (s : State) (r : Reg) (d : Nat) (hr : (r, d) ∈ saved) :
    (setupMem s).readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 = s.gpr r := by
  have skip64 (m : Mem) (v : BitVec 64) (d e : Nat)
      (sep : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
      (m.writeW (s.gpr .x4 + BitVec.ofNat 64 e) v).readW
        (s.gpr .x4 + BitVec.ofNat 64 d) 64 = m.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 :=
    Mem.readW_writeW_sep (Offset.sep _ sep hd he) (by decide)
  have skip32 (m : Mem) (v : BitVec 32) (d : Nat) (lo : 836 ≤ d) (hi : d + 8 ≤ 2 ^ 64) :
      (m.writeW (s.gpr .x4 + 832) v).readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 =
        m.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 :=
    Mem.readW_writeW_sep (Offset.sep _ (Or.inr lo) hi (by decide)) (by decide)
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp (disch := decide) only [setupMem, saved, List.foldl_cons, List.foldl_nil,
      skip32, skip64, Mem.readW_writeW_self64]

structure Setup (s t : State) : Prop where
  workspace : t.gpr .x24 = s.gpr .x4
  input : t.gpr .x20 = s.gpr .x0
  length : t.gpr .x21 = s.gpr .x1
  output : t.gpr .x22 = s.gpr .x2
  remaining : t.gpr .x23 = s.gpr .x3
  other : ∀ r, r ≠ .x24 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  mem : t.mem = setupMem s
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem setup_ok (s : State) (hw : (⟨s.gpr .x4, 16384⟩ : Region) ∈ s.wr) :
    WP isa (.block setup) s (Setup s) := by
  have write (d n : Nat) (h : d + n ≤ 16384) :
      InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 d) n :=
    ⟨_, hw, Offset.contains_base _ h (by omega_using [h])⟩
  have w832 := write 832 4 (by decide)
  have w840 := write 840 8 (by decide)
  have w848 := write 848 8 (by decide)
  have w856 := write 856 8 (by decide)
  have w864 := write 864 8 (by decide)
  have w872 := write 872 8 (by decide)
  have w888 := write 888 8 (by decide)
  have w880 := write 880 8 (by decide)
  apply WP.of_runBlock
  simp only [setup, saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
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

end

/-! ### `Argon2.AArch64.HPrime.Input`, which this module and modules that import it used -/

section

/-! # H′: arguments for the caller's input -/

@[expose] public section

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

theorem inputArgs_ok (s : State) : WP isa (.block inputArgs) s (InputArgs s) := by
  apply WP.of_runBlock
  simp only [inputArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    show (0 : Nat) < 4096 from by decide, show (16 * 0 : Nat) < 64 from by decide,
    State.read, Size.bits, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]

theorem InputArgs.keeps {s t : State} (h : InputArgs s t) : Keeps s t := by
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
      Keeps s t := by
  unfold absorbInput
  refine WP.seq ((inputArgs_ok s).mono fun u hu => ?_)
  have ku := hu.keeps
  have repr' : Repr b h0 u.mem (u.gpr .x24) headBytes := by rw [hu.mem, ku.x24]; exact repr
  have count : u.gpr .x1 = BitVec.ofNat 64 headBytes.length := by rw [prefixLen]; exact hu.count
  have bound : headBytes.length + (u.gpr .x3).toNat < 2 ^ 64 := by rw [prefixLen, hu.size]; omega_using [len]
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
  refine (update_ok v u h0 headBytes repr' count bound (by rw [ku.sp]; exact hsp) wr cover ds dw sw sd).mono ?_
  rintro t ⟨result, regs, rd, wr', sp', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', sp', update_frame _ _ frame⟩⟩
  simpa only [ku.x24, hu.mem, hu.data, hu.size] using result

end VG.Proof.Argon2.AArch64.HPrime

end

end

/-! ### `Argon2.AArch64.HPrime.Space`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.HPrime.Copy`, which this module and modules that import it used -/

section

/-! # H′: copying digest bytes -/

@[expose] public section

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
  mem : s.mem = writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)

theorem copyLoop_ok (s₀ : State) (src dst : Addr) (k : Nat)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 64)
    (hs : s₀.gpr .x2 = src) (hd : s₀.gpr .x22 = dst)
    (hn : s₀.gpr .x8 = BitVec.ofNat 64 k)
    (hr : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < k, InRegions s₀.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : Region.Disjoint ⟨src, k⟩ ⟨dst, k⟩) :
    WP isa (.loop (.block copyByte) (.nonzero .x .x8)) s₀ (CopyI s₀ src dst k k) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = k - j ∧ j < k ∧ CopyI s₀ src dst k j s)
    ?_ k s₀ ⟨0, by omega_using [], hk, by omega_using [], by simpa using hs, by simpa using hd,
      by simpa using hn, fun _ _ _ _ _ => rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hlen : (bytesAt s₀.mem src k).length = k := by simp [bytesAt]
  have htake : ((bytesAt s₀.mem src k).take j).length = j := by
    rw [List.length_take, hlen, Nat.min_eq_left (by omega_using [hj])]
  have hb : s.mem (src + BitVec.ofNat 64 j) = s₀.mem (src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    apply (writeBytes_frame s₀.mem dst _ (R := ⟨dst, k⟩)
      (by simpa only [BitVec.add_zero, htake] using
        (Offset.contains_base dst (k := k) (d := 0) (n := j) (by omega_using [hj]) (by decide)))).bytes
        (R := ⟨src, k⟩) _ (show k ≤ 2 ^ 64 by omega_using [hk']) hj
    simpa using hsep
  have hr' : InRegions (s.rd ++ s.wr) (s.gpr .x2) 1 := by
    rw [h.rd, h.wr, h.source]; exact hr j hj
  have hw' : InRegions s.wr (s.gpr .x22) 1 := by
    rw [h.wr, h.destination]; exact hw j hj
  refine (copyByte_ok s hr' hw').mono ?_
  rintro t ⟨hm, hs', hd', hn', ho, hrd, hwr⟩
  have hc : BitVec.ofNat 64 (k - j) - 1 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_using [hj] : 1 ≤ k - j)]
    congr 1
  have hi : CopyI s₀ src dst k (j + 1) t := by
    refine ⟨by omega_using [hj], ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, hrd.trans h.rd, hwr.trans h.wr, ?_⟩
    · rw [hs', h.source, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hd', h.destination, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hn', h.count, hc]
    · exact (ho r h1 h2 h3 h4).trans (h.other r h1 h2 h3 h4)
    · have hj' : j < (bytesAt s₀.mem src k).length := by omega_using [hj, hlen]
      rw [hm, h.source, h.destination, hb, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [htake]; omega_using [hk', hj]), htake]
      refine congrArg (fun b => (writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)).writeW
        (dst + BitVec.ofNat 64 j) b) ?_
      simp only [bytesAt, List.getElem_map, List.getElem_range]
  have hz' : (t.gpr .x8 == 0) = decide (k - (j + 1) = 0) := by
    rw [hi.count]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have ht := congrArg BitVec.toNat he
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk'] : k - (j + 1) < 2 ^ 64),
        show (0 : BitVec 64).toNat = 0 from rfl] using ht
    · intro he; rw [he]; rfl
  by_cases he : j + 1 = k
  · refine .inl ⟨?_, he ▸ hi⟩
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, bne, hz', show k - (j + 1) = 0 by omega_using [he], decide_true, Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, he], hi⟩
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, bne, hz', show k - (j + 1) ≠ 0 by omega_using [hj, he], decide_false, Bool.not_false]

end VG.Proof.Argon2.AArch64.HPrime

end

end

/-! ### `Argon2.AArch64.HPrime.Absorb`, which this module and modules that import it used -/

section

/-! # H′: absorbing the length prefix or previous digest -/

@[expose] public section

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
      Keeps s t := by
  unfold absorbFixed
  refine WP.seq ((fixedArgs_ok s offset size offsetUpper (by omega_using [sizeBound])).mono fun u hu => ?_)
  have p : u.gpr .x24 = s.gpr .x24 := hu.other _ (by decide) (by decide) (by decide)
  have sp := hu.sp
  have len : (u.gpr .x3).toNat = size := by
    rw [hu.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [sizeBound])]
  have wr : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [p, hu.wr]; exact hwr
  have hr : Repr b h0 u.mem (u.gpr .x24) [] := by rw [hu.mem, p]; exact repr
  have hc : u.gpr .x1 = BitVec.ofNat 64 ([] : List Byte).length := hu.count
  have hb : ([] : List Byte).length + (u.gpr .x3).toNat < 2 ^ 64 := by simp only [List.length_nil, Nat.zero_add, len]; omega_using [sizeBound]
  have cover : Covers [⟨u.gpr .x2, (u.gpr .x3).toNat⟩] (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .x24, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), offset, hu.data, ?_⟩
    change offset + (u.gpr .x3).toNat ≤ 16384
    rw [len]; exact sizeBound
  have ds : (⟨u.gpr .x2, (u.gpr .x3).toNat⟩ : Region).Disjoint ⟨u.gpr .x24, 192⟩ := by
    rw [hu.data, len, p]
    exact (Offset.base_disjoint _ (by omega_using [offsetLower]) (by omega_using [sizeBound])).symm
  have dw : (⟨u.gpr .x2, (u.gpr .x3).toNat⟩ : Region).Disjoint ⟨u.gpr .x24 + 192, 576⟩ := by
    rw [hu.data, len, p]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega_using [offsetLower]) (by omega_using [sizeBound]) (by decide)
  have sw : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
    rw [sp, p]; exact stackWork
  have sd : (below u.sp 16).Disjoint ⟨u.gpr .x2, (u.gpr .x3).toNat⟩ := by
    rw [sp, hu.data, len]
    exact stackWork.sub_right (Offset.sub_base _ sizeBound)
  refine (update_ok v u h0 [] hr hc hb (by rw [sp]; exact hsp) wr cover ds dw sw sd).mono ?_
  rintro t ⟨repr', regs, rd, wr', sp', frame⟩
  simp only [p, hu.data, len, hu.mem, List.nil_append] at repr'
  refine ⟨repr', fun r hr h30 => (regs r hr h30).trans ?_, rd.trans hu.rd, wr'.trans hu.wr, sp'.trans hu.sp, ?_⟩
  · have hn : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · simpa only [p, sp, hu.mem] using update_frame (u.gpr .x24) u.sp frame

end VG.Proof.Argon2.AArch64.HPrime

end

end

/-! ### `Argon2.AArch64.HPrime.Compare`, which this module and modules that import it used -/

section

/-! ### `Argon2.AArch64.HPrime.Length`, which this module and modules that import it used -/

section

/-! # H′: selecting the first digest length -/

@[expose] public section

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
    (h : Upd s t d v) (hd : d ∉ preserved) : Keeps s t := by
  refine ⟨fun r hr _ => h.other r ?_, h.rd, h.wr, h.sp, ?_⟩
  · intro he; subst r; exact hd hr
  · rw [h.mem]; exact Frame.refl _ _

theorem chooseLength_ok (s : State) (hb : (s.gpr .x23).toNat < 2 ^ 32) :
    WP isa chooseLength s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 (min (s.gpr .x23).toNat 64) ∧ Keeps s t := by
  unfold chooseLength
  refine WP.seq (wp_mov fun a ha => wp_subImm (by decide) fun b hb' =>
    wp_lsr (by decide) fun u hu => WP.block_nil ?_)
  have ku : Keeps s u :=
    (Keeps.of_upd ha (by decide)).trans
      ((Keeps.of_upd hb' (by decide)).trans (Keeps.of_upd hu (by decide)))
  have n : u.gpr .x1 = s.gpr .x23 := by
    rw [hu.other _ (by decide), hb'.other _ (by decide), ha.gpr]
  have comparison : u.gpr .x9 = if (s.gpr .x23).toNat < 65 then 1 else 0 := by
    rw [hu.gpr, hb'.gpr, ha.gpr]
    exact below65 _ hb
  have flag : isa.eval (.nonzero .x .x9) u = some (decide ((s.gpr .x23).toNat < 65)) := by
    by_cases hn : (s.gpr .x23).toNat < 65 <;>
      simp [eval, State.read, comparison, hn]
  refine WP.ite (decide ((s.gpr .x23).toNat < 65)) flag ?_ ?_
  · intro h
    have hn : (s.gpr .x23).toNat ≤ 64 := by have := of_decide_eq_true h; omega_using [this]
    apply WP.block_nil
    refine ⟨?_, ku⟩
    rw [n, Nat.min_eq_left hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro h
    have hn : 64 ≤ (s.gpr .x23).toNat := by have := of_decide_eq_false h; omega_using [this]
    refine wp_movz fun t ht => WP.block_nil ?_
    refine ⟨?_, ku.trans (Keeps.of_upd ht (by decide))⟩
    rw [Nat.min_eq_right hn]; exact ht.gpr

end VG.Proof.Argon2.AArch64.HPrime

end

end

/-! # H′: a bounded public length comparison -/

@[expose] public section

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
    WP isa (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63]) s (Compared s) := by
  refine wp_subImm (by decide) fun a ha => wp_lsr (by decide) fun t ht => WP.block_nil ?_
  refine ⟨?_, fun r hr => (ht.other r hr).trans (ha.other r hr), ht.mem.trans ha.mem,
    ht.rd.trans ha.rd, ht.wr.trans ha.wr, ht.sp.trans ha.sp⟩
  rw [ht.gpr, ha.gpr]
  exact below65 _ hb

theorem Compared.keeps {s t : State} (h : Compared s t) : Keeps s t := by
  refine ⟨fun r hr _ => h.other r ?_, h.rd, h.wr, h.sp, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [h.mem]; exact Frame.refl _ _

end VG.Proof.Argon2.AArch64.HPrime

end

end

/-! ### `Argon2.AArch64.HPrime.Output`, which this module and modules that import it used -/

section

/-! # H′: emitting a digest or its 32-byte prefix -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov wp_addImm wp_movz wp_subImm)
open VG.Spec.Blake2 (bytesAt)
open VG.WriteBytes

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn, hi] : i < 2 ^ 64),
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
  mem : t.mem = writeBytes s.mem (s.gpr .x22) (bytesAt s.mem (s.gpr .x24 + 768) k)

theorem copy_ok (s : State) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 64)
    (count : s.gpr .x8 = BitVec.ofNat 64 k)
    (work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < k, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .x24 + 768, k⟩ : Region).Disjoint ⟨s.gpr .x22, k⟩) :
    WP isa copy s (Copied s k) := by
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
      Offset.contains_base _ (by omega_using [hi, hi'] : 768 + i + 1 ≤ 16384) (by omega_using [hi, hi'])⟩
  have loop := copyLoop_ok u _ _ k lo (by omega_using [hi]) src (other .x22 (by decide))
    ((other .x8 (by decide)).trans count) read
    (by intro i hi'; rw [wr]; exact out i hi') sep
  obtain ⟨tr, t, he, ht⟩ := loop
  refine ⟨tr, t, he, ht.destination,
    fun r h1 h2 h3 h4 => (ht.other r h1 h2 h3 h4).trans (other r h3),
    ht.rd.trans rd, ht.wr.trans wr, (VG.AArch64.Exec.sp he).trans (hu.sp.trans ha.sp), ?_⟩
  rw [ht.mem, mem, List.take_of_length_le]
  simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl]

theorem Copied.frame {s t : State} {k : Nat} (h : Copied s k t) :
    Frame [⟨s.gpr .x22, k⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .x22) (d := 0) (n := k) (k := k) (by omega_using []) (by decide)

structure Emitted (s t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + 32
  remaining : t.gpr .x23 = s.gpr .x23 - 32
  other : ∀ r, r ≠ .x8 → r ≠ .x3 → r ≠ .x2 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = writeBytes s.mem (s.gpr .x22) (bytesAt s.mem (s.gpr .x24 + 768) 32)

theorem emitPrefix_ok (s : State)
    (work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .x24 + 768, 32⟩ : Region).Disjoint ⟨s.gpr .x22, 32⟩) :
    WP isa emitPrefix s (Emitted s) := by
  unfold emitPrefix
  refine WP.seq (wp_movz fun a ha => WP.block_nil ?_)
  have base : a.gpr .x24 = s.gpr .x24 := ha.other _ (by decide)
  have dst : a.gpr .x22 = s.gpr .x22 := ha.other _ (by decide)
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact work
  have outA : ∀ i < 32, InRegions a.wr (a.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact out
  have sepA : (⟨a.gpr .x24 + 768, 32⟩ : Region).Disjoint ⟨a.gpr .x22, 32⟩ := by
    rw [base, dst]; exact sep
  refine WP.seq ((copy_ok a 32 (by decide) (by decide) ha.gpr workA outA sepA).mono ?_)
  intro u hu
  refine wp_subImm (by decide) fun t ht => WP.block_nil ?_
  refine ⟨?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ht.rd.trans (hu.rd.trans ha.rd),
    ht.wr.trans (hu.wr.trans ha.wr), ht.sp.trans (hu.sp.trans ha.sp), ?_⟩
  · rw [ht.other _ (by decide), hu.output, dst]; rfl
  · rw [ht.gpr, hu.other _ (by decide) (by decide) (by decide) (by decide), ha.other _ (by decide)]
    rfl
  · exact (ht.other r h5).trans ((hu.other r h1 h2 h3 h4).trans (ha.other r h1))
  · rw [ht.mem, hu.mem, ha.mem, base, dst]

theorem Emitted.frame {s t : State} (h : Emitted s t) :
    Frame [⟨s.gpr .x22, 32⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .x22) (d := 0) (n := 32) (k := 32) (by decide) (by decide)

theorem Emitted.digest {s t : State} (h : Emitted s t)
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

end

/-! ### `Argon2.AArch64.HPrime.Chain`, which only this module used -/

section

/-! Merged from `Proof.Argon2.AArch64.HPrime.Next`. -/

@[expose] public section

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
        Spec.Argon2.H (s.gpr .x1).toNat (bytesAt s.mem (s.gpr .x24 + 768) 64) ∧ Keeps s t := by
  unfold next
  refine WP.seq ((init_ok v s hlen hwr).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, spA, frameA⟩
  have ka : Keeps s a := ⟨regsA, rdA, wrA, spA, init_frame _ _ frameA⟩
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
  refine WP.seq ((absorbFixed_ok v a _ 768 64 (by decide) (by rw [ka.sp]; exact hsp) (by decide) (by decide) reprA' wrA' swA).mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .x1).toNat 0) u.mem (u.gpr .x24)
      (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    rw [ku.x24]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_movz fun w hw => WP.block_nil ?_)
  have kw : Keeps u w := by
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
  refine (finalize_ok v w _ _ reprW count bound (by rw [ksw.sp]; exact hsp) wrW swW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, spT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, spT, finalize_frame _ _ frameT⟩⟩
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
      s (ChainStep s) := by
  refine WP.seq (wp_movz fun a ha => WP.block_nil ?_)
  have ka : Keeps s a := Keeps.of_upd ha (by decide)
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [ka.x24, ka.wr]; exact work
  have stackA : (below a.sp 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ka.x24, ka.sp]; exact stackWork
  have lengthA : (a.gpr .x1).toNat = 64 := by rw [ha.gpr]; rfl
  refine WP.seq ((next_ok v a (by rw [lengthA]; decide) (by rw [ka.sp]; exact hsp) workA stackA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .x22 = s.gpr .x22 := ksu.regs _ (by decide) (by decide)
  have digestU : bytesAt u.mem (s.gpr .x24 + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    simpa only [lengthA, ka.x24, ha.mem, bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ksu.x24, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .x24 + 768, 32⟩ : Region).Disjoint ⟨u.gpr .x22, 32⟩ := by
    rw [ksu.x24, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok u workU outU sepU).mono ?_)
  intro w hw
  have remainingW : (w.gpr .x23).toNat < 2 ^ 32 := by
    rw [hw.remaining, ksu.regs _ (by decide) (by decide),
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact remainingBound.1)]
    exact Nat.lt_of_le_of_lt (Nat.sub_le ..) remainingBound.2
  refine (compare_ok w remainingW).mono fun t compared => ?_
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
  · rw [mt, hw.mem, dstU, ksu.x24, ← digestU, bytesAt_take _ _ 32 64 (by decide)]
    exact bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
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

theorem ChainResult.refl (s : State) : ChainResult s 0 s :=
  ⟨by simp, by simp, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

theorem ChainResult.cons {s u t : State} {n : Nat} (step : ChainStep s u)
    (tail : ChainResult u n t) (bound : 32 * (n + 1) < 2 ^ 64)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, 32 * (n + 1)⟩)
    (stackOut : (below s.sp 16).Disjoint ⟨s.gpr .x22, 32 * (n + 1)⟩) :
    ChainResult s (n + 1) t := by
  have base := step.regs .x24 (by decide) (by decide) (by decide) (by decide)
  have sp := step.sp
  have sum : 32 * (n + 1) = 32 + 32 * n := by omega_arith
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
  · exact (extend 0 32 (by omega_arith) (by simpa only [BitVec.add_zero] using step.frame)).trans
      (extend 32 (32 * n) (by omega_arith) tf)
  · rw [← base, tail.digest, base, step.digest, Proof.Argon2.chainDigest]
  · have before : bytesAt t.mem (s.gpr .x22) 32 = bytesAt u.mem (s.gpr .x22) 32 := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .x22, 32⟩) _ (show 32 ≤ 2 ^ 64 by decide) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left
          (Region.sub_prefix (by omega_arith))
      · exact stackOut.symm.sub_left (Region.sub_prefix (by omega_arith))
      · exact Offset.base_disjoint _ (e := 32) (n := 32 * n) (k := 32) (by decide) (by omega_arith)
    rw [sum, Proof.Blake2.bytesAt_add, before, step.bytes,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl, ← step.output, tail.bytes,
      base, step.digest]
    rw [Proof.Argon2.chainPrefixes]

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
    WP isa (chain v.hash) s (ChainResult s n) := by
  induction n generalizing s with
  | zero => omega_arith
  | succ n ih =>
    have out32 : ∀ i < 32, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1 :=
      fun i hi => out i (by omega_arith)
    have sep32 := sep.sub_right (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega_arith))
    obtain ⟨trace, u, run, step⟩ := chainStep_ok v s hsp
      (by rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith) work out32 sep32 stackWork
    have base := step.regs .x24 (by decide) (by decide) (by decide) (by decide)
    have sp := step.sp
    have countU : u.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen) := by
      rw [step.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        Offset.ofNat_sub_ofNat (by omega_arith : 32 ≤ 32 * (n + 1) + lastLen)]
      rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_arith]
    have compareU : u.gpr .x9 = if 32 * n + lastLen < 65 then 1 else 0 := by
      rw [step.comparison, ← step.remaining, countU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    cases n with
    | zero =>
      have flag : isa.eval (.zero .x .x9) u = some false := by
        simp [eval, State.read, compareU, show lastLen < 65 by omega_arith]
      exact ⟨_, u, .loopExit run flag, (ChainResult.refl u).cons step (by omega_arith) sep stackOut⟩
    | succ n =>
      have workU : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [base, step.wr]; exact work
      have outU : ∀ i < 32 * (n + 1), InRegions u.wr (u.gpr .x22 + BitVec.ofNat 64 i) 1 := by
        intro i hi
        rw [step.wr, step.output, BitVec.add_assoc,
          show (32 : Addr) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
        exact out (32 + i) (by omega_arith)
      have suffix : Region.Sub ⟨u.gpr .x22, 32 * (n + 1)⟩ ⟨s.gpr .x22, 32 * (n + 1 + 1)⟩ := by
        rw [step.output]
        exact Offset.sub_base _ (by omega_arith : 32 + 32 * (n + 1) ≤ 32 * (n + 1 + 1))
      have sepU : (⟨u.gpr .x24, 16384⟩ : Region).Disjoint ⟨u.gpr .x22, 32 * (n + 1)⟩ := by
        rw [base]; exact sep.sub_right suffix
      have swU : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
        rw [sp, base]; exact stackWork
      have soU : (below u.sp 16).Disjoint ⟨u.gpr .x22, 32 * (n + 1)⟩ := by
        rw [sp]; exact stackOut.sub_right suffix
      obtain ⟨trace', t, run', result⟩ := ih u (by omega_arith) (by omega_arith) (by rw [sp]; exact hsp) countU workU outU sepU swU soU
      have flag : isa.eval (.zero .x .x9) u = some true := by
        simp [eval, State.read, compareU, show ¬ 32 * (n + 1) + lastLen < 65 by omega_arith]
      exact ⟨_, t, .loopNext run flag run', result.cons step (by omega_arith) sep stackOut⟩

end VG.Proof.Argon2.AArch64.HPrime

end

end


/-! Merged from `Proof.Argon2.AArch64.HPrime.Written`. -/

@[expose] public section

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

theorem Written.x24 {s t : State} {xs : List Byte} (h : Written s xs t) :
    t.gpr .x24 = s.gpr .x24 := h.regs _ (by decide) (by decide) (by decide) (by decide)

theorem Written.of_keeps {s t : State} (h : Keeps s t) : Written s [] t := by
  refine ⟨?_, fun r hr h30 _ _ => h.regs r hr h30, h.rd, h.wr, h.sp, ?_, rfl⟩
  · exact (h.regs .x22 (by decide) (by decide)).trans (BitVec.add_zero _).symm
  · exact h.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩

theorem Written.before_keeps {s u t : State} {xs : List Byte} (h : Written u xs t)
    (k : Keeps s u) : Written s xs t := by
  have dst := k.regs .x22 (by decide) (by decide)
  refine ⟨by rw [h.output, dst], fun r hr h30 h1 h2 => (h.regs r hr h30 h1 h2).trans (k.regs r hr h30),
    h.rd.trans k.rd, h.wr.trans k.wr, h.sp.trans k.sp, ?_, ?_⟩
  · have before : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16,
        ⟨s.gpr .x22, xs.length⟩] s.mem u.mem :=
      k.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    exact before.trans (by simpa only [dst, k.x24, k.sp] using h.frame)
  · rw [← dst]; exact h.bytes

theorem Written.of_copied {s t : State} {k : Nat} (h : Copied s k t) (hk : k < 2 ^ 64) :
    Written s (bytesAt s.mem (s.gpr .x24 + 768) k) t := by
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
    exact bytesAt_writeBytes _ _ _ (by rw [len]; exact hk)

theorem Written.of_emitted {s t : State} (h : Emitted s t) :
    Written s (bytesAt s.mem (s.gpr .x24 + 768) 32) t := by
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
    exact bytesAt_writeBytes _ _ _ (by rw [len]; decide)

theorem Written.of_chain {s t : State} {n : Nat} (h : ChainResult s n t) :
    Written s (Proof.Argon2.chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)) t := by
  refine ⟨?_, h.regs, h.rd, h.wr, h.sp, ?_, ?_⟩
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.output
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.frame
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.bytes

theorem Written.trans {s u t : State} {xs ys : List Byte} (first : Written s xs u)
    (last : Written u ys t) (bound : xs.length + ys.length < 2 ^ 64)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, xs.length + ys.length⟩)
    (stack : (below s.sp 16).Disjoint ⟨s.gpr .x22, xs.length + ys.length⟩) :
    Written s (xs ++ ys) t := by
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
  · exact (extend 0 xs.length (by omega_using []) (by simpa only [BitVec.add_zero] using first.frame)).trans
      (extend xs.length ys.length (by omega_using []) tf)
  · have before : bytesAt t.mem (s.gpr .x22) xs.length = bytesAt u.mem (s.gpr .x22) xs.length := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .x22, xs.length⟩) _ (show xs.length ≤ 2 ^ 64 by omega_using [bound]) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Region.sub_prefix (by omega_using []))
      · exact stack.symm.sub_left (Region.sub_prefix (by omega_using []))
      · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [bound])
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
    (h : Space s n) (written : Written s xs t) (size : xs.length + k ≤ n) : Space t k := by
  have suffix : Region.Sub ⟨t.gpr .x22, k⟩ ⟨s.gpr .x22, n⟩ := by
    rw [written.output]; exact Offset.sub_base _ size
  refine ⟨by have := h.bound; omega_using [size, this], by rw [written.sp]; exact h.spBound, ?_, ?_, ?_, ?_, ?_⟩
  · rw [written.wr, written.x24]; exact h.work
  · intro i hi
    rw [written.wr, written.output, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.out (xs.length + i) (by omega_using [size, hi])
  · rw [written.x24]; exact h.sep.sub_right suffix
  · rw [written.x24, written.sp]; exact h.stackWork
  · rw [written.sp]; exact h.stackOut.sub_right suffix

theorem Space.keeps {s t : State} {n : Nat} (h : Space s n) (k : Keeps s t) : Space t n :=
  h.advance (Written.of_keeps k) (by simp only [List.length_nil, Nat.zero_add, Nat.le_refl])

theorem Space.prefix {s : State} {n k : Nat} (h : Space s n) (hk : k ≤ n) : Space s k := by
  refine ⟨by have := h.bound; omega_using [hk, this], h.spBound, h.work, fun i hi => h.out i (by omega_using [hk, hi]),
    h.sep.sub_right (Region.sub_prefix hk), h.stackWork, h.stackOut.sub_right (Region.sub_prefix hk)⟩

theorem Space.join {s u t : State} {xs ys : List Byte} {n : Nat} (h : Space s n)
    (first : Written s xs u) (last : Written u ys t) (size : xs.length + ys.length ≤ n) :
    Written s (xs ++ ys) t :=
  first.trans last (by have := h.bound; omega_using [size, this])
    (h.sep.sub_right (Region.sub_prefix size)) (h.stackOut.sub_right (Region.sub_prefix size))

theorem copyRemaining_ok (s : State) (n : Nat) (space : Space s n)
    (lo : 1 ≤ n) (hi : n ≤ 64) (count : s.gpr .x23 = BitVec.ofNat 64 n) :
    WP isa copyRemaining s fun t => Written s (bytesAt s.mem (s.gpr .x24 + 768) n) t := by
  unfold copyRemaining
  refine WP.seq (wp_mov fun a ha => WP.block_nil ?_)
  have base := ha.other .x24 (by decide)
  have dst := ha.other .x22 (by decide)
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact space.work
  have outA : ∀ i < n, InRegions a.wr (a.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact space.out
  have sepA : (⟨a.gpr .x24 + 768, n⟩ : Region).Disjoint ⟨a.gpr .x22, n⟩ := by
    rw [base, dst]; exact space.sep.sub_left (Offset.sub_base _ (by omega_using [hi] : 768 + n ≤ 16384))
  refine (copy_ok a n lo hi (ha.gpr.trans count) workA outA sepA).mono ?_
  intro t ht
  have result := Written.of_copied ht (by have := space.bound; omega_using [hi])
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

end

/-! ### `Argon2.AArch64.HPrime.Contract`, which this module and modules that import it used -/

section

/-! # H′: a local ARM64 contract -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64

def inputR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
def outputR (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
def workR (s : State) : Region := ⟨s.gpr .x4, 16384⟩
def stackR (s : State) : Region := below s.sp 16

def localContract : Contract isa where
  pre s := s.rd = [inputR s] ∧ s.wr = [outputR s, workR s] ∧
    (s.gpr .x1).toNat < 2 ^ 32 ∧ 1 ≤ (s.gpr .x3).toNat ∧ (s.gpr .x3).toNat < 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧
    (inputR s).Disjoint (workR s) ∧ (outputR s).Disjoint (workR s) ∧
    (stackR s).Disjoint (inputR s) ∧ (stackR s).Disjoint (outputR s) ∧ (stackR s).Disjoint (workR s)
  post s t := Spec.Blake2.bytesAt t.mem (s.gpr .x2) (s.gpr .x3).toNat =
    Spec.Argon2.hPrime (s.gpr .x3).toNat (Spec.Blake2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s t := s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4 ∧ s.sp = t.sp

end VG.Proof.Argon2.AArch64.HPrime

end

end

/-! Merged from `Proof.Argon2.AArch64.HPrime.Restore`. -/

@[expose] public section

section
/-! # H′: restoring the caller's registers -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

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
    ⟨_, readable, Offset.contains_base _ h (by omega_arith)⟩
  obtain r840 := read 840 (by decide)
  obtain r848 := read 848 (by decide)
  obtain r856 := read 856 (by decide)
  obtain r864 := read 864 (by decide)
  obtain r872 := read 872 (by decide)
  obtain r888 := read 888 (by decide)
  obtain r880 := read 880 (by decide)
  obtain v840 := values .x19 840 (by decide)
  obtain v848 := values .x20 848 (by decide)
  obtain v856 := values .x21 856 (by decide)
  obtain v864 := values .x22 864 (by decide)
  obtain v872 := values .x23 872 (by decide)
  obtain v888 := values .x30 888 (by decide)
  obtain v880 := values .x24 880 (by decide)
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
      bytesAt t.mem (s.gpr .x24 + 768) 64 = Spec.Blake2.finalHash b h0 d ∧ Keeps s t := by
  unfold finishInput
  refine WP.seq (wp_mov fun a ha => wp_addImm (by decide) fun u hu => WP.block_nil ?_)
  obtain ku : Keeps s u := by
    refine ⟨fun r hr _ => ?_, hu.rd.trans ha.rd, hu.wr.trans ha.wr, hu.sp.trans ha.sp, ?_⟩
    · have hn : r ≠ .x1 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hu.other r hn).trans (ha.other r hn)
    · rw [hu.mem, ha.mem]; exact Frame.refl _ _
  obtain repr' : Repr b h0 u.mem (u.gpr .x24) d := by rw [hu.mem, ha.mem, ku.x24]; exact repr
  obtain count : u.gpr .x1 = BitVec.ofNat 64 d.length := by
    rw [hu.gpr, ha.gpr, length, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.add_comm _ _
  obtain len : d.length < 2 ^ 64 := by rw [length]; omega_arith
  obtain wr : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ku.x24, ku.wr]; exact hwr
  obtain sw : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
    rw [ku.x24, ku.sp]; exact stackWork
  refine (finalize_ok v u h0 d repr' count len (by rw [ku.sp]; exact hsp) wr sw).mono ?_
  rintro t ⟨out, regs, rd, wr', sp', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', sp', finalize_frame _ _ frame⟩⟩
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
      Keeps s t := by
  unfold first
  refine WP.seq ((chooseLength_ok s hlen.2).mono ?_)
  rintro a ⟨lengthA, ka⟩
  obtain na : (a.gpr .x1).toNat = min (s.gpr .x23).toNat 64 := by
    rw [lengthA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain wrA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [ka.x24, ka.wr]; exact hwr
  obtain swA : (below a.sp 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ka.x24, ka.sp]; exact stackWork
  obtain lenA : 1 ≤ (a.gpr .x1).toNat ∧ (a.gpr .x1).toNat ≤ 64 := by rw [na]; omega_arith
  refine WP.seq ((init_ok v a lenA wrA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  obtain ku : Keeps a u := ⟨regsU, rdU, wrU, spU, init_frame _ _ frameU⟩
  obtain ksu := ka.trans ku
  obtain reprU' : Repr b (Spec.Blake2.init b (min (s.gpr .x23).toNat 64) 0) u.mem (u.gpr .x24) [] := by
    rw [ku.x24]; simpa only [na] using reprU
  obtain wrU' : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ksu.x24, ksu.wr]; exact hwr
  obtain swU : (below u.sp 16).Disjoint ⟨u.gpr .x24, 16384⟩ := by
    rw [ksu.x24, ksu.sp]; exact stackWork
  obtain headU : bytesAt u.mem (u.gpr .x24 + 832) 4 = Spec.Argon2.le32 (s.gpr .x23).toNat := by
    rw [ksu.x24, ksu.prefix stackWork]; exact headBytes
  refine WP.seq ((absorbFixed_ok v u _ 832 4 (by decide) (by rw [ksu.sp]; exact hsp) (by decide) (by decide) reprU' wrU' swU).mono ?_)
  rintro w ⟨reprW, kw⟩
  obtain ksw := ksu.trans kw
  obtain r12 : w.gpr .x20 = s.gpr .x20 := ksw.regs _ (by decide) (by decide)
  obtain r13 : w.gpr .x21 = s.gpr .x21 := ksw.regs _ (by decide) (by decide)
  obtain headLen : (Spec.Argon2.le32 (s.gpr .x23).toNat).length = 4 := by
    simp only [Spec.Argon2.le32, Spec.Blake2.wordBytes, List.length_map, List.length_range]
  obtain reprW' : Repr b (Spec.Blake2.init b (min (s.gpr .x23).toNat 64) 0) w.mem (w.gpr .x24)
      (Spec.Argon2.le32 (s.gpr .x23).toNat) := by
    rw [kw.x24]
    simpa only [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, headU] using reprW
  obtain wrW : (⟨w.gpr .x24, 16384⟩ : Region) ∈ w.wr := by rw [ksw.x24, ksw.wr]; exact hwr
  obtain dataW : Covers [⟨w.gpr .x20, (w.gpr .x21).toNat⟩] (w.rd ++ w.wr) := by
    rw [r12, r13, ksw.rd, ksw.wr]; exact hdata
  obtain dwW : (⟨w.gpr .x20, (w.gpr .x21).toNat⟩ : Region).Disjoint ⟨w.gpr .x24, 16384⟩ := by
    rw [r12, r13, ksw.x24]; exact dataWork
  obtain swW : (below w.sp 16).Disjoint ⟨w.gpr .x24, 16384⟩ := by
    rw [ksw.sp, ksw.x24]; exact stackWork
  obtain sdW : (below w.sp 16).Disjoint ⟨w.gpr .x20, (w.gpr .x21).toNat⟩ := by
    rw [ksw.sp, r12, r13]; exact stackData
  obtain inputW : bytesAt w.mem (w.gpr .x20) (w.gpr .x21).toNat =
      bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat := by
    rw [r12, r13]
    exact ksw.bytes _ (show (s.gpr .x21).toNat ≤ 2 ^ 64 by omega_arith)
      (dataWork.sub_right (Region.sub_prefix (by decide))) stackData.symm
  refine WP.seq ((absorbInput_ok v w _ _ headLen reprW' (by rw [r13]; exact len)
    (by rw [ksw.sp]; exact hsp) wrW dataW dwW swW sdW).mono ?_)
  rintro x ⟨reprX, kx⟩
  obtain ksx := ksw.trans kx
  obtain reprX' : Repr b (Spec.Blake2.init b (min (s.gpr .x23).toNat 64) 0) x.mem (x.gpr .x24)
      (Spec.Argon2.le32 (s.gpr .x23).toNat ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat) := by
    rw [kx.x24]; simpa only [inputW] using reprX
  obtain r13X : x.gpr .x21 = s.gpr .x21 := ksx.regs _ (by decide) (by decide)
  obtain length : (Spec.Argon2.le32 (s.gpr .x23).toNat ++ bytesAt s.mem (s.gpr .x20) (s.gpr .x21).toNat).length =
      4 + (x.gpr .x21).toNat := by
    rw [List.length_append, headLen, r13X]
    simp only [bytesAt, List.length_map, List.length_range]
  obtain wrX : (⟨x.gpr .x24, 16384⟩ : Region) ∈ x.wr := by rw [ksx.x24, ksx.wr]; exact hwr
  obtain swX : (below x.sp 16).Disjoint ⟨x.gpr .x24, 16384⟩ := by
    rw [ksx.sp, ksx.x24]; exact stackWork
  refine (finishInput_ok v x _ _ reprX' length (by rw [r13X]; exact len) (by rw [ksx.sp]; exact hsp) wrX swX).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, ksx.trans kt⟩
  obtain result := congrArg (List.take (min (s.gpr .x23).toNat 64)) out
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
    (space : Space s (32 * n + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen))
    (comparison : s.gpr .x9 = if 32 * n + lastLen < 65 then 1 else 0) :
    WP isa (.ite (.nonzero .x .x9) (.block []) (chain v.hash)) s (ChainResult s n) := by
  refine WP.ite (decide (32 * n + lastLen < 65)) (by by_cases h : 32 * n + lastLen < 65 <;>
    simp [eval, State.read, comparison, h]) ?_ ?_
  · intro h
    obtain hn : n = 0 := by have := of_decide_eq_true h; omega_arith
    subst n
    exact WP.block_nil (ChainResult.refl s)
  · intro h
    obtain hn : 1 ≤ n := by have := of_decide_eq_false h; omega_arith
    obtain p := space.prefix (show 32 * n ≤ 32 * n + lastLen by omega_arith)
    exact chain_ok v n lastLen s hn last space.bound space.spBound count p.work p.out p.sep p.stackWork p.stackOut

theorem extendDigest_ok (v : Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .x23 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (extendDigest v.hash) s fun t =>
      Written s ((bytesAt s.mem (s.gpr .x24 + 768) 64).take 32 ++
        chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)) t ∧
      (bytesAt t.mem (s.gpr .x24 + 768) 64).take lastLen =
        Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .x24 + 768) 64)) ∧
      t.gpr .x23 = BitVec.ofNat 64 lastLen := by
  unfold extendDigest
  obtain short := space.prefix (show 32 ≤ 32 * (n + 1) + lastLen by omega_arith)
  obtain sep32 := short.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok s short.work short.out sep32).mono ?_)
  intro a ha
  obtain wa := Written.of_emitted ha
  obtain lenA : (bytesAt s.mem (s.gpr .x24 + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  obtain spaceA : Space a (32 * n + lastLen) := space.advance wa (by rw [lenA]; omega_arith)
  obtain countA : a.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen) := by
    rw [ha.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
      Offset.ofNat_sub_ofNat (by omega_arith : 32 ≤ 32 * (n + 1) + lastLen)]
    rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_arith]
  obtain digestA : bytesAt a.mem (a.gpr .x24 + 768) 64 = bytesAt s.mem (s.gpr .x24 + 768) 64 := by
    rw [wa.x24]; exact ha.digest short.sep
  refine WP.seq ((compare_ok a (by rw [countA, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := spaceA.bound; omega_arith)]; exact spaceA.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  obtain countU : u.gpr .x23 = BitVec.ofNat 64 (32 * n + lastLen) :=
    (compared.other _ (by decide)).trans countA
  obtain compareU : u.gpr .x9 = if 32 * n + lastLen < 65 then 1 else 0 := by
    rw [compared.value, countA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceA.bound; omega_arith)]
  refine WP.seq ((maybeChain_ok v n lastLen u (spaceA.keeps ku) last countU compareU).mono ?_)
  intro w hw
  obtain ww := (Written.of_chain hw).before_keeps ku
  obtain digestU : bytesAt u.mem (u.gpr .x24 + 768) 64 = bytesAt s.mem (s.gpr .x24 + 768) 64 := by
    rw [compared.mem, ku.x24]; exact digestA
  obtain ww' : Written a (chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)) w := by
    simpa only [digestU] using ww
  obtain wsw := space.join wa ww' (by rw [lenA, Proof.Argon2.chainPrefixes_length]; omega_arith)
  obtain produced : ((bytesAt s.mem (s.gpr .x24 + 768) 32) ++
      chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)).length = 32 * (n + 1) := by
    rw [List.length_append, lenA, Proof.Argon2.chainPrefixes_length]; omega_arith
  obtain spaceW : Space w lastLen := space.advance wsw (by rw [produced])
  obtain countW : w.gpr .x23 = BitVec.ofNat 64 lastLen := by
    rw [hw.remaining, countU, Offset.ofNat_sub_ofNat (by omega_arith : 32 * n ≤ 32 * n + lastLen)]
    rw [Nat.add_sub_cancel_left]
  obtain digestW : bytesAt w.mem (w.gpr .x24 + 768) 64 =
      chainDigest n (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    rw [hw.regs .x24 (by decide) (by decide) (by decide) (by decide), hw.digest, digestU]
  refine WP.seq (wp_mov fun x hx => WP.block_nil ?_)
  obtain kx : Keeps w x := Keeps.of_upd hx (by decide)
  obtain spaceX := spaceW.keeps kx
  obtain lenX : (x.gpr .x1).toNat = lastLen := by
    rw [hx.gpr, countW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := spaceW.bound; omega_arith)]
  refine (next_ok v x (by rw [lenX]; omega_arith) spaceX.spBound spaceX.work spaceX.stackWork).mono ?_
  rintro t ⟨dt, kt⟩
  obtain wwt := Written.of_keeps (kx.trans kt)
  obtain written := space.join wsw wwt (by rw [produced, List.length_nil]; omega_arith)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.append_nil, bytesAt_take _ _ 32 64 (by decide)] using written
  · rw [lenX, kx.x24, hx.mem, digestW, wsw.x24] at dt
    exact dt
  · rw [kt.regs _ (by decide) (by decide), kx.regs _ (by decide) (by decide)]; exact countW

theorem longOutput_ok (v : Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .x23 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (.seq (extendDigest v.hash) copyRemaining) s fun t =>
      Written s (Spec.Argon2.longHash lastLen (n + 1) (bytesAt s.mem (s.gpr .x24 + 768) 64)) t := by
  refine WP.seq ((extendDigest_ok v n lastLen s space last count).mono ?_)
  rintro u ⟨written, digest, remaining⟩
  obtain len : ((bytesAt s.mem (s.gpr .x24 + 768) 64).take 32 ++
      chainPrefixes n (bytesAt s.mem (s.gpr .x24 + 768) 64)).length = 32 * (n + 1) := by
    simp only [List.length_append, List.length_take, bytesAt, List.length_map,
      List.length_range, Proof.Argon2.chainPrefixes_length]
    omega_arith
  obtain spaceU : Space u lastLen := space.advance written (by rw [len])
  refine (copyRemaining_ok u lastLen spaceU (by omega_arith) last.2 remaining).mono ?_
  intro t copied
  obtain out : bytesAt u.mem (u.gpr .x24 + 768) lastLen =
      Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .x24 + 768) 64)) := by
    rw [written.x24, ← bytesAt_take _ _ lastLen 64 last.2]; exact digest
  obtain all := space.join written copied (by
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
    (space : Space s n) (positive : 1 ≤ n) (count : s.gpr .x23 = BitVec.ofNat 64 n)
    (digest : (bytesAt s.mem (s.gpr .x24 + 768) 64).take (min n 64) =
      Spec.Argon2.H (min n 64) (Spec.Argon2.le32 n ++ input)) :
    WP isa (finishOutput v.hash) s (Written s (Spec.Argon2.hPrime n input)) := by
  unfold finishOutput
  refine WP.seq ((compare_ok s (by rw [count, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := space.bound; omega_arith)]; exact space.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  obtain countU : u.gpr .x23 = BitVec.ofNat 64 n := (compared.other _ (by decide)).trans count
  obtain compareU : u.gpr .x9 = if n < 65 then 1 else 0 := by
    rw [compared.value, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := space.bound; omega_arith)]
  apply WP.seq
  refine WP.ite (decide (n < 65)) (by by_cases h : n < 65 <;> simp [eval, State.read, compareU, h]) ?_ ?_
  · intro h
    obtain short : n ≤ 64 := by have := of_decide_eq_true h; omega_arith
    apply WP.block_nil
    refine (copyRemaining_ok u n (space.keeps ku) positive short countU).mono ?_
    intro t ht
    obtain result := ht.before_keeps ku
    obtain value : bytesAt u.mem (u.gpr .x24 + 768) n = Spec.Argon2.hPrime n input := by
      rw [compared.mem, ku.x24, ← bytesAt_take _ _ n 64 short]
      simpa only [Nat.min_eq_left short, Spec.Argon2.hPrime, ite_eq_left short] using digest
    rw [value] at result
    exact result
  · intro h
    obtain long : 64 < n := by have := of_decide_eq_false h; omega_arith
    let r := (n + 31) / 32 - 2
    let lastLen := n - 32 * r
    obtain bounds : 1 ≤ r ∧ 33 ≤ lastLen ∧ lastLen ≤ 64 ∧ 32 * r + lastLen = n :=
      Proof.Argon2.longHash_bounds n long
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega_arith)
    change r = q + 1 at hq
    obtain size : 32 * (q + 1) + lastLen = n := by rw [← hq]; exact bounds.2.2.2
    obtain spaceU : Space u (32 * (q + 1) + lastLen) := by rw [size]; exact space.keeps ku
    obtain countLong : u.gpr .x23 = BitVec.ofNat 64 (32 * (q + 1) + lastLen) := by rw [size]; exact countU
    apply WP.seq_iff.mp
    refine (longOutput_ok v q lastLen u spaceU ⟨bounds.2.1, bounds.2.2.1⟩ countLong).mono ?_
    intro t ht
    obtain result := ht.before_keeps ku
    obtain digestU : bytesAt u.mem (u.gpr .x24 + 768) 64 =
        Spec.Argon2.H 64 (Spec.Argon2.le32 n ++ input) := by
      rw [compared.mem, ku.x24]
      simpa only [Nat.min_eq_right (show 64 ≤ n by omega_arith), bytesAt_take _ _ 64 64 (by decide)] using digest
    obtain value : Spec.Argon2.longHash lastLen (q + 1) (bytesAt u.mem (u.gpr .x24 + 768) 64) =
        Spec.Argon2.hPrime n input := by
      rw [digestU, ← hq, Spec.Argon2.hPrime, ite_eq_right (show ¬ n ≤ 64 by omega_arith)]
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
      Frame [outputR s, workR s, stackR s] s.mem t.mem := by
  obtain ⟨rd, wr, len, lo, hi, hsp, dw, ow, sd, so, sw⟩ := pre
  obtain work : (workR s) ∈ s.wr := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unfold code
  refine WP.seq ((setup_ok s work).mono ?_)
  intro a ha
  have sp := ha.sp
  obtain workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by
    rw [ha.workspace, ha.wr]; exact work
  obtain dataA : Covers [⟨a.gpr .x20, (a.gpr .x21).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.input, ha.length, ha.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  obtain dwA : (⟨a.gpr .x20, (a.gpr .x21).toNat⟩ : Region).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ha.input, ha.length, ha.workspace]; exact dw
  obtain swA : (below (a.sp) 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [sp, ha.workspace]; exact sw
  obtain sdA : (below (a.sp) 16).Disjoint ⟨a.gpr .x20, (a.gpr .x21).toNat⟩ := by
    rw [sp, ha.input, ha.length]; exact sd
  obtain inputA : bytesAt a.mem (a.gpr .x20) (a.gpr .x21).toNat =
      bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat := by
    rw [ha.input, ha.length, ha.mem]
    apply Proof.Blake2.bytesAt_congr
    intro i hi'
    apply (setupMem_frame s).bytes (R := inputR s) _ (show (s.gpr .x1).toNat ≤ 2 ^ 64 by omega_arith) hi'
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact dw.sub_right (Offset.sub_base _ (by decide : 832 + 64 ≤ 16384))
  obtain headA : bytesAt a.mem (a.gpr .x24 + 832) 4 = Spec.Argon2.le32 (a.gpr .x23).toNat := by
    rw [ha.mem, ha.workspace, ha.remaining]; exact setupMem_prefix s
  obtain spaceA : Space a (s.gpr .x3).toNat := by
    refine ⟨hi, by rw [sp]; exact hsp, workA, ?_, ?_, swA, ?_⟩
    · intro i hi'
      rw [ha.wr, ha.output, wr]
      exact ⟨outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [ha.workspace, ha.output]; exact ow.symm
    · rw [sp, ha.output]; exact so
  refine WP.seq ((first_ok v a (by rw [ha.remaining]; exact ⟨lo, hi⟩)
    (by rw [ha.length]; exact len) headA (by rw [sp]; exact hsp) workA dataA dwA swA sdA).mono ?_)
  rintro b ⟨digestB, kb⟩
  obtain spaceB := spaceA.keeps kb
  obtain countB : b.gpr .x23 = BitVec.ofNat 64 (s.gpr .x3).toNat := by
    rw [kb.regs _ (by decide) (by decide), ha.remaining, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain digestB' : (bytesAt b.mem (b.gpr .x24 + 768) 64).take (min (s.gpr .x3).toNat 64) =
      Spec.Argon2.H (min (s.gpr .x3).toNat 64)
        (Spec.Argon2.le32 (s.gpr .x3).toNat ++ bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) := by
    rw [kb.x24]
    simpa only [ha.remaining, inputA] using digestB
  refine WP.seq ((finishOutput_ok v b (s.gpr .x3).toNat
    (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) spaceB lo countB digestB').mono ?_)
  intro x hx
  obtain baseB : b.gpr .x24 = s.gpr .x4 := kb.x24.trans ha.workspace
  obtain spB : b.sp = s.sp := kb.sp.trans sp
  obtain dstB : b.gpr .x22 = s.gpr .x2 := (kb.regs _ (by decide) (by decide)).trans ha.output
  obtain wrX : x.wr = s.wr := hx.wr.trans (kb.wr.trans ha.wr)
  obtain frame : Frame [⟨s.gpr .x4, 832⟩, stackR s, outputR s] a.mem x.mem := by
    obtain fb : Frame [⟨s.gpr .x4, 832⟩, stackR s, outputR s] a.mem b.mem := by
      apply kb.frame.sub
      intro r hr
      rw [ha.workspace, sp] at hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    exact fb.trans (by simpa only [baseB, spB, dstB, stackR, outputR, Proof.Argon2.hPrime_length] using hx.frame)
  obtain values : ∀ r d, (r, d) ∈ saved →
      x.mem.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hr
    obtain bounds : ∀ rd ∈ saved, 832 ≤ rd.2 ∧ rd.2 + 8 ≤ 16384 := by decide
    obtain ⟨dlo, dhi⟩ := bounds (r, d) hr
    obtain keep : x.mem.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 =
        a.mem.readW (s.gpr .x4 + BitVec.ofNat 64 d) 64 := by
      apply frame.readW (r := ⟨s.gpr .x4 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact (Offset.base_disjoint _ dlo (by omega_arith)).symm
      · exact (sw.sub_right (Offset.sub_base _ dhi)).symm
      · exact (ow.sub_right (Offset.sub_base _ dhi)).symm
    rw [keep, ha.mem]; exact setupMem_saved s r d hr
  obtain baseX := hx.x24.trans baseB
  obtain spX := hx.sp.trans spB
  obtain readable : workR s ∈ x.rd ++ x.wr := List.mem_append_right _ (wrX.symm ▸ work)
  refine (restore_ok s x baseX (by
    intro r hr
    obtain hp : r ∈ preserved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    obtain h30 : r ≠ .x30 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    obtain h22 : r ≠ .x22 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    obtain h23 : r ≠ .x23 := by
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
    obtain setupFrame : Frame [outputR s, workR s, stackR s] s.mem a.mem := by
      rw [ha.mem]
      apply (setupMem_frame s).sub
      intro r hr
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        Offset.sub_base _ (by decide : 832 + 64 ≤ 16384)⟩
    apply setupFrame.trans
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨stackR s, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
    · exact ⟨outputR s, List.mem_cons_self .., fun _ h => h⟩

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
  obtain ⟨tr, t, run, post, regs, _⟩ := code_wp v s pre
  exact ⟨tr, t, run, ⟨regs, VG.AArch64.Exec.sp run,
    VG.AArch64.Exec.preservedV run (code_keepsV v)⟩, post⟩

end VG.Proof.Argon2.AArch64.HPrime
