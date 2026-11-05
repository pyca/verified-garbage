module

public import VerifiedGarbage.Proof.X448.X86.Verified
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.X448.X86.Verified
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.X448.X86.CT
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.X448.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.X448.X86.CT
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.X448.X86.Instr
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.X448.Bytes
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# X448 of the base point on x86 (32-bit)

`vg_x448_base(out, scalar, scratch)` calls `vg_x448(out, scalar, point,
scratch)` (`Impl.X448.X86.x448Base`), with `point` the base point's
u-coordinate, 5, in a frame of its own below the return address: the frame's
push stores the caller's `ebx`, then the coordinate's fourteen words, which
the call reads as 56 bytes (`basePoint`). `vg_x448`'s proofs (`x448_ok`,
`x448_ct`) give the call's result and its trace (`WP.callWith`,
`RelCT.callWith`), from the facts of its contract that the frames and the
contract of `vg_x448_base` give (`callPre`). The frame's pop restores `ebx`,
which nothing between the push and the pop writes.
-/

@[expose] public section

namespace VG.Proof.X448

open VG VG.X86 in
/-- `vg_x448_base(out, scalar, scratch)`, whose arguments are on the stack
(cdecl), with the 100 bytes below the return address that the frames, the
call of `vg_x448` and its own calls use. -/
def x448BaseX86 : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 56⟩
    let scalar : Region := ⟨(arg s 1).setWidth 64, 56⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - 100#64, 100⟩
    s.rd = [scalar, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 56 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 56 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧ 100 ≤ (s.gpr .esp).toNat ∧ stk.Disjoint out ∧
      stk.Disjoint scratch ∧ stk.Disjoint scalar
  post s s' := Spec.X448.bytesAt s'.mem ((arg s 0).setWidth 64) 56 =
    Spec.X448.x448 (Spec.X448.bytesAt s.mem ((arg s 1).setWidth 64) 56) Spec.X448.basePoint
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2

end VG.Proof.X448

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- `vg_x448_base`'s precondition, by name. -/
structure BPre (s : State) : Prop where
  rd : s.rd = [scalarR s, ⟨argAddr s 0, 12⟩]
  wr : s.wr = [outR s, scR (arg s 2)]
  out_sc : (outR s).Disjoint (scR (arg s 2))
  scalar_sc : (scalarR s).Disjoint (scR (arg s 2))
  args_out : (⟨argAddr s 0, 12⟩ : Region).Disjoint (outR s)
  args_sc : (⟨argAddr s 0, 12⟩ : Region).Disjoint (scR (arg s 2))
  ret_out : (retR s).Disjoint (outR s)
  ret_sc : (retR s).Disjoint (scR (arg s 2))
  out_fit : (arg s 0).toNat + 56 ≤ 2 ^ 32
  scalar_fit : (arg s 1).toNat + 56 ≤ 2 ^ 32
  sc_fit : (arg s 2).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  sp_room : 100 ≤ (s.gpr .esp).toNat
  stk_out : (⟨(s.gpr .esp).setWidth 64 - 100#64, 100⟩ : Region).Disjoint (outR s)
  stk_sc : (⟨(s.gpr .esp).setWidth 64 - 100#64, 100⟩ : Region).Disjoint (scR (arg s 2))
  stk_scalar : (⟨(s.gpr .esp).setWidth 64 - 100#64, 100⟩ : Region).Disjoint (scalarR s)

theorem BPre.of (s : State) (h : Proof.X448.x448BaseX86.pre s) : BPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

namespace BPre
variable {s : State} (hp : BPre s)
include hp

/-- The stack the frames and the call use, as `below`. -/
theorem stk_eq : (⟨(s.gpr .esp).setWidth 64 - 100#64, 100⟩ : Region) = below (s.gpr .esp) 100 := by
  simp only [below]; rw [VG.X86.Taint.sub_setWidth hp.sp_room]

/-- A range of the stack below `esp - k`, among the 100 bytes. -/
theorem stk_sub {a k : Nat} (h : a + k ≤ 100) :
    Region.Sub (below (s.gpr .esp - BitVec.ofNat 32 k) a) (below (s.gpr .esp) 100) :=
  below_inner h hp.sp_room

theorem below_out {a k : Nat} (h : a + k ≤ 100) :
    (below (s.gpr .esp - BitVec.ofNat 32 k) a).Disjoint (outR s) := by
  have := hp.stk_out; rw [hp.stk_eq] at this; exact this.sub_left (hp.stk_sub h)

theorem below_sc {a k : Nat} (h : a + k ≤ 100) :
    (below (s.gpr .esp - BitVec.ofNat 32 k) a).Disjoint (scR (arg s 2)) := by
  have := hp.stk_sc; rw [hp.stk_eq] at this; exact this.sub_left (hp.stk_sub h)

theorem below_scalar {a k : Nat} (h : a + k ≤ 100) :
    (below (s.gpr .esp - BitVec.ofNat 32 k) a).Disjoint (scalarR s) := by
  have := hp.stk_scalar; rw [hp.stk_eq] at this; exact this.sub_left (hp.stk_sub h)

theorem top_out {a : Nat} (h : a ≤ 100) : (below (s.gpr .esp) a).Disjoint (outR s) := by
  have := hp.below_out (a := a) (k := 0) (by omega); rwa [BitVec.sub_zero] at this

theorem top_sc {a : Nat} (h : a ≤ 100) : (below (s.gpr .esp) a).Disjoint (scR (arg s 2)) := by
  have := hp.below_sc (a := a) (k := 0) (by omega); rwa [BitVec.sub_zero] at this

theorem top_scalar {a : Nat} (h : a ≤ 100) : (below (s.gpr .esp) a).Disjoint (scalarR s) := by
  have := hp.below_scalar (a := a) (k := 0) (by omega); rwa [BitVec.sub_zero] at this

end BPre

/-! ## The frame -/

theorem baseFrame_get : ∀ j (hj : j < 15),
    baseFrame[j]'(by simpa [baseFrame] using hj) = if j = 0 then .ebx else if j = 14 then .edx else .eax := by
  decide

theorem baseFrame_esp : Reg.esp ∉ baseFrame := by decide

theorem baseFrame_length : baseFrame.length = 15 := rfl

/-- The frame's base, 60 bytes below `esp`. -/
theorem pushed_esp60 (s : State) :
    (pushed baseFrame s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 60 := by
  rw [pushed_esp]; rfl

/-- Word `w` of the frame: the base point's word `w` (for `w < 14`), then the
caller's `ebx`. -/
theorem frame_word {s : State} (hn : 60 ≤ (s.gpr .esp).toNat) {w : Nat} (hw : w < 15) :
    (pushed baseFrame s).mem.readW (((s.gpr .esp - BitVec.ofNat 32 60).setWidth 64) +
      BitVec.ofNat 64 (4 * w)) 32 =
      if w = 14 then s.gpr .ebx else if w = 0 then s.gpr .edx else s.gpr .eax := by
  have h := pushed_word (s := s) baseFrame_esp (by rw [baseFrame_length]; omega)
    (i := w) (by rw [baseFrame_length]; exact hw)
  rw [pushed_esp60] at h
  rw [← addr_eq (x := s.gpr .esp - BitVec.ofNat 32 60) (k := 4 * w)
    (by rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega)]
  refine h.trans ?_
  simp only [baseFrame_length]
  rw [baseFrame_get _ (by omega)]
  by_cases h14 : w = 14
  · subst h14; rfl
  · by_cases h0 : w = 0
    · subst h0; rfl
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h14, ite_eq_right h0]

/-- The base point's bytes, as the frame holds them. -/
theorem five_bytes : ∀ i < 56,
    ((if i / 4 = 0 then (5 : BitVec 32) else 0).extractLsb' (8 * (i % 4)) 8) =
      Spec.X448.basePoint.getD i 0 := by decide

/-- The 56 bytes at the frame's base are the base point's u-coordinate, with
`edx = 5` and `eax = 0` when it is pushed. -/
theorem frame_bytes {s : State} (hn : 60 ≤ (s.gpr .esp).toNat) (h5 : s.gpr .edx = 5) (h0 : s.gpr .eax = 0) :
    Spec.X448.bytesAt (pushed baseFrame s).mem ((s.gpr .esp - BitVec.ofNat 32 60).setWidth 64) 56 =
      Spec.X448.basePoint := by
  refine List.ext_getElem (by simp [Spec.X448.bytesAt, Spec.X448.basePoint]) fun i hi _ => ?_
  have hi' : i < 56 := by simpa [Spec.X448.bytesAt] using hi
  simp only [Spec.X448.bytesAt, List.getElem_map, List.getElem_range]
  rw [List.getElem_eq_getD 0, ← five_bytes i hi']
  have e : (s.gpr .esp - BitVec.ofNat 32 60).setWidth 64 + BitVec.ofNat 64 i =
      (s.gpr .esp - BitVec.ofNat 32 60).setWidth 64 + BitVec.ofNat 64 (4 * (i / 4)) +
        BitVec.ofNat 64 (i % 4) := by
    rw [Offset.add_add]; congr 2; omega
  rw [e, Mem.readW_byte (pushed baseFrame s).mem _ (i := i % 4) (Nat.mod_lt _ (by decide)), frame_word hn (by omega),
    ite_eq_right (by omega)]
  by_cases h : i / 4 = 0
  · rw [ite_eq_left h, ite_eq_left h, h5]
  · rw [ite_eq_right h, ite_eq_right h, h0]

/-! ## The call of `vg_x448` -/

theorem sub_sub' (x : BitVec 32) (a b : Nat) :
    x - BitVec.ofNat 32 a - BitVec.ofNat 32 b = x - BitVec.ofNat 32 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

/-- The arguments of `vg_x448` pushed, last to first. -/
abbrev callRegs : List Reg := [.edx, .ebx, .ecx, .eax]

/-- What `vg_x448` reads: the scalar, the base point in the frame, and its
arguments, which the call's frame holds. -/
abbrev rdC (s : State) : List Region :=
  [scalarR s, below (s.gpr .esp - BitVec.ofNat 32 4) 56, below (s.gpr .esp - BitVec.ofNat 32 60) 16]

/-- What `vg_x448` writes. -/
abbrev wrC (s : State) : List Region := [outR s, scR (arg s 2)]

/-- The state the call of `vg_x448` is made from, after `baseArgs`. -/
structure AtCall (s q : State) : Prop where
  esp : q.gpr .esp = s.gpr .esp - BitVec.ofNat 32 60
  eax : q.gpr .eax = arg s 0
  ecx : q.gpr .ecx = arg s 1
  ebx : q.gpr .ebx = s.gpr .esp - BitVec.ofNat 32 60
  edx : q.gpr .edx = arg s 2
  rd : q.rd = s.rd
  wr : q.wr = below (s.gpr .esp) 60 :: s.wr

theorem callPre {s q : State} (hp : BPre s) (h : AtCall s q) :
    CallPre Proof.X448.x448X86 callRegs (rdC s) (wrC s) q := by
  have hn := hp.sp_room
  have hs := hp.sp_fit
  have he : 4 * callRegs.length + 4 ≤ (q.gpr .esp).toNat := by
    rw [h.esp, sub_toNat (by omega)]; simp only [List.length_cons, List.length_nil]; omega
  have a : ∀ i (hi : i < 4), arg (pushed callRegs q).callEntry i = q.gpr callRegs[3 - i] :=
    fun i hi => callEntry_arg he (by decide) hi
  have a0 := a 0 (by decide); have a1 := a 1 (by decide)
  have a2 := a 2 (by decide); have a3 := a 3 (by decide)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, Nat.reduceSub] at a0 a1 a2 a3
  rw [h.eax] at a0; rw [h.ecx] at a1; rw [h.ebx] at a2; rw [h.edx] at a3
  have cesp : (pushed callRegs q).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 80 := by
    rw [callEntry_esp', h.esp, sub_sub']; rfl
  have cargs : argAddr (pushed callRegs q).callEntry 0 =
      (s.gpr .esp - BitVec.ofNat 32 60 - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_argAddr0, h.esp]; rfl
  have aw : ∀ i, arg ((pushed callRegs q).callEntry.withRegions (rdC s) (wrC s)) i =
      arg (pushed callRegs q).callEntry i := fun _ => rfl
  have cesp' : ((pushed callRegs q).callEntry.withRegions (rdC s) (wrC s)).gpr .esp =
      s.gpr .esp - BitVec.ofNat 32 80 := cesp
  have cargs' : argAddr ((pushed callRegs q).callEntry.withRegions (rdC s) (wrC s)) 0 =
      (s.gpr .esp - BitVec.ofNat 32 60 - BitVec.ofNat 32 16).setWidth 64 := cargs
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.X448.x448X86, aw, a0, a1, a2, a3, cesp', cargs']
    have rpt : (⟨(s.gpr .esp - BitVec.ofNat 32 60).setWidth 64, 56⟩ : Region) =
        below (s.gpr .esp - BitVec.ofNat 32 4) 56 := by
      show _ = (⟨(s.gpr .esp - BitVec.ofNat 32 4 - BitVec.ofNat 32 56).setWidth 64, 56⟩ : Region)
      rw [sub_sub']
    have rargs : (⟨(s.gpr .esp - BitVec.ofNat 32 60 - BitVec.ofNat 32 16).setWidth 64, 16⟩ : Region) =
        below (s.gpr .esp - BitVec.ofNat 32 60) 16 := rfl
    have rret : (⟨(s.gpr .esp - BitVec.ofNat 32 80).setWidth 64, 4⟩ : Region) =
        below (s.gpr .esp - BitVec.ofNat 32 76) 4 := by
      show _ = (⟨(s.gpr .esp - BitVec.ofNat 32 76 - BitVec.ofNat 32 4).setWidth 64, 4⟩ : Region)
      rw [sub_sub']
    have h80 : (s.gpr .esp - BitVec.ofNat 32 80).toNat = (s.gpr .esp).toNat - 80 := sub_toNat (by omega)
    have h60 : (s.gpr .esp - BitVec.ofNat 32 60).toNat = (s.gpr .esp).toNat - 60 := sub_toNat (by omega)
    have rstk : (⟨(s.gpr .esp - BitVec.ofNat 32 80).setWidth 64 - 20#64, 20⟩ : Region) =
        below (s.gpr .esp - BitVec.ofNat 32 80) 20 := by
      show _ = (⟨(s.gpr .esp - BitVec.ofNat 32 80 - BitVec.ofNat 32 20).setWidth 64, 20⟩ : Region)
      rw [VG.X86.Taint.sub_setWidth (e := s.gpr .esp - BitVec.ofNat 32 80) (m := 20) (by omega)]
    rw [rpt, rargs, rret, rstk]
    refine ⟨?_, rfl, hp.out_sc, hp.scalar_sc, hp.below_sc (by omega), hp.below_out (by omega),
      hp.below_sc (by omega), hp.below_out (by omega), hp.below_sc (by omega), hp.out_fit, hp.scalar_fit,
      by omega, hp.sc_fit, by omega, by omega, hp.below_out (by omega), hp.below_sc (by omega)⟩
    show [scalarR s, below (s.gpr .esp - BitVec.ofNat 32 4) 56, below (s.gpr .esp - BitVec.ofNat 32 60) 16] = _
    rw [← rpt, ← rargs]
  · rw [h.rd, h.wr, h.esp, hp.rd, hp.wr, show 4 * callRegs.length = 16 from rfl]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl | rfl
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
    · refine ⟨below (s.gpr .esp) 60, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self),
        0, ?_, by show 0 + 56 ≤ 60; omega⟩
      rw [BitVec.add_zero]; show (s.gpr .esp - BitVec.ofNat 32 4 - BitVec.ofNat 32 56).setWidth 64 = _
      rw [sub_sub']
    · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, (BitVec.add_zero _).symm,
        Nat.le_of_eq (Nat.zero_add _)⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
        0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))), 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_mem fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-! ## What the frames leave alone -/

namespace BPre
variable {s : State} (hp : BPre s)
include hp

theorem argAddr_eq (i : Nat) (hi : i < 3) :
    argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 + BitVec.ofNat 64 (4 * i) := by
  have := hp.sp_fit
  rw [Offset.add_add, argAddr, ← addr_eq (by omega)]; rfl

/-- The `n ≤ 100` bytes below `esp` are apart from the arguments. -/
theorem args_below {n : Nat} (hn : n ≤ 100) :
    (⟨argAddr s 0, 12⟩ : Region).Disjoint (below (s.gpr .esp) n) := by
  have := hp.sp_room
  have h := Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := n) (a := 4) (l := 12) (by omega)
  have e : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := by
    rw [hp.argAddr_eq 0 (by decide)]; exact BitVec.add_zero _
  rw [e]; simp only [below]; rw [VG.X86.Taint.sub_setWidth (by omega)]; exact h.symm

/-- The return address is apart from the `n ≤ 100` bytes below `esp`. -/
theorem ret_below {n : Nat} (hn : n ≤ 100) :
    (retR s).Disjoint (below (s.gpr .esp) n) := by
  have := hp.sp_room
  have h := Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := n) (a := 0) (l := 4) (by omega)
  rw [BitVec.add_zero] at h
  simp only [below]; rw [VG.X86.Taint.sub_setWidth (by omega)]; exact h.symm

/-- An argument, in memory that differs from the entry's only below `esp`. -/
theorem arg_same {m : Mem} {n : Nat} (hn : n ≤ 100) (hf : Frame [below (s.gpr .esp) n] s.mem m)
    {i : Nat} (hi : i < 3) : m.readW (argAddr s i) 32 = arg s i := by
  refine hf.readW (r := ⟨argAddr s 0, 12⟩) ?_ ?_ (by decide)
  · rw [hp.argAddr_eq i hi, show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 by
      rw [hp.argAddr_eq 0 (by decide)]; exact BitVec.add_zero _]
    exact Offset.contains_base _ (by omega) (by omega)
  · intro r hr; rw [List.mem_singleton.mp hr]; exact hp.args_below hn

/-- The arguments' region, in what the code may read. -/
theorem arg_in {i : Nat} (hi : i < 3) {rd : List Region} (hrd : rd = s.rd) (wr : List Region) :
    InRegions (rd ++ wr) (argAddr s i) 4 := by
  refine ⟨⟨argAddr s 0, 12⟩, by rw [hrd, hp.rd]; simp, ?_⟩
  rw [hp.argAddr_eq i hi, show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 by
    rw [hp.argAddr_eq 0 (by decide)]; exact BitVec.add_zero _]
  exact Offset.contains_base _ (by omega) (by omega)

omit hp in
/-- The scalar's bytes, in memory that differs from the entry's only in
regions apart from it. -/
theorem scalar_same {m : Mem} {rs : List Region}
    (hf : Frame rs s.mem m) (hd : ∀ r ∈ rs, (scalarR s).Disjoint r) :
    Spec.X448.bytesAt m ((arg s 1).setWidth 64) 56 = Spec.X448.bytesAt s.mem ((arg s 1).setWidth 64) 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := scalarR s) hd (by show 56 ≤ 2 ^ 64; omega) (by simpa using hi)

end BPre

/-- A frame's pop into `d` leaves in `d` the last word it pops. -/
theorem popReg_last (d : Reg) (hd : d ≠ .esp) :
    ∀ (k : Nat) (s : State), (popReg s d (k + 1)).gpr d =
      s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 (4 * k)).setWidth 64) 32
  | 0, s => by
    simp only [popReg, Nat.mul_zero, BitVec.add_zero]
    rw [VG.X86.RegUpd.gpr_setReg_of_ne (s := s.setReg d _) _ hd, VG.X86.RegUpd.gpr_setReg_self]
  | k + 1, s => by
    rw [popReg, popReg_last d hd k]
    rw [VG.X86.RegUpd.mem_setReg, VG.X86.RegUpd.mem_setReg, VG.X86.RegUpd.gpr_setReg_self, BitVec.add_assoc,
      show (4 : BitVec 32) + BitVec.ofNat 32 (4 * k) = BitVec.ofNat 32 (4 * (k + 1)) by
        rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]; congr 1; omega]

theorem popped_last (d : Reg) (hd : d ≠ .esp) (k : Nat) (s : State) :
    (popped d (k + 1) s).gpr d = s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 (4 * k)).setWidth 64) 32 :=
  popReg_last d hd k s

/-! ## The whole function -/

theorem stackUse_x448 : stackUse Impl.X448.X86.x448 ≤ 20 := by lit_decide

theorem noSp_x448 : NoSp Impl.X448.X86.x448 := NoSp.of_all (by lit_decide)

/-- `baseArgs`, from the frame's push: the state of the call (`AtCall`). -/
theorem baseArgs_ok {s p : State} (hp : BPre s) (esp : p.gpr .esp = s.gpr .esp - BitVec.ofNat 32 60)
    (hf : Frame [below (s.gpr .esp) 60] s.mem p.mem) (rd : p.rd = s.rd)
    (wr : p.wr = below (s.gpr .esp) 60 :: s.wr) :
    WP isa (.block baseArgs) p fun q => AtCall s q ∧ q.mem = p.mem ∧
      ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → q.gpr r = p.gpr r := by
  have hn := hp.sp_room
  have hs := hp.sp_fit
  have ea : ∀ (t : State) (i : Nat), t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 60 → i < 3 →
      t.ea (at_ .esp (64 + 4 * i)) = argAddr s i := fun t i ht hi => by
    rw [ea_mk]
    show (t.gpr .esp + BitVec.ofNat 32 (64 + 4 * i)).setWidth 64 = (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64
    rw [ht]
    rw [show 64 + 4 * i = 60 + (4 + 4 * i) by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
      BitVec.sub_add_cancel]
  unfold baseArgs
  refine wp_mov rfl fun q1 v1 => ?_
  have e1 : q1.gpr .esp = s.gpr .esp - BitVec.ofNat 32 60 := (v1.other _ (by decide)).trans esp
  refine wp_load (a := argAddr s 0) (ea q1 0 e1 (by decide))
    (hp.arg_in (by decide) (by rw [v1.rd, rd]) _) fun q2 v2 => ?_
  have e2 : q2.gpr .esp = s.gpr .esp - BitVec.ofNat 32 60 := (v2.other _ (by decide)).trans e1
  refine wp_load (a := argAddr s 1) (ea q2 1 e2 (by decide))
    (hp.arg_in (by decide) (by rw [v2.rd, v1.rd, rd]) _) fun q3 v3 => ?_
  have e3 : q3.gpr .esp = s.gpr .esp - BitVec.ofNat 32 60 := (v3.other _ (by decide)).trans e2
  refine wp_load (a := argAddr s 2) (ea q3 2 e3 (by decide))
    (hp.arg_in (by decide) (by rw [v3.rd, v2.rd, v1.rd, rd]) _) fun q4 v4 => WP.block_nil ?_
  have m3 : q3.mem = p.mem := by rw [v3.mem, v2.mem, v1.mem]
  have m2 : q2.mem = p.mem := by rw [v2.mem, v1.mem]
  have m1 : q1.mem = p.mem := v1.mem
  refine ⟨⟨(v4.other _ (by decide)).trans e3, ?_, ?_, ?_, ?_, by rw [v4.rd, v3.rd, v2.rd, v1.rd, rd],
    by rw [v4.wr, v3.wr, v2.wr, v1.wr, wr]⟩, by rw [v4.mem, m3], fun r h0 h1 h2 h3 => ?_⟩
  · rw [v4.other _ (by decide), v3.other _ (by decide), v2.gpr, m1, hp.arg_same (by decide) hf (by decide)]
  · rw [v4.other _ (by decide), v3.gpr, m2, hp.arg_same (by decide) hf (by decide)]
  · rw [v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), v1.gpr, esp]
  · rw [v4.gpr, m3, hp.arg_same (by decide) hf (by decide)]
  · rw [v4.other _ h3, v3.other _ h2, v2.other _ h0, v1.other _ h1]

/-- The arguments `vg_x448` reads, from the state of the call. -/
theorem call_args {s q : State} (hp : BPre s) (h : AtCall s q) :
    arg (pushed callRegs q).callEntry 0 = arg s 0 ∧ arg (pushed callRegs q).callEntry 1 = arg s 1 ∧
      arg (pushed callRegs q).callEntry 2 = s.gpr .esp - BitVec.ofNat 32 60 := by
  have hn := hp.sp_room
  have he : 4 * callRegs.length + 4 ≤ (q.gpr .esp).toNat := by
    rw [h.esp, sub_toNat (by omega)]; simp only [List.length_cons, List.length_nil]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [callEntry_arg he (by decide) (i := 0) (by decide)]; exact h.eax
  · rw [callEntry_arg he (by decide) (i := 1) (by decide)]; exact h.ecx
  · rw [callEntry_arg he (by decide) (i := 2) (by decide)]; exact h.ebx

theorem correctBase {s : State} (hp : BPre s) :
    WP isa x448Base s fun f => abiPreserved s f ∧ Proof.X448.x448BaseX86.post s f := by
  have hn := hp.sp_room
  have hs := hp.sp_fit
  unfold x448Base
  refine WP.seq (wp_mov rfl fun t1 u1 => wp_mov rfl fun t2 u2 => WP.block_nil ?_)
  have g2 : ∀ r, r ≠ .edx → r ≠ .eax → t2.gpr r = s.gpr r := fun r h1 h2 =>
    (u2.other r h1).trans (u1.other r h2)
  have esp2 : t2.gpr .esp = s.gpr .esp := g2 _ (by decide) (by decide)
  have eax2 : t2.gpr .eax = 0 := (u2.other _ (by decide)).trans u1.gpr
  have edx2 : t2.gpr .edx = 5 := u2.gpr
  have m2 : t2.mem = s.mem := u2.mem.trans u1.mem
  have rd2 : t2.rd = s.rd := u2.rd.trans u1.rd
  have wr2 : t2.wr = s.wr := u2.wr.trans u1.wr
  have hn2 : 4 * baseFrame.length ≤ (t2.gpr .esp).toNat := by rw [baseFrame_length, esp2]; omega
  refine WP.frame (by decide) baseFrame_esp (by decide) hn2 (NoSp.of_all (by lit_decide)) ?_
  -- The frame: the base point, below the caller's `ebx`.
  have pesp : (pushed baseFrame t2).gpr .esp = s.gpr .esp - BitVec.ofNat 32 60 := by
    rw [pushed_esp60, esp2]
  have pf : Frame [below (s.gpr .esp) 60] s.mem (pushed baseFrame t2).mem := by
    have := pushed_frame (s := t2) baseFrame_esp hn2; rwa [m2, esp2, baseFrame_length] at this
  have pbytes := frame_bytes (s := t2) (by rw [esp2]; omega) edx2 eax2
  have pebx := frame_word (s := t2) (by rw [esp2]; omega) (w := 14) (by decide)
  rw [esp2] at pbytes pebx
  rw [ite_eq_left rfl, g2 _ (by decide) (by decide)] at pebx
  refine WP.seq (WP.mono (baseArgs_ok hp pesp pf (by rw [pushed_rd, rd2])
    (by rw [pushed_wr, esp2, wr2, baseFrame_length])) fun q ⟨hq, qm, qg⟩ => ?_)
  -- The call.
  refine WP.callWith (k := Proof.X448.x448X86) x448_ok noSp_x448 (by decide) (by decide)
    (by rw [hq.esp, sub_toNat (by omega)]; have := stackUse_x448; simp only [List.length_cons, List.length_nil]; omega)
    (callPre hp hq) fun s' rd' wr' cs' fr' ⟨s₂, m₂, post₂⟩ => ?_
  obtain ⟨a0, a1, a2⟩ := call_args hp hq
  have hsu := stackUse_x448
  have h60 : (s.gpr .esp - BitVec.ofNat 32 60).toNat = (s.gpr .esp).toNat - 60 := sub_toNat (by omega)
  -- The frame's base, and the regions near it.
  have E60 : (below (s.gpr .esp) 60) = ⟨(s.gpr .esp - BitVec.ofNat 32 60).setWidth 64, 60⟩ := rfl
  have hlen : 4 * callRegs.length + stackUse Impl.X448.X86.x448 + 4 ≤ 40 := by
    simp only [List.length_cons, List.length_nil]; omega
  have lowE : below (q.gpr .esp) (4 * callRegs.length + stackUse Impl.X448.X86.x448 + 4) =
      ⟨(s.gpr .esp - BitVec.ofNat 32 60).setWidth 64 -
        BitVec.ofNat 64 (4 * callRegs.length + stackUse Impl.X448.X86.x448 + 4),
        4 * callRegs.length + stackUse Impl.X448.X86.x448 + 4⟩ := by
    simp only [below]; rw [hq.esp, VG.X86.Taint.sub_setWidth (by rw [h60]; omega)]
  -- What the call leaves of the frame and the arguments, which are apart from what it writes.
  have keep : ∀ (d n : Nat), d ≤ 100 → n ≤ 100 →
      (⟨(s.gpr .esp - BitVec.ofNat 32 60).setWidth 64 + BitVec.ofNat 64 d, n⟩ : Region).Disjoint
        (below (q.gpr .esp) (4 * callRegs.length + stackUse Impl.X448.X86.x448 + 4)) := by
    intro d n hd hn'
    rw [lowE]; exact (Offset.disjoint_below_above _ (by omega)).symm
  have hE : ∀ k ≤ 60, ((s.gpr .esp - BitVec.ofNat 32 60) + BitVec.ofNat 32 k).setWidth 64 =
      (s.gpr .esp - BitVec.ofNat 32 60).setWidth 64 + BitVec.ofNat 64 k := fun k hk =>
    addr_eq (by rw [h60]; have := (s.gpr .esp).isLt; omega)
  have hsp : (s.gpr .esp).setWidth 64 = (s.gpr .esp - BitVec.ofNat 32 60).setWidth 64 + BitVec.ofNat 64 60 := by
    rw [← hE 60 (by omega), BitVec.sub_add_cancel]
  have F' : Frame (wrC s ++ [below (q.gpr .esp) (4 * callRegs.length + stackUse Impl.X448.X86.x448 + 4)])
      (pushed baseFrame t2).mem s'.mem := by rw [← qm]; exact fr'
  -- The caller's `ebx`, at the top of the frame.
  have topw : s'.mem.readW ((s.gpr .esp - BitVec.ofNat 32 60).setWidth 64 + BitVec.ofNat 64 56) 32 =
      s.gpr .ebx := by
    have sub : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 60).setWidth 64 + BitVec.ofNat 64 56, 4⟩
        (below (s.gpr .esp) 60) := Offset.sub_base _ (by omega)
    rw [F'.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl
      · exact (hp.top_out (by omega)).sub_left sub
      · exact (hp.top_sc (by omega)).sub_left sub
      · exact keep 56 4 (by omega) (by omega)) (by decide)]
    exact pebx
  -- The return address.
  have retw : s'.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    rw [F'.readW (r := retR s) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl
      · exact hp.ret_out
      · exact hp.ret_sc
      · show (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint _
        rw [hsp]; exact keep 60 4 (by omega) (by omega)) (by decide)]
    exact pf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.ret_below (by omega)) (by decide)
  -- What `vg_x448` read: the scalar, and the base point in the frame.
  have he : 4 * callRegs.length + 4 ≤ (q.gpr .esp).toNat := by
    rw [hq.esp, h60]; simp only [List.length_cons, List.length_nil]; omega
  have cf := callEntry_frame (s := q) he (by decide)
  rw [qm, hq.esp] at cf
  have cfE : below (s.gpr .esp - BitVec.ofNat 32 60) (4 * callRegs.length + 4) =
      ⟨(s.gpr .esp - BitVec.ofNat 32 60).setWidth 64 - BitVec.ofNat 64 20, 20⟩ := by
    simp only [below, List.length_cons, List.length_nil]
    rw [VG.X86.Taint.sub_setWidth (by rw [h60]; omega)]
  have kb : Spec.X448.bytesAt (pushed callRegs q).callEntry.mem ((arg s 1).setWidth 64) 56 =
      Spec.X448.bytesAt s.mem ((arg s 1).setWidth 64) 56 :=
    BPre.scalar_same (rs := [below (s.gpr .esp) 60,
        below (s.gpr .esp - BitVec.ofNat 32 60) (4 * callRegs.length + 4)])
      ((pf.mono (by simp)).trans (cf.mono (by simp))) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hp.top_scalar (by omega)).symm
        · exact (hp.below_scalar (by simp only [List.length_cons, List.length_nil]; omega)).symm
  have pb : Spec.X448.bytesAt (pushed callRegs q).callEntry.mem
      ((s.gpr .esp - BitVec.ofNat 32 60).setWidth 64) 56 = Spec.X448.basePoint := by
    rw [← pbytes]
    simp only [Spec.X448.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    refine cf.bytes (R := ⟨(s.gpr .esp - BitVec.ofNat 32 60).setWidth 64, 56⟩) (fun r hr => ?_)
      (by show 56 ≤ 2 ^ 64; omega) (by simpa using hi)
    rw [List.mem_singleton.mp hr, cfE]
    have := (Offset.disjoint_below_above ((s.gpr .esp - BitVec.ofNat 32 60).setWidth 64)
      (m := 20) (a := 0) (l := 56) (by omega)).symm
    rwa [BitVec.add_zero] at this
  have p2 : Spec.X448.bytesAt s₂.mem ((arg s 0).setWidth 64) 56 =
      Spec.X448.x448 (Spec.X448.bytesAt s.mem ((arg s 1).setWidth 64) 56) Spec.X448.basePoint := by
    have := post₂
    change Spec.X448.bytesAt s₂.mem ((arg (pushed callRegs q).callEntry 0).setWidth 64) 56 =
      Spec.X448.x448 (Spec.X448.bytesAt (pushed callRegs q).callEntry.mem
        ((arg (pushed callRegs q).callEntry 1).setWidth 64) 56)
        (Spec.X448.bytesAt (pushed callRegs q).callEntry.mem
          ((arg (pushed callRegs q).callEntry 2).setWidth 64) 56) at this
    rwa [a0, a1, a2, kb, pb] at this
  refine ⟨⟨fun r hr => ?_, by rw [popped_mem]; exact retw⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    have qsave : ∀ r, r ∈ calleeSaved → r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .esp →
        (popped .ebx baseFrame.length s').gpr r = s.gpr r := fun r hc h0 h1 h2 h3 h4 => by
      rw [popped_gpr _ _ _ h4 h1, cs' r hc, qg r h0 h1 h2 h3, pushed_gpr _ _ h4, g2 r h3 h0]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show baseFrame.length = 14 + 1 from rfl, popped_last .ebx (by decide) 14, cs' .esp (by decide),
        hq.esp, hE 56 (by omega)]
      exact topw
    · exact qsave _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact qsave _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact qsave _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [popped_esp, cs' .esp (by decide), hq.esp]
      exact BitVec.sub_add_cancel _ _
  · show Spec.X448.bytesAt (popped .ebx 15 s').mem ((arg s 0).setWidth 64) 56 = _
    rw [popped_mem, ← m₂]; exact p2

/-! ## Constant time -/

/-- Two entry states the constant-time statement relates. -/
def Pb (σ₁ σ₂ : State) : Prop :=
  Proof.X448.x448BaseX86.pre σ₁ ∧ Proof.X448.x448BaseX86.pre σ₂ ∧ Proof.X448.x448BaseX86.pub σ₁ σ₂

/-- Two runs, each in a state `F` says of its own run. -/
def Wb (F : State → State → Prop) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, Pb σ₁ σ₂ ∧ F σ₁ s₁ ∧ F σ₂ s₂

theorem Wb.step {F G : State → State → Prop} {R : State → State → Prop} {c : Prog isa}
    (htr : RelCT isa (Wb F) c R) (hw : ∀ σ s, BPre σ → F σ s → WP isa c s (G σ)) :
    RelCT isa (Wb F) c (Wb G) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := htr _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨σ₁, σ₂, hP, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, g₁⟩ := hw _ _ (BPre.of _ hP.1) f₁
  obtain ⟨_, u₂, x₂, g₂⟩ := hw _ _ (BPre.of _ hP.2.1) f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, σ₁, σ₂, hP, g₁, g₂⟩

/-- After the first block. -/
def F1 (σ t : State) : Prop :=
  t.gpr .esp = σ.gpr .esp ∧ t.gpr .eax = 0 ∧ t.gpr .edx = 5 ∧ t.mem = σ.mem ∧ t.rd = σ.rd ∧
    t.wr = σ.wr ∧ ∀ r, r ≠ .edx → r ≠ .eax → t.gpr r = σ.gpr r

theorem first_ok (σ : State) :
    WP isa (.block ([.mov .eax (.imm 0), .mov .edx (.imm 5)] : List Instr)) σ (F1 σ) :=
  wp_mov rfl fun t1 u1 => wp_mov rfl fun t2 u2 => WP.block_nil
    ⟨(u2.other _ (by decide)).trans (u1.other _ (by decide)), (u2.other _ (by decide)).trans u1.gpr,
      u2.gpr, u2.mem.trans u1.mem, u2.rd.trans u1.rd, u2.wr.trans u1.wr,
      fun r h1 h2 => (u2.other r h1).trans (u1.other r h2)⟩

/-- In the frame, before `baseArgs`. -/
def F2 (σ a : State) : Prop := ∃ t, F1 σ t ∧ a = pushed baseFrame t

theorem Pb.sp {σ₁ σ₂ : State} (h : Pb σ₁ σ₂) : σ₁.gpr .esp = σ₂.gpr .esp := h.2.2.1

theorem x448Base_ct : ConstantTime isa Proof.X448.x448BaseX86.pre Proof.X448.x448BaseX86.pub
    Impl.X448.X86.x448Base := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    ((?_ : RelCT isa (Wb fun σ s => s = σ) x448Base fun _ _ => True).mono
      (fun s₁ s₂ h => ⟨s₁, s₂, h, rfl, rfl⟩) fun _ _ h => h)
  unfold x448Base
  refine RelCT.seq (Wb.step (G := F1) (RelCT.taint (A := taint) (τr [.esp]) ?_ (by taint_decide))
    fun σ s _ e => by rw [e]; exact first_ok σ) ?_
  · rintro s₁ s₂ ⟨σ₁, σ₂, hP, rfl, rfl⟩
    exact agree_regs fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hP.sp
  refine RelCT.frame (R := fun _ _ => True) (fun s₁ s₂ h => by
    obtain ⟨σ₁, σ₂, hP, f₁, f₂⟩ := h; exact f₁.1.trans (hP.sp.trans f₂.1.symm)) ?_
  refine (?_ : RelCT isa (Wb F2) _ _).mono
    (fun a b h => by
      obtain ⟨s₁, s₂, ⟨σ₁, σ₂, hP, f₁, f₂⟩, ea, eb⟩ := h
      exact ⟨σ₁, σ₂, hP, ⟨s₁, f₁, ea⟩, ⟨s₂, f₂, eb⟩⟩)
    fun _ _ h => h
  refine RelCT.seq (Wb.step (G := AtCall) (RelCT.taint (A := taint) (τr [.esp]) ?_ (by taint_decide))
    fun σ a hp ⟨t, f, e⟩ => ?_) ?_
  · rintro a b ⟨σ₁, σ₂, hP, ⟨t₁, f₁, rfl⟩, ⟨t₂, f₂, rfl⟩⟩
    refine agree_regs fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rw [pushed_esp, pushed_esp, f₁.1, f₂.1, hP.sp]
  · subst e
    obtain ⟨esp, eax, edx, m, rd, wr, g⟩ := f
    have hn := hp.sp_room
    have hn2 : 4 * baseFrame.length ≤ (t.gpr .esp).toNat := by rw [baseFrame_length, esp]; omega
    refine WP.mono (baseArgs_ok hp (by rw [pushed_esp60, esp])
      (by have := pushed_frame (s := t) baseFrame_esp hn2; rwa [m, esp, baseFrame_length] at this)
      (by rw [pushed_rd, rd]) (by rw [pushed_wr, esp, wr, baseFrame_length])) fun q h => h.1
  · intro x y t₁ t₂ x' y' hxy e₁ e₂
    obtain ⟨σ₁, σ₂, hP, h₁, h₂⟩ := hxy
    have hp₁ := BPre.of _ hP.1
    have hp₂ := BPre.of _ hP.2.1
    obtain ⟨esp, a0, a1, a2⟩ := hP.2.2
    have hR : rdC σ₁ = rdC σ₂ := by simp only [rdC, scalarR, esp, a1]
    have hW : wrC σ₁ = wrC σ₂ := by simp only [wrC, outR, a0, a2]
    refine RelCT.callWith (k := Proof.X448.x448X86) x448_ok x448_ct (rdC σ₁) (wrC σ₁)
      (P := fun a b => AtCall σ₁ a ∧ AtCall σ₂ b) ?_ x y t₁ t₂ x' y' ⟨h₁, h₂⟩ e₁ e₂
    clear h₁ h₂ e₁ e₂
    intro x y ⟨h₁, h₂⟩
    obtain ⟨c0, c1, c2⟩ := call_args hp₁ h₁
    obtain ⟨d0, d1, d2⟩ := call_args hp₂ h₂
    refine ⟨callPre hp₁ h₁, hR ▸ hW ▸ callPre hp₂ h₂, by rw [h₁.esp, h₂.esp, esp], ?_⟩
    have he : ∀ {σ q : State}, BPre σ → AtCall σ q → 4 * callRegs.length + 4 ≤ (q.gpr .esp).toNat :=
      fun {σ q} hp h => by
        have := hp.sp_room
        rw [h.esp, sub_toNat (by omega)]; simp only [List.length_cons, List.length_nil]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (pushed callRegs x).callEntry.gpr .esp = (pushed callRegs y).callEntry.gpr .esp
      rw [callEntry_esp', callEntry_esp', h₁.esp, h₂.esp, esp]
    · show arg (pushed callRegs x).callEntry 0 = arg (pushed callRegs y).callEntry 0
      rw [c0, d0, a0]
    · show arg (pushed callRegs x).callEntry 1 = arg (pushed callRegs y).callEntry 1
      rw [c1, d1, a1]
    · show arg (pushed callRegs x).callEntry 2 = arg (pushed callRegs y).callEntry 2
      rw [c2, d2, esp]
    · show arg (pushed callRegs x).callEntry 3 = arg (pushed callRegs y).callEntry 3
      rw [callEntry_arg (he hp₁ h₁) (by decide) (i := 3) (by decide),
        callEntry_arg (he hp₂ h₂) (by decide) (i := 3) (by decide)]
      exact h₁.edx.trans (a2.trans h₂.edx.symm)

/-! ## `Verified` -/

/-- Memory holding the arguments `0x1000, 0x2000, 0x4000` at `0x8004`. -/
def satBaseMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

/-- A state satisfying the precondition. -/
def satBaseState : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satBaseMem
  rd := [⟨0x2000, 56⟩, ⟨0x8004, 12⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448Base_ok (s : State) (hs : Proof.X448.x448BaseX86.pre s) :
    ∃ t s', Exec isa Impl.X448.X86.x448Base s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448BaseX86.post s s' :=
  correctBase (BPre.of s hs)

theorem x448Base_verified :
    Verified X86.target Impl.X448.X86.x448Base (Spec.X448.x448BaseContract X86.abi 100) :=
  Verified.of_correct x448Base_ok x448Base_ct (by
    have a0 : arg satBaseState 0 = 0x1000 := by decide
    have a1 : arg satBaseState 1 = 0x2000 := by decide
    have a2 : arg satBaseState 2 = 0x4000 := by decide
    have e : argAddr satBaseState 0 = 0x8004 := by decide
    have esp : satBaseState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, Proof.X448.x448BaseX86, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, e, esp] using Proof.X448.X86.satBaseState)

end VG.Proof.X448.X86
