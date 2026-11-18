module

import VerifiedGarbage.Proof.MlKem.Arm.Keccak
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
public import VerifiedGarbage.Proof.MlKem.Arm.CallF
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Frag
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `MlDsa.Arm.Sign.Lay`, which this module and modules that import it used -/

section

/-!
# ML-DSA signing on ARMv7: the buffers of the function

As on x86-64 (`Proof/MlDsa/X86_64/Sign/Glue.lean`): the function keeps the
address of each buffer it works in (its arguments and its working space) in a
callee-saved register; a layout (`Lay`) lists these registers with the lengths
of their buffers, which are apart from each other and from the `D` bytes of
stack below the stack pointer that the calls use, and do not wrap around the
32-bit address space. A pointer (a register and an offset) into a buffer, and
two pointers into the same buffer or different ones, are then checked by
evaluation (`inB`, `sepB`): each pair of regions a call needs apart is, and
each region is readable or writable (`Lay.disj`, `Lay.stkD`, `Lay.cR`,
`Lay.cW`). A call leaves the layout as it was (`Lay.post`), and the bytes of a
region apart from those it writes (`Lay.keepBytes`, `Lay.keepPoly`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The address of the pointer `p` in `s`. -/
abbrev pa (s : State) (p : Ptr) : Addr := State.addr (s.gpr p.1) + BitVec.ofNat 64 p.2

/-- `s'` keeps the callee-saved registers of `s` (but `lr`). -/
abbrev CS (s s' : State) : Prop := ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r

theorem CS.trans {s₁ s₂ s₃ : State} (h₁ : CS s₁ s₂) (h₂ : CS s₂ s₃) : CS s₁ s₃ :=
  fun r hr hl => (h₂ r hr hl).trans (h₁ r hr hl)

/-! ## Checks -/

/-- The `len` bytes at `p` lie within the buffer of its register in the layout `bs`. -/
def inB (bs : List (Reg × Nat)) (p : Ptr) (len : Nat) : Bool :=
  match bs.lookup p.1 with
  | some n => decide (p.2 + len ≤ n)
  | none => false

/-- The registers of the buffers the function writes (`scratch` and `sig`):
a buffer it only reads may overlap another such buffer, but not one of
these. -/
abbrev wRegs : List Reg := [.r7, .r8]

/-- The `l` bytes at `p` and the `k` bytes at `q` lie within their buffers,
apart: in different buffers, one of them written, or in the same buffer. -/
def sepB (bs : List (Reg × Nat)) (p : Ptr) (l : Nat) (q : Ptr) (k : Nat) : Bool :=
  inB bs p l && inB bs q k &&
    ((p.1 != q.1 && (decide (p.1 ∈ wRegs) || decide (q.1 ∈ wRegs))) ||
      (p.1 == q.1 && (decide (p.2 + l ≤ q.2) || decide (q.2 + k ≤ p.2))))

theorem lookup_mem : ∀ {bs : List (Reg × Nat)} {r : Reg} {n : Nat}, bs.lookup r = some n → (r, n) ∈ bs
  | [], _, _, h => by simp [List.lookup] at h
  | (r', n') :: bs, r, n, h => by
    unfold List.lookup at h
    by_cases e : r = r'
    · subst e
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · have : (r == r') = false := by simp [e]
      rw [this] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem inB_spec {bs : List (Reg × Nat)} {p : Ptr} {l : Nat} (h : inB bs p l = true) :
    ∃ n, (p.1, n) ∈ bs ∧ p.2 + l ≤ n := by
  unfold inB at h
  split at h
  · rename_i n hn; exact ⟨n, lookup_mem hn, of_decide_eq_true h⟩
  · cases h

theorem sepB_spec {bs : List (Reg × Nat)} {p q : Ptr} {l k : Nat} (h : sepB bs p l q k = true) :
    inB bs p l = true ∧ inB bs q k = true ∧
      ((p.1 ≠ q.1 ∧ (p.1 ∈ wRegs ∨ q.1 ∈ wRegs)) ∨ (p.1 = q.1 ∧ (p.2 + l ≤ q.2 ∨ q.2 + k ≤ p.2))) := by
  simp only [sepB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.1 |> fun h1 => ⟨h1, h.1.2, h.2⟩

/-! ## Regions -/

/-- A range at an offset of a range a region contains. -/
theorem contains_sub {r : Region} {a : Addr} {n off l : Nat} (h : r.Contains a n) (hl : off + l ≤ n)
    (hn : n < 2 ^ 64) : r.Contains (a + BitVec.ofNat 64 off) l := by
  simp only [Region.Contains] at h ⊢
  rw [Offset.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega_using [hl, hn])]
  have := Nat.mod_le ((a - r.base).toNat + off) (2 ^ 64)
  omega_using [h, hl]

theorem inRegions_sub {X : List Region} {a : Addr} {n off l : Nat} (h : InRegions X a n) (hl : off + l ≤ n)
    (hn : n < 2 ^ 64) : InRegions X (a + BitVec.ofNat 64 off) l := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, contains_sub hc hl hn⟩

/-! ## Layouts -/

section
variable (D : Nat)

/-- The buffers of `rbs` (read) and `wbs` (written), at the addresses in
their registers: small, apart from each other and from the `D` bytes of
stack below the stack pointer, not wrapping around, and permitted; and `D`
bytes of stack below the stack pointer that do not wrap around. -/
structure Lay (rbs wbs : List (Reg × Nat)) (s : State) : Prop where
  small : ∀ b ∈ rbs ++ wbs, b.2 < 2 ^ 32
  dj : ∀ b ∈ rbs ++ wbs, ∀ b' ∈ rbs ++ wbs, b.1 ≠ b'.1 → (b.1 ∈ wRegs ∨ b'.1 ∈ wRegs) →
    Region.Disjoint ⟨State.addr (s.gpr b.1), b.2⟩ ⟨State.addr (s.gpr b'.1), b'.2⟩
  stk : ∀ b ∈ rbs ++ wbs, (belowA s.sp D).Disjoint ⟨State.addr (s.gpr b.1), b.2⟩
  nw : ∀ b ∈ rbs ++ wbs, (s.gpr b.1).toNat + b.2 ≤ 2 ^ 32
  rd : ∀ b ∈ rbs ++ wbs, InRegions (s.rd ++ s.wr) (State.addr (s.gpr b.1)) b.2
  wr : ∀ b ∈ wbs, InRegions s.wr (State.addr (s.gpr b.1)) b.2
  sp : D ≤ s.sp.toNat

end

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s)
include L

omit L in
theorem sub_of_inB {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    ∃ n, (p.1, n) ∈ rbs ++ wbs ∧ Region.Sub ⟨pa s p, l⟩ ⟨State.addr (s.gpr p.1), n⟩ := by
  obtain ⟨n, hm, hl⟩ := inB_spec h
  exact ⟨n, hm, Offset.sub_base _ hl⟩

theorem Lay.disj {p q : Ptr} {l k : Nat} (h : sepB (rbs ++ wbs) p l q k = true) :
    Region.Disjoint ⟨pa s p, l⟩ ⟨pa s q, k⟩ := by
  obtain ⟨hp, hq, hs⟩ := sepB_spec h
  obtain ⟨n, hn, hl⟩ := inB_spec hp
  obtain ⟨m, hm, hk⟩ := inB_spec hq
  have sn := L.small _ hn
  have sm := L.small _ hm
  rcases hs with ⟨e, hw⟩ | ⟨e, hs⟩
  · exact ((L.dj _ hn _ hm e hw).sub_left (Offset.sub_base _ hl)).sub_right (Offset.sub_base _ hk)
  · show Region.Disjoint ⟨State.addr (s.gpr p.1) + _, l⟩ ⟨State.addr (s.gpr q.1) + _, k⟩
    rw [← e]
    exact Offset.disjoint _ hs (by omega) (by omega)

theorem Lay.stkD {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    (belowA s.sp D).Disjoint ⟨pa s p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := sub_of_inB (s := s) h
  exact (L.stk _ hn).sub_right hsub

/-- The region does not wrap around the 32-bit address space. -/
theorem Lay.nwp {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    (s.gpr p.1).toNat + p.2 + l ≤ 2 ^ 32 := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  have h1 := L.nw _ hn
  simp only at h1
  omega_using [hl, h1]

/-- The 32-bit sum of a register and an offset, as a 64-bit address. -/
theorem Lay.pa32 {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) (hl : 0 < l) :
    State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2) = pa s p :=
  addr_add (by have := L.nwp h; omega_using [hl, this])

/-- `Lay.pa32`, as the contracts state addresses. -/
theorem Lay.w {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) (hl : 0 < l) :
    BitVec.setWidth 64 (s.gpr p.1 + BitVec.ofNat 32 p.2) = pa s p :=
  L.pa32 h hl

theorem Lay.fit {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) (hl : 0 < l) :
    (s.gpr p.1 + BitVec.ofNat 32 p.2).toNat + l ≤ 2 ^ 32 := by
  have := L.nwp h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.2) (by omega_using [hl, this]), Nat.mod_eq_of_lt (by omega_using [hl, this])]
  omega_using [this]

theorem Lay.lenlt {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : l < 2 ^ 32 := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  have := L.small _ hn
  simp only at this; omega_using [hl, this]

/-- `Lay.pa32`, for a buffer written. -/
theorem Lay.pa32W {p : Ptr} {l : Nat} (h : inB wbs p l = true) (hl : 0 < l) :
    State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2) = pa s p := by
  obtain ⟨n, hn, hl'⟩ := inB_spec h
  have := L.nw _ (List.mem_append_right _ hn)
  exact addr_add (by simp only at this; omega_using [hl, hl', this])

theorem Lay.iR {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : InRegions (s.rd ++ s.wr) (pa s p) l := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  exact inRegions_sub (L.rd (p.1, n) hn) hl (by have := L.small _ hn; omega_using [this])

theorem Lay.iW {p : Ptr} {l : Nat} (h : inB wbs p l = true) : InRegions s.wr (pa s p) l := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  exact inRegions_sub (L.wr (p.1, n) hn) hl (by have := L.small _ (List.mem_append_right _ hn); omega_using [this])

theorem Lay.cR {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : Covers [⟨pa s p, l⟩] (s.rd ++ s.wr) :=
  Covers.one (L.iR h)

theorem Lay.cW {p : Ptr} {l : Nat} (h : inB wbs p l = true) : Covers [⟨pa s p, l⟩] s.wr :=
  Covers.one (L.iW h)

end

/-! ## What a piece of code leaves -/

/-- The region of `w.2` bytes at the pointer `w.1`. -/
abbrev toR (s : State) (w : Ptr × Nat) : Region := ⟨pa s w.1, w.2⟩

/-- The registers the function keeps the addresses of its buffers in. -/
abbrev bases : List Reg := [.r7, .r4, .r5, .r6, .r8, .r9]

theorem bases_cs : ∀ r ∈ bases, r ∈ preserved ∧ r ≠ .lr := by decide

/-- What a piece of code leaves: the permissions, the registers `bases` and
the stack pointer, and memory but within `W` and the `D` bytes of stack. -/
structure PostB (D : Nat) (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bs : ∀ r ∈ bases, s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  frame : Frame (W ++ [belowA s.sp D]) s.mem s'.mem

/-- `PostB`, with the regions written given as pointers. -/
abbrev PPostB (D : Nat) (s s' : State) (ws : List (Ptr × Nat)) : Prop := PostB D s s' (ws.map (toR s))

/-- The `l` bytes at `p` lie in the layout, apart from the regions `ws`, and
`p`'s register is one of `bases`. -/
def keepB (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (p : Ptr) (l : Nat) : Bool :=
  decide (p.1 ∈ bases) && inB bs p l && ws.all fun w => sepB bs p l w.1 w.2

theorem inB_sub {bs : List (Reg × Nat)} {r : Reg} {o L o' l : Nat} (h : inB bs (r, o) L = true)
    (h2 : o' + l ≤ o + L) : inB bs (r, o') l = true := by
  unfold inB at h ⊢
  split at h
  · rename_i n hn
    simp only [hn, decide_eq_true_eq] at h ⊢
    omega_using [h2, h]
  · cases h

theorem sepB_sub {bs : List (Reg × Nat)} {r : Reg} {o L o' l : Nat} {q : Ptr} {k : Nat}
    (h : sepB bs (r, o) L q k = true) (h1 : o ≤ o') (h2 : o' + l ≤ o + L) : sepB bs (r, o') l q k = true := by
  unfold sepB at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨hp, hq⟩, hs⟩ := h
  refine ⟨⟨inB_sub hp h2, hq⟩, ?_⟩
  rcases hs with hs | ⟨he, hs⟩
  · exact .inl hs
  · exact .inr ⟨he, by omega_using [h1, h2, hs]⟩

theorem keepB_sub {bs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {r : Reg} {o L o' l : Nat}
    (h : keepB bs ws (r, o) L = true) (h1 : o ≤ o') (h2 : o' + l ≤ o + L) : keepB bs ws (r, o') l = true := by
  unfold keepB at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨⟨h.1.1, inB_sub h.1.2 h2⟩, fun w hw => sepB_sub (h.2 w hw) h1 h2⟩

theorem PostB.pa {D : Nat} {s s' : State} {W : List Region} (hP : PostB D s s' W) {p : Ptr} (h : p.1 ∈ bases) :
    pa s' p = pa s p := by
  simp only [VG.Proof.MlDsa.Arm.Sign.pa, hP.bs _ h]

theorem PostB.refl (D : Nat) (s : State) (W : List Region) : PostB D s s W :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl, Frame.refl _ _⟩

theorem PostB.of_cs {D : Nat} {s s' : State} (hcs : CS s s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {W : List Region} (hf : Frame W s.mem s'.mem) : PostB D s s' W :=
  ⟨hrd, hwr, fun r hr => hcs r (bases_cs r hr).1 (bases_cs r hr).2, hsp,
    hf.mono fun _ hr => List.mem_append_left _ hr⟩

theorem PostB.trans {D : Nat} {s s₁ s₂ : State} {W₁ W₂ W : List Region} (h₁ : PostB D s s₁ W₁)
    (h₂ : PostB D s₁ s₂ W₂) (hw₁ : ∀ r ∈ W₁, r ∈ W) (hw₂ : ∀ r ∈ W₂, r ∈ W) : PostB D s s₂ W := by
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.bs r hr).trans (h₁.bs r hr),
    h₂.sp.trans h₁.sp, ?_⟩
  have f₂ := h₂.frame
  rw [h₁.sp] at f₂
  refine (h₁.frame.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₁ r hr), List.mem_append_right _ hr]
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₂ r hr), List.mem_append_right _ hr]

theorem map_toR_post {D : Nat} {s s' : State} {W : List Region} (hP : PostB D s s' W) {ws : List (Ptr × Nat)}
    (h : ∀ w ∈ ws, w.1.1 ∈ bases) : ws.map (toR s') = ws.map (toR s) :=
  List.map_congr_left fun w hw => by simp only [toR, hP.pa (h w hw)]

/-- `PostB.trans`, with the regions written given as pointers. -/
theorem PPostB.trans {D : Nat} {s s₁ s₂ : State} {ws₁ ws₂ ws : List (Ptr × Nat)} (h₁ : PPostB D s s₁ ws₁)
    (h₂ : PPostB D s₁ s₂ ws₂) (hcs : ∀ w ∈ ws₂, w.1.1 ∈ bases) (hw₁ : ∀ w ∈ ws₁, w ∈ ws)
    (hw₂ : ∀ w ∈ ws₂, w ∈ ws) : PPostB D s s₂ ws := by
  have h₂' : PostB D s₁ s₂ (ws₂.map (toR s)) := by rw [← map_toR_post h₁ hcs]; exact h₂
  refine PostB.trans h₁ h₂' (fun r hr => ?_) fun r hr => ?_
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₁ w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₂ w hw)

theorem Lay.post {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} {W : List Region} (L : Lay D rbs wbs s)
    (hP : PostB D s s' W) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) : Lay D rbs wbs s' := by
  have e : ∀ b ∈ rbs ++ wbs, s'.gpr b.1 = s.gpr b.1 := fun b hb => hP.bs _ (hcs b hb)
  refine ⟨L.small, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    ?_⟩
  · rw [e b hb, e b' hb']; exact L.dj b hb b' hb' hne hw
  · rw [e b hb, hP.sp]; exact L.stk b hb
  · rw [e b hb]; exact L.nw b hb
  · rw [e b hb, hP.rd, hP.wr]; exact L.rd b hb
  · rw [e b (List.mem_append_right _ hb), hP.wr]; exact L.wr b hb
  · rw [hP.sp]; exact L.sp

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay D rbs wbs s) {ws : List (Ptr × Nat)}
  {p : Ptr} {l : Nat}
include L

theorem Lay.fdisj (hc : keepB (rbs ++ wbs) ws p l = true) :
    ∀ r ∈ ws.map (toR s) ++ [belowA s.sp D], Region.Disjoint ⟨pa s p, l⟩ r := by
  simp only [keepB, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨_, hin⟩, hall⟩ := hc
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact L.disj (hall w hw)
  · rw [List.mem_singleton] at hr
    subst hr
    exact (L.stkD hin).symm

omit L in
theorem keepB_cs (hc : keepB (rbs ++ wbs) ws p l = true) : p.1 ∈ bases := by
  simp only [keepB, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1.1

omit L in
theorem keepB_in (hc : keepB (rbs ++ wbs) ws p l = true) : inB (rbs ++ wbs) p l = true := by
  simp only [keepB, Bool.and_eq_true] at hc; exact hc.1.2

theorem Lay.keepBytes (hP : PPostB D s s' ws) (hc : keepB (rbs ++ wbs) ws p l = true) :
    bytesAt s'.mem (pa s' p) l = bytesAt s.mem (pa s p) l := by
  rw [hP.pa (keepB_cs hc)]
  obtain ⟨n, hn, hl⟩ := inB_spec (keepB_in hc)
  exact VG.Proof.MlKem.bytesAt_frame hP.frame (L.fdisj hc) (by have := L.small _ hn; omega)

theorem Lay.keepPoly {f : Poly} (hP : PPostB D s s' ws) (hc : keepB (rbs ++ wbs) ws p 1024 = true)
    (h : PolyIs s.mem (pa s p) f) : PolyIs s'.mem (pa s' p) f := by
  rw [hP.pa (keepB_cs hc)]
  exact polyIs_frame hP.frame (L.fdisj hc) h

theorem Lay.keepRed (hP : PPostB D s s' ws) (hc : keepB (rbs ++ wbs) ws p 1024 = true)
    (h : Reduced s.mem (pa s p)) : Reduced s'.mem (pa s' p) := by
  rw [hP.pa (keepB_cs hc)]
  exact reduced_frame hP.frame (L.fdisj hc) h

theorem Lay.keepW (hP : PPostB D s s' ws) (hc : keepB (rbs ++ wbs) ws p 4 = true) :
    s'.mem.readW (pa s' p) 32 = s.mem.readW (pa s p) 32 := by
  rw [hP.pa (keepB_cs hc)]
  exact hP.frame.readW (Region.contains_self _ _) (L.fdisj hc) (by decide)

end

/-! ## Two runs in the same layout -/

/-- Two states in the same layout, with the same stack pointer. -/
structure LRel (D : Nat) (rbs wbs : List (Reg × Nat)) (x y : State) : Prop where
  lx : Lay D rbs wbs x
  ly : Lay D rbs wbs y
  regs : ∀ b ∈ rbs ++ wbs, x.gpr b.1 = y.gpr b.1
  sp : x.sp = y.sp

theorem LRel.eq {D : Nat} {rbs wbs : List (Reg × Nat)} {x y : State} (h : LRel D rbs wbs x y) {p : Ptr} {l : Nat}
    (hp : inB (rbs ++ wbs) p l = true) : x.gpr p.1 = y.gpr p.1 := by
  obtain ⟨n, hn, _⟩ := inB_spec hp
  exact h.regs (p.1, n) hn

theorem LRel.post {D : Nat} {rbs wbs : List (Reg × Nat)} {x y x' y' : State} {W₁ W₂ : List Region}
    (h : LRel D rbs wbs x y) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hx : PostB D x x' W₁) (hy : PostB D y y' W₂) :
    LRel D rbs wbs x' y' :=
  ⟨h.lx.post hx hcs, h.ly.post hy hcs, fun b hb => by rw [hx.bs _ (hcs b hb), hy.bs _ (hcs b hb), h.regs b hb],
    by rw [hx.sp, hy.sp, h.sp]⟩

end VG.Proof.MlDsa.Arm.Sign

end

end

/-!
# ML-DSA signing on ARMv7: calls of verified code

`setArgs as` moves each argument (a pointer or an immediate) into its register
(`r0`–`r3`, `r12`, `lr`): afterwards each holds the argument's value in the
state before the moves, and nothing else changed but those registers
(`setArgs_ok`). A primitive the function calls is any code verified against
its shared contract (`Proof/MlDsa/Contract.lean`) for some stack of `S` bytes that,
with the `F` bytes of the frame the call pushes, fits in the `D` bytes the
function gives its calls, and whose own frames use at most `S` bytes
(`Callee`). A call with at most four arguments (`callR_ok`), or with its fifth
and sixth pushed in a frame (`callS_ok`), leaves the permissions and the
callee-saved registers as they were, and changes memory only within the
buffers it writes and the `D` bytes of stack below the stack pointer. Two runs
of it leak the same when the callee's public data agree (`callR_tr`,
`callS_tr`), and a callee whose result is public in its own runs (`RetPub`)
returns the same in both (`callRRet_tr`, `callSRet_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (push2_frame addr_sub view_gpr)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa

/-! ## Registers a block writes -/

/-- `s'` differs from `s` only in the registers `rs` (and the flags). -/
structure Keep (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs s₂ s₃) : Keep rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s') (hs : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp⟩

/-- The registers the moves of arguments write. -/
abbrev argRegs : List Reg := [.r0, .r1, .r2, .r3, .r12, .lr]

theorem argRegs_cs : ∀ r ∈ preserved, r ≠ .lr → r ∉ argRegs := by decide

theorem Keep.cs {s s' : State} (h : Keep argRegs s s') : CS s s' := fun r hr hl => h.gpr r (argRegs_cs r hr hl)

/-! ## Moves -/

theorem movi_val (v : Nat) :
    (BitVec.ofNat 16 (v / 65536) ++ ((BitVec.ofNat 16 v).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 v := by
  have e1 : BitVec.ofNat 16 (v / 65536) = (BitVec.ofNat 32 v).extractLsb' 16 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_using []
  have e2 : BitVec.ofNat 16 v = (BitVec.ofNat 32 v).extractLsb' 0 16 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega_using []
  rw [e1, e2]; exact movw_movt _

theorem movi_ok (d : Reg) (v : Nat) (s : State) :
    WP isa (.block (movi d v)) s fun s1 => s1.gpr d = BitVec.ofNat 32 v ∧ Keep [d] s s1 := by
  run_block [movi]
  refine ⟨by simp [movi_val], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp [hr]

theorem lea_ok (d : Reg) (p : Ptr) (hd : p.1 ≠ d) (s : State) :
    WP isa (.block (lea d p)) s fun s1 => s1.gpr d = s.gpr p.1 + BitVec.ofNat 32 p.2 ∧ Keep [d] s s1 := by
  run_block [lea, movi, hd]
  refine ⟨by simp [movi_val, BitVec.add_comm], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp [hr]

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.Arm.Sign.Arg.val (s : State) : Arg → BitVec 32
  | .ptr p => s.gpr p.1 + BitVec.ofNat 32 p.2
  | .imm v => BitVec.ofNat 32 v

/-- A pointer in a register of `bases`, or an immediate. -/
def _root_.VG.Impl.MlDsa.Arm.Sign.Arg.ok : Arg → Bool
  | .ptr p => decide (p.1 ∈ bases)
  | .imm _ => true

theorem Arg.mov_ok (d : Reg) (a : Arg) (ha : a.ok = true) (hd : d ∈ argRegs) (s : State) :
    WP isa (.block (a.mov d)) s fun s1 => s1.gpr d = a.val s ∧ Keep [d] s s1 := by
  cases a with
  | ptr p =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    exact lea_ok d p (fun e => by revert ha hd; rw [e]; cases d <;> decide) s
  | imm v => exact movi_ok d v s

theorem setArgsTo_ok : ∀ (ds : List Reg) (as : List Arg), ds.Nodup → (∀ d ∈ ds, d ∈ argRegs) →
    as.all Arg.ok = true → ∀ s : State,
    WP isa (.block (setArgsTo ds as)) s fun s1 => (∀ da ∈ ds.zip as, s1.gpr da.1 = da.2.val s) ∧ Keep ds s s1
  | [], _, _, _, _, s => WP.block_nil ⟨fun _ h => by simp at h, Keep.refl _ _⟩
  | _ :: _, [], _, _, _, s => WP.block_nil ⟨fun _ h => by simp at h, Keep.refl _ _⟩
  | d :: ds, a :: as, hn, hd, ha, s => by
    rw [List.nodup_cons] at hn
    simp only [List.all_cons, Bool.and_eq_true] at ha
    simp only [setArgsTo, List.zip_cons_cons, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine WP.mono (Arg.mov_ok d a ha.1 (hd d (List.mem_cons_self ..)) s) fun s1 ⟨h1, k1⟩ => ?_
    refine WP.mono (setArgsTo_ok ds as hn.2 (fun d' h => hd d' (List.mem_cons_of_mem _ h)) ha.2 s1)
      fun s2 ⟨h2, k2⟩ => ⟨fun da hda => ?_, (k1.mono fun r hr => by simp_all).trans (k2.mono fun r hr => by simp [hr])⟩
    -- The values in `s1` are those in `s`: the moves keep the bases.
    have hval : ∀ b : Arg, b.ok = true → b.val s1 = b.val s := fun b hb => by
      cases b with
      | ptr p =>
        simp only [Arg.ok, decide_eq_true_eq] at hb
        simp only [Arg.val]
        have hdb : d ∈ argRegs := hd d (List.mem_cons_self ..)
        rw [k1.gpr p.1 (by simp only [List.mem_singleton]; intro e; revert hb hdb; rw [e]; cases d <;> decide)]
      | imm v => rfl
    rcases List.mem_cons.mp hda with rfl | hda
    · rw [k2.gpr _ hn.1, h1]
    · have := List.of_mem_zip hda
      rw [h2 da hda, hval da.2 (List.all_eq_true.mp ha.2 _ this.2)]

theorem argRegs6_nodup : argRegs6.Nodup := by decide

/-- The moves of the arguments `as`. -/
theorem setArgs_ok (as : List Arg) (ha : as.all Arg.ok = true) (s : State) :
    WP isa (.block (setArgs as)) s fun s1 => (∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s) ∧
      Keep argRegs s s1 :=
  setArgsTo_ok argRegs6 as argRegs6_nodup (fun _ h => h) ha s

theorem setArgsTo_nomem (ds : List Reg) (as : List Arg) : ∀ i ∈ setArgsTo ds as, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [setArgsTo, List.mem_flatMap] at hi
  obtain ⟨⟨d, a⟩, _, hi⟩ := hi
  cases a with
  | ptr p =>
    simp only [Arg.mov, lea, movi, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rfl
  | imm v =>
    simp only [Arg.mov, movi, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> rfl

/-! ## Blocks without memory accesses -/

theorem execBlock_nomem {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) :
    ∀ {s s' : State} {t : List Leak}, execBlock isa is s = some (s', t) → t = [] := by
  induction is with
  | nil => intro s s' t e; simp [execBlock] at e; exact e.2
  | cons i is ih =>
    intro s s' t e
    simp only [execBlock] at e
    split at e
    · cases e
    · obtain ⟨⟨s₂, t₂⟩, e₂, he⟩ := Option.map_eq_some_iff.mp e
      simp only [Prod.mk.injEq] at he
      rw [← he.2, show addrs i s = [] from h i (List.mem_cons_self ..) s,
        ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) e₂]
      rfl

/-- A block that accesses no memory leaks nothing. -/
theorem block_nomem_tr {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) {P : State → State → Prop} :
    RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨(execBlock_nomem h e₁).trans (execBlock_nomem h e₂).symm, trivial⟩

/-- A relation of the final states from facts each run proves of its own. -/
theorem postDep {P Q : State → State → Prop} {c : Prog isa} {F : State → State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x (F x) ∧ WP isa c y (F y))
    (hQ : ∀ x y x' y', P x y → F x x' → F y y' → Q x' y') : RelCT isa P c Q :=
  RelCT.mono (RelCT.wpDep h hw) (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, f₁, f₂⟩ => hQ _ _ _ _ hp f₁ f₂

/-! ## Callees -/

/-- Code verified against the contract `k S` for a stack of `S` bytes, that
with the `F` bytes of the frame its calls push fits in `D`, and whose frames
use at most `S` bytes. -/
structure Callee (k : Nat → Contract isa) (F D : Nat) (c : Prog isa) where
  /-- The stack its contract gives it. -/
  S : Nat
  hS : S + F ≤ D
  ver : Verified Arm.target c (k S)
  su : stackUse c ≤ S

/-- The result of `c` (`r0`) is the same in two runs from states that
satisfy `k.pre` and agree on `k.pub`. -/
def RetPub (k : Contract isa) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0

/-- The arguments of `as`, in their registers after the moves. -/
abbrev ArgsIn (as : List Arg) (s s1 : State) : Prop := ∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s

theorem argsIn2 {a b : Arg} {s s1 : State} (h : ArgsIn [a, b] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6])⟩

theorem argsIn3 {a b c : Arg} {s s1 : State} (h : ArgsIn [a, b, c] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s ∧ s1.gpr .r2 = c.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6]), h (.r2, c) (by simp [argRegs6])⟩

theorem argsIn4 {a b c d : Arg} {s s1 : State} (h : ArgsIn [a, b, c, d] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s ∧ s1.gpr .r2 = c.val s ∧ s1.gpr .r3 = d.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6]), h (.r2, c) (by simp [argRegs6]),
    h (.r3, d) (by simp [argRegs6])⟩

theorem argsIn5 {a b c d e : Arg} {s s1 : State} (h : ArgsIn [a, b, c, d, e] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s ∧ s1.gpr .r2 = c.val s ∧ s1.gpr .r3 = d.val s ∧
      s1.gpr .r12 = e.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6]), h (.r2, c) (by simp [argRegs6]),
    h (.r3, d) (by simp [argRegs6]), h (.r12, e) (by simp [argRegs6])⟩

theorem argsIn6 {a b c d e f : Arg} {s s1 : State} (h : ArgsIn [a, b, c, d, e, f] s s1) :
    s1.gpr .r0 = a.val s ∧ s1.gpr .r1 = b.val s ∧ s1.gpr .r2 = c.val s ∧ s1.gpr .r3 = d.val s ∧
      s1.gpr .r12 = e.val s ∧ s1.gpr .lr = f.val s :=
  ⟨h (.r0, a) (by simp [argRegs6]), h (.r1, b) (by simp [argRegs6]), h (.r2, c) (by simp [argRegs6]),
    h (.r3, d) (by simp [argRegs6]), h (.r12, e) (by simp [argRegs6]), h (.lr, f) (by simp [argRegs6])⟩

/-! ## The stack -/

theorem belowA_mono {sp : BitVec 32} {a b : Nat} (hab : a ≤ b) {W : List Region} {m m' : Mem}
    (h : Frame (W ++ [belowA sp a]) m m') : Frame (W ++ [belowA sp b]) m m' :=
  Frame.sub h fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_sub hab⟩

/-- The argument on the stack of a call with a frame: the word at the
stack pointer of the callee. -/
abbrev argR (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 4⟩

/-! ## Calls with their arguments in registers -/

/-- The moves of the arguments, then a call of verified code. -/
theorem callR_ok {D : Nat} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsu : stackUse c ≤ D) {as : List Arg} (ha : as.all Arg.ok = true) {s : State} (hsp : D ≤ s.sp.toNat)
    {rd wr : List Region}
    (hpre : ∀ s1, ArgsIn as s s1 → Keep argRegs s s1 → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (callR n c as) s fun s' => PostB D s s' wr ∧ CS s s' ∧
      ∃ s1, ArgsIn as s s1 ∧ Keep argRegs s s1 ∧ k.post (s1.callEntry.withRegions rd wr) (s'.withRegions rd wr) := by
  refine WP.seq (WP.mono (setArgs_ok as ha s) fun s1 ⟨hA, k1⟩ => ?_)
  refine WP.callF hv (hpre s1 hA k1) (by rw [k1.rd, k1.wr]; exact hc) (by rw [k1.wr]; exact hw)
    (by rw [k1.sp]; omega_using [hsu, hsp]) fun s' hrd hwr hsp' hf hcs hpost => ?_
  have hcs' : CS s s' := CS.trans k1.cs hcs
  rw [k1.mem, k1.sp] at hf
  exact ⟨⟨hrd.trans k1.rd, hwr.trans k1.wr, fun r hr => hcs' r (bases_cs r hr).1 (bases_cs r hr).2,
    hsp'.trans k1.sp, belowA_mono hsu hf⟩, hcs', s1, hA, k1, hpost⟩

/-! ## Calls with arguments on the stack -/

theorem frame8 {s : State} (hsp : 8 ≤ s.sp.toNat) :
    (⟨State.addr (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)), 4 * [Reg.r12, Reg.lr].length⟩ : Region) =
      belowA s.sp 8 := by
  simp only [belowA, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
  rw [addr_sub hsp]

theorem ne12_pres : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r12 := by decide

theorem argR_contains {s : State} {x : Addr} {m : Nat} (h : (argR s).Contains x m) :
    (belowA s.sp 8).Contains x m := by
  simp only [Region.Contains, belowA] at h ⊢; omega_using [h]

theorem sp_sub8 {sp : BitVec 32} (h : 8 ≤ sp.toNat) : (sp - BitVec.ofNat 32 8).toNat = sp.toNat - 8 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_using [h]

theorem argR_sub (s : State) : Region.Sub (argR s) (belowA s.sp 8) := fun x hx => by
  simp only [Region.Contains, belowA] at hx ⊢; omega_using [hx]

/-- The moves of the arguments, then a call of verified code in a frame that
pushes its fifth and sixth arguments (`r12`, `lr`). -/
theorem callS_ok {D : Nat} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsu : 8 + stackUse c ≤ D) {as : List Arg} (ha : as.all Arg.ok = true) {s : State} (hsp : D ≤ s.sp.toNat)
    {rd wr : List Region}
    (hpre : ∀ s1, ArgsIn as s s1 → Keep argRegs s s1 →
      k.pre ((pushed [.r12, .lr] s1).callEntry.withRegions (rd ++ [argR s]) wr))
    (hc : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (callS n c as) s fun s' => PostB D s s' wr ∧ CS s s' ∧
      ∃ s1, ArgsIn as s s1 ∧ Keep argRegs s s1 ∧ ∃ s₂ : State, Frame [belowA s.sp D] s₂.mem s'.mem ∧
        (∀ r, r ≠ .r12 → s₂.gpr r = s'.gpr r) ∧
        k.post ((pushed [.r12, .lr] s1).callEntry.withRegions (rd ++ [argR s]) wr)
          (s₂.withRegions (rd ++ [argR s]) wr) := by
  have h8 : 8 ≤ s.sp.toNat := by omega_using [hsu, hsp]
  refine WP.seq (WP.mono (setArgs_ok as ha s) fun s1 ⟨hA, k1⟩ => ?_)
  have h8' : 8 ≤ s1.sp.toNat := by rw [k1.sp]; exact h8
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h8') (by decide) ?_
  have hwp : (pushed [.r12, .lr] s1).wr = belowA s.sp 8 :: s.wr := by
    rw [VG.Arm.pushed_wr, frame8 h8', k1.wr, k1.sp]
  refine WP.callF hv (hpre s1 hA k1) (fun x m hx => ?_) (fun x m hx => ?_) ?_ fun s₂ hrd hwr hsp₂ hf hcs hpost mL uL hfl => ?_
  · rw [VG.Arm.pushed_rd, hwp, k1.rd]
    rcases (by simpa only [InRegions, List.mem_append, or_assoc] using hx : ∃ r, (r ∈ rd ∨ r ∈ [argR s] ∨ r ∈ wr) ∧
      r.Contains x m) with ⟨r, (hr | hr | hr), hcr⟩
    · obtain ⟨r', hr', hc'⟩ := hc x m ⟨r, hr, hcr⟩
      rcases List.mem_append.mp hr' with h | h
      · exact ⟨r', List.mem_append_left _ h, hc'⟩
      · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h), hc'⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), argR_contains hcr⟩
    · obtain ⟨r', hr', hc'⟩ := hw x m ⟨r, hr, hcr⟩
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · rw [hwp]
    obtain ⟨r', hr', hc'⟩ := hw x m hx
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · rw [VG.Arm.pushed_sp, k1.sp, show BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = BitVec.ofNat 32 8 from rfl,
      sp_sub8 h8]; omega_using [hsu, hsp]
  · have hcs₂ : CS s s₂ := fun r hr hl => by rw [hcs r hr hl, VG.Arm.pushed_gpr]; exact k1.cs r hr hl
    have hsp₂' : s₂.sp = s.sp - BitVec.ofNat 32 8 := by rw [hsp₂, VG.Arm.pushed_sp, k1.sp]; rfl
    have f₁ := push2_frame h8'
    rw [k1.mem] at f₁
    have hsu' : 8 + stackUse c ≤ s.sp.toNat := by omega_using [hsu, hsp]
    rw [frame8 h8', k1.sp] at hfl
    have hflD : Frame [belowA s.sp D] s₂.mem mL := hfl.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact belowA_sub (by omega_using [hsu])⟩
    refine ⟨⟨by simp only [popped_rd, hrd, VG.Arm.pushed_rd, k1.rd], by simp only [popped_wr, hwr, hwp, List.tail_cons],
      fun r hr => (popped_gpr (ne12_pres r (bases_cs r hr).1 (bases_cs r hr).2) 8 s₂).trans
        (hcs₂ r (bases_cs r hr).1 (bases_cs r hr).2), by rw [popped_sp, hsp₂']; exact BitVec.sub_add_cancel _ _, ?_⟩,
      fun r hr hl => by rw [popped_gpr (ne12_pres r hr hl)]; exact hcs₂ r hr hl,
      s1, hA, k1, s₂, hflD, fun r hr => (popped_gpr hr 8 s₂).symm, hpost⟩
    dsimp only
    refine Frame.trans ?_ (hflD.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
    rw [VG.Arm.pushed_sp, k1.sp] at hf
    refine (f₁.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      show ∃ r', r' ∈ wr ++ [belowA s.sp D] ∧ (belowA s1.sp 8).Sub r'
      rw [k1.sp]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_sub (by omega_using [hsu])⟩
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          fun x h => belowA_sub (show 8 + stackUse c ≤ D by omega_using [hsu]) x (belowA_push hsu' x h)⟩

/-! ## Two runs of a call -/

/-- A call of verified code leaks the same in two runs whose narrowed entry
states satisfy its precondition and agree on its public data; and its
result is the same if it is public in its own runs (`RetPub`). -/
theorem RelCT.callEx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 ∨ True)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧ k.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr) :
    RelCT isa P (.call n c) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨_, n₁⟩ := trace_narrow hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨_, n₂⟩ := trace_narrow hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ n₁ n₂
      exact ⟨by simp only [ht], trivial⟩

/-- The run of a call narrowed to the regions its contract gives it: the
same trace, and the same registers. -/
theorem narrow_run {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} {t : List Leak} {s' : State}
    (hpre : k.pre (s.withRegions rd wr)) (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr)
    (he : Exec isa c s t s') : ∃ s'', Exec isa c (s.withRegions rd wr) t s'' ∧ s''.gpr = s'.gpr := by
  obtain ⟨t', s'', he', -⟩ := hv _ hpre
  have hw' := Exec.widen he' (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at hw'
  obtain ⟨rfl, rfl⟩ := Exec.det he hw'
  exact ⟨_, he', rfl⟩

theorem RelCT.callRet {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧ k.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr) :
    RelCT isa P (.call n c) fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨n₁, x₁, g₁⟩ := narrow_run hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨n₂, x₂, g₂⟩ := narrow_run hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      obtain ⟨ht, hrax⟩ := hr _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ x₁ x₂
      rw [ret_eq r₁, ret_eq r₂]
      exact ⟨by simp only [ht], show _ = _ by rw [← g₁, ← g₂]; exact hrax⟩

/-- Constant time, as `RelCT.callEx` needs it. -/
theorem ct_or {k : Contract isa} {c : Prog isa} (hct : ConstantTime isa k.pre k.pub c) :
    RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 ∨ True :=
  fun _ _ _ _ _ _ ⟨h₁, h₂, hp⟩ e₁ e₂ => ⟨hct _ _ _ _ _ _ h₁ h₂ hp e₁ e₂, .inr trivial⟩

/-- The moves of the arguments, from two related states. -/
theorem setArgs_rel {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop} :
    RelCT isa P (.block (setArgs as)) fun x1 y1 => ∃ x y, P x y ∧ (ArgsIn as x x1 ∧ Keep argRegs x x1) ∧
      (ArgsIn as y y1 ∧ Keep argRegs y y1) :=
  RelCT.mono (RelCT.wpDep (block_nomem_tr (setArgsTo_nomem _ _))
    (fun x y _ => ⟨setArgs_ok as ha x, setArgs_ok as ha y⟩)) (fun _ _ h => h)
    fun _ _ ⟨_, x, y, hp, h1, h2⟩ => ⟨x, y, hp, h1, h2⟩

/-- Region lists for the two runs of a call. -/
abbrev Regs2 (k : Contract isa) (x1 y1 : State) : Prop := ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
  k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
  k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
  Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧ Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr

theorem callR_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → ArgsIn as x x1 ∧ Keep argRegs x x1 → ArgsIn as y y1 ∧ Keep argRegs y y1 →
      Regs2 k x1 y1) :
    RelCT isa P (callR n c as) fun _ _ => True :=
  RelCT.seq (setArgs_rel ha) (RelCT.callEx hv (ct_or hct) fun _ _ ⟨x, y, hp, h1, h2⟩ => hP x y _ _ hp h1 h2)

theorem callRRet_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → ArgsIn as x x1 ∧ Keep argRegs x x1 → ArgsIn as y y1 ∧ Keep argRegs y y1 →
      Regs2 k x1 y1) :
    RelCT isa P (callR n c as) fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 :=
  RelCT.seq (setArgs_rel ha) (RelCT.callRet hv hr fun _ _ ⟨x, y, hp, h1, h2⟩ => hP x y _ _ hp h1 h2)

/-- A frame of the stack arguments around a call whose runs relate by `Q`
(on `r0`, which the pop does not change). -/
theorem RelCT.frame12 {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp)
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed [.r12, .lr] s₁ ∧ b = pushed [.r12, .lr] s₂) body
      fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0) :
    RelCT isa P (.frame (.push [.r12, .lr]) body (.pop .r12 8)) fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain ⟨rfl, -⟩ := VG.Arm.push_pushed' p₁
      obtain ⟨rfl, -⟩ := VG.Arm.push_pushed' p₂
      obtain ⟨ht, h0⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      have hq₁ := pop_eq q₁
      have hq₂ := pop_eq q₂
      have e := hsp _ _ hp
      refine ⟨?_, ?_⟩
      · rw [ht]
        simp only [addrs, hq₁.2.2.2.2.1, hq₂.2.2.2.2.1, VG.Arm.pushed_sp, e]
      · show _ = _
        rw [hq₁.2.2.2.1 .r0 (by decide), hq₂.2.2.2.1 .r0 (by decide)]; exact h0

theorem callS_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hsp : ∀ x y, P x y → x.sp = y.sp)
    (hP : ∀ x y x1 y1, P x y → ArgsIn as x x1 ∧ Keep argRegs x x1 → ArgsIn as y y1 ∧ Keep argRegs y y1 →
      Regs2 k (pushed [.r12, .lr] x1) (pushed [.r12, .lr] y1)) :
    RelCT isa P (callS n c as) fun _ _ => True :=
  RelCT.seq (setArgs_rel ha) (VG.Arm.RelCT.frame
    (fun _ _ ⟨x, y, hp, h1, h2⟩ => by rw [h1.2.sp, h2.2.sp]; exact hsp x y hp)
    (RelCT.callEx hv (ct_or hct) fun _ _ ⟨x1, y1, ⟨x, y, hp, h1, h2⟩, ea, eb⟩ => by
      rw [(VG.Arm.push_pushed' ea).1, (VG.Arm.push_pushed' eb).1]; exact hP x y x1 y1 hp h1 h2))

theorem callSRet_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hsp : ∀ x y, P x y → x.sp = y.sp)
    (hP : ∀ x y x1 y1, P x y → ArgsIn as x x1 ∧ Keep argRegs x x1 → ArgsIn as y y1 ∧ Keep argRegs y y1 →
      Regs2 k (pushed [.r12, .lr] x1) (pushed [.r12, .lr] y1)) :
    RelCT isa P (callS n c as) fun s₁ s₂ => s₁.gpr .r0 = s₂.gpr .r0 :=
  RelCT.seq (setArgs_rel ha) (RelCT.frame12
    (fun _ _ ⟨x, y, hp, h1, h2⟩ => by rw [h1.2.sp, h2.2.sp]; exact hsp x y hp)
    (RelCT.callRet hv hr fun _ _ ⟨x1, y1, ⟨x, y, hp, h1, h2⟩, ea, eb⟩ => ea ▸ eb ▸ hP x y x1 y1 hp h1 h2))

end VG.Proof.MlDsa.Arm.Sign
