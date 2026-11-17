module

import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.MlDsa.Sign.Mem
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Framework.X86_64.ModeSim
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Frag

/-! ### `MlDsa.X86_64.Sign.Call`, which this module and modules that import it used -/

section

/-! ### `MlDsa.X86_64.Sign.Lay`, which this module and modules that import it used -/

section

/-!
# ML-DSA signing on x86-64: the buffers of the function

The function keeps the address of each buffer it works in (its arguments and
its working space) in a callee-saved register; a layout (`Lay`) lists these
registers with the lengths of their buffers, which are apart from each other
and from the `D` bytes of stack below `rsp` that the calls use. A pointer (a
register and an offset) into a buffer, and two pointers into the same buffer
or different ones, are then checked by evaluation (`inB`, `sepB`): each pair
of regions a call needs apart is, and each region is readable or writable
(`Lay.disj`, `Lay.stkD`, `Lay.cR`, `Lay.cW`). A call leaves the layout as it
was (`Lay.post`), and the bytes of a region apart from those it writes
(`Lay.keepBytes`, `Lay.keepPoly`).

(As ML-KEM's `Proof/MlKem/X86_64/Lay.lean`, with the stack below `rsp` a
parameter: the primitives' own calls may nest.)
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The address of the pointer `p` in `s`. -/
abbrev pa (s : State) (p : Ptr) : Addr := s.gpr p.1 + BitVec.ofNat 64 p.2

/-- The return address. -/
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-! ## Checks -/

/-- The `len` bytes at `p` lie within the buffer of its register in the layout `bs`. -/
def inB (bs : List (Reg × Nat)) (p : Ptr) (len : Nat) : Bool :=
  match bs.lookup p.1 with
  | some n => decide (p.2 + len ≤ n)
  | none => false

/-- The registers of the buffers the function writes (`scratch` and `sig`):
a buffer it only reads may overlap another such buffer, but not one of
these. -/
abbrev wRegs : List Reg := [.rbx, .r14]

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

theorem contains_offset' {base : Addr} {off len n : Nat} (h : off + len ≤ n) (hn : n < 2 ^ 64) :
    (⟨base, n⟩ : Region).Contains (base + BitVec.ofNat 64 off) len := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_using [h, hn])]
  omega_using [h]

theorem sub_offset' {base : Addr} {off len n : Nat} (h : off + len ≤ n) (hn : n < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, n⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [show a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by bv_omega, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega_using [h, hn])]
  have := Nat.mod_le ((a - (base + BitVec.ofNat 64 off)).toNat + off) (2 ^ 64)
  omega_using [h, ha]

theorem off_disj {base : Addr} {a b la lb : Nat} (h : a + la ≤ b) (hb : b + lb < 2 ^ 64) :
    Region.Disjoint ⟨base + BitVec.ofNat 64 a, la⟩ ⟨base + BitVec.ofNat 64 b, lb⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have e : x - (base + BitVec.ofNat 64 a) = (x - (base + BitVec.ofNat 64 b)) + BitVec.ofNat 64 (b - a) := by
    rw [show BitVec.ofNat 64 (b - a) = BitVec.ofNat 64 b - BitVec.ofNat 64 a by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using [h]]
    bv_omega
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b - a) (by omega_using [hb]),
    Nat.mod_eq_of_lt (by omega_using [hb, h₂])] at h₁
  omega_using [h, h₁]

theorem inRegions_sub {X : List Region} {a : Addr} {n off l : Nat} (h : InRegions X a n) (hl : off + l ≤ n)
    (hn : n < 2 ^ 64) : InRegions X (a + BitVec.ofNat 64 off) l := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  rw [show a + BitVec.ofNat 64 off - r.base = (a - r.base) + BitVec.ofNat 64 off by bv_omega, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega_using [hl, hn])]
  have := Nat.mod_le ((a - r.base).toNat + off) (2 ^ 64)
  omega_using [hl, hc]

/-! ## Layouts -/

section
variable (D : Nat)

/-- The buffers of `rbs` (read) and `wbs` (written), at the addresses in
their registers: small, apart from each other, from the return address and
from the `D` bytes of stack below `rsp`, not wrapping around, and
permitted; and `D` bytes of stack below `rsp` that do not wrap around. -/
structure Lay (rbs wbs : List (Reg × Nat)) (s : State) : Prop where
  small : ∀ b ∈ rbs ++ wbs, b.2 < 2 ^ 32
  dj : ∀ b ∈ rbs ++ wbs, ∀ b' ∈ rbs ++ wbs, b.1 ≠ b'.1 → (b.1 ∈ wRegs ∨ b'.1 ∈ wRegs) →
    Region.Disjoint ⟨s.gpr b.1, b.2⟩ ⟨s.gpr b'.1, b'.2⟩
  stk : ∀ b ∈ rbs ++ wbs, (below (s.gpr .rsp) D).Disjoint ⟨s.gpr b.1, b.2⟩
  nw : ∀ b ∈ rbs ++ wbs, (s.gpr b.1).toNat + b.2 ≤ 2 ^ 64
  rd : ∀ b ∈ rbs ++ wbs, InRegions (s.rd ++ s.wr) (s.gpr b.1) b.2
  wr : ∀ b ∈ wbs, InRegions s.wr (s.gpr b.1) b.2
  ret : ∀ b ∈ rbs ++ wbs, (retR s).Disjoint ⟨s.gpr b.1, b.2⟩
  sp : D ≤ (s.gpr .rsp).toNat
  dsm : D < 2 ^ 32

end

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s)
include L

theorem Lay.sub {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    ∃ n, (p.1, n) ∈ rbs ++ wbs ∧ Region.Sub ⟨pa s p, l⟩ ⟨s.gpr p.1, n⟩ := by
  obtain ⟨n, hm, hl⟩ := inB_spec h
  exact ⟨n, hm, sub_offset' hl (by have := L.small _ hm; omega)⟩

theorem Lay.disj {p q : Ptr} {l k : Nat} (h : sepB (rbs ++ wbs) p l q k = true) :
    Region.Disjoint ⟨pa s p, l⟩ ⟨pa s q, k⟩ := by
  obtain ⟨hp, hq, hs⟩ := sepB_spec h
  obtain ⟨n, hn, hl⟩ := inB_spec hp
  obtain ⟨m, hm, hk⟩ := inB_spec hq
  have sn := L.small _ hn
  have sm := L.small _ hm
  rcases hs with ⟨e, hw⟩ | ⟨e, hs⟩
  · exact ((L.dj _ hn _ hm e hw).sub_left (sub_offset' hl (by omega_using [sn]))).sub_right (sub_offset' hk (by omega_using [sm]))
  · show Region.Disjoint ⟨s.gpr p.1 + _, l⟩ ⟨s.gpr q.1 + _, k⟩
    rw [← e]
    rcases hs with h1 | h2
    · exact off_disj h1 (by omega)
    · exact (off_disj h2 (by omega)).symm

theorem Lay.stkD {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) :
    (below (s.gpr .rsp) D).Disjoint ⟨pa s p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := L.sub h
  exact (L.stk _ hn).sub_right hsub

theorem Lay.nwp {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true) : (pa s p).toNat + l ≤ 2 ^ 64 := by
  obtain ⟨n, hn, hl⟩ := inB_spec h
  have h1 := L.nw _ hn
  have h2 := L.small _ hn
  simp only at h1 h2
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.2) (by omega_using [hl, h2])]
  have := Nat.mod_le ((s.gpr p.1).toNat + p.2) (2 ^ 64)
  omega_using [hl, h1]

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
abbrev bases : List Reg := [.rbx, .rbp, .r12, .r13, .r14]

/-- What a piece of code leaves: the permissions, the registers `bases` and
the stack pointer, and memory but within `W` and the `D` bytes of stack. -/
structure PostB (D : Nat) (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bs : ∀ r ∈ bases, s'.gpr r = s.gpr r
  rsp : s'.gpr .rsp = s.gpr .rsp
  frame : Frame (W ++ [below (s.gpr .rsp) D]) s.mem s'.mem

/-- `PostB`, with the regions written given as pointers. -/
abbrev PPostB (D : Nat) (s s' : State) (ws : List (Ptr × Nat)) : Prop := PostB D s s' (ws.map (toR s))

/-- The `l` bytes at `p` lie in the layout, apart from the regions `ws`, and
`p`'s register is one of `bases`. -/
def keepB (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (p : Ptr) (l : Nat) : Bool :=
  decide (p.1 ∈ bases) && inB bs p l && ws.all fun w => sepB bs p l w.1 w.2

theorem PostB.pa {D : Nat} {s s' : State} {W : List Region} (hP : PostB D s s' W) {p : Ptr} (h : p.1 ∈ bases) :
    pa s' p = pa s p := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.pa, hP.bs _ h]

theorem PostB.refl (D : Nat) (s : State) (W : List Region) : PostB D s s W :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl, Frame.refl _ _⟩

theorem PostB.trans {D : Nat} {s s₁ s₂ : State} {W₁ W₂ W : List Region} (h₁ : PostB D s s₁ W₁)
    (h₂ : PostB D s₁ s₂ W₂) (hw₁ : ∀ r ∈ W₁, r ∈ W) (hw₂ : ∀ r ∈ W₂, r ∈ W) : PostB D s s₂ W := by
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.bs r hr).trans (h₁.bs r hr),
    h₂.rsp.trans h₁.rsp, ?_⟩
  have f₂ := h₂.frame
  rw [h₁.rsp] at f₂
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
    fun b hb => ?_, ?_, ?_⟩
  · rw [e b hb, e b' hb']; exact L.dj b hb b' hb' hne hw
  · rw [e b hb, hP.rsp]; exact L.stk b hb
  · rw [e b hb]; exact L.nw b hb
  · rw [e b hb, hP.rd, hP.wr]; exact L.rd b hb
  · rw [e b (List.mem_append_right _ hb), hP.wr]; exact L.wr b hb
  · simp only [retR, e b hb, hP.rsp]; exact L.ret b hb
  · rw [hP.rsp]; exact L.sp
  · exact L.dsm

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay D rbs wbs s) {ws : List (Ptr × Nat)}
  {p : Ptr} {l : Nat}
include L

theorem Lay.fdisj (hc : keepB (rbs ++ wbs) ws p l = true) :
    ∀ r ∈ ws.map (toR s) ++ [below (s.gpr .rsp) D], Region.Disjoint ⟨pa s p, l⟩ r := by
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

theorem Lay.keepW (hP : PPostB D s s' ws) (hc : keepB (rbs ++ wbs) ws p 8 = true) :
    s'.mem.readW (pa s' p) 64 = s.mem.readW (pa s p) 64 := by
  rw [hP.pa (keepB_cs hc)]
  exact hP.frame.readW (Region.contains_self _ _) (L.fdisj hc) (by decide)

end

/-- The return address is kept by code that writes within the layout and the stack. -/
theorem Lay.keepRet {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hin : ∀ w ∈ ws, inB (rbs ++ wbs) w.1 w.2 = true) :
    s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  refine hP.frame.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    obtain ⟨n, hn, hsub⟩ := L.sub (hin w hw)
    exact (L.ret _ hn).sub_right hsub
  · rw [List.mem_singleton] at hr; subst hr
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    have := L.sp
    have := L.dsm
    bv_omega

/-! ## Two runs in the same layout -/

/-- Two states in the same layout, with the same stack pointer. -/
structure LRel (D : Nat) (rbs wbs : List (Reg × Nat)) (x y : State) : Prop where
  lx : Lay D rbs wbs x
  ly : Lay D rbs wbs y
  regs : ∀ b ∈ rbs ++ wbs, x.gpr b.1 = y.gpr b.1
  rsp : x.gpr .rsp = y.gpr .rsp

theorem LRel.eq {D : Nat} {rbs wbs : List (Reg × Nat)} {x y : State} (h : LRel D rbs wbs x y) {p : Ptr} {l : Nat}
    (hp : inB (rbs ++ wbs) p l = true) : x.gpr p.1 = y.gpr p.1 := by
  obtain ⟨n, hn, _⟩ := inB_spec hp
  exact h.regs (p.1, n) hn

theorem LRel.pa {D : Nat} {rbs wbs : List (Reg × Nat)} {x y : State} (h : LRel D rbs wbs x y) {p : Ptr} {l : Nat}
    (hp : inB (rbs ++ wbs) p l = true) : pa x p = pa y p := by
  simp only [VG.Proof.MlDsa.X86_64.Sign.pa, h.eq hp]

theorem LRel.post {D : Nat} {rbs wbs : List (Reg × Nat)} {x y x' y' : State} {W₁ W₂ : List Region}
    (h : LRel D rbs wbs x y) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hx : PostB D x x' W₁) (hy : PostB D y y' W₂) :
    LRel D rbs wbs x' y' :=
  ⟨h.lx.post hx hcs, h.ly.post hy hcs, fun b hb => by rw [hx.bs _ (hcs b hb), hy.bs _ (hcs b hb), h.regs b hb],
    by rw [hx.rsp, hy.rsp, h.rsp]⟩

end VG.Proof.MlDsa.X86_64.Sign

end

end

/-!
# ML-DSA signing on x86-64: calls of verified code

A primitive the function calls is any code verified against its shared contract
(`Proof/MlDsa/Contract.lean`) for some stack of `S` bytes that leaves 8 bytes for
the return address in the `D` bytes the function gives its calls, and that
never writes `rsp` (`Callee`). A call, with the moves of its arguments before
it (`glueCall_ok`), leaves the permissions and the callee-saved registers as
they were, and changes memory only within the buffers it writes and the `D`
bytes of stack below `rsp`. Two runs of it leak the same when the callee's
public data agree (`glueCall_tr`), and a callee whose result is public in its
own runs (`RetPub`) returns the same in both (`glueCallRet_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The registers the moves of arguments write. -/
abbrev argRegs : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9]

theorem argRegs_cs : ∀ r ∈ calleeSaved, r ∉ argRegs := by decide

theorem bases_cs : ∀ r ∈ bases, r ∈ calleeSaved := by decide

/-- Code verified against the contract `k S` for a stack of `S` bytes, with
8 bytes to spare in `D`, which never writes `rsp` and whose calls nest
within `D` bytes. -/
structure Callee (k : Nat → Contract isa) (D : Nat) (c : Prog isa) where
  /-- The stack its contract gives it. -/
  S : Nat
  hS : S + 8 ≤ D
  ver : Verified X86_64.target c (k S)
  nosp : NoSp c
  mx : c.allInstrs (fun i => !touchesMxcsr i) = true
  depth : 8 * (c.depth + 1) ≤ D

/-- A callee is constant time from states whose public data agree but in
MXCSR, which it never touches (`Contract.mxFree`). -/
theorem Callee.ctMx {k : Nat → Contract isa} {D : Nat} {c : Prog isa} (C : Callee k D c)
    (hpre : ∀ s m, (k C.S).pre s → (k C.S).pre (s.withMx m)) :
    ConstantTime isa (k C.S).mxFree.pre (k C.S).mxFree.pub c :=
  Contract.ct_mxFree C.mx C.ver.2.1 hpre

/-- `C.ver`'s correctness, for `Contract.mxFree`, whose precondition and
postcondition are those of the callee's contract. -/
theorem Callee.okMx {k : Nat → Contract isa} {D : Nat} {c : Prog isa} (C : Callee k D c) :
    ∀ s, (k C.S).mxFree.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (k C.S).mxFree.post s s' :=
  C.ver.1

/-- The result of `c` (the low 32 bits of `rax`) is the same in two runs from
states that satisfy `k.pre` and agree on `k.pub`. -/
def RetPub (k : Contract isa) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c
    fun s₁ s₂ => (s₁.gpr .rax).setWidth 32 = (s₂.gpr .rax).setWidth 32

/-- `RetPub` from public data that agree but in MXCSR, for code that never
touches it (`Exec.withMx`). -/
theorem RetPub.mxFree {k : Contract isa} {c : Prog isa} (h : RetPub k c)
    (hc : c.allInstrs (fun i => !touchesMxcsr i) = true) (hpre : ∀ s m, k.pre s → k.pre (s.withMx m)) :
    RetPub k.mxFree c := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
  h s₁ (s₂.withMx s₁.mxcsr) t₁ t₂ s₁' (s₂'.withMx s₁.mxcsr) ⟨h₁, hpre _ _ h₂, hp⟩ e₁
    (Exec.withMx (noTouch_instrs hc) e₂ _)

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

theorem nomem_append {a b : List Instr} (ha : ∀ i ∈ a, ∀ s, isa.addrs i s = [])
    (hb : ∀ i ∈ b, ∀ s, isa.addrs i s = []) : ∀ i ∈ a ++ b, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  rcases List.mem_append.mp hi with h | h
  exacts [ha i h s, hb i h s]

theorem lea_nomem (d : Reg) (p : Ptr) : ∀ i ∈ lea d p, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [lea, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem movi_nomem (d : Reg) (v : Nat) : ∀ i ∈ movi d v, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [movi, List.mem_singleton] at hi
  subst hi; rfl

/-! ## The stack of a call -/

theorem ce_ret {sp : Addr} {D : Nat} {R : Region} (h : (below sp D).Disjoint R) (hD : 8 ≤ D) (hDs : D < 2 ^ 32) :
    Region.Disjoint ⟨sp - 8, 8⟩ R :=
  h.sub_left fun x hx => by
    simp only [Region.Contains] at hx ⊢
    rw [show x - (sp - BitVec.ofNat 64 D) = (x - (sp - 8)) + BitVec.ofNat 64 (D - 8) by
      rw [show BitVec.ofNat 64 (D - 8) = BitVec.ofNat 64 D - 8 by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have : (8 : BitVec 64).toNat = 8 := rfl
        rw [this]; omega_using [hD]]
      bv_omega, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := D - 8) (by omega_using [hDs])]
    rw [Nat.mod_eq_of_lt (by omega_using [hDs, hx])]
    omega_using [hD, hx]

theorem ce_below {sp : Addr} {D S : Nat} {R : Region} (h : (below sp D).Disjoint R) (hS : S + 8 ≤ D)
    (hDs : D < 2 ^ 32) : (below (sp - 8) S).Disjoint R :=
  (h.sub_left (below_sub hS (by omega_using [hDs]))).sub_left (below_callee sp S)

theorem ce_wf {sp : Addr} {D S : Nat} (hS : S + 8 ≤ D) (hsp : D ≤ sp.toNat) :
    S ≤ (sp - 8).toNat := by
  rw [BitVec.toNat_sub]
  have : (8 : BitVec 64).toNat = 8 := rfl
  rw [this]
  have := sp.isLt
  omega_using [hS, hsp]

theorem abi_wf_of {ws : List Nat} (hws : ws.length ≤ 6) {S : Nat} {s : State} (h : S ≤ (s.gpr .rsp).toNat) :
    X86_64.abi.wf ws S s := by
  simp only [X86_64.abi, VG.X86_64.argRegs, List.length_cons, List.length_nil, Nat.reduceAdd, hws, ite_true]
  cases S <;> simp_all

/-- The facts about the stack a callee's contract needs, on entry: its
stack pointer leaves `S` bytes below it. -/
theorem ce_wfS {ws : List Nat} (hws : ws.length ≤ 6) {D S : Nat} (hS : S + 8 ≤ D) {s : State}
    (hsp : D ≤ (s.gpr .rsp).toNat) (rd wr : List Region) : X86_64.abi.wf ws S (s.callEntry.withRegions rd wr) :=
  abi_wf_of hws (by simp only [State.withRegions_gpr, State.callEntry_rsp]; exact ce_wf hS hsp)

/-- The regions of the stack a callee's contract gives it, apart from each buffer. -/
theorem conj_stk {sp : Addr} {S : Nat} (bs : List Region) (h : ∀ B ∈ bs, (below sp S).Disjoint B) :
    Sig.conj ((List.map (fun r => bs.map fun B => r.Disjoint B) (stackBelow sp S)).flatten) := by
  cases S with
  | zero => exact trivial
  | succ S =>
    simp only [stackBelow, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [Sig.conj_map]
    exact h

/-! ## Memory on entry to a callee -/

theorem ce_byte (s : State) {D : Nat} {R : Region} (h : (below (s.gpr .rsp) D).Disjoint R) (hD : 8 ≤ D)
    (hDs : D < 2 ^ 32) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    s.callEntry.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [⟨s.gpr .rsp - 8, 8⟩])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (by simpa using (ce_ret h hD hDs).symm) hR hi

theorem ce_polyAt (s : State) {D : Nat} {p : Addr} (h : (below (s.gpr .rsp) D).Disjoint (pR p)) (hD : 8 ≤ D)
    (hDs : D < 2 ^ 32) : polyAt s.callEntry.mem p = polyAt s.mem p :=
  polyAt_congr fun _ hi => ce_byte s (R := pR p) h hD hDs (show 1024 ≤ 2 ^ 64 by decide) hi

theorem ce_natPolyAt (s : State) {D : Nat} {p : Addr} (h : (below (s.gpr .rsp) D).Disjoint (pR p)) (hD : 8 ≤ D)
    (hDs : D < 2 ^ 32) : natPolyAt s.callEntry.mem p = natPolyAt s.mem p :=
  natPolyAt_congr fun _ hi => ce_byte s (R := pR p) h hD hDs (show 1024 ≤ 2 ^ 64 by decide) hi

theorem ce_reduced (s : State) {D : Nat} {p : Addr} (h : (below (s.gpr .rsp) D).Disjoint (pR p)) (hD : 8 ≤ D)
    (hDs : D < 2 ^ 32) : Reduced s.callEntry.mem p ↔ Reduced s.mem p :=
  ⟨reduced_congr fun _ hi => (ce_byte s (R := pR p) h hD hDs (show 1024 ≤ 2 ^ 64 by decide) hi).symm,
    reduced_congr fun _ hi => ce_byte s (R := pR p) h hD hDs (show 1024 ≤ 2 ^ 64 by decide) hi⟩

theorem ce_bytesAt (s : State) {D : Nat} {p : Addr} {n : Nat} (hn : n ≤ 2 ^ 64)
    (h : (below (s.gpr .rsp) D).Disjoint ⟨p, n⟩) (hD : 8 ≤ D) (hDs : D < 2 ^ 32) :
    bytesAt s.callEntry.mem p n = bytesAt s.mem p n :=
  VG.Proof.MlKem.bytesAt_congr fun _ hi => ce_byte s (R := ⟨p, n⟩) h hD hDs hn hi

/-! ## A call, with the moves of its arguments -/

/-- The moves of the arguments, then a call of verified code. -/
theorem glueCall_ok {D : Nat} {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : 8 * (c.depth + 1) ≤ D) (hD : D < 2 ^ 32) {s : State} {V : State → Prop}
    (hg : WP isa (.block glue) s fun s1 => (V s1 ∧ s1.mem = s.mem) ∧ Keep argRegs s s1)
    {rd wr : List Region} (hpre : ∀ s1, V s1 → s1.mem = s.mem → Keep argRegs s s1 →
      k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.seq (.block glue) (.call n c)) s fun s' => PostB D s s' wr ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ∃ s1, V s1 ∧ s1.mem = s.mem ∧ Keep argRegs s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧ k.post (s1.callEntry.withRegions rd wr) s₂ := by
  refine WP.seq (WP.mono hg fun s1 ⟨⟨hV, hm⟩, k1⟩ => ?_)
  refine WP.call hv hsp (by omega_using [hd, hD]) (hpre s1 hV hm k1) (by rw [k1.2.1, k1.2.2]; exact hc)
    (by rw [k1.2.2]; exact hw) fun s' hrd hwr hcs hf _ hpost => ⟨⟨hrd.trans k1.2.1, hwr.trans k1.2.2,
      fun r hr => by rw [hcs r (bases_cs r hr), k1.gpr (argRegs_cs r (bases_cs r hr))],
      by rw [hcs .rsp (by decide), k1.gpr (by decide)], ?_⟩,
      fun r hr => by rw [hcs r hr, k1.gpr (argRegs_cs r hr)], s1, hV, hm, k1, hpost⟩
  have hsp1 : s1.gpr .rsp = s.gpr .rsp := k1.gpr (by decide)
  rw [hm, hsp1] at hf
  exact Frame.below_mono hf hd (by omega_using [hD])

/-- The trace of the moves then a call, from two runs where the moves are
the same and the callee's public data agree. -/
theorem glueCall_tr {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} {V : State → State → Prop}
    (hgt : RelCT isa P (.block glue) fun _ _ => True)
    (hg : ∀ x y, P x y → WP isa (.block glue) x (V x) ∧ WP isa (.block glue) y (V y))
    (hP : ∀ x y x1 y1, P x y → V x x1 → V y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (.seq (.block glue) (.call n c)) fun _ _ => True :=
  RelCT.seq (VG.Proof.MlKem.X86_64.RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ V x x1 ∧ V y y1) hgt hg
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callEx hv hct fun x1 y1 ⟨x, y, hp, h1, h2⟩ => hP x y x1 y1 hp h1 h2)

/-- A call of verified code whose result is public in its own runs, narrowed
in each run to regions of its own: the same trace, and the same result. -/
theorem RelCT.callRet {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.callEntry.withRegions rd₁ wr₁) ∧ k.pre (s₂.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (s₁.callEntry.withRegions rd₁ wr₁) (s₂.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (.call n c) fun s₁ s₂ => (s₁.gpr .rax).setWidth 32 = (s₂.gpr .rax).setWidth 32 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂, hsp⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      -- Each run is the widening of the narrowed run.
      have narrow : ∀ {s : State} {rd wr : List Region} {t : List Leak} {s' : State},
          k.pre (s.callEntry.withRegions rd wr) → Covers (rd ++ wr) (s.rd ++ s.wr) → Covers wr s.wr →
          Exec isa c s.callEntry t s' → ∃ s'', Exec isa c (s.callEntry.withRegions rd wr) t s'' ∧
            s''.gpr = s'.gpr := by
        intro s rd wr t s' hpre hc hw he
        obtain ⟨t', s'', he', -⟩ := hv _ hpre
        have hw' := Exec.widen he' (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
        simp only [State.withRegions_withRegions] at hw'
        rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl] at hw'
        obtain ⟨rfl, rfl⟩ := Exec.det he hw'
        exact ⟨_, he', rfl⟩
      obtain ⟨n₁, x₁, g₁⟩ := narrow p₁ c₁ w₁ b₁
      obtain ⟨n₂, x₂, g₂⟩ := narrow p₂ c₂ w₂ b₂
      obtain ⟨ht, hrax⟩ := hr _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ x₁ x₂
      have q₁ := VG.X86_64.ret_rsp r₁
      have q₂ := VG.X86_64.ret_rsp r₂
      simp only [State.callEntry_rsp] at q₁ q₂
      refine ⟨?_, ?_⟩
      · simp only [q₁, q₂, hsp, ht]
      · simp only [isa, ret] at r₁ r₂
        split at r₁ <;> [skip; cases r₁]
        split at r₂ <;> [skip; cases r₂]
        cases r₁; cases r₂
        simp only [State.setReg]
        rw [← g₁, ← g₂]; exact hrax

/-- The moves of the arguments then a call whose result is public: the same
trace, and the same result, in both runs. -/
theorem glueCallRet_tr {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {P : State → State → Prop} {V : State → State → Prop}
    (hgt : RelCT isa P (.block glue) fun _ _ => True)
    (hg : ∀ x y, P x y → WP isa (.block glue) x (V x) ∧ WP isa (.block glue) y (V y))
    (hP : ∀ x y x1 y1, P x y → V x x1 → V y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (.seq (.block glue) (.call n c))
      fun s₁ s₂ => (s₁.gpr .rax).setWidth 32 = (s₂.gpr .rax).setWidth 32 :=
  RelCT.seq (VG.Proof.MlKem.X86_64.RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ V x x1 ∧ V y y1) hgt hg
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callRet hv hr fun x1 y1 ⟨x, y, hp, h1, h2⟩ => hP x y x1 y1 hp h1 h2)

end VG.Proof.MlDsa.X86_64.Sign

end

end

/-!
# ML-DSA signing on x86-64: the moves of a call's arguments

`setArgs as` moves each argument (a pointer or an immediate) into its
register: afterwards each argument register holds the argument's value in the
state before the moves (`setArgs_ok`), and nothing else changed but those
registers. With it, a call of verified code (`callP_ok`, `callP_tr`,
`callPRet_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)
open VG.Spec.MlDsa

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega_using [h]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [h]

theorem sw_ofNat {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_using [h])]

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.X86_64.Sign.Arg.val (s : State) : Arg → BitVec 64
  | .ptr p => pa s p
  | .imm v => BitVec.ofNat 64 v

/-- A pointer in a register of `bases`, with an offset that is an
immediate; or an immediate of 32 bits. -/
def _root_.VG.Impl.MlDsa.X86_64.Sign.Arg.ok : Arg → Bool
  | .ptr p => decide (p.1 ∈ bases) && decide (p.2 < 2 ^ 31)
  | .imm v => decide (v < 2 ^ 32)

theorem Arg.mov_ok (d : Reg) (a : Arg) (ha : a.ok = true) (hd : d ∈ argRegs6) (s : State) :
    WP isa (.block (a.mov d)) s fun s1 => (s1.gpr d = a.val s ∧ s1.mem = s.mem) ∧ Keep [d] s s1 := by
  have hd' : d ∉ bases := fun h => by revert h hd; cases d <;> decide
  refine WP.keep [d] ?_ (by cases a <;> cases d <;> rfl)
  cases a with
  | ptr p =>
    simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at ha
    have hne : p.1 ≠ d := fun e => hd' (e ▸ ha.1)
    simp only [Arg.mov, lea, Arg.val]
    xrun [sx_ofNat ha.2]
  | imm v =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    simp only [Arg.mov, movi, Arg.val]
    xrun [sw_ofNat ha]

theorem setArgsGen_ok : ∀ (ds : List Reg) (as : List Arg), ds.Nodup → (∀ d ∈ ds, d ∈ argRegs6) →
    as.all Arg.ok = true → ∀ s : State,
    WP isa (.block ((ds.zip as).flatMap fun (d, a) => a.mov d)) s fun s1 =>
      ((∀ da ∈ ds.zip as, s1.gpr da.1 = da.2.val s) ∧ s1.mem = s.mem) ∧ Keep ds s s1
  | [], _, _, _, _, s => WP.block_nil ⟨⟨fun _ h => by simp at h, rfl⟩, Keep.refl _ _⟩
  | _ :: _, [], _, _, _, s => WP.block_nil ⟨⟨fun _ h => by simp at h, rfl⟩, Keep.refl _ _⟩
  | d :: ds, a :: as, hn, hd, ha, s => by
    rw [List.nodup_cons] at hn
    simp only [List.all_cons, Bool.and_eq_true] at ha
    simp only [List.zip_cons_cons, List.flatMap_cons]
    rw [WP.block_append_iff]
    refine WP.mono (Arg.mov_ok d a ha.1 (hd d (List.mem_cons_self ..)) s) fun s1 ⟨⟨h1, hm1⟩, k1⟩ => ?_
    refine WP.mono (setArgsGen_ok ds as hn.2 (fun d' h => hd d' (List.mem_cons_of_mem _ h)) ha.2 s1)
      fun s2 ⟨⟨h2, hm2⟩, k2⟩ => ⟨⟨fun da hda => ?_, hm2.trans hm1⟩, (k1.trans k2).mono fun r hr => by simpa using hr⟩
    -- The values in `s1` are those in `s`: the moves keep the bases.
    have hval : ∀ b : Arg, b.ok = true → b.val s1 = b.val s := fun b hb => by
      cases b with
      | ptr p =>
        simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at hb
        simp only [Arg.val, pa]
        have hdb : d ∉ bases := fun h => by have := hd d (List.mem_cons_self ..); revert h this; cases d <;> decide
        rw [k1.gpr (by simp only [List.mem_singleton]; exact fun e => hdb (e ▸ hb.1))]
      | imm v => rfl
    rcases List.mem_cons.mp hda with rfl | hda
    · rw [k2.gpr hn.1, h1]
    · have := List.of_mem_zip hda
      rw [h2 da hda, hval da.2 (List.all_eq_true.mp ha.2 _ this.2)]

theorem argRegs6_nodup : argRegs6.Nodup := by decide


/-- The moves of the arguments `as`. -/
theorem setArgs_ok (as : List Arg) (ha : as.all Arg.ok = true) (s : State) :
    WP isa (.block (setArgs as)) s fun s1 =>
      ((∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  refine WP.mono (setArgsGen_ok argRegs6 as argRegs6_nodup (fun _ h => h) ha s) fun s1 ⟨h, k⟩ => ⟨h, ?_⟩
  refine ⟨fun r hr => k.gpr fun hm => hr ?_, k.2⟩
  simp only [argRegs6, argRegs, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  rcases hm with h | h | h | h | h | h <;> simp [h]

theorem setArgs_nomem (as : List Arg) : ∀ i ∈ setArgs as, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [setArgs, List.mem_flatMap] at hi
  obtain ⟨⟨d, a⟩, _, hi⟩ := hi
  cases a with
  | ptr p => exact lea_nomem d p i hi s
  | imm v => exact movi_nomem d v i hi s

/-! ## Calls -/

/-- The arguments of `as`, in their registers after the moves. -/
abbrev ArgsIn (as : List Arg) (s s1 : State) : Prop := ∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s

theorem argsIn2 {a b : Arg} {s s1 : State} (h : ArgsIn [a, b] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6])⟩

theorem argsIn3 {a b c : Arg} {s s1 : State} (h : ArgsIn [a, b, c] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6])⟩

theorem argsIn4 {a b c d : Arg} {s s1 : State} (h : ArgsIn [a, b, c, d] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6])⟩

theorem argsIn5 {a b c d e : Arg} {s s1 : State} (h : ArgsIn [a, b, c, d, e] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s ∧
      s1.gpr .r8 = e.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6]), h (.r8, e) (by simp [argRegs6])⟩

theorem argsIn6 {a b c d e f : Arg} {s s1 : State} (h : ArgsIn [a, b, c, d, e, f] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s ∧
      s1.gpr .r8 = e.val s ∧ s1.gpr .r9 = f.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6]), h (.r8, e) (by simp [argRegs6]), h (.r9, f) (by simp [argRegs6])⟩

theorem callP_ok {D : Nat} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : 8 * (c.depth + 1) ≤ D) (hD : D < 2 ^ 32) {as : List Arg} (ha : as.all Arg.ok = true)
    {s : State} {rd wr : List Region}
    (hpre : ∀ s1, ArgsIn as s s1 → s1.mem = s.mem → Keep argRegs s s1 → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (callP n c as) s fun s' => PostB D s s' wr ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ∃ s1, ArgsIn as s s1 ∧ s1.mem = s.mem ∧ Keep argRegs s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧ k.post (s1.callEntry.withRegions rd wr) s₂ :=
  glueCall_ok hv hsp hd hD (setArgs_ok as ha s) hpre hc hw

theorem callP_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → (ArgsIn as x x1 ∧ x1.mem = x.mem) ∧ Keep argRegs x x1 →
      (ArgsIn as y y1 ∧ y1.mem = y.mem) ∧ Keep argRegs y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (callP n c as) fun _ _ => True :=
  glueCall_tr hv hct (block_nomem_tr (setArgs_nomem as)) (fun x y _ => ⟨setArgs_ok as ha x, setArgs_ok as ha y⟩) hP

theorem callPRet_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {as : List Arg} (ha : as.all Arg.ok = true) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → (ArgsIn as x x1 ∧ x1.mem = x.mem) ∧ Keep argRegs x x1 →
      (ArgsIn as y y1 ∧ y1.mem = y.mem) ∧ Keep argRegs y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (callP n c as) fun s₁ s₂ => (s₁.gpr .rax).setWidth 32 = (s₂.gpr .rax).setWidth 32 :=
  glueCallRet_tr hv hr (block_nomem_tr (setArgs_nomem as)) (fun x y _ => ⟨setArgs_ok as ha x, setArgs_ok as ha y⟩)
    hP

end VG.Proof.MlDsa.X86_64.Sign
